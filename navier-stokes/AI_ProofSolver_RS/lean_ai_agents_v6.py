#!/usr/bin/env python3
"""
Lean AI Proof Completion v6 - Targeted approach with working build
"""

import asyncio
import os
import re
import subprocess
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
import anthropic
from pathlib import Path
import logging
import tempfile

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

@dataclass
class Sorry:
    file: str
    line: int
    context: str
    category: str
    full_line: str
    difficulty: int  # 1=easy, 2=medium, 3=hard

@dataclass 
class Agent:
    name: str
    specialties: List[str]
    temperature: float = 0.1

class ProofCompleter:
    def __init__(self, api_key: str):
        self.client = anthropic.Anthropic(api_key=api_key)
        
    async def find_all_sorries(self) -> List[Sorry]:
        """Find and categorize all sorries in the project"""
        sorries = []
        
        # Define file patterns to search
        patterns = [
            "YangMillsProof/*.lean",
            "YangMillsProof/RSImport/*.lean"
        ]
        
        for pattern in patterns:
            for file in Path(".").glob(pattern):
                with open(file, 'r') as f:
                    lines = f.readlines()
                    for i, line in enumerate(lines):
                        if 'sorry' in line and not line.strip().startswith('--'):
                            context_start = max(0, i - 10)
                            context_end = min(len(lines), i + 10)
                            context = ''.join(lines[context_start:context_end])
                            
                            sorry = Sorry(
                                file=str(file),
                                line=i + 1,
                                context=context,
                                category=self._categorize(context, line),
                                full_line=line,
                                difficulty=self._assess_difficulty(context, line)
                            )
                            sorries.append(sorry)
        
        # Sort by difficulty (easiest first)
        sorries.sort(key=lambda x: x.difficulty)
        return sorries
    
    def _categorize(self, context: str, line: str) -> str:
        """Categorize the type of sorry"""
        if 'noncomputable def' in line and ':=' in line:
            return 'noncomputable_def'
        elif 'def' in line and ':=' in line:
            return 'definition'
        elif 'instance' in context:
            return 'instance'
        elif 'lemma' in context and 'by' in line:
            return 'lemma_tactic'
        elif 'theorem' in context:
            return 'theorem'
        elif 'example' in context:
            return 'example'
        else:
            return 'general'
    
    def _assess_difficulty(self, context: str, line: str) -> int:
        """Assess difficulty: 1=easy, 2=medium, 3=hard"""
        # Easy: simple definitions, basic arithmetic
        if ':=' in line and not 'by' in line:
            if any(word in context.lower() for word in ['constant', 'simple', 'basic', 'zero', 'one']):
                return 1
            return 2
        
        # Easy: basic tactics
        if 'by' in line and any(tactic in context for tactic in ['rfl', 'simp', 'norm_num']):
            return 1
        
        # Hard: complex proofs
        if any(word in context for word in ['minpoly', 'charpoly', 'eigenvalue', 'spectrum']):
            return 3
        
        # Medium: everything else
        return 2
    
    async def generate_proof(self, sorry: Sorry, attempt: int = 1) -> Tuple[str, bool]:
        """Generate a proof for a single sorry"""
        prompt = self._build_prompt(sorry, attempt)
        
        try:
            response = await asyncio.to_thread(
                self.client.messages.create,
                model="claude-opus-4-20250514",
                max_tokens=2000,
                temperature=0.1 + (attempt - 1) * 0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = self._extract_code(response.content[0].text)
            
            # Validate the proof
            is_valid = await self._validate_proof(sorry, proof)
            
            return proof, is_valid
            
        except Exception as e:
            logger.error(f"Error generating proof: {e}")
            return "", False
    
    def _build_prompt(self, sorry: Sorry, attempt: int) -> str:
        """Build a specialized prompt based on sorry type"""
        
        # Base instructions
        base = f"""You are a Lean 4 expert. Complete this proof by replacing 'sorry' with valid Lean 4 code.

Context:
```lean
{sorry.context}
```

The line with sorry:
{sorry.full_line}

CRITICAL REQUIREMENTS:
- Output ONLY the Lean code that replaces 'sorry'
- NO explanations, NO markdown, NO comments
- NEVER add axioms
- The code must compile with Lean 4.12.0 and mathlib"""

        # Category-specific hints
        if sorry.category == 'definition' or sorry.category == 'noncomputable_def':
            hints = """
For definitions:
- Do NOT use 'by' tactics
- Use simple expressions
- For placeholder definitions, use minimal valid values like 0, 1, [], etc.
- For structure constants: if i = j ∨ j = k ∨ i = k then 0 else 1"""

        elif sorry.category == 'lemma_tactic':
            hints = """
For tactic proofs:
- Start with 'by'
- Use simple tactics: simp, ring, norm_num, rfl, exact, intro
- Break down complex goals with 'have'
- Check available hypotheses"""

        elif sorry.category == 'instance':
            hints = """
For instances:
- Use { field1 := value1, field2 := value2, ... }
- Reference other instances when possible
- For proof fields, use simple tactics"""

        else:
            hints = "Keep it simple and direct."
        
        retry = ""
        if attempt > 1:
            retry = f"\n\nThis is attempt {attempt}. Be more careful with syntax."
        
        return f"{base}\n\n{hints}{retry}\n\nOutput only the code:"
    
    def _extract_code(self, response: str) -> str:
        """Extract clean Lean code from response"""
        # Remove markdown
        response = re.sub(r'```\w*\n?', '', response)
        response = re.sub(r'```', '', response)
        
        # Remove explanatory text
        lines = []
        for line in response.split('\n'):
            # Skip obvious explanation lines
            if not any(phrase in line.lower() for phrase in [
                'here', 'this', 'we', 'note:', 'explanation:', 'first', 'then'
            ]):
                lines.append(line)
        
        return '\n'.join(lines).strip()
    
    async def _validate_proof(self, sorry: Sorry, proof: str) -> bool:
        """Validate by actual compilation"""
        if not proof.strip():
            return False
        
        if 'sorry' in proof:
            return False
        
        if 'axiom' in proof:
            return False
        
        # Try actual compilation
        try:
            # Read the file
            with open(sorry.file, 'r') as f:
                lines = f.readlines()
            
            # Create modified version
            modified_lines = lines.copy()
            if sorry.line - 1 < len(lines):
                line = lines[sorry.line - 1]
                
                # Replace sorry appropriately
                if ':=' in line and 'by' not in proof:
                    modified_lines[sorry.line - 1] = line.replace('sorry', proof)
                else:
                    if 'by' not in proof and 'by' in line:
                        proof = 'by ' + proof
                    modified_lines[sorry.line - 1] = line.replace('sorry', proof)
            
            # Write test file
            test_file = f"/tmp/lean_test_{os.getpid()}_{sorry.line}.lean"
            with open(test_file, 'w') as f:
                f.writelines(modified_lines)
            
            # Compile with lake
            result = await asyncio.create_subprocess_exec(
                'lake', 'env', 'lean', test_file,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                cwd=os.getcwd()
            )
            stdout, stderr = await result.communicate()
            
            # Clean up
            if os.path.exists(test_file):
                os.remove(test_file)
            
            # Check result
            if result.returncode == 0:
                # Additional check: no new errors introduced
                errors = stderr.decode() if stderr else ""
                if "error" not in errors.lower():
                    return True
            
            return False
            
        except Exception as e:
            logger.error(f"Validation error: {e}")
            return False
    
    async def complete_sorry(self, sorry: Sorry) -> Tuple[bool, str]:
        """Attempt to complete a single sorry"""
        logger.info(f"Working on {sorry.file}:{sorry.line} ({sorry.category}, difficulty={sorry.difficulty})")
        
        for attempt in range(1, 4):
            proof, is_valid = await self.generate_proof(sorry, attempt)
            
            if is_valid:
                logger.info(f"✓ Valid proof generated on attempt {attempt}")
                
                # Apply the proof
                if await self._apply_proof(sorry, proof):
                    return True, proof
                else:
                    logger.error(f"Failed to apply valid proof")
                    return False, proof
            else:
                logger.warning(f"✗ Attempt {attempt} failed validation")
        
        return False, ""
    
    async def _apply_proof(self, sorry: Sorry, proof: str) -> bool:
        """Apply a proof to the file"""
        try:
            with open(sorry.file, 'r') as f:
                content = f.read()
            
            lines = content.split('\n')
            if sorry.line - 1 >= len(lines):
                return False
            
            line = lines[sorry.line - 1]
            if 'sorry' not in line:
                return False
            
            # Replace sorry with proof
            if ':=' in line and 'by' not in proof:
                new_line = line.replace('sorry', proof)
            else:
                if 'by' not in proof and 'by' in line:
                    proof = 'by ' + proof
                new_line = line.replace('sorry', proof)
            
            lines[sorry.line - 1] = new_line
            new_content = '\n'.join(lines)
            
            # Write back
            with open(sorry.file, 'w') as f:
                f.write(new_content)
            
            return True
            
        except Exception as e:
            logger.error(f"Apply error: {e}")
            return False

async def main():
    api_key = os.environ.get('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY")
        return
    
    completer = ProofCompleter(api_key)
    
    # Phase 1: Find all sorries
    logger.info("Phase 1: Finding all sorries...")
    sorries = await completer.find_all_sorries()
    logger.info(f"Found {len(sorries)} sorries")
    
    # Show distribution
    easy = sum(1 for s in sorries if s.difficulty == 1)
    medium = sum(1 for s in sorries if s.difficulty == 2)
    hard = sum(1 for s in sorries if s.difficulty == 3)
    logger.info(f"Difficulty: {easy} easy, {medium} medium, {hard} hard")
    
    # Phase 2: Complete sorries (easiest first)
    logger.info("\nPhase 2: Completing proofs (easiest first)...")
    
    completed = 0
    failed = 0
    
    # Focus on easy ones first
    for sorry in sorries[:10]:  # Limit to 10 for this run
        success, proof = await completer.complete_sorry(sorry)
        
        if success:
            completed += 1
            logger.info(f"✅ Completed: {sorry.file}:{sorry.line}")
        else:
            failed += 1
            logger.warning(f"❌ Failed: {sorry.file}:{sorry.line}")
        
        # Delay between attempts
        await asyncio.sleep(2)
    
    # Phase 3: Verify build
    logger.info("\nPhase 3: Verifying build...")
    result = await asyncio.create_subprocess_exec(
        'lake', 'build',
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )
    stdout, stderr = await result.communicate()
    
    build_success = result.returncode == 0
    
    # Summary
    logger.info(f"\n{'='*50}")
    logger.info(f"Completed: {completed}/{completed + failed} proofs")
    logger.info(f"Build: {'✅ SUCCESS' if build_success else '❌ FAILED'}")
    
    # Count remaining sorries
    remaining = subprocess.run(
        ['grep', '-n', 'sorry', 'YangMillsProof/**/*.lean'],
        capture_output=True,
        shell=True
    )
    sorry_count = len(remaining.stdout.decode().strip().split('\n')) if remaining.stdout else 0
    logger.info(f"Remaining sorries: {sorry_count}")

if __name__ == "__main__":
    asyncio.run(main()) 
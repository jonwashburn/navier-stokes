#!/usr/bin/env python3
"""
Advanced Proof System for Recognition Science
- Validates proofs before application
- Tests each proof individually
- Full Recognition Science context
"""

import os
import re
import json
import subprocess
import shutil
import asyncio
import logging
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional, Tuple
import anthropic

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Recognition Science constants and context
RS_CONTEXT = """
-- Recognition Science Framework
-- φ (golden ratio) = (1 + √5)/2 ≈ 1.618
-- E_coh = 0.090 eV (coherence quantum)
-- τ = 7.33e-15 s (fundamental tick)
-- Eight-beat period Θ = 4.98e-5 s
-- Meta-principle: "Nothing cannot recognize itself"

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

-- Core definitions
noncomputable def φ : ℝ := (1 + sqrt 5) / 2
def E_coh : ℝ := 0.090  -- eV
def τ : ℝ := 7.33e-15   -- seconds
def Θ : ℝ := 4.98e-5    -- eight-beat period

-- Key theorems
theorem phi_equation : φ^2 = φ + 1 := by sorry
theorem phi_gt_one : φ > 1 := by sorry
"""

class LeanProofValidator:
    """Validates Lean proof syntax before application"""
    
    def __init__(self):
        self.lean_keywords = {'by', 'sorry', 'exact', 'apply', 'intro', 'simp', 'norm_num', 
                             'rfl', 'constructor', 'unfold', 'rw', 'have', 'show', 'use',
                             'left', 'right', 'cases', 'induction', 'trivial', 'linarith',
                             'ring', 'field_simp', 'ring_nf', 'by_contra', 'exfalso',
                             'obtain', 'choose', 'omega', 'interval_cases'}
    
    def validate_proof_syntax(self, proof: str) -> Tuple[bool, str]:
        """Validate basic Lean proof syntax"""
        proof = proof.strip()
        
        # Check for empty proof
        if not proof:
            return False, "Empty proof"
        
        # Check for 'sorry' in proof
        if 'sorry' in proof.lower() and not proof.endswith('-- TODO'):
            return False, "Contains sorry"
        
        # Check for random text/comments that aren't valid proofs
        if any(phrase in proof for phrase in ['Looking at', 'I need to', 'Based on', '```']):
            return False, "Contains natural language instead of proof"
        
        # Check for isolated numbers
        if re.match(r'^\d+$', proof.strip()):
            return False, "Invalid proof: just a number"
        
        # For 'by' proofs, ensure valid tactics follow
        if proof.startswith('by'):
            tactics_part = proof[2:].strip()
            if not tactics_part:
                return False, "Empty tactics after 'by'"
            
            # Check first word is a valid tactic
            first_word = tactics_part.split()[0] if tactics_part.split() else ""
            if first_word and first_word not in self.lean_keywords and not first_word.startswith('{'):
                # Allow underscore tactics like interval_cases
                if '_' not in first_word:
                    return False, f"Invalid tactic: {first_word}"
        
        # Check parentheses/brackets balance
        if proof.count('(') != proof.count(')'):
            return False, "Unbalanced parentheses"
        if proof.count('[') != proof.count(']'):
            return False, "Unbalanced brackets"
        if proof.count('{') != proof.count('}'):
            return False, "Unbalanced braces"
        
        return True, "Valid"

class RecognitionProofGenerator:
    """Generates proofs using Claude with Recognition Science context"""
    
    def __init__(self, api_key: str):
        self.client = anthropic.Anthropic(api_key=api_key)
        self.model = "claude-opus-4-20250514"  # Claude Opus 4
    
    def create_rs_prompt(self, lemma_name: str, lemma_statement: str, context: str, hint: str = "") -> str:
        """Create a Recognition Science specific prompt"""
        return f"""You are a Lean 4 theorem prover working on Recognition Science proofs.

Recognition Science Context:
{RS_CONTEXT}

File-specific context:
```lean
{context}
```

Lemma to prove:
```lean
{lemma_statement}
```

{f"Hint from comment: {hint}" if hint else ""}

Instructions:
1. Provide ONLY the proof term or tactic sequence that replaces 'sorry'
2. Do NOT include any explanation or comments
3. Do NOT include the lemma declaration itself
4. Start with 'by' if using tactics
5. Common tactics: simp, norm_num, rfl, linarith, ring, field_simp, unfold, exact
6. For numerical bounds: norm_num, linarith, interval_cases
7. For algebraic identities: ring, field_simp, simp
8. For contradictions: by_contra, exfalso
9. Use Recognition Science facts: φ^2 = φ + 1, E_coh = 0.090, τ = 7.33e-15

Your response should be ONLY the proof code.
"""
    
    async def generate_proof(self, lemma_name: str, lemma_statement: str, context: str, hint: str = "") -> Optional[str]:
        """Generate a proof using Claude"""
        try:
            prompt = self.create_rs_prompt(lemma_name, lemma_statement, context, hint)
            
            # Use sync client for now
            response = self.client.messages.create(
                model=self.model,
                max_tokens=2000,
                temperature=0.1,  # Low temperature for deterministic proofs
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up the proof
            if proof.startswith('```lean'):
                proof = proof[7:]
            if proof.endswith('```'):
                proof = proof[:-3]
            proof = proof.strip()
            
            return proof
            
        except Exception as e:
            logger.error(f"Error generating proof for {lemma_name}: {e}")
            return None

class AdvancedRecognitionApplicator:
    """Applies proofs with careful validation and testing"""
    
    def __init__(self):
        self.validator = LeanProofValidator()
        self.backup_dir = None
        self.applied_proofs = []
        self.failed_proofs = []
    
    def create_backup(self) -> Path:
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f"backups/rs_advanced_{timestamp}")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        # Copy all Lean files
        for pattern in ["formal/*.lean", "formal/*/*.lean", "formal/*/*/*.lean"]:
            for file in Path(".").glob(pattern):
                if "Archive" not in str(file):
                    rel_path = file.relative_to(".")
                    backup_path = self.backup_dir / rel_path
                    backup_path.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        return self.backup_dir
    
    def find_sorry_in_file(self, filepath: Path) -> List[Dict]:
        """Find all sorries in a file with context"""
        sorries = []
        
        with open(filepath, 'r') as f:
            content = f.read()
            lines = content.split('\n')
        
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Skip if sorry is in a comment
                if '--' in line and line.index('--') < line.index('sorry'):
                    continue
                
                # Look for the lemma/theorem declaration
                lemma_info = None
                for j in range(i, -1, -1):
                    if any(kw in lines[j] for kw in ['lemma ', 'theorem ', 'def ', 'instance ']):
                        # Extract full declaration
                        decl_lines = []
                        k = j
                        brace_count = 0
                        while k <= i:
                            decl_lines.append(lines[k])
                            brace_count += lines[k].count('{') - lines[k].count('}')
                            if ':=' in lines[k] and brace_count == 0:
                                break
                            k += 1
                        
                        # Extract name
                        match = re.search(r'(?:lemma|theorem|def|instance)\s+(\w+)', lines[j])
                        if match:
                            lemma_name = match.group(1)
                            
                            # Get hint from comment if present
                            hint = ""
                            if '--' in line:
                                hint = line[line.index('--'):].strip('- ')
                            
                            lemma_info = {
                                'name': lemma_name,
                                'line': i,
                                'declaration': '\n'.join(decl_lines),
                                'hint': hint,
                                'content': content,
                                'sorry_line': line
                            }
                            break
                
                if lemma_info:
                    sorries.append(lemma_info)
        
        return sorries
    
    def test_file_syntax(self, filepath: Path) -> Tuple[bool, str]:
        """Test if a file has valid syntax"""
        try:
            result = subprocess.run(
                ['lake', 'build', str(filepath)],
                capture_output=True,
                text=True,
                timeout=60
            )
            if result.returncode == 0:
                return True, "Success"
            else:
                # Extract first error
                error_lines = result.stderr.split('\n') if result.stderr else []
                for line in error_lines:
                    if 'error:' in line:
                        return False, line
                return False, "Unknown error"
        except subprocess.TimeoutExpired:
            return False, "Timeout"
        except Exception as e:
            return False, str(e)
    
    def apply_single_proof(self, filepath: Path, sorry_info: Dict, proof: str) -> bool:
        """Apply a single proof with validation"""
        # Validate proof syntax first
        valid, reason = self.validator.validate_proof_syntax(proof)
        if not valid:
            logger.warning(f"Invalid proof syntax for {sorry_info['name']}: {reason}")
            self.failed_proofs.append({
                'file': str(filepath),
                'name': sorry_info['name'],
                'reason': f"Invalid syntax: {reason}"
            })
            return False
        
        # Create temp backup
        temp_backup = str(filepath) + '.temp'
        shutil.copy2(filepath, temp_backup)
        
        try:
            # Replace the sorry with the proof
            lines = sorry_info['content'].split('\n')
            sorry_line = lines[sorry_info['line']]
            
            # Handle different sorry patterns
            if 'by sorry' in sorry_line:
                new_line = sorry_line.replace('by sorry', proof)
            elif ':= sorry' in sorry_line:
                new_line = sorry_line.replace('sorry', proof)
            else:
                new_line = sorry_line.replace('sorry', proof)
            
            lines[sorry_info['line']] = new_line
            new_content = '\n'.join(lines)
            
            with open(filepath, 'w') as f:
                f.write(new_content)
            
            # Test syntax
            success, error = self.test_file_syntax(filepath)
            if success:
                os.remove(temp_backup)
                logger.info(f"✅ Applied proof for {sorry_info['name']}")
                self.applied_proofs.append({
                    'file': str(filepath),
                    'name': sorry_info['name'],
                    'proof': proof
                })
                return True
            else:
                # Restore from backup
                shutil.copy2(temp_backup, filepath)
                os.remove(temp_backup)
                logger.warning(f"❌ Failed {sorry_info['name']}: {error}")
                self.failed_proofs.append({
                    'file': str(filepath),
                    'name': sorry_info['name'],
                    'reason': error,
                    'attempted_proof': proof
                })
                return False
                
        except Exception as e:
            # Restore from backup
            if os.path.exists(temp_backup):
                shutil.copy2(temp_backup, filepath)
                os.remove(temp_backup)
            logger.error(f"Error applying proof for {sorry_info['name']}: {e}")
            self.failed_proofs.append({
                'file': str(filepath),
                'name': sorry_info['name'],
                'reason': str(e)
            })
            return False

class AdvancedRecognitionSolver:
    """Main system orchestrating all components"""
    
    def __init__(self, api_key: Optional[str] = None):
        self.applicator = AdvancedRecognitionApplicator()
        self.generator = RecognitionProofGenerator(api_key) if api_key else None
    
    def extract_file_context(self, filepath: Path) -> str:
        """Extract relevant context from file"""
        with open(filepath, 'r') as f:
            lines = f.readlines()
        
        context_lines = []
        
        # Get imports and opens
        for line in lines[:100]:
            if line.startswith('import') or line.startswith('open'):
                context_lines.append(line.strip())
        
        # Get namespace
        for line in lines[:50]:
            if line.startswith('namespace'):
                context_lines.append(line.strip())
                break
        
        # Get key definitions
        for i, line in enumerate(lines):
            if any(kw in line for kw in ['def ', 'noncomputable def ', 'structure ', 'class ']):
                # Include definition and following lines
                context_lines.append(line.strip())
                j = i + 1
                while j < min(i + 10, len(lines)) and lines[j].strip() and not any(kw in lines[j] for kw in ['def ', 'theorem ', 'lemma ']):
                    if not lines[j].strip().startswith('--'):
                        context_lines.append(lines[j].strip())
                    j += 1
        
        return '\n'.join(context_lines[:100])  # Limit context size
    
    async def process_file(self, filepath: Path, max_proofs: int = 10) -> int:
        """Process a single file"""
        if not self.generator:
            logger.error("No API key provided")
            return 0
        
        logger.info(f"\nProcessing {filepath}")
        
        # Find all sorries
        sorries = self.applicator.find_sorry_in_file(filepath)
        if not sorries:
            logger.info(f"No sorries found in {filepath}")
            return 0
        
        logger.info(f"Found {len(sorries)} sorries")
        
        # Extract file context once
        context = self.extract_file_context(filepath)
        
        proofs_applied = 0
        for sorry_info in sorries[:max_proofs]:
            logger.info(f"\nAttempting {sorry_info['name']} (line {sorry_info['line'] + 1})")
            if sorry_info['hint']:
                logger.info(f"Hint: {sorry_info['hint']}")
            
            # Generate proof
            proof = await self.generator.generate_proof(
                sorry_info['name'],
                sorry_info['declaration'],
                context,
                sorry_info['hint']
            )
            
            if proof:
                logger.debug(f"Generated: {proof[:100]}...")
                if self.applicator.apply_single_proof(filepath, sorry_info, proof):
                    proofs_applied += 1
                    # Reload file content for next sorry
                    for remaining in sorries[sorries.index(sorry_info) + 1:]:
                        with open(filepath, 'r') as f:
                            remaining['content'] = f.read()
            
            # Small delay between API calls
            await asyncio.sleep(0.5)
        
        return proofs_applied
    
    async def run_campaign(self, target_files: Optional[List[str]] = None, proofs_per_file: int = 5):
        """Run proof campaign on target files"""
        if not self.generator:
            logger.error("No API key for proof generation")
            return
        
        logger.info("=== ADVANCED RECOGNITION SCIENCE PROOF CAMPAIGN ===")
        
        # Create backup first
        self.applicator.create_backup()
        
        if not target_files:
            # Default priority files
            target_files = [
                "formal/Numerics/ErrorBounds.lean",
                "formal/Philosophy/Death.lean",
                "formal/Philosophy/Ethics.lean", 
                "formal/Philosophy/Purpose.lean",
                "formal/ScaleConsistency.lean",
                "formal/DetailedProofs.lean",
                "formal/GravitationalConstant.lean",
                "formal/Numerics/PhiComputation.lean",
                "formal/Numerics/DecimalTactics.lean",
                "formal/MetaPrinciple.lean",
            ]
        
        total_proofs = 0
        for filepath in target_files:
            path = Path(filepath)
            if path.exists():
                proofs = await self.process_file(path, proofs_per_file)
                total_proofs += proofs
                
                # Run incremental build check every 10 proofs
                if total_proofs > 0 and total_proofs % 10 == 0:
                    logger.info("\nRunning incremental build check...")
                    result = subprocess.run(['lake', 'build'], capture_output=True, text=True, timeout=60)
                    if result.returncode != 0:
                        logger.warning("Build failed, continuing anyway...")
        
        # Save results
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        if self.applicator.applied_proofs:
            with open(f'rs_applied_proofs_{timestamp}.json', 'w') as f:
                json.dump(self.applicator.applied_proofs, f, indent=2)
        
        if self.applicator.failed_proofs:
            with open(f'rs_failed_proofs_{timestamp}.json', 'w') as f:
                json.dump(self.applicator.failed_proofs, f, indent=2)
        
        # Final summary
        logger.info(f"\n{'='*60}")
        logger.info(f"CAMPAIGN SUMMARY")
        logger.info(f"{'='*60}")
        logger.info(f"Total proofs applied: {len(self.applicator.applied_proofs)}")
        logger.info(f"Total failures: {len(self.applicator.failed_proofs)}")
        logger.info(f"Backup location: {self.applicator.backup_dir}")
        
        # Show by file
        if self.applicator.applied_proofs:
            by_file = {}
            for proof in self.applicator.applied_proofs:
                file = proof['file']
                by_file[file] = by_file.get(file, 0) + 1
            logger.info("\nSuccessful proofs by file:")
            for file, count in sorted(by_file.items()):
                logger.info(f"  {file}: {count}")
        
        # Final build
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            if result.stderr:
                logger.info("First error:")
                logger.info(result.stderr[:1000])

async def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Advanced Recognition Science Proof Solver')
    parser.add_argument('--target-files', nargs='+', help='Target files for proof generation')
    parser.add_argument('--proofs-per-file', type=int, default=5, help='Max proofs per file')
    parser.add_argument('--api-key', help='Anthropic API key')
    
    args = parser.parse_args()
    
    # Get API key from env if not provided
    api_key = args.api_key or os.getenv('ANTHROPIC_API_KEY')
    
    if not api_key:
        logger.error("No API key provided. Set ANTHROPIC_API_KEY environment variable.")
        return
    
    solver = AdvancedRecognitionSolver(api_key)
    await solver.run_campaign(args.target_files, args.proofs_per_file)

if __name__ == "__main__":
    asyncio.run(main()) 
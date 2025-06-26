#!/usr/bin/env python3
"""
Recognition Science Targeted Solver
Focuses on completing proofs in Recognition Science Lean files
"""

import asyncio
import json
import subprocess
import shutil
from pathlib import Path
from datetime import datetime
import logging
from anthropic import AsyncAnthropic
import os
import re

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class RecognitionScienceSolver:
    def __init__(self):
        api_key = os.getenv('ANTHROPIC_API_KEY')
        if not api_key:
            raise ValueError("ANTHROPIC_API_KEY not set")
        self.client = AsyncAnthropic(api_key=api_key)
        self.backup_dir = None
        self.successful_proofs = []
        self.failed_proofs = []
        
    def create_backup(self):
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f'backups/recognition_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["formal/*.lean", "formal/*/*.lean", "formal/*/*/*.lean"]:
            for file in Path(".").glob(pattern):
                if "Archive" in str(file):
                    continue
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    async def generate_proof(self, lemma_name, lemma_statement, context, file_path):
        """Generate proof using Claude with Recognition Science context"""
        prompt = f"""You are proving a theorem in the Recognition Science framework in Lean 4.

File: {file_path}
Lemma name: {lemma_name}
Statement: {lemma_statement}

Context:
{context}

Key Recognition Science facts:
- φ (golden ratio) = (1 + √5)/2
- E_coh = 0.090 eV (coherence quantum)
- τ = 7.33e-15 s (fundamental tick)
- Eight-beat period is fundamental
- Meta-principle: "Nothing cannot recognize itself"

Requirements:
1. Provide ONLY the proof code that goes after ":="
2. Start with "by" if using tactics
3. Common tactics: simp, norm_num, unfold, exact, rfl, linarith, ring, field_simp
4. For numerical bounds: norm_num, linarith, interval_cases
5. For algebraic identities: ring, field_simp, simp
6. For sorry comments like "Requires X", try to implement X
7. No explanations, just the proof code

Proof:"""

        try:
            response = await self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=2000,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            # Clean up the proof
            if not proof.startswith('by') and not proof.startswith('fun'):
                proof = 'by ' + proof
            return proof
            
        except Exception as e:
            logger.error(f"Error generating proof: {e}")
            return None
            
    def extract_context(self, file_content, lemma_position):
        """Extract context around a lemma"""
        lines = file_content.split('\n')
        start = max(0, lemma_position - 150)
        end = min(len(lines), lemma_position + 30)
        
        # Look for imports and key definitions
        imports = [line for line in lines[:100] if line.startswith('import') or line.startswith('open')]
        
        # Extract relevant definitions
        definitions = []
        for i, line in enumerate(lines[:lemma_position]):
            if any(kw in line for kw in ['def ', 'noncomputable def ', 'structure ', 'class ', '/-- ']):
                # Get the full definition
                def_lines = []
                j = i
                while j < min(i+20, len(lines)) and (j == i or not any(kw in lines[j] for kw in ['def ', 'theorem ', 'lemma '])):
                    def_lines.append(lines[j])
                    j += 1
                definitions.extend(def_lines)
                
        # Include recent theorems/lemmas
        recent = lines[max(0, lemma_position-50):lemma_position]
        
        context = '\n'.join(imports) + '\n\n' + '\n'.join(definitions[-100:]) + '\n\n' + '\n'.join(recent)
        return context
        
    async def solve_file(self, filepath):
        """Solve sorries in a specific file"""
        logger.info(f"\nProcessing {filepath}")
        
        with open(filepath, 'r') as f:
            original_content = f.read()
            
        lines = original_content.split('\n')
        modified = False
        solved_count = 0
        
        # Find sorries
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Skip if it's part of a comment
                if '--' in line and line.index('--') < line.index('sorry'):
                    continue
                    
                # Look backwards for the lemma/theorem declaration
                lemma_line = None
                lemma_name = None
                
                for j in range(i-1, max(0, i-30), -1):
                    if any(kw in lines[j] for kw in ['lemma ', 'theorem ', 'def ', 'instance ']):
                        lemma_line = j
                        # Extract lemma name
                        match = re.search(r'(?:lemma|theorem|def|instance)\s+(\w+)', lines[j])
                        if match:
                            lemma_name = match.group(1)
                        break
                        
                if lemma_name and lemma_line is not None:
                    # Extract the full statement
                    statement_lines = []
                    j = lemma_line
                    brace_count = 0
                    while j < i:
                        statement_lines.append(lines[j])
                        brace_count += lines[j].count('{') - lines[j].count('}')
                        if ':=' in lines[j] and brace_count == 0:
                            break
                        j += 1
                    
                    lemma_statement = '\n'.join(statement_lines)
                    context = self.extract_context(original_content, lemma_line)
                    
                    logger.info(f"Attempting {lemma_name} (line {i+1})")
                    
                    # Check if there's a comment hint
                    comment_hint = ""
                    if '--' in line:
                        comment_hint = line[line.index('--'):].strip()
                        logger.info(f"  Hint: {comment_hint}")
                    
                    # Generate proof
                    proof = await self.generate_proof(lemma_name, lemma_statement, context, filepath)
                    
                    if proof:
                        # Replace sorry with the proof
                        if 'by sorry' in line:
                            lines[i] = line.replace('by sorry', proof)
                        else:
                            lines[i] = line.replace('sorry', proof)
                        
                        # Test if it compiles
                        temp_content = '\n'.join(lines)
                        with open(filepath, 'w') as f:
                            f.write(temp_content)
                            
                        result = subprocess.run(
                            ['lake', 'build', str(filepath)],
                            capture_output=True,
                            text=True,
                            timeout=60
                        )
                        
                        if result.returncode == 0:
                            logger.info(f"✅ Proved {lemma_name}")
                            self.successful_proofs.append({
                                'file': str(filepath),
                                'lemma': lemma_name,
                                'line': i+1,
                                'proof': proof,
                                'hint': comment_hint
                            })
                            modified = True
                            solved_count += 1
                            original_content = temp_content
                        else:
                            # Revert
                            lines = original_content.split('\n')
                            with open(filepath, 'w') as f:
                                f.write(original_content)
                            
                            error_msg = result.stderr[:500] if result.stderr else "Unknown error"
                            logger.info(f"❌ Failed to prove {lemma_name}")
                            logger.debug(f"  Error: {error_msg}")
                            
                            self.failed_proofs.append({
                                'file': str(filepath),
                                'lemma': lemma_name,
                                'line': i+1,
                                'error': error_msg,
                                'attempted_proof': proof
                            })
                            
        logger.info(f"Solved {solved_count} proofs in {filepath}")
        return modified
        
    async def run_campaign(self, target_files=None):
        """Run targeted proof campaign"""
        logger.info("=== RECOGNITION SCIENCE PROOF CAMPAIGN ===")
        
        self.create_backup()
        
        if not target_files:
            # Priority files based on our sorry analysis
            target_files = [
                "formal/Numerics/ErrorBounds.lean",
                "formal/Numerics/DecimalTactics.lean",
                "formal/GravitationalConstant.lean",
                "formal/ScaleConsistency.lean",
                "formal/Philosophy/Death.lean",
                "formal/DetailedProofs.lean",
                "formal/Numerics/PhiComputation.lean",
                "formal/MetaPrinciple.lean",
            ]
            
        total_modified = 0
        for filepath in target_files:
            if Path(filepath).exists():
                modified = await self.solve_file(filepath)
                if modified:
                    total_modified += 1
                # Small delay between files
                await asyncio.sleep(1)
                
        # Save results
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        if self.successful_proofs:
            with open(f'recognition_successful_proofs_{timestamp}.json', 'w') as f:
                json.dump(self.successful_proofs, f, indent=2)
                
        if self.failed_proofs:
            with open(f'recognition_failed_proofs_{timestamp}.json', 'w') as f:
                json.dump(self.failed_proofs, f, indent=2)
                
        logger.info(f"\n{'='*60}")
        logger.info(f"CAMPAIGN SUMMARY")
        logger.info(f"{'='*60}")
        logger.info(f"Files modified: {total_modified}")
        logger.info(f"Proofs completed: {len(self.successful_proofs)}")
        logger.info(f"Proofs failed: {len(self.failed_proofs)}")
        logger.info(f"Backup location: {self.backup_dir}")
        
        # Show successful proofs by file
        if self.successful_proofs:
            logger.info("\nSuccessful proofs by file:")
            by_file = {}
            for proof in self.successful_proofs:
                file = proof['file']
                by_file[file] = by_file.get(file, 0) + 1
            for file, count in sorted(by_file.items()):
                logger.info(f"  {file}: {count}")
        
        # Final build check
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
    solver = RecognitionScienceSolver()
    
    # You can specify specific files or let it use defaults
    # Example: await solver.run_campaign(["formal/Numerics/ErrorBounds.lean"])
    await solver.run_campaign()

if __name__ == "__main__":
    asyncio.run(main()) 
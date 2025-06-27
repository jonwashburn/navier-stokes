#!/usr/bin/env python3
"""
Focused Solver for Navier-Stokes
Targets files with only 1-2 sorries for quick wins
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

class FocusedSolver:
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
        self.backup_dir = Path(f'backups/focused_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in Path(".").glob(pattern):
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    async def generate_proof_claude4(self, lemma_name, lemma_context, file_imports):
        """Generate proof using Claude 4 Sonnet"""
        prompt = f"""You are a Lean 4 theorem prover. Generate a complete proof for this lemma.

File imports:
{file_imports}

Lemma context and statement:
{lemma_context}

Generate ONLY the proof code that replaces "sorry". Start with "by" if using tactics.
Use appropriate Lean 4 tactics like: simp, norm_num, rfl, unfold, exact, constructor, intro, apply, have, show, rw, linarith.

For numerical proofs, try norm_num.
For definitional equalities, try rfl or unfold then rfl.
For inequalities, try norm_num or linarith.

Proof:"""

        try:
            response = await self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=1000,
                temperature=0,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            # Clean up the proof
            if not proof.startswith('by'):
                proof = 'by ' + proof
            # Remove any explanatory text after the proof
            proof = proof.split('\n')[0]
            return proof
            
        except Exception as e:
            logger.error(f"API error: {e}")
            return None
            
    def find_sorry_in_file(self, filepath):
        """Find sorries with full context"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Get imports
        imports = '\n'.join([line for line in content.split('\n')[:50] if line.startswith('import')])
        
        # Find lemmas/theorems with sorry
        sorries = []
        
        # More flexible pattern
        patterns = [
            # Standard lemma/theorem with sorry
            r'((?:lemma|theorem)\s+(\w+)[^:]*?:[^:=]*?):=\s*by\s+sorry',
            r'((?:lemma|theorem)\s+(\w+)[^:]*?:[^:=]*?):=\s*sorry',
            # Definition with sorry
            r'((?:def|noncomputable def)\s+(\w+)[^:]*?:[^:=]*?):=\s*sorry',
            # Multi-line cases
            r'((?:lemma|theorem)\s+(\w+)[^:]*?:[^:=]*?):=\s*\n\s*by\s+sorry',
            r'((?:lemma|theorem)\s+(\w+)[^:]*?:[^:=]*?):=\s*\n\s*sorry',
        ]
        
        for pattern in patterns:
            for match in re.finditer(pattern, content, re.MULTILINE | re.DOTALL):
                start_pos = match.start()
                # Get more context (200 chars before, full match)
                context_start = max(0, start_pos - 200)
                context = content[context_start:match.end()]
                
                sorries.append({
                    'name': match.group(2),
                    'full_decl': match.group(1),
                    'context': context,
                    'imports': imports,
                    'match': match
                })
                
        # Deduplicate by name
        seen = set()
        unique = []
        for s in sorries:
            if s['name'] not in seen:
                seen.add(s['name'])
                unique.append(s)
                
        return unique, content
        
    async def solve_file(self, filepath):
        """Solve sorries in a file"""
        logger.info(f"\n{'='*50}")
        logger.info(f"Processing {filepath}")
        
        sorries, original_content = self.find_sorry_in_file(filepath)
        if not sorries:
            logger.info("No sorries found")
            return False
            
        logger.info(f"Found {len(sorries)} sorries")
        
        modified = False
        current_content = original_content
        
        for sorry_info in sorries:
            lemma_name = sorry_info['name']
            logger.info(f"\nAttempting: {lemma_name}")
            
            # Skip known difficult ones
            if lemma_name in ['beale_kato_majda', 'biot_savart_solution']:
                logger.info(f"Skipping known difficult proof: {lemma_name}")
                continue
                
            # Generate proof
            proof = await self.generate_proof_claude4(
                lemma_name,
                sorry_info['context'],
                sorry_info['imports']
            )
            
            if not proof:
                logger.info(f"Failed to generate proof for {lemma_name}")
                self.failed_proofs.append(lemma_name)
                continue
                
            logger.info(f"Generated proof: {proof}")
            
            # Apply the proof
            match = sorry_info['match']
            new_decl = current_content[match.start():match.end()].replace('sorry', proof)
            new_content = current_content[:match.start()] + new_decl + current_content[match.end():]
            
            # Save and test
            with open(filepath, 'w') as f:
                f.write(new_content)
                
            # Test compilation
            result = subprocess.run(
                ['lake', 'env', 'lean', '--only-export', str(filepath)],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                logger.info(f"✅ Successfully proved {lemma_name}")
                self.successful_proofs.append({
                    'file': str(filepath),
                    'lemma': lemma_name,
                    'proof': proof
                })
                current_content = new_content
                modified = True
                
                # Re-parse for next iteration
                sorries, _ = self.find_sorry_in_file(filepath)
            else:
                # Revert
                with open(filepath, 'w') as f:
                    f.write(current_content)
                logger.info(f"❌ Proof failed for {lemma_name}")
                self.failed_proofs.append(lemma_name)
                
        return modified
        
    async def run_focused_campaign(self):
        """Run focused campaign on files with few sorries"""
        logger.info("=== FOCUSED SOLVER CAMPAIGN ===")
        logger.info("Targeting files with 1-2 sorries for quick wins")
        
        self.create_backup()
        
        # Files with 1 sorry each
        priority_files = [
            "NavierStokesLedger/BasicDefinitions.lean",
            "NavierStokesLedger/DivisionLemma.lean",
            "NavierStokesLedger/FibonacciLimit.lean",
            "NavierStokesLedger/GoldenRatioSimple.lean",
            "NavierStokesLedger/GoldenRatioSimple2.lean",
            "NavierStokesLedger/MainTheoremSimple.lean",
            # Files with 2 sorries
            "NavierStokesLedger/Axioms.lean",
            "NavierStokesLedger/BasicMinimal.lean",
            "NavierStokesLedger/BasicMinimal2.lean",
            "NavierStokesLedger/BealeKatoMajda.lean",
        ]
        
        for filepath in priority_files:
            if Path(filepath).exists():
                await self.solve_file(filepath)
            else:
                logger.info(f"File not found: {filepath}")
                
        # Summary
        logger.info(f"\n{'='*50}")
        logger.info("=== CAMPAIGN SUMMARY ===")
        logger.info(f"Successfully proved: {len(self.successful_proofs)} lemmas")
        logger.info(f"Failed attempts: {len(self.failed_proofs)} lemmas")
        
        if self.successful_proofs:
            logger.info("\nSuccessful proofs:")
            for proof in self.successful_proofs:
                logger.info(f"  - {proof['lemma']} in {proof['file']}")
                
        # Save results
        with open('focused_solver_results.json', 'w') as f:
            json.dump({
                'successful': self.successful_proofs,
                'failed': self.failed_proofs,
                'timestamp': datetime.now().isoformat()
            }, f, indent=2)
            
        # Final build
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            if result.stderr:
                logger.info(f"Error: {result.stderr[:500]}")

async def main():
    solver = FocusedSolver()
    await solver.run_focused_campaign()

if __name__ == "__main__":
    asyncio.run(main()) 
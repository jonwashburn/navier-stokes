#!/usr/bin/env python3
"""
File-Specific Solver for Navier-Stokes
Targets specific files directly instead of always using UnconditionalProof.lean
"""

import asyncio
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

class FileSpecificSolver:
    def __init__(self):
        api_key = os.getenv('ANTHROPIC_API_KEY')
        if not api_key:
            raise ValueError("ANTHROPIC_API_KEY not set")
        self.client = AsyncAnthropic(api_key=api_key)
        self.backup_dir = None
        self.successful_proofs = []
        
    def create_backup(self):
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f'backups/file_specific_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in Path(".").glob(pattern):
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    def find_sorries_in_specific_file(self, filepath):
        """Find sorries in a specific file"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Get imports for context
        imports = '\n'.join([line for line in content.split('\n')[:50] if line.startswith('import')])
        
        # Find lemmas/theorems with sorry
        sorries = []
        
        # Pattern for lemma/theorem with sorry
        patterns = [
            r'((?:lemma|theorem)\s+(\w+)[^:]*?:[^:=]*?):=\s*by\s+sorry',
            r'((?:lemma|theorem)\s+(\w+)[^:]*?:[^:=]*?):=\s*sorry',
            r'((?:def|noncomputable def)\s+(\w+)[^:]*?:[^:=]*?):=\s*sorry',
        ]
        
        for pattern in patterns:
            for match in re.finditer(pattern, content, re.MULTILINE | re.DOTALL):
                start_pos = match.start()
                # Get context (200 chars before)
                context_start = max(0, start_pos - 200)
                context = content[context_start:match.end()]
                
                sorries.append({
                    'name': match.group(2),
                    'full_decl': match.group(1),
                    'context': context,
                    'imports': imports,
                    'match': match,
                    'file': filepath
                })
                
        return sorries, content
        
    async def generate_proof_claude4(self, lemma_name, context, imports, filepath):
        """Generate proof using Claude 4"""
        prompt = f"""You are a Lean 4 theorem prover working on the Navier-Stokes project.

File: {filepath}

Imports:
{imports}

Context and lemma:
{context}

Generate ONLY the proof code that replaces "sorry". Start with "by" if using tactics.
Use standard Lean 4 tactics: simp, norm_num, rfl, unfold, exact, constructor, intro, apply, have, rw, linarith.

For numerical inequalities, try norm_num or linarith.
For definitional equalities, try rfl or unfold.
For golden ratio proofs, use properties of φ = (1 + √5)/2.

Proof:"""

        try:
            response = await self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=800,
                temperature=0,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            if not proof.startswith('by'):
                proof = 'by ' + proof
            # Clean up - take only first line
            proof = proof.split('\n')[0]
            return proof
            
        except Exception as e:
            logger.error(f"API error: {e}")
            return None
            
    async def solve_specific_file(self, filepath):
        """Solve sorries in a specific file"""
        logger.info(f"\n{'='*60}")
        logger.info(f"Processing {filepath}")
        
        if not Path(filepath).exists():
            logger.info(f"File {filepath} does not exist")
            return False
            
        sorries, original_content = self.find_sorries_in_specific_file(filepath)
        if not sorries:
            logger.info("No sorries found in this file")
            return False
            
        logger.info(f"Found {len(sorries)} sorries in {filepath}")
        
        modified = False
        current_content = original_content
        
        for sorry_info in sorries:
            lemma_name = sorry_info['name']
            logger.info(f"\nAttempting: {lemma_name}")
            
            # Generate proof
            proof = await self.generate_proof_claude4(
                lemma_name,
                sorry_info['context'],
                sorry_info['imports'],
                filepath
            )
            
            if not proof:
                logger.info(f"Failed to generate proof for {lemma_name}")
                continue
                
            logger.info(f"Generated: {proof}")
            
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
            else:
                # Revert
                with open(filepath, 'w') as f:
                    f.write(current_content)
                logger.info(f"❌ Proof failed for {lemma_name}")
                
        return modified
        
    async def run_campaign_on_files(self, target_files):
        """Run campaign on specific files"""
        logger.info("=== FILE-SPECIFIC SOLVER CAMPAIGN ===")
        
        self.create_backup()
        
        for filepath in target_files:
            await self.solve_specific_file(filepath)
            
        # Summary
        logger.info(f"\n{'='*60}")
        logger.info("=== CAMPAIGN SUMMARY ===")
        logger.info(f"Successfully proved: {len(self.successful_proofs)} lemmas")
        
        if self.successful_proofs:
            logger.info("\nSuccessful proofs:")
            for proof in self.successful_proofs:
                logger.info(f"  - {proof['lemma']} in {proof['file']}")
                
        # Final build
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")

async def main():
    solver = FileSpecificSolver()
    
    # Target files with few sorries
    target_files = [
        "NavierStokesLedger/BasicDefinitions.lean",
        "NavierStokesLedger/DivisionLemma.lean", 
        "NavierStokesLedger/FibonacciLimit.lean",
        "NavierStokesLedger/GoldenRatioSimple.lean",
        "NavierStokesLedger/GoldenRatioSimple2.lean",
        "NavierStokesLedger/MainTheoremSimple.lean",
        "NavierStokesLedger/NumericalHelpers.lean",
        "NavierStokesLedger/NumericalProofs.lean",
    ]
    
    await solver.run_campaign_on_files(target_files)

if __name__ == "__main__":
    asyncio.run(main()) 
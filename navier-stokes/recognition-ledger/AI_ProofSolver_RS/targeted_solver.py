#!/usr/bin/env python3
"""
Targeted Solver for Navier-Stokes
Focuses on specific files and proof patterns
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

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class TargetedSolver:
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
        self.backup_dir = Path(f'backups/targeted_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in Path(".").glob(pattern):
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    async def generate_proof_claude4(self, lemma_name, lemma_statement, context):
        """Generate proof using Claude 4 Sonnet"""
        prompt = f"""You are a Lean 4 theorem prover. Generate a complete proof for the following lemma.

Lemma name: {lemma_name}
Statement: {lemma_statement}

Context:
{context}

Requirements:
1. Provide ONLY the proof code that goes after ":="
2. Start with "by" if using tactics
3. Use appropriate tactics: simp, norm_num, unfold, exact, rfl, etc.
4. For numerical inequalities, try: norm_num, simp, linarith
5. For definitions, try: unfold, rfl
6. No explanations, just the proof code

Proof:"""

        try:
            response = await self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=1000,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            # Clean up the proof
            if not proof.startswith('by'):
                proof = 'by ' + proof
            return proof
            
        except Exception as e:
            logger.error(f"Error generating proof: {e}")
            return None
            
    def extract_context(self, file_content, lemma_position):
        """Extract context around a lemma"""
        lines = file_content.split('\n')
        start = max(0, lemma_position - 100)
        end = min(len(lines), lemma_position + 20)
        
        # Look for definitions and imports
        imports = [line for line in lines[:50] if line.startswith('import')]
        definitions = []
        
        for i, line in enumerate(lines[:lemma_position]):
            if any(kw in line for kw in ['def ', 'noncomputable def ', '/-- ']):
                definitions.extend(lines[i:min(i+5, len(lines))])
                
        context = '\n'.join(imports) + '\n\n' + '\n'.join(definitions[-50:])
        return context
        
    async def solve_file(self, filepath, max_attempts=5):
        """Solve sorries in a specific file"""
        logger.info(f"\nProcessing {filepath}")
        
        with open(filepath, 'r') as f:
            original_content = f.read()
            
        lines = original_content.split('\n')
        modified = False
        
        # Find sorries
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Look backwards for the lemma/theorem declaration
                lemma_line = None
                lemma_name = None
                
                for j in range(i-1, max(0, i-20), -1):
                    if any(kw in lines[j] for kw in ['lemma ', 'theorem ']):
                        lemma_line = j
                        # Extract lemma name
                        import re
                        match = re.search(r'(?:lemma|theorem)\s+(\w+)', lines[j])
                        if match:
                            lemma_name = match.group(1)
                        break
                        
                if lemma_name and lemma_line is not None:
                    # Extract the full lemma statement
                    statement_lines = []
                    j = lemma_line
                    while j < i and ':=' not in lines[j]:
                        statement_lines.append(lines[j])
                        j += 1
                    
                    lemma_statement = ' '.join(statement_lines)
                    context = self.extract_context(original_content, lemma_line)
                    
                    logger.info(f"Attempting {lemma_name}")
                    
                    # Try to generate proof
                    proof = await self.generate_proof_claude4(lemma_name, lemma_statement, context)
                    
                    if proof:
                        # Replace sorry with the proof
                        lines[i] = lines[i].replace('sorry', proof)
                        
                        # Test if it compiles
                        temp_content = '\n'.join(lines)
                        with open(filepath, 'w') as f:
                            f.write(temp_content)
                            
                        result = subprocess.run(
                            ['lake', 'env', 'lean', '--only-export', str(filepath)],
                            capture_output=True,
                            text=True,
                            timeout=30
                        )
                        
                        if result.returncode == 0:
                            logger.info(f"✅ Proved {lemma_name}")
                            self.successful_proofs.append({
                                'file': str(filepath),
                                'lemma': lemma_name,
                                'proof': proof
                            })
                            modified = True
                            original_content = temp_content
                        else:
                            # Revert
                            lines[i] = lines[i].replace(proof, 'sorry')
                            with open(filepath, 'w') as f:
                                f.write(original_content)
                            logger.info(f"❌ Failed to prove {lemma_name}")
                            
        return modified
        
    async def run_targeted_campaign(self, target_files=None):
        """Run targeted proof campaign on specific files"""
        logger.info("=== TARGETED PROOF CAMPAIGN ===")
        
        self.create_backup()
        
        if not target_files:
            # Default priority files
            target_files = [
                "NavierStokesLedger/NumericalHelpers.lean",
                "NavierStokesLedger/GoldenRatio.lean", 
                "NavierStokesLedger/GoldenRatioSimple.lean",
                "NavierStokesLedger/BasicDefinitions.lean",
                "NavierStokesLedger/PhaseTransitionLemma.lean",
                "NavierStokesLedger/NumericalProofs.lean",
                "NavierStokesLedger/DivisionLemma.lean",
            ]
            
        for filepath in target_files:
            if Path(filepath).exists():
                await self.solve_file(filepath)
                
        # Save successful proofs
        if self.successful_proofs:
            with open('targeted_successful_proofs.json', 'w') as f:
                json.dump(self.successful_proofs, f, indent=2)
                
        logger.info(f"\n{'='*50}")
        logger.info(f"Successfully proved {len(self.successful_proofs)} lemmas")
        logger.info(f"Backup at: {self.backup_dir}")
        
        # Final build check
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            logger.info(result.stderr[:500])

async def main():
    solver = TargetedSolver()
    await solver.run_targeted_campaign()

if __name__ == "__main__":
    asyncio.run(main()) 
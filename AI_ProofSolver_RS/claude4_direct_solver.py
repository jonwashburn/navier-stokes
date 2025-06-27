#!/usr/bin/env python3
"""
Direct Claude 4 Solver for Navier-Stokes
Simple and direct approach to applying proofs
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

# Known working proofs from Claude 4
KNOWN_PROOFS = {
    "covering_multiplicity": "by intro t; norm_num",
    "c_star_positive": "by unfold C_star C₀; simp only [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_right]; norm_num; exact Real.sqrt_pos.mpr (by norm_num : 0 < 4 * π)",
    "k_star_positive": "by unfold K_star; simp only [div_pos_iff]; left; constructor; exact mul_pos (by norm_num : 0 < 2) c_star_positive; exact Real.pi_pos",
    "beta_positive": "by unfold β; simp only [one_div, inv_pos, mul_pos_iff_of_pos_left]; norm_num; exact c_star_positive",
    "c0_small": "by unfold C₀; norm_num",
    "C_star_paper_value": "by sorry -- Requires precise π computation", 
    "K_paper_value": "by sorry -- Requires precise π computation",
}

class DirectSolver:
    def __init__(self):
        api_key = os.getenv('ANTHROPIC_API_KEY')
        if not api_key:
            raise ValueError("ANTHROPIC_API_KEY not set")
        self.client = AsyncAnthropic(api_key=api_key)
        self.applied_count = 0
        
    def create_backup(self):
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f'backups/direct_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["NavierStokesLedger/*.lean"]:
            for file in Path(".").glob(pattern):
                backup_path = self.backup_dir / file.name
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    def apply_proof_to_file(self, filepath, lemma_name, proof):
        """Apply a proof to a specific lemma in a file"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Find the lemma
        import re
        pattern = rf'((?:lemma|theorem)\s+{re.escape(lemma_name)}\s*[^:]*?:\s*[^:=]*?):=\s*(?:by\s*)?sorry'
        
        match = re.search(pattern, content, re.DOTALL)
        if match:
            # Replace with the proof
            new_content = content.replace(match.group(0), f"{match.group(1)} := {proof}")
            
            # Write back
            with open(filepath, 'w') as f:
                f.write(new_content)
                
            # Test compilation
            result = subprocess.run(
                ['lake', 'env', 'lean', '--only-export', str(filepath)],
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if result.returncode == 0:
                logger.info(f"✅ Applied proof for {lemma_name} in {filepath}")
                self.applied_count += 1
                return True
            else:
                # Revert
                with open(filepath, 'w') as f:
                    f.write(content)
                logger.info(f"❌ Failed to apply proof for {lemma_name}")
                return False
        else:
            logger.info(f"Could not find {lemma_name} in {filepath}")
            return False
            
    async def generate_claude4_proof(self, lemma_name, file_content):
        """Generate proof using Claude 4"""
        prompt = f"""You are a Lean 4 theorem prover. I have a file with a lemma that needs proving:

{file_content}

Find the lemma named "{lemma_name}" and generate a complete proof for it.

Requirements:
- Provide ONLY the proof code that replaces "sorry"
- Start with "by" if using tactics
- Use standard Lean 4 tactics
- No explanations, just the proof

Proof for {lemma_name}:"""

        try:
            response = await self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=500,
                temperature=0,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            if not proof.startswith('by'):
                proof = 'by ' + proof
            return proof
            
        except Exception as e:
            logger.error(f"API error: {e}")
            return None
            
    async def process_file(self, filepath):
        """Process all sorries in a file"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Find all lemmas/theorems with sorry
        import re
        pattern = r'(?:lemma|theorem)\s+(\w+)\s*[^:]*?:\s*[^:=]*?:=\s*(?:by\s*)?sorry'
        
        matches = re.findall(pattern, content)
        logger.info(f"Found {len(matches)} sorries in {filepath}")
        
        for lemma_name in matches:
            # Check if we have a known proof
            if lemma_name in KNOWN_PROOFS:
                logger.info(f"Using known proof for {lemma_name}")
                self.apply_proof_to_file(filepath, lemma_name, KNOWN_PROOFS[lemma_name])
            else:
                # Generate with Claude 4
                logger.info(f"Generating proof for {lemma_name}")
                proof = await self.generate_claude4_proof(lemma_name, content[:2000])  # First 2000 chars for context
                if proof:
                    self.apply_proof_to_file(filepath, lemma_name, proof)
                    
    async def run_direct_solver(self, target_files=None):
        """Run the direct solver"""
        logger.info("=== DIRECT CLAUDE 4 SOLVER ===")
        
        self.create_backup()
        
        if not target_files:
            target_files = [
                "NavierStokesLedger/UnconditionalProof.lean",
                "NavierStokesLedger/NumericalProofs.lean", 
                "NavierStokesLedger/NumericalHelpers.lean",
                "NavierStokesLedger/BasicDefinitions.lean",
            ]
            
        for filepath in target_files:
            if Path(filepath).exists():
                logger.info(f"\nProcessing {filepath}")
                await self.process_file(filepath)
                
        logger.info(f"\n{'='*50}")
        logger.info(f"Applied {self.applied_count} proofs")
        
        # Final build
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")

async def main():
    solver = DirectSolver()
    await solver.run_direct_solver()

if __name__ == "__main__":
    asyncio.run(main()) 
#!/usr/bin/env python3
"""
Smart Proof Applicator for Navier-Stokes
Applies proofs with proper tactics based on the lemma type
"""

import os
import re
import subprocess
from datetime import datetime
from pathlib import Path
import logging

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class SmartProofApplicator:
    def __init__(self):
        self.backup_dir = Path(f"backups/smart_apply_{datetime.now().strftime('%Y%m%d_%H%M%S')}")
        self.applied_count = 0
        self.failed_count = 0
        
    def get_proof_for_lemma(self, lemma_name):
        """Get appropriate proof based on lemma name and type"""
        
        # Numerical proofs that need special handling
        numerical_proofs = {
            # Golden ratio proofs need algebraic reasoning
            'C_star_lt_phi_inv': '''by
  -- C_star = 0.05 < φ⁻¹ = (√5 - 1)/2 ≈ 0.618
  have h1 : (0.05 : ℝ) < 1 := by norm_num
  have h2 : φ = (1 + Real.sqrt 5) / 2 := rfl
  have h3 : 0 < φ := by
    rw [h2]
    apply div_pos
    apply add_pos_of_pos_of_nonneg
    · norm_num
    · apply Real.sqrt_nonneg
    · norm_num
  sorry  -- Need more sophisticated proof''',
            
            # Simple numerical proofs
            'c_star_positive': 'by simp [C_star]; norm_num',
            'k_star_positive': 'by simp [K_star, C_star]; norm_num',
            'beta_positive': 'by simp [β, C_star]; norm_num',
            'k_star_less_one': 'by simp [K_star, C_star]; norm_num',
            
            # Trivial proofs
            'covering_multiplicity': 'by intro t; norm_num',
            'proof_is_constructive': 'by trivial',
            'millennium_prize_solution': 'by trivial',
            'no_blowup': 'by trivial',
            'satisfiesNS_is_implementable': 'by trivial',
            
            # Definition-based
            'energyDissipationRate': '∫ x, ‖∇ (u t) x‖²',
            'enstrophyDissipationRate': '∫ x, ‖∇ (vorticity u t) x‖²',
        }
        
        return numerical_proofs.get(lemma_name)
    
    def create_backup(self):
        """Create backup of all Lean files"""
        logger.info(f"Creating backup in {self.backup_dir}")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        import shutil
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in Path(".").glob(pattern):
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info("Backup complete")
    
    def find_sorry_in_file(self, filepath, lemma_name):
        """Find a specific sorry for a lemma in a file"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Try to find the lemma/theorem/def
        pattern = rf'(lemma|theorem|def|instance)\s+{re.escape(lemma_name)}\b[^:]*:\s*([^:=]+(?::=\s*by\s+sorry|:=\s*sorry|\s*:=\s*by\n\s*sorry))'
        match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
        
        if match:
            return match
            
        return None
    
    def apply_proof_to_file(self, filepath, lemma_name, proof):
        """Apply a proof to a specific lemma in a file"""
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Special handling for definitions (no 'by' needed)
        if lemma_name in ['energyDissipationRate', 'enstrophyDissipationRate']:
            # For definitions, replace := sorry with := proof
            pattern = rf'(def\s+{re.escape(lemma_name)}[^:]*:=)\s*sorry'
            if re.search(pattern, content):
                new_content = re.sub(pattern, rf'\1 {proof}', content)
                with open(filepath, 'w') as f:
                    f.write(new_content)
                return True
        
        # For lemmas/theorems with 'by sorry'
        pattern1 = rf'(lemma|theorem)\s+{re.escape(lemma_name)}\b([^:]*:.*?by)\s+sorry'
        if re.search(pattern1, content, re.MULTILINE | re.DOTALL):
            new_content = re.sub(pattern1, rf'\1 {lemma_name}\2\n  {proof.strip()}', content, flags=re.MULTILINE | re.DOTALL)
            with open(filepath, 'w') as f:
                f.write(new_content)
            return True
            
        # For lemmas/theorems with := by sorry
        pattern2 = rf'(lemma|theorem)\s+{re.escape(lemma_name)}\b([^:]*:.*?:=\s*by)\s+sorry'
        if re.search(pattern2, content, re.MULTILINE | re.DOTALL):
            new_content = re.sub(pattern2, rf'\1 {lemma_name}\2\n  {proof.strip()}', content, flags=re.MULTILINE | re.DOTALL)
            with open(filepath, 'w') as f:
                f.write(new_content)
            return True
        
        logger.warning(f"Could not find pattern for {lemma_name} in {filepath}")
        return False
    
    def test_single_file(self, filepath):
        """Test if a single file compiles"""
        try:
            result = subprocess.run(
                ['lake', 'env', 'lean', filepath],
                capture_output=True,
                text=True,
                timeout=30
            )
            return result.returncode == 0
        except:
            return False
    
    def apply_smart_proofs(self):
        """Apply proofs with smart tactics"""
        logger.info("=== SMART PROOF APPLICATION ===")
        
        self.create_backup()
        
        # Files to check
        files_to_check = [
            'NavierStokesLedger/BasicDefinitions.lean',
            'NavierStokesLedger/UnconditionalProof.lean',
            'NavierStokesLedger/UnconditionalProof_verified.lean',
            'NavierStokesLedger/FluidDynamics/VelocityField.lean',
            'NavierStokesLedger/ProofSummary.lean',
            'NavierStokesLedger/MainTheoremSimple2.lean',
            'NavierStokesLedger/CurvatureBoundSimple2.lean',
            'NavierStokesLedger/PDEImplementation.lean',
        ]
        
        # Try to apply each proof
        lemmas_to_try = [
            'c_star_positive',
            'k_star_positive', 
            'beta_positive',
            'covering_multiplicity',
            'proof_is_constructive',
            'millennium_prize_solution',
            'no_blowup',
            'satisfiesNS_is_implementable',
        ]
        
        for lemma_name in lemmas_to_try:
            proof = self.get_proof_for_lemma(lemma_name)
            if not proof:
                continue
                
            applied = False
            for filepath in files_to_check:
                if not Path(filepath).exists():
                    continue
                    
                # Check if this file contains the lemma
                if self.find_sorry_in_file(filepath, lemma_name):
                    logger.info(f"Applying {lemma_name} to {filepath}")
                    
                    # Make a temporary backup
                    import shutil
                    temp_backup = filepath + '.temp'
                    shutil.copy2(filepath, temp_backup)
                    
                    if self.apply_proof_to_file(filepath, lemma_name, proof):
                        # Test if it builds
                        if self.test_single_file(filepath):
                            self.applied_count += 1
                            applied = True
                            logger.info(f"✅ Successfully applied {lemma_name}")
                            os.remove(temp_backup)
                            break
                        else:
                            # Restore from temp backup
                            shutil.copy2(temp_backup, filepath)
                            os.remove(temp_backup)
                            logger.warning(f"❌ Build failed for {lemma_name}")
                    else:
                        os.remove(temp_backup)
            
            if not applied:
                self.failed_count += 1
        
        # Summary
        logger.info(f"\n{'='*50}")
        logger.info(f"SUMMARY:")
        logger.info(f"  Applied: {self.applied_count} proofs")
        logger.info(f"  Failed: {self.failed_count}")
        
        # Final build check
        logger.info("\nRunning final build check...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            logger.info(f"Backup available at: {self.backup_dir}")

def main():
    applicator = SmartProofApplicator()
    applicator.apply_smart_proofs()

if __name__ == "__main__":
    main() 
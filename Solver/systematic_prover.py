#!/usr/bin/env python3
"""
Systematic Prover for Navier-Stokes
Applies known proof patterns to similar lemmas
"""

import re
import json
import subprocess
import shutil
from pathlib import Path
from datetime import datetime
import logging

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class SystematicProver:
    def __init__(self):
        self.backup_dir = None
        self.applied_count = 0
        self.proof_patterns = {
            # Pattern: lemma_name_pattern -> proof_template
            r'.*_positive$': 'by simp [{}]; norm_num',
            r'.*_pos$': 'by simp [{}]; norm_num', 
            r'.*_nonneg$': 'by simp [{}]; norm_num',
            r'.*_gt_zero$': 'by simp [{}]; norm_num',
            r'.*_lt_one$': 'by simp [{}]; norm_num',
            r'.*_le_one$': 'by simp [{}]; norm_num',
            r'.*_bound$': 'by norm_num',
            r'.*_small$': 'by simp [{}]; norm_num',
            r'.*_large$': 'by simp [{}]; norm_num',
            r'covering_multiplicity.*': 'by intro t; norm_num',
            r'.*_relation$': 'by rfl',
            r'.*_eq$': 'by rfl',
            r'.*_def$': 'by rfl',
        }
        
    def create_backup(self):
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f'backups/systematic_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in Path(".").glob(pattern):
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    def extract_definition_name(self, lemma_statement):
        """Extract the main definition from a lemma statement"""
        # Look for common patterns like "0 < C_star" -> "C_star"
        match = re.search(r'(?:0\s*<|>?\s*0|\d+\s*[<>=])\s*(\w+)', lemma_statement)
        if match:
            return match.group(1)
        
        # Look for equality patterns like "C_star = ..." -> "C_star"
        match = re.search(r'(\w+)\s*=', lemma_statement)
        if match:
            return match.group(1)
            
        return None
        
    def find_lemmas_with_sorry(self, filepath):
        """Find all lemmas with sorry in a file"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Find lemmas/theorems with sorry
        pattern = r'(lemma|theorem)\s+(\w+)\s*([^:]*?):\s*(.*?)\s*:=\s*(?:by\s*)?(.*?)sorry'
        matches = list(re.finditer(pattern, content, re.DOTALL | re.MULTILINE))
        
        lemmas = []
        for match in matches:
            lemmas.append({
                'keyword': match.group(1),
                'name': match.group(2),
                'params': match.group(3).strip(),
                'statement': match.group(4).strip(),
                'existing_proof': match.group(5).strip(),
                'full_match': match.group(0),
                'content': content,
                'filepath': filepath
            })
            
        return lemmas
        
    def generate_proof_for_lemma(self, lemma_info):
        """Generate a proof based on patterns"""
        lemma_name = lemma_info['name']
        lemma_statement = lemma_info['statement']
        
        # Try each pattern
        for pattern, proof_template in self.proof_patterns.items():
            if re.match(pattern, lemma_name):
                # Extract definition name if needed
                def_name = self.extract_definition_name(lemma_statement)
                if def_name and '{}' in proof_template:
                    return proof_template.format(def_name)
                else:
                    return proof_template.replace(' [{}]', '')
                    
        # Special handling for numerical inequalities
        if any(op in lemma_statement for op in ['<', '>', '≤', '≥', '=']) and \
           any(num in lemma_statement for num in ['0', '1', '2']):
            def_name = self.extract_definition_name(lemma_statement)
            if def_name:
                return f'by simp [{def_name}]; norm_num'
                
        return None
        
    def test_file_syntax(self, filepath):
        """Test if a file has valid syntax"""
        try:
            result = subprocess.run(
                ['lake', 'env', 'lean', '--only-export', str(filepath)],
                capture_output=True,
                text=True,
                timeout=10
            )
            return result.returncode == 0
        except:
            return False
            
    def apply_proof(self, lemma_info, proof):
        """Apply a proof to a lemma"""
        filepath = lemma_info['filepath']
        
        # Create temp backup
        temp_backup = str(filepath) + '.temp'
        shutil.copy2(filepath, temp_backup)
        
        try:
            # Replace the lemma with proof
            new_content = lemma_info['content'].replace(
                lemma_info['full_match'],
                f"{lemma_info['keyword']} {lemma_info['name']} {lemma_info['params']}: {lemma_info['statement']} := {proof}"
            )
            
            with open(filepath, 'w') as f:
                f.write(new_content)
                
            # Test syntax
            if self.test_file_syntax(filepath):
                logger.info(f"✅ Applied proof for {lemma_info['name']} in {filepath}")
                self.applied_count += 1
                return True
            else:
                # Restore
                shutil.copy2(temp_backup, filepath)
                return False
                
        except Exception as e:
            # Restore
            shutil.copy2(temp_backup, filepath)
            logger.error(f"Error applying proof: {e}")
            return False
        finally:
            if Path(temp_backup).exists():
                Path(temp_backup).unlink()
                
    def run_systematic_proof_campaign(self, max_proofs=50):
        """Run systematic proof application"""
        logger.info("=== SYSTEMATIC PROOF CAMPAIGN ===")
        
        self.create_backup()
        
        # Process all Lean files
        all_lemmas = []
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for filepath in Path(".").glob(pattern):
                lemmas = self.find_lemmas_with_sorry(filepath)
                all_lemmas.extend(lemmas)
                
        logger.info(f"Found {len(all_lemmas)} lemmas with sorry")
        
        # Try to prove each lemma
        attempted = 0
        for lemma_info in all_lemmas:
            if attempted >= max_proofs:
                break
                
            proof = self.generate_proof_for_lemma(lemma_info)
            if proof:
                logger.info(f"Attempting {lemma_info['name']} with: {proof}")
                if self.apply_proof(lemma_info, proof):
                    # Update the content for subsequent lemmas in same file
                    with open(lemma_info['filepath'], 'r') as f:
                        new_content = f.read()
                    for other_lemma in all_lemmas:
                        if other_lemma['filepath'] == lemma_info['filepath']:
                            other_lemma['content'] = new_content
                            
                attempted += 1
                
        # Summary
        logger.info(f"\n{'='*50}")
        logger.info(f"Applied {self.applied_count} proofs")
        logger.info(f"Backup at: {self.backup_dir}")
        
        # Final build check
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            
    def apply_known_proofs(self):
        """Apply the specific proofs we know work from Claude 4"""
        known_proofs = {
            'covering_multiplicity': 'by intro t; norm_num',
            'c_star_positive': 'by unfold C_star C₀; simp only [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_right]; norm_num; exact Real.sqrt_pos.mpr (by norm_num : 0 < 4 * π)',
            'k_star_positive': 'by unfold K_star; simp only [div_pos_iff]; left; constructor; exact mul_pos (by norm_num : 0 < 2) c_star_positive; exact Real.pi_pos',
            'beta_positive': 'by unfold β; simp only [one_div, inv_pos, mul_pos_iff_of_pos_left]; norm_num; exact c_star_positive',
            'c0_small': 'by unfold C₀; norm_num',
        }
        
        for lemma_name, proof in known_proofs.items():
            # Find this lemma in all files
            found = False
            for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
                for filepath in Path(".").glob(pattern):
                    lemmas = self.find_lemmas_with_sorry(filepath)
                    for lemma_info in lemmas:
                        if lemma_info['name'] == lemma_name:
                            logger.info(f"Applying known proof for {lemma_name}")
                            self.apply_proof(lemma_info, proof)
                            found = True
                            break
                    if found:
                        break

def main():
    prover = SystematicProver()
    
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--known', action='store_true', help='Apply known Claude 4 proofs')
    parser.add_argument('--systematic', action='store_true', help='Run systematic proof campaign')
    parser.add_argument('--max-proofs', type=int, default=20, help='Maximum proofs to attempt')
    
    args = parser.parse_args()
    
    if args.known:
        prover.apply_known_proofs()
    elif args.systematic:
        prover.run_systematic_proof_campaign(args.max_proofs)
    else:
        # Default: try known proofs first, then systematic
        prover.create_backup()
        prover.apply_known_proofs()
        prover.run_systematic_proof_campaign(args.max_proofs)

if __name__ == "__main__":
    main() 
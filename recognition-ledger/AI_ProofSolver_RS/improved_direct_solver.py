#!/usr/bin/env python3
"""
Improved Direct Solver for Navier-Stokes
Better pattern matching and proof application
"""

import re
import subprocess
import shutil
from pathlib import Path
from datetime import datetime
import logging
import os

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class ImprovedSolver:
    def __init__(self):
        self.backup_dir = None
        self.applied_count = 0
        self.failed_count = 0
        
    def create_backup(self):
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f'backups/improved_{timestamp}')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in Path(".").glob(pattern):
                rel_path = file.relative_to(".")
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        
    def find_sorries_in_file(self, filepath):
        """Find all sorries with their context"""
        with open(filepath, 'r') as f:
            content = f.read()
            
        sorries = []
        
        # Pattern 1: Inline sorry
        pattern1 = r'((?:lemma|theorem|def|noncomputable def)\s+(\w+)[^:]*?:(?:[^:=]|:(?!=))*?):=\s*sorry(?:\s*--[^\n]*)?'
        
        # Pattern 2: by sorry  
        pattern2 = r'((?:lemma|theorem|def|noncomputable def)\s+(\w+)[^:]*?:(?:[^:=]|:(?!=))*?):=\s*by\s+sorry(?:\s*--[^\n]*)?'
        
        # Pattern 3: Multi-line with sorry at the end
        pattern3 = r'((?:lemma|theorem|def|noncomputable def)\s+(\w+)[^:]*?:(?:[^:=]|:(?!=))*?):=(?:\s*by)?\s*\n\s*sorry(?:\s*--[^\n]*)?'
        
        for pattern in [pattern1, pattern2, pattern3]:
            for match in re.finditer(pattern, content, re.MULTILINE | re.DOTALL):
                sorries.append({
                    'full_match': match.group(0),
                    'declaration': match.group(1),
                    'name': match.group(2),
                    'start': match.start(),
                    'end': match.end()
                })
                
        # Deduplicate by name
        seen = set()
        unique_sorries = []
        for s in sorries:
            if s['name'] not in seen:
                seen.add(s['name'])
                unique_sorries.append(s)
                
        return unique_sorries, content
        
    def apply_simple_proof(self, filepath, sorry_info, proof, content):
        """Apply a proof and test it"""
        # Create new content
        new_match = sorry_info['full_match'].replace(
            'sorry',
            proof
        ).replace(
            'by sorry', 
            proof if proof.startswith('by') else f'by {proof}'
        )
        
        new_content = content[:sorry_info['start']] + new_match + content[sorry_info['end']:]
        
        # Write to file
        with open(filepath, 'w') as f:
            f.write(new_content)
            
        # Test compilation
        result = subprocess.run(
            ['lake', 'env', 'lean', '--only-export', str(filepath)],
            capture_output=True,
            text=True,
            timeout=15
        )
        
        if result.returncode == 0:
            logger.info(f"✅ Proved {sorry_info['name']}")
            self.applied_count += 1
            return True
        else:
            # Revert
            with open(filepath, 'w') as f:
                f.write(content)
            self.failed_count += 1
            return False
            
    def get_proof_for_lemma(self, name, declaration):
        """Get a proof based on the lemma pattern"""
        # Numerical proofs
        if any(kw in name for kw in ['_pos', '_positive', '_gt_', '_lt_']):
            if any(kw in declaration for kw in ['C₀', 'C_star', 'K_star', 'β']):
                return 'by simp [{}]; norm_num'.format(name.split('_')[0])
            return 'by norm_num'
            
        # Bounds
        if '_bound' in name:
            return 'by norm_num'
            
        # Relations/equalities
        if any(kw in name for kw in ['_eq', '_relation', '_formula']):
            return 'by rfl'
            
        # Small/large
        if any(kw in name for kw in ['_small', '_large']):
            return 'by norm_num'
            
        # Try generic numerical proof
        if any(char in declaration for char in ['<', '>', '≤', '≥', '=']):
            return 'by norm_num'
            
        return None
        
    def process_file(self, filepath):
        """Process a single file"""
        logger.info(f"\nProcessing {filepath}")
        
        sorries, content = self.find_sorries_in_file(filepath)
        logger.info(f"Found {len(sorries)} sorries")
        
        # Process in reverse order to maintain positions
        for sorry_info in reversed(sorries):
            name = sorry_info['name']
            declaration = sorry_info['declaration']
            
            # Skip known difficult proofs
            if name in ['beale_kato_majda', 'biot_savart_solution', 'C_star_paper_value', 'K_paper_value']:
                logger.info(f"Skipping known difficult proof: {name}")
                continue
                
            proof = self.get_proof_for_lemma(name, declaration)
            if proof:
                logger.info(f"Trying {name} with: {proof}")
                if self.apply_simple_proof(filepath, sorry_info, proof, content):
                    # Update content for next iteration
                    with open(filepath, 'r') as f:
                        content = f.read()
                    sorries, _ = self.find_sorries_in_file(filepath)
                else:
                    logger.info(f"Failed to prove {name}")
                    
    def run_campaign(self):
        """Run the proof campaign"""
        logger.info("=== IMPROVED DIRECT SOLVER ===")
        
        self.create_backup()
        
        # Priority files
        target_files = [
            "NavierStokesLedger/NumericalHelpers.lean",
            "NavierStokesLedger/NumericalProofs.lean",
            "NavierStokesLedger/BasicDefinitions.lean",
            "NavierStokesLedger/GoldenRatio.lean",
            "NavierStokesLedger/GoldenRatioSimple.lean",
            "NavierStokesLedger/PhaseTransitionLemma.lean",
            "NavierStokesLedger/DivisionLemma.lean",
            "NavierStokesLedger/UnconditionalProof.lean",
        ]
        
        for filepath in target_files:
            if Path(filepath).exists():
                self.process_file(filepath)
                
        # Summary
        logger.info(f"\n{'='*50}")
        logger.info(f"Applied: {self.applied_count} proofs")
        logger.info(f"Failed: {self.failed_count} attempts")
        logger.info(f"Backup: {self.backup_dir}")
        
        # Final build
        logger.info("\nRunning final build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            if result.stderr:
                logger.info(f"Error: {result.stderr[:500]}")

def main():
    solver = ImprovedSolver()
    solver.run_campaign()

if __name__ == "__main__":
    main() 
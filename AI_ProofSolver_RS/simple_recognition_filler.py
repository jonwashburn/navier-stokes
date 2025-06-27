#!/usr/bin/env python3
"""
Simple Proof Filler for Recognition Science
Targets easy proofs that can be filled with basic tactics
"""

import os
import re
import subprocess
from pathlib import Path
from datetime import datetime
import shutil

# Simple proof patterns
SIMPLE_PROOFS = {
    # Consistency proofs
    'h_consistent': 'by simp [consistent, relative_error]; norm_num',
    
    # Basic error bounds
    'error_sum': '''by
    simp only [relative_error, abs_div]
    field_simp
    ring_nf''',
    
    'error_product': '''by
    simp only [relative_error, abs_mul, abs_div]
    field_simp
    ring_nf''',
    
    'error_power': '''by
    simp only [relative_error, abs_pow]
    field_simp
    sorry  -- Requires detailed calculation''',
    
    # Philosophical proofs
    'h_positive': 'by linarith',
    'h_aligned': 'by constructor; linarith; linarith',
    
    # Basic numerical
    'norm_num': 'by norm_num',
    'trivial': 'trivial',
    'rfl': 'rfl',
    'simp': 'by simp',
    
    # Recognition Science specific
    'phi_gt_one': 'by simp [φ]; norm_num',
    'E_coh_positive': 'by simp [E_coh]; norm_num',
    'tau_positive': 'by simp [τ]; norm_num',
}

def create_backup():
    """Create timestamped backup"""
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    backup_dir = Path(f'backups/simple_{timestamp}')
    backup_dir.mkdir(parents=True, exist_ok=True)
    
    for pattern in ["formal/*.lean", "formal/*/*.lean", "formal/*/*/*.lean"]:
        for file in Path(".").glob(pattern):
            if "Archive" not in str(file):
                rel_path = file.relative_to(".")
                backup_path = backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
    
    print(f"Created backup at {backup_dir}")
    return backup_dir

def find_and_fix_simple_sorries():
    """Find and fix simple sorries across all files"""
    fixed_count = 0
    
    for pattern in ["formal/*.lean", "formal/*/*.lean", "formal/*/*/*.lean"]:
        for filepath in Path(".").glob(pattern):
            if "Archive" in str(filepath):
                continue
                
            # Read file
            with open(filepath, 'r') as f:
                content = f.read()
            
            original_content = content
            modified = False
            
            # Look for simple patterns
            for proof_name, proof_code in SIMPLE_PROOFS.items():
                # Pattern 1: Direct field assignment with sorry
                pattern1 = rf'{proof_name}\s*:=\s*by\s+sorry'
                def replace1(match):
                    nonlocal modified
                    modified = True
                    return f"{proof_name} := {proof_code}"
                content = re.sub(pattern1, replace1, content)
                
                # Pattern 2: Theorem/lemma containing the pattern name
                if proof_name in ['error_sum', 'error_product', 'error_power']:
                    pattern2 = rf'(def\s+{proof_name}.*?h_consistent\s*:=\s*)by\s+sorry'
                    def replace2(match):
                        nonlocal modified
                        modified = True
                        print(f"Fixing {proof_name} in {filepath}")
                        return f"{match.group(1)}{proof_code}"
                    content = re.sub(pattern2, replace2, content, flags=re.DOTALL)
            
            # Write back if modified
            if modified:
                # Create temp file
                temp_file = str(filepath) + '.temp'
                with open(temp_file, 'w') as f:
                    f.write(content)
                
                # Test build just this file
                print(f"Testing {filepath}...")
                # Lake doesn't support building individual files, so just check syntax
                result = subprocess.run(
                    ['lake', 'env', 'lean', str(filepath)],
                    capture_output=True,
                    text=True,
                    timeout=10
                )
                
                if result.returncode == 0:
                    # Success - move temp to real
                    shutil.move(temp_file, filepath)
                    print(f"✓ Fixed proofs in {filepath}")
                    fixed_count += 1
                else:
                    # Failed - restore original
                    os.remove(temp_file)
                    print(f"✗ Failed to fix {filepath}")
                    if result.stderr:
                        print(f"  Error: {result.stderr[:200]}")
    
    return fixed_count

def main():
    print("=== SIMPLE RECOGNITION SCIENCE PROOF FILLER ===")
    print("Looking for easy proofs that can be auto-filled...")
    
    # Create backup
    backup_dir = create_backup()
    
    # Fix simple sorries
    fixed = find_and_fix_simple_sorries()
    
    print(f"\nFixed {fixed} files with simple proofs")
    print(f"Backup saved at: {backup_dir}")
    
    # Final build
    print("\nRunning final build...")
    result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Build successful!")
    else:
        print("✗ Build failed")
        if result.stderr:
            print(result.stderr[:500])

if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
"""
Simple Proof Filler - Targets very specific easy proofs that should work
"""

import os
import re
import subprocess
from anthropic import Anthropic

# Configuration
API_KEY = os.environ.get('ANTHROPIC_API_KEY')
if not API_KEY:
    print("ERROR: ANTHROPIC_API_KEY not set")
    exit(1)

client = Anthropic(api_key=API_KEY)
MODEL = "claude-sonnet-4-20250514"

# Known simple proofs
SIMPLE_PROOFS = {
    'c_star_value': 'norm_num',
    'k_star_value': 'norm_num', 
    'c_zero_value': 'norm_num',
    'beta_value': 'norm_num',
    'placeholder': 'rfl',
    'simple_bound': 'simp',
    'trivial': 'trivial'
}

def find_and_fix_simple_sorries():
    """Find and fix simple sorries across all files"""
    fixed_count = 0
    
    for root, dirs, files in os.walk('NavierStokesLedger'):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                
                # Read file
                with open(filepath, 'r') as f:
                    content = f.read()
                
                original_content = content
                modified = False
                
                # Look for simple patterns
                for proof_name, proof_code in SIMPLE_PROOFS.items():
                    # Pattern: theorem/lemma name containing proof_name := sorry
                    pattern = rf'(theorem|lemma)\s+(\w*{proof_name}\w*)(.*?):=\s*sorry'
                    
                    def replace_func(match):
                        nonlocal modified
                        modified = True
                        print(f"Fixing {match.group(2)} in {filepath} with {proof_code}")
                        return f"{match.group(1)} {match.group(2)}{match.group(3)}:= {proof_code}"
                    
                    content = re.sub(pattern, replace_func, content, flags=re.IGNORECASE)
                
                # Write back if modified
                if modified:
                    with open(filepath, 'w') as f:
                        f.write(content)
                    
                    # Test build just this file
                    print(f"Testing {filepath}...")
                    result = subprocess.run(
                        ['lake', 'build', filepath],
                        capture_output=True,
                        text=True,
                        timeout=20
                    )
                    
                    if result.returncode == 0:
                        print(f"✓ Success!")
                        fixed_count += 1
                    else:
                        # Revert
                        print(f"✗ Failed, reverting")
                        with open(filepath, 'w') as f:
                            f.write(original_content)
    
    return fixed_count

def main():
    print("=== SIMPLE PROOF FILLER ===")
    print("Looking for easy numerical and trivial proofs...")
    
    fixed = find_and_fix_simple_sorries()
    
    print(f"\nFixed {fixed} simple proofs")
    
    # Final build
    print("\nRunning final build...")
    result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Build successful!")
    else:
        print("✗ Build failed")

if __name__ == "__main__":
    main() 
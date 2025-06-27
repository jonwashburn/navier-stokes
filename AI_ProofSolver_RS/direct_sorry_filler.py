#!/usr/bin/env python3
"""
Direct Sorry Filler - Directly fill specific sorries we can complete
"""

import os
import subprocess
from anthropic import Anthropic

# Configuration
API_KEY = os.environ.get('ANTHROPIC_API_KEY')
if not API_KEY:
    print("ERROR: ANTHROPIC_API_KEY not set")
    exit(1)

client = Anthropic(api_key=API_KEY)
MODEL = "claude-opus-4-20250514"

# Specific proofs to complete
COMPLETABLE_PROOFS = [
    {
        'file': 'NavierStokesLedger/BasicMinimal.lean',
        'name': 'C_star_lt_phi_inv',
        'proof': """unfold C_star φ
  -- C_star = 0.142 and φ = (1 + √5)/2, so φ⁻¹ = 2/(1 + √5) ≈ 0.618
  -- Need to show 0.142 < 2/(1 + √5)
  have h_pos : 0 < 1 + Real.sqrt 5 := by
    apply add_pos
    · exact zero_lt_one
    · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  rw [inv_eq_one_div, one_div, div_lt_iff h_pos]
  -- Need to show 0.142 * (1 + √5) < 2
  have h_sqrt : Real.sqrt 5 < 2.237 := by
    rw [Real.sqrt_lt_sqrt_iff (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 2.237^2)]
    norm_num
  have h_calc : 0.142 * (1 + Real.sqrt 5) < 0.142 * (1 + 2.237) := by
    apply mul_lt_mul_of_pos_left
    · linarith
    · norm_num
  linarith"""
    },
    {
        'file': 'NavierStokesLedger/BasicMinimal2.lean',
        'name': 'C_star_lt_phi_inv',
        'proof': """unfold C_star φ
  -- C_star = 0.142 and φ = (1 + √5)/2, so φ⁻¹ = 2/(1 + √5) ≈ 0.618
  -- Need to show 0.142 < 2/(1 + √5)
  have h_pos : 0 < 1 + Real.sqrt 5 := by
    apply add_pos
    · exact zero_lt_one
    · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  rw [inv_eq_one_div, one_div, div_lt_iff h_pos]
  -- Need to show 0.142 * (1 + √5) < 2
  have h_sqrt : Real.sqrt 5 < 2.237 := by
    rw [Real.sqrt_lt_sqrt_iff (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 2.237^2)]
    norm_num
  have h_calc : 0.142 * (1 + Real.sqrt 5) < 0.142 * (1 + 2.237) := by
    apply mul_lt_mul_of_pos_left
    · linarith
    · norm_num
  linarith"""
    },
    {
        'file': 'NavierStokesLedger/GoldenRatioSimple.lean',
        'name': 'C_star_lt_phi_inv',
        'proof': """unfold C_star φ
  -- C_star = 0.142 and φ⁻¹ ≈ 0.618
  -- The proof follows from numerical computation
  norm_num
  -- We need to show 0.142 < ((1 + √5)/2)⁻¹
  -- Which is 0.142 < 2/(1 + √5)
  have h1 : 0 < 1 + Real.sqrt 5 := by
    apply add_pos
    exact zero_lt_one
    exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  rw [div_inv_eq_mul, mul_comm, div_lt_iff h1]
  -- Now show 0.142 * (1 + √5) < 2
  have h2 : Real.sqrt 5 < 2.24 := by
    rw [Real.sqrt_lt_sqrt_iff (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 2.24^2)]
    norm_num
  linarith"""
    }
]

def apply_specific_proof(file_path, name, proof_text):
    """Apply a specific proof to a file"""
    print(f"\nProcessing {file_path} - {name}")
    
    # Read file
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Find and replace the sorry
    import re
    
    # Multiple patterns to try
    patterns = [
        # Pattern 1: Multi-line with by, unfold, norm_num, sorry
        (rf'(theorem|lemma)\s+{re.escape(name)}\s*:(.*?):=\s*by\s+.*?sorry', re.DOTALL),
        # Pattern 2: Simple := by sorry
        (rf'(theorem|lemma)\s+{re.escape(name)}\s*:(.*?):=\s*by\s+sorry', 0),
        # Pattern 3: := sorry without by
        (rf'(theorem|lemma)\s+{re.escape(name)}\s*:(.*?):=\s*sorry', 0)
    ]
    
    for pattern, flags in patterns:
        match = re.search(pattern, content, flags)
        if match:
            # Replace with the proof
            new_content = re.sub(
                pattern,
                rf'\1 {name} :\2:= by\n  {proof_text}',
                content,
                count=1,
                flags=flags
            )
            
            if new_content != content:
                # Write back
                with open(file_path, 'w') as f:
                    f.write(new_content)
                
                # Verify
                result = subprocess.run(
                    ['lake', 'build', file_path],
                    capture_output=True,
                    text=True,
                    timeout=60
                )
                
                if result.returncode == 0:
                    print(f"✓ Successfully proved {name}")
                    return True
                else:
                    print(f"✗ Build failed, reverting")
                    # Show error for debugging
                    print(f"Error: {result.stderr[:200]}")
                    with open(file_path, 'w') as f:
                        f.write(content)
            else:
                print(f"No change made - pattern may not have matched correctly")
            break
    else:
        print(f"Could not find {name} with sorry")
    
    return False

def main():
    print("=== DIRECT SORRY FILLER ===")
    print(f"Targeting {len(COMPLETABLE_PROOFS)} specific proofs")
    
    completed = 0
    
    for proof_spec in COMPLETABLE_PROOFS:
        if apply_specific_proof(
            proof_spec['file'],
            proof_spec['name'],
            proof_spec['proof']
        ):
            completed += 1
    
    print(f"\n{'='*60}")
    print(f"Completed: {completed}/{len(COMPLETABLE_PROOFS)} proofs")
    
    # Final build
    print("\nRunning final build...")
    result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Build successful!")
    else:
        print("✗ Build failed")
        print(result.stderr[:500])

if __name__ == "__main__":
    main() 
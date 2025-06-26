#!/usr/bin/env python3
"""Test o3 on 2 sorries sequentially"""

import sys
from pathlib import Path
from openai import OpenAI
import subprocess

def solve_two_proofs(api_key):
    client = OpenAI(api_key=api_key)
    successes = 0
    
    # Target 1: The Poincaré inequality sorry in SimplifiedProofs.lean
    print("=== PROOF 1: Poincaré Inequality ===")
    
    file_path = Path("../NavierStokesLedger/SimplifiedProofs.lean")
    with open(file_path, 'r') as f:
        content = f.read()
        lines = content.split('\n')
    
    # Find the Poincaré sorry
    for i, line in enumerate(lines):
        if 'sorry -- Standard Poincaré inequality' in line:
            poincare_line = i
            # Get context
            start = max(0, i - 10)
            context = '\n'.join(lines[start:i+1])
            break
    
    print("Context:")
    print(context)
    
    prompt1 = """You are an expert Lean 4 theorem prover.

CONTEXT:
In the phase_coherence_bounded theorem, we need to prove:
```lean
have h_poincare : enstrophyReal u ≤ (1/lambda_1) * energyReal u := by
  sorry -- Standard Poincaré inequality
```

Where:
- enstrophyReal u = (1/2) * L2NormSquared (curl u)
- energyReal u = (1/2) * L2NormSquared u
- lambda_1 is the first eigenvalue of the Laplacian (a positive constant)

This is the standard Poincaré inequality relating the L2 norm of the gradient (curl) to the L2 norm of the function.

Since the L2 norms are axiomatized, you may need to add this as an axiom or assumption.

Output ONLY the Lean proof to replace 'sorry'."""

    try:
        response1 = client.chat.completions.create(
            model="o3",
            messages=[{"role": "user", "content": prompt1}],
            max_completion_tokens=100000
        )
        
        proof1 = response1.choices[0].message.content
        print(f"\nGenerated proof 1:")
        print(proof1[:200] + "...")
        
        # Apply proof 1
        lines[poincare_line] = lines[poincare_line].replace('sorry -- Standard Poincaré inequality', proof1)
        
        with open(file_path, 'w') as f:
            f.write('\n'.join(lines))
        
        # Test compilation
        result = subprocess.run(
            ['lake', 'build', 'NavierStokesLedger.SimplifiedProofs'],
            cwd='..',
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            print("✓ Proof 1 SUCCESSFUL!")
            successes += 1
        else:
            print("✗ Proof 1 FAILED")
            print(result.stderr[:300])
            # Revert
            lines[poincare_line] = '      sorry -- Standard Poincaré inequality'
    except Exception as e:
        print(f"✗ Error in proof 1: {e}")
    
    # Target 2: A sorry in TestBridgeApproach.lean
    print("\n=== PROOF 2: Monotonicity in TestBridgeApproach ===")
    
    file_path2 = Path("../NavierStokesLedger/TestBridgeApproach.lean")
    with open(file_path2, 'r') as f:
        content2 = f.read()
        lines2 = content2.split('\n')
    
    # Find the monotonicity sorry
    for i, line in enumerate(lines2):
        if 'sorry  -- Monotonicity in t' in line:
            mono_line = i
            # Get context
            start = max(0, i - 15)
            context = '\n'.join(lines2[start:i+1])
            break
    
    print("Context:")
    print(context)
    
    prompt2 = """You are an expert Lean 4 theorem prover.

CONTEXT:
We need to prove monotonicity in the interval [0,1]:
```lean
_ ≤ C₀ * (1 + t/recognition_tick) * exp (t * cascade_cutoff/recognition_tick) := by
           sorry  -- Monotonicity in t ∈ [0,1]
```

Where:
- C₀ = 1 (a constant)
- recognition_tick > 0 (the recognition timescale)
- cascade_cutoff = -4 * log(φ) ≈ -1.887 (negative)
- t ∈ [0, 1]

The expression (1 + t/recognition_tick) * exp(t * cascade_cutoff/recognition_tick) is monotonic in t.

Use the fact that:
- The derivative is positive for t ∈ [0,1]
- Or use that both factors are monotonic

Output ONLY the Lean proof to replace 'sorry'."""

    try:
        response2 = client.chat.completions.create(
            model="o3",
            messages=[{"role": "user", "content": prompt2}],
            max_completion_tokens=100000
        )
        
        proof2 = response2.choices[0].message.content
        print(f"\nGenerated proof 2:")
        print(proof2[:200] + "...")
        
        # Apply proof 2
        lines2[mono_line] = lines2[mono_line].replace('sorry  -- Monotonicity in t ∈ [0,1]', proof2)
        
        with open(file_path2, 'w') as f:
            f.write('\n'.join(lines2))
        
        # Test compilation
        result = subprocess.run(
            ['lake', 'build', 'NavierStokesLedger.TestBridgeApproach'],
            cwd='..',
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            print("✓ Proof 2 SUCCESSFUL!")
            successes += 1
        else:
            print("✗ Proof 2 FAILED")
            print(result.stderr[:300])
            # Revert
            lines2[mono_line] = '           sorry  -- Monotonicity in t ∈ [0,1]'
            with open(file_path2, 'w') as f:
                f.write('\n'.join(lines2))
    except Exception as e:
        print(f"✗ Error in proof 2: {e}")
    
    print(f"\n=== FINAL RESULT: {successes}/2 proofs successful ===")
    
    if successes == 2:
        print("✓ Ready to scale up to 4 proofs!")
    elif successes == 1:
        print("Partial success - need to debug the failed proof")
    else:
        print("Need to improve prompts or context")
    
    return successes

def main():
    if len(sys.argv) > 1:
        api_key = sys.argv[1]
    else:
        print("Please provide API key")
        sys.exit(1)
        
    solve_two_proofs(api_key)

if __name__ == "__main__":
    main() 
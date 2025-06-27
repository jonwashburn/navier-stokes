#!/usr/bin/env python3
"""Fix and prove L2_norm_mono theorem correctly"""

import sys
from pathlib import Path
from openai import OpenAI
from compile_checker import CompileChecker

def fix_and_prove_theorem(api_key):
    client = OpenAI(api_key=api_key)
    compiler = CompileChecker()
    
    file_path = Path("../NavierStokesLedger/SimplifiedProofs.lean")
    
    # Create a prompt to fix the theorem
    prompt = """You are an expert Lean 4 theorem prover.

CONTEXT:
In PDEOperators.lean, L2NormSquared is defined as:
```lean
noncomputable def L2NormSquared : VectorField → ℝ := fun u =>
  sorry  -- Axiomatized: this should be ∫ ‖u x‖² dx
```

There are also axioms:
- axiom L2_norm_nonneg (u : VectorField) : 0 ≤ L2NormSquared u
- axiom L2_norm_zero_iff (u : VectorField) : L2NormSquared u = 0 ↔ (∀ x, u x = 0)
- axiom L2_norm_triangle (u v : VectorField) : ...

The current theorem is BROKEN because it references undefined items:
```lean
theorem L2_norm_mono {u v : VectorField}
    (h : ∀ x i, ‖u x i‖ ≤ ‖v x i‖) :
    L2NormSquared u ≤ L2NormSquared v := by
  -- Use the measure theory version
  rw [L2_norm_equiv, L2_norm_equiv]  -- L2_norm_equiv doesn't exist!
  -- Apply the proven version (assuming integrability)
  have hu : Integrable (fun x => ‖u x‖^2) volume3 := by
    sorry
  have hv : Integrable (fun x => ‖v x‖^2) volume3 := by
    sorry
  exact L2_norm_mono_proven h hu hv  -- L2_norm_mono_proven doesn't exist!
```

TASK: Provide a COMPLETE CORRECT theorem and proof.

Since L2NormSquared is axiomatized, you need to either:
1. Add an axiom that relates pointwise bounds to L2 bounds
2. Or make the theorem conditional on some assumptions

Output the complete theorem with proof starting with 'theorem L2_norm_mono'."""

    print("=== ASKING O3 TO FIX AND PROVE THE THEOREM ===")
    
    try:
        response = client.chat.completions.create(
            model="o3",
            messages=[
                {"role": "user", "content": prompt}
            ],
            max_completion_tokens=100000
        )
        
        theorem = response.choices[0].message.content
        usage = response.usage
        
        print(f"\n=== O3 RESPONSE ===")
        print(f"Reasoning tokens: {usage.completion_tokens_details.reasoning_tokens}")
        print(f"Output tokens: {usage.completion_tokens - usage.completion_tokens_details.reasoning_tokens}")
        print(f"\n=== COMPLETE THEOREM ===")
        print(theorem)
        
        # Replace the broken theorem
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Find the theorem location
        start = content.find("theorem L2_norm_mono")
        end = content.find("exact L2_norm_mono_proven h hu hv") + len("exact L2_norm_mono_proven h hu hv")
        
        if start >= 0 and end > start:
            # Replace with the new theorem
            new_content = content[:start] + theorem + content[end:]
            
            # Write back
            with open(file_path, 'w') as f:
                f.write(new_content)
                
            print(f"\n=== TESTING COMPILATION ===")
            # Run lean build
            import subprocess
            result = subprocess.run(
                ['lake', 'build', 'NavierStokesLedger.SimplifiedProofs'],
                cwd='../NavierStokesLedger/..',
                capture_output=True,
                text=True
            )
            
            if result.returncode == 0:
                print("✓ BUILD SUCCESSFUL!")
                return True
            else:
                print(f"✗ BUILD FAILED:")
                print(result.stderr[:1000])
                return False
        else:
            print("Could not find theorem in file")
            return False
            
    except Exception as e:
        print(f"\n✗ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    if len(sys.argv) > 1:
        api_key = sys.argv[1]
    else:
        print("Please provide API key")
        sys.exit(1)
        
    fix_and_prove_theorem(api_key)

if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
"""Test o3 on a clean single theorem"""

import sys
from pathlib import Path
from openai import OpenAI

def test_clean_sorry(api_key):
    client = OpenAI(api_key=api_key)
    
    # Read the actual theorem from file
    file_path = Path("../NavierStokesLedger/SimplifiedProofs.lean")
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Extract just the theorem declaration without the partial proof
    theorem_text = """theorem L2_norm_mono {u v : VectorField}
    (h : ∀ x i, ‖u x i‖ ≤ ‖v x i‖) :
    L2NormSquared u ≤ L2NormSquared v"""
    
    print("=== TARGET THEOREM ===")
    print(theorem_text)
    
    # Create a focused prompt
    prompt = f"""You are an expert Lean 4 theorem prover working on Navier-Stokes equations.

Given:
- VectorField is a type representing vector fields on ℝ³
- L2NormSquared u = ∫ x, ‖u x‖^2 (the L2 norm squared)
- h says: for all points x and components i, ‖u x i‖ ≤ ‖v x i‖

Prove:
{theorem_text} := by
  sorry

Replace 'sorry' with a complete proof. Use standard Lean 4 tactics. Output ONLY the proof starting with 'by'."""

    print("\n=== PROMPT TO O3 ===")
    print(prompt)
    
    try:
        response = client.chat.completions.create(
            model="o3",  # Use full o3 for maximum capability
            messages=[
                {"role": "user", "content": prompt}
            ],
            max_completion_tokens=25000  # Maximum tokens for o3's deep reasoning
        )
        
        print("\n=== O3 RESPONSE DETAILS ===")
        print(f"Finish reason: {response.choices[0].finish_reason}")
        print(f"Usage: {response.usage}")
        
        proof = response.choices[0].message.content
        print(f"\n=== O3 GENERATED PROOF ===")
        print(proof)
        
        # Show complete theorem
        print(f"\n=== COMPLETE THEOREM ===")
        print(f"{theorem_text} := {proof}")
        
    except Exception as e:
        print(f"\nError: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    if len(sys.argv) > 1:
        test_clean_sorry(sys.argv[1])
    else:
        print("Please provide API key")
        sys.exit(1) 
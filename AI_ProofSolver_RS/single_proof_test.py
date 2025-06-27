#!/usr/bin/env python3
"""Test o3 on single proofs with 100k token limit"""

import sys
import os
from pathlib import Path
from openai import OpenAI
from compile_checker import CompileChecker

def test_single_proof(api_key):
    client = OpenAI(api_key=api_key)
    compiler = CompileChecker()
    
    # Target: SimplifiedProofs.lean, L2_norm_mono theorem
    file_path = Path("../NavierStokesLedger/SimplifiedProofs.lean")
    
    # Read file
    with open(file_path, 'r') as f:
        lines = f.readlines()
    
    # Find L2_norm_mono (around line 20-30)
    sorry_line = None
    for i, line in enumerate(lines):
        if 'theorem L2_norm_mono' in line:
            for j in range(i, min(i+20, len(lines))):
                if 'sorry' in lines[j]:
                    sorry_line = j + 1
                    break
            break
    
    if not sorry_line:
        print("Could not find L2_norm_mono sorry")
        return
        
    print(f"=== TESTING SINGLE PROOF ===")
    print(f"File: {file_path}")
    print(f"Sorry at line: {sorry_line}")
    
    # Extract full context
    theorem_start = sorry_line - 10
    theorem_end = sorry_line
    theorem_context = ''.join(lines[theorem_start:theorem_end])
    
    print(f"\n=== THEOREM CONTEXT ===")
    print(theorem_context)
    
    # Create comprehensive prompt
    prompt = f"""You are an expert Lean 4 theorem prover working on Navier-Stokes equations using Recognition Science.

CONTEXT:
- File: SimplifiedProofs.lean
- This file contains simplified versions of key theorems
- L2NormSquared u = ∫ x, ‖u x‖² over ℝ³
- VectorField is a type for vector fields on ℝ³

AVAILABLE DEFINITIONS:
- L2_norm_equiv : relates L2NormSquared to the measure theory integral
- volume3 : the standard measure on ℝ³
- Integrable : standard measure theory integrability

THEOREM TO PROVE:
{theorem_context}

The hypothesis h says: for all points x and components i, ‖u x i‖ ≤ ‖v x i‖

TASK: Replace the first 'sorry' with a complete proof. 

IMPORTANT:
- The proof should handle the integrability requirement
- Use standard Lean 4 tactics
- The key is to show that pointwise inequality implies L2 inequality
- You may assume basic properties about norms and integrals

Output ONLY the Lean proof code to replace 'sorry'."""

    print(f"\n=== CALLING O3 WITH 100K TOKENS ===")
    
    try:
        response = client.chat.completions.create(
            model="o3",
            messages=[
                {"role": "system", "content": "You are a Lean 4 expert. Generate only valid Lean proof code."},
                {"role": "user", "content": prompt}
            ],
            max_completion_tokens=100000
        )
        
        proof = response.choices[0].message.content
        usage = response.usage
        
        print(f"\n=== O3 RESPONSE ===")
        print(f"Reasoning tokens: {usage.completion_tokens_details.reasoning_tokens}")
        print(f"Output tokens: {usage.completion_tokens - usage.completion_tokens_details.reasoning_tokens}")
        print(f"Total tokens: {usage.total_tokens}")
        print(f"\n=== GENERATED PROOF ===")
        print(proof)
        
        # Test compilation
        print(f"\n=== TESTING COMPILATION ===")
        success, error = compiler.check_proof(file_path, sorry_line, proof)
        
        if success:
            print("✓ PROOF COMPILES SUCCESSFULLY!")
            
            # Apply the proof
            lines[sorry_line - 1] = lines[sorry_line - 1].replace('sorry', proof)
            with open(file_path, 'w') as f:
                f.writelines(lines)
                
            print("✓ PROOF APPLIED TO FILE!")
            return True
        else:
            print(f"✗ COMPILATION FAILED:")
            print(error[:500])
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
        
    success = test_single_proof(api_key)
    
    if success:
        print("\n=== SUCCESS: Ready to scale up to 2 proofs ===")
    else:
        print("\n=== FAILED: Need to debug before scaling ===")

if __name__ == "__main__":
    main() 
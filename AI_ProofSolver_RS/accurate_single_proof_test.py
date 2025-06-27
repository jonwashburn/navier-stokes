#!/usr/bin/env python3
"""Accurate test for o3 with real file context"""

import sys
from pathlib import Path
from openai import OpenAI
from compile_checker import CompileChecker

def test_accurate_proof(api_key):
    client = OpenAI(api_key=api_key)
    compiler = CompileChecker()
    
    # Read the actual file
    file_path = Path("../NavierStokesLedger/SimplifiedProofs.lean")
    with open(file_path, 'r') as f:
        full_content = f.read()
        lines = full_content.split('\n')
    
    # Find the theorem and its context
    theorem_line = None
    for i, line in enumerate(lines):
        if 'theorem L2_norm_mono' in line:
            theorem_line = i
            break
    
    if theorem_line is None:
        print("Could not find theorem")
        return
    
    # Extract the full theorem including the partial proof
    theorem_end = theorem_line + 15  # Get enough context
    theorem_text = '\n'.join(lines[theorem_line:theorem_end])
    
    print("=== ACTUAL THEOREM FROM FILE ===")
    print(theorem_text)
    
    # Read PDEOperators to understand L2NormSquared
    pde_path = Path("../NavierStokesLedger/PDEOperators.lean")
    with open(pde_path, 'r') as f:
        pde_content = f.read()
    
    # Extract L2NormSquared definition
    l2_def_start = pde_content.find("L2NormSquared")
    l2_def_end = pde_content.find("L2Norm (u", l2_def_start)
    l2_def = pde_content[l2_def_start:l2_def_end]
    
    print("\n=== L2NormSquared DEFINITION ===")
    print(l2_def)
    
    # Create accurate prompt
    prompt = f"""You are an expert Lean 4 theorem prover.

ACTUAL FILE CONTEXT:
The theorem uses L2NormSquared which is defined as:
{l2_def}

Note: L2NormSquared is currently axiomatized with a sorry.
Also note: L2_norm_equiv is NOT defined - it was incorrectly referenced.

THEOREM TO COMPLETE:
{theorem_text}

The proof has two sorries:
1. First sorry: proving integrability of (fun x => ‖u x‖^2)
2. Second sorry: proving integrability of (fun x => ‖v x‖^2)

TASK: Replace ONLY the FIRST sorry with a proof for integrability of u.

IMPORTANT:
- Since L2NormSquared is axiomatized, you cannot use its definition
- You need to establish integrability directly
- The hypothesis h gives: ∀ x i, ‖u x i‖ ≤ ‖v x i‖
- You may need to add assumptions about boundedness or decay

Output ONLY the Lean code to replace the first sorry."""

    print(f"\n=== CALLING O3 ===")
    
    try:
        response = client.chat.completions.create(
            model="o3",
            messages=[
                {"role": "user", "content": prompt}
            ],
            max_completion_tokens=100000
        )
        
        proof = response.choices[0].message.content
        usage = response.usage
        
        print(f"\n=== O3 RESPONSE ===")
        print(f"Reasoning tokens: {usage.completion_tokens_details.reasoning_tokens}")
        print(f"Output tokens: {usage.completion_tokens - usage.completion_tokens_details.reasoning_tokens}")
        print(f"\n=== GENERATED PROOF ===")
        print(proof)
        
        # Find the exact line with the first sorry
        sorry_line = None
        for i, line in enumerate(lines):
            if 'sorry' in line and 'Requires boundedness/decay assumption on u' in line:
                sorry_line = i + 1
                break
                
        if sorry_line:
            print(f"\n=== TESTING COMPILATION (line {sorry_line}) ===")
            success, error = compiler.check_proof(file_path, sorry_line, proof)
            
            if success:
                print("✓ PROOF COMPILES!")
                return True
            else:
                print(f"✗ FAILED: {error[:500]}")
                return False
        else:
            print("Could not find sorry line")
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
        
    test_accurate_proof(api_key)

if __name__ == "__main__":
    main() 
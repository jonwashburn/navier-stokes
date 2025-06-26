#!/usr/bin/env python3
"""Test o3 on the simplest sorry - φ approximation"""

import sys
from pathlib import Path
from openai import OpenAI

def test_phi_approx(api_key):
    client = OpenAI(api_key=api_key)
    
    # Read RSImports.lean which has the φ approximation sorry
    file_path = Path("../NavierStokesLedger/RSImports.lean")
    with open(file_path, 'r') as f:
        content = f.read()
        lines = content.split('\n')
    
    # Find the φ_approx lemma
    for i, line in enumerate(lines):
        if 'lemma φ_approx' in line:
            start = i
            end = i + 5
            lemma_text = '\n'.join(lines[start:end])
            sorry_line = i + 3  # The sorry is 3 lines after the lemma start
            break
    
    print("=== TARGET LEMMA ===")
    print(lemma_text)
    
    prompt = """You are an expert Lean 4 theorem prover.

CONTEXT:
φ (phi) is the golden ratio = (1 + √5)/2 ≈ 1.618033988749895

LEMMA TO PROVE:
lemma φ_approx : abs (φ - 1.618033988749895) < 1e-14 := by
  sorry

This is asking to prove that the approximation 1.618033988749895 is within 1e-14 of the true value of φ.

APPROACH:
Since this is a numerical approximation, you'll need to either:
1. Use Lean's interval arithmetic capabilities
2. Or use existing bounds on φ
3. Or compute explicit bounds using the definition φ = (1 + √5)/2

Output ONLY the Lean proof to replace 'sorry'."""

    print("\n=== CALLING O3 ===")
    
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
        
        # Apply the proof
        lines[sorry_line] = lines[sorry_line].replace('sorry  -- Numerical approximation', proof)
        
        with open(file_path, 'w') as f:
            f.write('\n'.join(lines))
            
        print(f"\n=== TESTING BUILD ===")
        import subprocess
        result = subprocess.run(
            ['lake', 'build', 'NavierStokesLedger.RSImports'],
            cwd='..',
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            print("✓ BUILD SUCCESSFUL!")
            print("✓ Successfully solved 1 sorry!")
            return True
        else:
            print(f"✗ BUILD FAILED:")
            print(result.stderr[:500])
            
            # Revert the change
            lines[sorry_line] = '  sorry  -- Numerical approximation'
            with open(file_path, 'w') as f:
                f.write('\n'.join(lines))
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
        
    success = test_phi_approx(api_key)
    
    if success:
        print("\n=== SUCCESS! Ready to double to 2 proofs ===")

if __name__ == "__main__":
    main() 
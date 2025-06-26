#!/usr/bin/env python3
"""Test o3 with a very simple prompt"""

import sys
from openai import OpenAI

def test_o3_simple(api_key):
    client = OpenAI(api_key=api_key)
    
    prompt = """Prove this simple Lean 4 theorem:

theorem simple_le : ∀ n : Nat, n ≤ n + 1 := by
  sorry

Replace sorry with the proof. Output only Lean code."""

    print("=== TESTING O3 WITH SIMPLE THEOREM ===")
    print(prompt)
    print("\n=== O3 RESPONSE ===")
    
    try:
        response = client.chat.completions.create(
            model="o3",
            messages=[
                {"role": "user", "content": prompt}
            ],
            max_completion_tokens=2000  # O3 needs more tokens for reasoning
        )
        
        content = response.choices[0].message.content
        print(f"Response: '{content}'")
        print(f"Finish reason: {response.choices[0].finish_reason}")
        print(f"Usage: {response.usage}")
        
    except Exception as e:
        print(f"Error: {e}")
        print(f"Error type: {type(e).__name__}")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        test_o3_simple(sys.argv[1])
    else:
        print("Please provide API key")
        sys.exit(1) 
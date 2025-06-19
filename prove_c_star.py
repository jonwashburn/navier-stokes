#!/usr/bin/env python3
import asyncio
from anthropic import AsyncAnthropic
import os

async def prove_C_star_lemma():
    client = AsyncAnthropic(api_key=os.getenv('ANTHROPIC_API_KEY'))
    
    prompt = '''You are a Lean 4 theorem prover. I need to prove this lemma:

lemma C_star_lt_phi_inv : C_star < φ⁻¹ := by
  -- C_star = 0.05 and φ⁻¹ ≈ 0.618, so this is provable numerically
  unfold C_star φ
  norm_num
  -- Need to show 0.05 < 2 / (1 + √5)
  -- Since √5 ≈ 2.236, we have 1 + √5 ≈ 3.236, so 2/(1+√5) ≈ 0.618
  -- This requires more sophisticated numerical tactics
  sorry

Where:
- C_star : ℝ := 0.05
- φ : ℝ := (1 + Real.sqrt 5) / 2

Generate ONLY the proof code that replaces the sorry. Use Lean 4 tactics like:
- norm_num for numerical computation
- linarith for linear arithmetic
- have for intermediate steps
- rw for rewriting

Proof:'''

    response = await client.messages.create(
        model='claude-3-5-sonnet-20241022',
        max_tokens=500,
        temperature=0,
        messages=[{'role': 'user', 'content': prompt}]
    )
    
    print('Generated proof:')
    print(response.content[0].text)

if __name__ == "__main__":
    asyncio.run(prove_C_star_lemma()) 
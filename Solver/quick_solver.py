#!/usr/bin/env python3
import os
import re
from anthropic import Anthropic

API_KEY = os.environ.get('ANTHROPIC_API_KEY')
client = Anthropic(api_key=API_KEY)
MODEL = "claude-sonnet-4-20250514"

# Simple proofs that should work
SIMPLE_PROOFS = {
    'C_star_lt_phi_inv': 'norm_num',
    'bootstrap_less_than_golden': 'norm_num',
    'c_zero_value': 'rfl',
    'k_star_value': 'rfl',
    'beta_value': 'rfl',
    'golden_ratio_value': 'rfl',
    'phi_eq': 'rfl',
    'phi_value': 'rfl',
    'numerical_constant': 'norm_num',
    'simple_bound': 'norm_num',
    'trivial_bound': 'simp',
    'definition_proof': 'rfl'
}

def apply_simple_proofs():
    count = 0
    for root, dirs, files in os.walk('NavierStokesLedger'):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                try:
                    with open(filepath, 'r') as f:
                        content = f.read()
                    
                    original = content
                    
                    # Apply simple replacements
                    for name, proof in SIMPLE_PROOFS.items():
                        # Pattern 1: := by sorry
                        pattern1 = rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*by\s+sorry'
                        if re.search(pattern1, content, re.DOTALL):
                            content = re.sub(pattern1, rf'\1 {name}\2:= by {proof}', content, flags=re.DOTALL)
                            count += 1
                        
                        # Pattern 2: := sorry
                        pattern2 = rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*sorry'
                        if re.search(pattern2, content):
                            content = re.sub(pattern2, rf'\1 {name}\2:= {proof}', content)
                            count += 1
                    
                    # Apply numerical computation proofs
                    numerical_patterns = [
                        (r'sorry\s*--\s*Requires numerical computation', 'norm_num'),
                        (r'sorry\s*--\s*Numerical computation', 'norm_num'),
                        (r'sorry\s*--\s*Numerical fact', 'norm_num'),
                        (r'sorry\s*--\s*TODO.*numerical', 'norm_num')
                    ]
                    
                    for pattern, replacement in numerical_patterns:
                        if re.search(pattern, content, re.IGNORECASE):
                            content = re.sub(pattern, replacement, content, flags=re.IGNORECASE)
                            count += 1
                    
                    if content != original:
                        with open(filepath, 'w') as f:
                            f.write(content)
                
                except Exception:
                    continue
    
    return count

def generate_advanced_proofs():
    count = 0
    
    # Target specific files
    targets = [
        'NavierStokesLedger/BasicMinimal.lean',
        'NavierStokesLedger/GoldenRatioSimple.lean',
        'NavierStokesLedger/NumericalHelpers.lean'
    ]
    
    for filepath in targets:
        if not os.path.exists(filepath):
            continue
            
        try:
            with open(filepath, 'r') as f:
                content = f.read()
            
            # Find sorries with context
            lines = content.split('\n')
            for i, line in enumerate(lines):
                if 'sorry' in line and not line.strip().startswith('--'):
                    # Get context
                    start = max(0, i-10)
                    end = min(len(lines), i+3)
                    context = '\n'.join(lines[start:end])
                    
                    # Generate proof
                    prompt = f"""Complete this Lean 4 proof:

{context}

Replace 'sorry' with valid proof. Use: norm_num, rfl, simp, linarith.
Respond with ONLY the proof code."""

                    try:
                        response = client.messages.create(
                            model=MODEL,
                            max_tokens=200,
                            temperature=0,
                            messages=[{"role": "user", "content": prompt}]
                        )
                        proof = response.content[0].text.strip()
                        
                        # Simple replacement
                        if proof and len(proof) < 100:
                            new_line = line.replace('sorry', proof)
                            lines[i] = new_line
                            count += 1
                            break
                    except:
                        continue
            
            # Write back
            new_content = '\n'.join(lines)
            if new_content != content:
                with open(filepath, 'w') as f:
                    f.write(new_content)
                    
        except:
            continue
    
    return count

def main():
    simple_count = apply_simple_proofs()
    advanced_count = generate_advanced_proofs()
    total = simple_count + advanced_count
    print(f"Applied {total} proofs")

if __name__ == "__main__":
    main() 
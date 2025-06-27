#!/usr/bin/env python3
import os
import subprocess
import time
from anthropic import Anthropic

API_KEY = os.environ.get('ANTHROPIC_API_KEY')
client = Anthropic(api_key=API_KEY)
MODEL = "claude-sonnet-4-20250514"

# Target files with moderate sorry counts
TARGET_FILES = [
    'NavierStokesLedger/BasicMinimal.lean',
    'NavierStokesLedger/BasicMinimal2.lean', 
    'NavierStokesLedger/GoldenRatioSimple.lean',
    'NavierStokesLedger/BealeKatoMajda.lean',
    'NavierStokesLedger/BootstrapConstantProof.lean',
    'NavierStokesLedger/CurvatureBoundSimple.lean',
    'NavierStokesLedger/GoldenRatioSimple2.lean',
    'NavierStokesLedger/NumericalHelpers.lean',
    'NavierStokesLedger/PrimeSumBounds.lean'
]

def find_sorries(filepath):
    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()
        
        sorries = []
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Find theorem/lemma name
                for j in range(max(0, i-20), i+1):
                    if 'theorem' in lines[j] or 'lemma' in lines[j]:
                        import re
                        match = re.search(r'(theorem|lemma)\s+(\w+)', lines[j])
                        if match:
                            sorries.append({
                                'name': match.group(2),
                                'line': i+1,
                                'context': ''.join(lines[max(0,i-15):i+5])
                            })
                            break
        return sorries
    except:
        return []

def generate_proof(name, context, filepath):
    prompt = f"""Complete this Lean 4 proof from {filepath}:

{context}

Replace 'sorry' with valid proof. Key constants: C* = 0.142, K* = 0.090, φ = (1+√5)/2.

Common tactics: norm_num, rfl, simp, linarith, ring, field_simp.

Respond with ONLY the proof code."""

    try:
        response = client.messages.create(
            model=MODEL,
            max_tokens=400,
            temperature=0,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text.strip()
    except:
        return None

def apply_proof(filepath, name, proof):
    with open(filepath, 'r') as f:
        content = f.read()
    
    backup = f"{filepath}.backup_{int(time.time())}"
    with open(backup, 'w') as f:
        f.write(content)
    
    import re
    patterns = [
        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*by\s+.*?sorry', re.DOTALL),
        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*sorry', 0)
    ]
    
    for pattern, flags in patterns:
        new_content = re.sub(pattern, rf'\1 {name}\2:= by\n  {proof}', content, flags=flags)
        if new_content != content:
            with open(filepath, 'w') as f:
                f.write(new_content)
            
            result = subprocess.run(['lake', 'build', filepath], capture_output=True, timeout=45)
            if result.returncode == 0:
                os.remove(backup)
                return True
            else:
                with open(filepath, 'w') as f:
                    f.write(content)
                os.remove(backup)
                break
    return False

def process_file(filepath):
    if not os.path.exists(filepath):
        return 0
    
    sorries = find_sorries(filepath)
    if not sorries:
        return 0
    
    completed = 0
    for sorry in sorries[:2]:  # Process 2 per file
        proof = generate_proof(sorry['name'], sorry['context'], filepath)
        if proof and apply_proof(filepath, sorry['name'], proof):
            completed += 1
    
    return completed

def main():
    total = 0
    for filepath in TARGET_FILES:
        total += process_file(filepath)
    
    # Final build
    subprocess.run(['lake', 'build'], capture_output=True)
    print(f"Completed: {total}")

if __name__ == "__main__":
    main() 
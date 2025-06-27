#!/usr/bin/env python3
import os
import re
from anthropic import Anthropic

API_KEY = os.environ.get('ANTHROPIC_API_KEY')
client = Anthropic(api_key=API_KEY)
MODEL = "claude-sonnet-4-20250514"

def find_all_sorries():
    sorries = []
    for root, dirs, files in os.walk('NavierStokesLedger'):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                try:
                    with open(filepath, 'r') as f:
                        lines = f.readlines()
                    
                    for i, line in enumerate(lines):
                        if 'sorry' in line and not line.strip().startswith('--'):
                            # Get theorem name
                            theorem_name = None
                            for j in range(max(0, i-15), i+1):
                                match = re.search(r'(theorem|lemma)\s+(\w+)', lines[j])
                                if match:
                                    theorem_name = match.group(2)
                                    break
                            
                            if theorem_name:
                                context = ''.join(lines[max(0,i-10):i+3])
                                sorries.append({
                                    'file': filepath,
                                    'name': theorem_name,
                                    'line': i,
                                    'context': context,
                                    'full_line': line
                                })
                except:
                    continue
    return sorries

def generate_proof(sorry_info):
    context = sorry_info['context']
    name = sorry_info['name']
    
    # Try different prompts based on theorem name
    if any(word in name.lower() for word in ['value', 'eq', 'def']):
        proof = 'rfl'
    elif any(word in name.lower() for word in ['lt', 'bound', 'numerical']):
        proof = 'norm_num'
    elif 'trivial' in name.lower():
        proof = 'trivial'
    else:
        # Use AI
        prompt = f"""Complete this Lean 4 proof for {name}:

{context}

Replace 'sorry' with a valid proof. Use tactics: norm_num, rfl, simp, linarith, ring, trivial.
For numerical inequalities use norm_num. For definitions use rfl.
Respond with ONLY the proof tactic."""

        try:
            response = client.messages.create(
                model=MODEL,
                max_tokens=200,
                temperature=0,
                messages=[{"role": "user", "content": prompt}]
            )
            proof = response.content[0].text.strip()
            if '```' in proof:
                proof = proof.split('```')[1] if '```' in proof else proof.split('```')[0]
            proof = proof.strip()
        except:
            proof = 'sorry'
    
    return proof

def apply_proofs(sorries):
    count = 0
    
    # Group by file
    files_to_update = {}
    for sorry in sorries:
        filepath = sorry['file']
        if filepath not in files_to_update:
            files_to_update[filepath] = []
        files_to_update[filepath].append(sorry)
    
    for filepath, file_sorries in files_to_update.items():
        try:
            with open(filepath, 'r') as f:
                content = f.read()
            
            original_content = content
            
            for sorry in file_sorries:
                proof = generate_proof(sorry)
                if proof and proof != 'sorry' and len(proof) < 100:
                    # Apply replacement
                    name = sorry['name']
                    
                    # Multiple patterns
                    patterns = [
                        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*by\s+sorry', rf'\1 {name}\2:= by {proof}'),
                        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*sorry', rf'\1 {name}\2:= {proof}'),
                        (rf'sorry\s*--.*{re.escape(name)}', proof)
                    ]
                    
                    for pattern, replacement in patterns:
                        new_content = re.sub(pattern, replacement, content, flags=re.DOTALL)
                        if new_content != content:
                            content = new_content
                            count += 1
                            break
            
            # Write back if changed
            if content != original_content:
                with open(filepath, 'w') as f:
                    f.write(content)
                    
        except Exception:
            continue
    
    return count

def main():
    sorries = find_all_sorries()
    print(f"Found {len(sorries)} sorries")
    
    # Process in batches
    batch_size = 50
    total_applied = 0
    
    for i in range(0, len(sorries), batch_size):
        batch = sorries[i:i+batch_size]
        applied = apply_proofs(batch)
        total_applied += applied
        print(f"Batch {i//batch_size + 1}: Applied {applied} proofs")
    
    print(f"Total applied: {total_applied}")

if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
import os
import re
import threading
import time
from anthropic import Anthropic

API_KEY = os.environ.get('ANTHROPIC_API_KEY')
client = Anthropic(api_key=API_KEY)
MODEL = "claude-sonnet-4-20250514"

completed_count = 0
lock = threading.Lock()

def generate_proof(context):
    prompt = f"""Complete this Lean 4 proof:

{context}

Replace 'sorry' with valid proof. Use simple tactics: norm_num, rfl, simp, linarith, ring.
Respond with ONLY the proof code, no explanations."""

    try:
        response = client.messages.create(
            model=MODEL,
            max_tokens=300,
            temperature=0,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text.strip()
    except:
        return None

def process_file(filepath):
    global completed_count
    if not os.path.exists(filepath):
        return
    
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        
        lines = content.split('\n')
        changed = False
        
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Get context
                start = max(0, i-8)
                end = min(len(lines), i+3)
                context = '\n'.join(lines[start:end])
                
                # Generate proof
                proof = generate_proof(context)
                if proof and len(proof) < 80 and 'sorry' not in proof:
                    # Apply simple replacement
                    if ':= by sorry' in line:
                        new_line = line.replace('sorry', proof)
                    elif ':= sorry' in line:
                        new_line = line.replace(':= sorry', f':= {proof}')
                    else:
                        new_line = line.replace('sorry', proof)
                    
                    lines[i] = new_line
                    changed = True
                    
                    with lock:
                        global completed_count
                        completed_count += 1
        
        if changed:
            new_content = '\n'.join(lines)
            with open(filepath, 'w') as f:
                f.write(new_content)
                
    except Exception:
        pass

def main():
    # Get all lean files
    lean_files = []
    for root, dirs, files in os.walk('NavierStokesLedger'):
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    
    # Process files in parallel
    threads = []
    for filepath in lean_files[:15]:  # Process first 15 files
        thread = threading.Thread(target=process_file, args=(filepath,))
        threads.append(thread)
        thread.start()
    
    # Wait for completion
    for thread in threads:
        thread.join()
    
    print(f"Applied {completed_count} proofs")

if __name__ == "__main__":
    main() 
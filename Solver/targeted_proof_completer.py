#!/usr/bin/env python3
"""
Targeted Proof Completer - Focus on specific types of proofs we can complete
"""

import os
import re
import subprocess
import time
from anthropic import Anthropic

# Configuration
API_KEY = os.environ.get('ANTHROPIC_API_KEY')
if not API_KEY:
    print("ERROR: ANTHROPIC_API_KEY not set")
    exit(1)

client = Anthropic(api_key=API_KEY)
MODEL = "claude-sonnet-4-20250514"

# Target specific files with fewer sorries first
TARGET_FILES = [
    'NavierStokesLedger/GoldenRatioSimple2.lean',
    'NavierStokesLedger/Axioms.lean',
    'NavierStokesLedger/BasicMinimal.lean',
    'NavierStokesLedger/BasicMinimal2.lean',
    'NavierStokesLedger/BealeKatoMajda.lean',
    'NavierStokesLedger/NumericalHelpers.lean',
    'NavierStokesLedger/PrimeSumBounds.lean'
]

def find_sorries_in_file(filepath):
    """Find sorries with context"""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except:
        return []
    
    sorries = []
    lines = content.split('\n')
    
    for i, line in enumerate(lines):
        if 'sorry' in line and not line.strip().startswith('--'):
            # Get extensive context
            start = max(0, i - 30)
            end = min(len(lines), i + 10)
            context = '\n'.join(lines[start:end])
            
            # Find the theorem/lemma name
            for j in range(start, i + 1):
                match = re.search(r'(theorem|lemma)\s+(\w+)', lines[j])
                if match:
                    sorries.append({
                        'name': match.group(2),
                        'line': i + 1,
                        'context': context,
                        'type': match.group(1)
                    })
                    break
    
    return sorries

def generate_proof(name, context, filepath):
    """Generate proof using Claude 4"""
    # Check for simple cases first
    if any(keyword in name.lower() for keyword in ['value', 'constant', 'def']):
        return "rfl"
    
    prompt = f"""You are a Lean 4 expert. Complete this proof from {filepath}:

{context}

The {name} has 'sorry'. Provide ONLY the proof code to replace 'sorry'.

Key facts:
- C* = 0.142, K* = 0.090, C₀ = 0.02, β = 0.110
- φ = (1 + √5) / 2 (golden ratio)
- This is part of a Navier-Stokes proof

Common tactics:
- For numerical values: norm_num
- For definitions: rfl
- For inequalities: linarith, ring_nf
- For real number properties: field_simp

Respond with ONLY the proof code, no explanations."""

    try:
        response = client.messages.create(
            model=MODEL,
            max_tokens=500,
            temperature=0,
            messages=[{"role": "user", "content": prompt}]
        )
        proof = response.content[0].text.strip()
        # Clean up the proof
        if proof.startswith('```'):
            proof = proof.split('\n', 1)[1].rsplit('\n```', 1)[0]
        return proof
    except Exception as e:
        print(f"API error for {name}: {e}")
        return None

def apply_proof(filepath, name, proof):
    """Apply proof to file"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Create backup
    backup = f"{filepath}.backup_{int(time.time())}"
    with open(backup, 'w') as f:
        f.write(content)
    
    # Try different patterns for sorry replacement
    patterns = [
        # Pattern 1: := by sorry
        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*by\s+sorry', 
         rf'\1 {name}\2:= by\n  {proof}'),
        # Pattern 2: := sorry
        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*sorry',
         rf'\1 {name}\2:= {proof}'),
        # Pattern 3: Multi-line with by and sorry on next line
        (rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*by\n\s*sorry',
         rf'\1 {name}\2:= by\n  {proof}')
    ]
    
    new_content = content
    replaced = False
    
    for pattern, replacement in patterns:
        test_content = re.sub(pattern, replacement, content, flags=re.DOTALL)
        if test_content != content:
            new_content = test_content
            replaced = True
            break
    
    if replaced:
        with open(filepath, 'w') as f:
            f.write(new_content)
        return True, backup
    
    os.remove(backup)
    return False, None

def verify_file(filepath):
    """Quick verification of single file"""
    result = subprocess.run(
        ['lake', 'build', filepath],
        capture_output=True,
        text=True,
        timeout=45
    )
    return result.returncode == 0

def process_file(filepath):
    """Process a single file"""
    print(f"\n{'='*60}")
    print(f"Processing: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"File not found: {filepath}")
        return 0
    
    sorries = find_sorries_in_file(filepath)
    if not sorries:
        print("No sorries found")
        return 0
    
    print(f"Found {len(sorries)} sorries")
    completed = 0
    
    for sorry in sorries[:3]:  # Process up to 3 per file
        name = sorry['name']
        print(f"\nAttempting: {name}")
        
        proof = generate_proof(name, sorry['context'], filepath)
        if not proof:
            print("Failed to generate proof")
            continue
        
        print(f"Generated: {proof[:50]}...")
        
        applied, backup = apply_proof(filepath, name, proof)
        if not applied:
            print("Failed to apply proof")
            continue
        
        if verify_file(filepath):
            print(f"✓ Success!")
            completed += 1
            if backup and os.path.exists(backup):
                os.remove(backup)
        else:
            print("✗ Verification failed, reverting")
            if backup and os.path.exists(backup):
                with open(backup, 'r') as f:
                    content = f.read()
                with open(filepath, 'w') as f:
                    f.write(content)
                os.remove(backup)
    
    return completed

def main():
    print("=== TARGETED PROOF COMPLETER ===")
    print(f"Using Claude 4 Sonnet ({MODEL})")
    
    total_completed = 0
    
    for filepath in TARGET_FILES:
        completed = process_file(filepath)
        total_completed += completed
    
    print(f"\n{'='*60}")
    print(f"TOTAL COMPLETED: {total_completed} proofs")
    
    # Final build check
    print("\nRunning final build...")
    result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Build successful!")
    else:
        print("✗ Build failed")

if __name__ == "__main__":
    main() 
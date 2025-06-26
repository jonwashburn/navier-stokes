#!/usr/bin/env python3
"""
Incremental Solver - Processes one file at a time to avoid build issues
"""

import os
import sys
import re
import subprocess
import json
import time
from datetime import datetime
from anthropic import Anthropic

# Configuration
API_KEY = os.environ.get('ANTHROPIC_API_KEY')
if not API_KEY:
    print("ERROR: ANTHROPIC_API_KEY not set")
    sys.exit(1)

client = Anthropic(api_key=API_KEY)
MODEL = "claude-opus-4-20250514"  # Claude 4 Opus

def log(msg):
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{timestamp}] {msg}")

def find_sorries_in_file(filepath):
    """Find all sorries in a file with their context"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    sorries = []
    lines = content.split('\n')
    
    # Find theorem/lemma declarations with sorry
    pattern = r'^(theorem|lemma)\s+(\w+).*?:=\s*sorry'
    
    for i, line in enumerate(lines):
        if 'sorry' in line and not line.strip().startswith('--'):
            # Get context
            start = max(0, i - 10)
            end = min(len(lines), i + 5)
            context = '\n'.join(lines[start:end])
            
            # Try to extract the name
            match = re.search(r'(theorem|lemma)\s+(\w+)', context)
            if match:
                name = match.group(2)
                sorries.append({
                    'name': name,
                    'line': i + 1,
                    'context': context,
                    'type': match.group(1)
                })
    
    return sorries

def generate_proof_with_claude4(name, context, filepath):
    """Generate proof using Claude 4 Sonnet"""
    prompt = f"""You are a Lean 4 theorem prover. Complete this proof from {filepath}:

{context}

The theorem/lemma '{name}' currently has 'sorry'. Provide a complete proof.

Important context:
- This is part of a Navier-Stokes proof using Recognition Science's eight-beat framework
- Key constants: C₀ = 0.02, C* = 0.142, K* = 0.090, β = 0.110
- The golden ratio φ = (1 + √5) / 2 appears frequently
- Use available lemmas and theorems from the file

Respond with ONLY the proof code that should replace 'sorry'. No explanations."""

    try:
        response = client.messages.create(
            model=MODEL,
            max_tokens=2000,
            temperature=0,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text.strip()
    except Exception as e:
        log(f"API error for {name}: {e}")
        return None

def verify_proof(filepath):
    """Verify that the file still builds"""
    result = subprocess.run(
        ['lake', 'build', filepath],
        capture_output=True,
        text=True,
        timeout=30
    )
    return result.returncode == 0

def apply_proof_to_file(filepath, name, proof):
    """Apply a single proof to a file"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Pattern to match the specific sorry
    pattern = rf'(theorem|lemma)\s+{re.escape(name)}(.*?):=\s*sorry'
    
    def replace_sorry(match):
        return f"{match.group(1)} {name}{match.group(2)}:= {proof}"
    
    new_content = re.sub(pattern, replace_sorry, content, flags=re.DOTALL)
    
    if new_content != content:
        # Create backup
        backup_path = f"{filepath}.backup_{int(time.time())}"
        with open(backup_path, 'w') as f:
            f.write(content)
        
        # Write new content
        with open(filepath, 'w') as f:
            f.write(new_content)
        
        return True, backup_path
    return False, None

def process_file(filepath):
    """Process all sorries in a single file"""
    log(f"\n{'='*60}")
    log(f"Processing: {filepath}")
    
    sorries = find_sorries_in_file(filepath)
    if not sorries:
        log("No sorries found in this file")
        return 0
    
    log(f"Found {len(sorries)} sorries")
    completed = 0
    
    for sorry_info in sorries:
        name = sorry_info['name']
        log(f"\nAttempting: {name}")
        
        # Generate proof
        proof = generate_proof_with_claude4(name, sorry_info['context'], filepath)
        if not proof:
            log(f"Failed to generate proof for {name}")
            continue
        
        # Apply proof
        applied, backup_path = apply_proof_to_file(filepath, name, proof)
        if not applied:
            log(f"Failed to apply proof for {name}")
            continue
        
        # Verify build
        if verify_proof(filepath):
            log(f"✓ Successfully proved {name}")
            completed += 1
        else:
            # Restore backup
            log(f"✗ Proof failed verification, restoring backup")
            with open(backup_path, 'r') as f:
                content = f.read()
            with open(filepath, 'w') as f:
                f.write(content)
        
        # Clean up backup if successful
        if os.path.exists(backup_path):
            os.remove(backup_path)
    
    return completed

def main():
    log("=== INCREMENTAL PROOF SOLVER ===")
    log(f"Using Claude 4 Sonnet ({MODEL})")
    
    # Find all Lean files with sorries
    files_with_sorries = []
    for root, dirs, files in os.walk('NavierStokesLedger'):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                if find_sorries_in_file(filepath):
                    files_with_sorries.append(filepath)
    
    log(f"\nFound {len(files_with_sorries)} files with sorries")
    
    # Process each file
    total_completed = 0
    for filepath in sorted(files_with_sorries):
        completed = process_file(filepath)
        total_completed += completed
        
        # Run a full build after each file
        log("\nRunning full build...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
        if result.returncode == 0:
            log("✓ Build successful")
        else:
            log("✗ Build failed, but continuing...")
    
    log(f"\n{'='*60}")
    log(f"FINAL SUMMARY: Completed {total_completed} proofs")

if __name__ == "__main__":
    main() 
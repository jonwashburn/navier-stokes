#!/usr/bin/env python3
"""
Smart Incremental Solver - Targets easy proofs first with better error handling
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
MODEL = "claude-sonnet-4-20250514"  # Claude 4 Sonnet

# Categories of easy proofs
EASY_PATTERNS = [
    r'c_star_value',
    r'k_star_value', 
    r'c_zero_value',
    r'beta_value',
    r'golden_ratio',
    r'goldenRatio',
    r'phi_value',
    r'numerical',
    r'simple_bound',
    r'trivial',
    r'placeholder',
    r'definition'
]

def log(msg):
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{timestamp}] {msg}")

def is_easy_proof(name):
    """Check if a proof name matches easy patterns"""
    name_lower = name.lower()
    for pattern in EASY_PATTERNS:
        if re.search(pattern.lower(), name_lower):
            return True
    return False

def find_sorries_in_file(filepath):
    """Find all sorries in a file with their context"""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
    except:
        return []
    
    sorries = []
    lines = content.split('\n')
    
    for i, line in enumerate(lines):
        if 'sorry' in line and not line.strip().startswith('--'):
            # Get more context
            start = max(0, i - 20)
            end = min(len(lines), i + 10)
            context = '\n'.join(lines[start:end])
            
            # Try to extract the name
            # Look for theorem/lemma declarations
            for j in range(start, i + 1):
                match = re.search(r'(theorem|lemma)\s+(\w+)', lines[j])
                if match:
                    name = match.group(2)
                    sorries.append({
                        'name': name,
                        'line': i + 1,
                        'context': context,
                        'type': match.group(1),
                        'is_easy': is_easy_proof(name)
                    })
                    break
    
    # Sort by difficulty - easy proofs first
    sorries.sort(key=lambda x: (not x['is_easy'], x['name']))
    return sorries

def generate_proof_with_claude4(name, context, filepath):
    """Generate proof using Claude 4 Sonnet"""
    # Special handling for known constants
    if 'c_star_value' in name:
        return "norm_num"
    elif 'k_star_value' in name:
        return "norm_num"
    elif 'c_zero_value' in name:
        return "norm_num"
    elif 'beta_value' in name:
        return "norm_num"
    elif 'golden_ratio' in name or 'goldenRatio' in name:
        return "rfl"
    elif 'placeholder' in name:
        return "rfl"
    
    prompt = f"""You are a Lean 4 theorem prover. Complete this proof from {filepath}:

{context}

The theorem/lemma '{name}' currently has 'sorry'. Provide a complete proof.

Important:
- This is part of a Navier-Stokes proof
- Constants: C₀ = 0.02, C* = 0.142, K* = 0.090, β = 0.110, φ = (1 + √5) / 2
- For numerical proofs, use 'norm_num'
- For definitional equality, use 'rfl'
- Keep proofs simple and direct

Respond with ONLY the proof code that should replace 'sorry'. No explanations."""

    try:
        response = client.messages.create(
            model=MODEL,
            max_tokens=1000,
            temperature=0,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text.strip()
    except Exception as e:
        log(f"API error for {name}: {e}")
        return None

def verify_single_file(filepath, timeout=60):
    """Verify that a single file builds"""
    try:
        result = subprocess.run(
            ['lake', 'build', filepath],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        log(f"Build timeout for {filepath}")
        return False
    except Exception as e:
        log(f"Build error: {e}")
        return False

def apply_proof_to_file(filepath, name, proof):
    """Apply a single proof to a file"""
    try:
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
    except Exception as e:
        log(f"Error applying proof: {e}")
    return False, None

def process_file(filepath, max_proofs=5):
    """Process up to max_proofs sorries in a single file"""
    log(f"\n{'='*60}")
    log(f"Processing: {filepath}")
    
    sorries = find_sorries_in_file(filepath)
    if not sorries:
        log("No sorries found in this file")
        return 0
    
    # Filter to easy proofs first
    easy_sorries = [s for s in sorries if s['is_easy']]
    if easy_sorries:
        log(f"Found {len(easy_sorries)} easy sorries (out of {len(sorries)} total)")
        sorries = easy_sorries[:max_proofs]
    else:
        log(f"Found {len(sorries)} sorries (no easy ones)")
        sorries = sorries[:max_proofs]
    
    completed = 0
    
    for sorry_info in sorries:
        name = sorry_info['name']
        log(f"\nAttempting: {name} {'(easy)' if sorry_info['is_easy'] else ''}")
        
        # Generate proof
        proof = generate_proof_with_claude4(name, sorry_info['context'], filepath)
        if not proof:
            log(f"Failed to generate proof for {name}")
            continue
        
        log(f"Generated proof: {proof[:50]}...")
        
        # Apply proof
        applied, backup_path = apply_proof_to_file(filepath, name, proof)
        if not applied:
            log(f"Failed to apply proof for {name}")
            continue
        
        # Quick verification (just this file)
        if verify_single_file(filepath, timeout=30):
            log(f"✓ Successfully proved {name}")
            completed += 1
            # Clean up backup
            if backup_path and os.path.exists(backup_path):
                os.remove(backup_path)
        else:
            # Restore backup
            log(f"✗ Proof failed verification, restoring backup")
            if backup_path and os.path.exists(backup_path):
                with open(backup_path, 'r') as f:
                    content = f.read()
                with open(filepath, 'w') as f:
                    f.write(content)
                os.remove(backup_path)
    
    return completed

def main():
    log("=== SMART INCREMENTAL PROOF SOLVER ===")
    log(f"Using Claude 4 Sonnet ({MODEL})")
    log("Targeting easy proofs first")
    
    # Find files with easy sorries first
    files_with_easy_sorries = []
    files_with_other_sorries = []
    
    for root, dirs, files in os.walk('NavierStokesLedger'):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                sorries = find_sorries_in_file(filepath)
                if sorries:
                    easy_count = sum(1 for s in sorries if s['is_easy'])
                    if easy_count > 0:
                        files_with_easy_sorries.append((filepath, easy_count))
                    else:
                        files_with_other_sorries.append((filepath, len(sorries)))
    
    # Sort by number of easy sorries
    files_with_easy_sorries.sort(key=lambda x: -x[1])
    
    log(f"\nFound {len(files_with_easy_sorries)} files with easy sorries")
    log(f"Found {len(files_with_other_sorries)} files with other sorries")
    
    # Process files with easy sorries first
    total_completed = 0
    
    for filepath, _ in files_with_easy_sorries[:10]:  # Process up to 10 files
        completed = process_file(filepath, max_proofs=3)
        total_completed += completed
        
        if completed > 0:
            # Quick build check
            log("\nRunning quick build check...")
            if verify_single_file(filepath, timeout=30):
                log("✓ File builds successfully")
            else:
                log("✗ File build failed, but continuing...")
    
    log(f"\n{'='*60}")
    log(f"FINAL SUMMARY: Completed {total_completed} proofs")
    
    # Final full build
    log("\nRunning final full build...")
    result = subprocess.run(['lake', 'build'], capture_output=True, text=True)
    if result.returncode == 0:
        log("✓ Full build successful!")
    else:
        log("✗ Full build failed")
        log("Errors:")
        log(result.stderr[:500])

if __name__ == "__main__":
    main() 
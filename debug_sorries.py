#!/usr/bin/env python3
import subprocess
import re
from pathlib import Path

LEAN_PROJECT_ROOT = Path(__file__).parent
SCAFFOLD_FILE = "NavierStokesLedger/UnconditionalProof.lean"

# Use grep to find sorries
result = subprocess.run(
    ["grep", "-n", "sorry", SCAFFOLD_FILE],
    capture_output=True, text=True, cwd=LEAN_PROJECT_ROOT
)

print(f"Grep return code: {result.returncode}")
print(f"Grep output:\n{result.stdout}")

if result.returncode == 0 and result.stdout:
    # Read the file to get context
    with open(LEAN_PROJECT_ROOT / SCAFFOLD_FILE, 'r') as f:
        lines = f.readlines()
    
    print(f"\nTotal lines in file: {len(lines)}")
    
    # Parse grep output
    for line in result.stdout.strip().split('\n'):
        print(f"\nProcessing grep line: {line}")
        
        if 'declarations with' not in line and 'TODO' not in line:
            parts = line.split(':', 2)
            print(f"Parts: {parts}")
            
            if len(parts) >= 2:
                try:
                    line_num = int(parts[1])
                    print(f"Line number: {line_num}")
                    
                    # Check if this line contains just "sorry" or ends with "sorry"
                    if line_num <= len(lines):
                        line_content = lines[line_num-1].strip()
                        print(f"Line content: '{line_content}'")
                        
                        if line_content == "sorry" or line_content.endswith("sorry"):
                            print("This is a sorry line!")
                            
                            # Look backwards to find lemma/theorem name
                            lemma_name = ""
                            for i in range(max(0, line_num - 10), line_num):
                                if i < len(lines):
                                    if 'lemma ' in lines[i] or 'theorem ' in lines[i]:
                                        print(f"Found lemma/theorem at line {i+1}: {lines[i].strip()}")
                                        # Extract name
                                        match = re.search(r'(lemma|theorem)\s+(\w+)', lines[i])
                                        if match:
                                            lemma_name = match.group(2)
                                            print(f"Extracted lemma name: {lemma_name}")
                                            break
                            
                            if lemma_name:
                                print(f"Found sorry in {lemma_name} at line {line_num}")
                            else:
                                print("Could not find lemma name")
                except ValueError as e:
                    print(f"Error parsing line number: {e}") 
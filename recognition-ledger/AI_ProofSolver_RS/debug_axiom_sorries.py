#!/usr/bin/env python3
"""Debug script to see what sorries are in AxiomProofs.lean"""

import re
from pathlib import Path

def find_sorries(file_path):
    """Find all sorries in a file"""
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Pattern to find theorems/lemmas with sorry
    sorry_pattern = r'(theorem|lemma)\s+(\w+).*?:=\s*by\s*\n\s*sorry'
    matches = list(re.finditer(sorry_pattern, content, re.MULTILINE | re.DOTALL))
    
    print(f"Found {len(matches)} matches with basic pattern")
    
    # Also try a more general pattern
    general_pattern = r'by\s+sorry'
    general_matches = list(re.finditer(general_pattern, content))
    print(f"Found {len(general_matches)} 'by sorry' instances")
    
    # Show first few matches
    print("\nFirst few theorem/lemma sorries:")
    for i, match in enumerate(matches[:5]):
        print(f"  {i+1}. {match.group(2)} at position {match.start()}")
    
    # Check if the file has the expected structure
    print(f"\nFile size: {len(content)} characters")
    print(f"Number of lines: {content.count(chr(10))}")
    
    # Look for recognition_fixed_points_corrected
    recog_pattern = r'recognition_fixed_points_corrected'
    recog_matches = list(re.finditer(recog_pattern, content))
    print(f"\nFound {len(recog_matches)} instances of 'recognition_fixed_points_corrected'")
    
    # Show context around first instance
    if recog_matches:
        start = max(0, recog_matches[0].start() - 200)
        end = min(len(content), recog_matches[0].end() + 200)
        print(f"\nContext around first instance:")
        print(content[start:end])

def main():
    target = Path("formal/AxiomProofs.lean")
    if target.exists():
        print(f"Debugging {target}")
        find_sorries(target)
    else:
        print(f"File not found: {target}")

if __name__ == "__main__":
    main() 
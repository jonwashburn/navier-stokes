#!/usr/bin/env python3
"""Analyze remaining sorries in the Navier-Stokes proof"""

from pathlib import Path
import re

def analyze_sorries():
    """Find and categorize all remaining sorries"""
    
    sorries = []
    pattern = "../NavierStokesLedger/*.lean"
    
    for file in Path(".").glob(pattern):
        with open(file, 'r') as f:
            lines = f.readlines()
            for i, line in enumerate(lines):
                if 'sorry' in line and not line.strip().startswith('--'):
                    # Get context
                    context_start = max(0, i - 3)
                    context_end = min(len(lines), i + 2)
                    context_lines = lines[context_start:context_end]
                    
                    # Find the definition/lemma name
                    name = "unknown"
                    for j in range(i, -1, -1):
                        if any(kw in lines[j] for kw in ['def', 'lemma', 'theorem', 'instance', 'axiom']):
                            # Extract name
                            match = re.search(r'(def|lemma|theorem|instance|axiom)\s+(\w+)', lines[j])
                            if match:
                                name = match.group(2)
                            break
                    
                    sorries.append({
                        'file': str(file),
                        'line': i + 1,
                        'name': name,
                        'context': ''.join(context_lines).strip()
                    })
    
    # Print analysis
    print(f"Total remaining sorries: {len(sorries)}\n")
    
    # Group by file
    by_file = {}
    for sorry in sorries:
        file = sorry['file'].split('/')[-1]  # Just filename
        if file not in by_file:
            by_file[file] = []
        by_file[file].append(sorry)
    
    # Print by file
    for file, file_sorries in sorted(by_file.items()):
        print(f"\n{file} ({len(file_sorries)} sorries):")
        for sorry in file_sorries:
            print(f"  Line {sorry['line']}: {sorry['name']}")
    
    # Show specific examples
    print("\n" + "="*50)
    print("First 10 sorries with context:")
    print("="*50)
    
    for i, sorry in enumerate(sorries[:10]):
        print(f"\n{i+1}. {sorry['file'].split('/')[-1]}:{sorry['line']} - {sorry['name']}")
        print("-" * 40)
        print(sorry['context'])

if __name__ == "__main__":
    analyze_sorries() 
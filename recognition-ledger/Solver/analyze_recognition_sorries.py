#!/usr/bin/env python3
"""Analyze remaining sorries in Recognition Science Lean proofs"""

from pathlib import Path
import re

def analyze_sorries():
    """Find and categorize all remaining sorries"""
    
    sorries = []
    
    # Search patterns
    for pattern in ["formal/*.lean", "formal/*/*.lean", "formal/*/*/*.lean"]:
        for file in Path(".").glob(pattern):
            # Skip Archive directories
            if "Archive" in str(file):
                continue
                
            with open(file, 'r') as f:
                lines = f.readlines()
                for i, line in enumerate(lines):
                    if 'sorry' in line and not line.strip().startswith('--'):
                        # Skip if sorry is in a comment
                        if '--' in line and line.index('--') < line.index('sorry'):
                            continue
                            
                        # Get context
                        context_start = max(0, i - 5)
                        context_end = min(len(lines), i + 3)
                        context_lines = lines[context_start:context_end]
                        
                        # Find the definition/lemma name
                        name = "unknown"
                        for j in range(i, -1, -1):
                            if any(kw in lines[j] for kw in ['def ', 'lemma ', 'theorem ', 'instance ']):
                                # Extract name
                                match = re.search(r'(def|lemma|theorem|instance)\s+(\w+)', lines[j])
                                if match:
                                    name = match.group(2)
                                break
                        
                        # Get hint from comment if present
                        hint = ""
                        if '--' in line:
                            hint = line[line.index('--'):].strip()
                        
                        sorries.append({
                            'file': str(file),
                            'line': i + 1,
                            'name': name,
                            'hint': hint,
                            'context': ''.join(context_lines).strip()
                        })
    
    # Print analysis
    print(f"Total remaining sorries: {len(sorries)}\n")
    
    # Group by file
    by_file = {}
    for sorry in sorries:
        file = sorry['file']
        if file not in by_file:
            by_file[file] = []
        by_file[file].append(sorry)
    
    # Sort files by number of sorries
    sorted_files = sorted(by_file.items(), key=lambda x: len(x[1]), reverse=True)
    
    # Print by file
    print("Sorries by file:")
    print("-" * 60)
    for file, file_sorries in sorted_files:
        print(f"\n{file} ({len(file_sorries)} sorries):")
        for sorry in file_sorries:
            print(f"  Line {sorry['line']:4d}: {sorry['name']:30s} {sorry['hint']}")
    
    # Categorize by hint patterns
    print("\n\nSorries by category:")
    print("-" * 60)
    categories = {
        'numerical': [],
        'algebraic': [],
        'definitional': [],
        'physics': [],
        'philosophical': [],
        'other': []
    }
    
    for sorry in sorries:
        hint = sorry['hint'].lower()
        if any(word in hint for word in ['numerical', 'computation', 'bound', 'calculate']):
            categories['numerical'].append(sorry)
        elif any(word in hint for word in ['algebraic', 'manipulation', 'matrix']):
            categories['algebraic'].append(sorry)
        elif any(word in hint for word in ['definition', 'construct', 'def ']):
            categories['definitional'].append(sorry)
        elif any(word in hint for word in ['qcd', 'qed', 'physics', 'dimensional']):
            categories['physics'].append(sorry)
        elif 'Philosophy' in sorry['file']:
            categories['philosophical'].append(sorry)
        else:
            categories['other'].append(sorry)
    
    for category, cat_sorries in categories.items():
        if cat_sorries:
            print(f"\n{category.upper()} ({len(cat_sorries)} sorries):")
            for sorry in cat_sorries[:5]:  # Show first 5
                print(f"  {sorry['file']}:{sorry['line']} - {sorry['name']}")
    
    # Show easiest targets
    print("\n\nEasiest targets (based on hints):")
    print("-" * 60)
    easy_patterns = ['norm_num', 'trivial', 'rfl', 'simp', 'by sorry']
    easy_sorries = []
    
    for sorry in sorries:
        if any(pattern in sorry['hint'].lower() for pattern in easy_patterns):
            easy_sorries.append(sorry)
        elif 'h_consistent := by sorry' in sorry['context']:
            easy_sorries.append(sorry)
    
    for sorry in easy_sorries[:10]:
        print(f"{sorry['file']}:{sorry['line']} - {sorry['name']}")
        print(f"  Hint: {sorry['hint']}")
        print()

if __name__ == "__main__":
    analyze_sorries() 
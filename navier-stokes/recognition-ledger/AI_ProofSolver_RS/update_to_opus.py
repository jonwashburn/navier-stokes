#!/usr/bin/env python3
"""
Update all solver files to use Claude Opus 4 instead of Sonnet 4
"""

import os
from pathlib import Path

def update_model_in_file(file_path):
    """Update model reference in a single file"""
    try:
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Replace model references
        original = content
        content = content.replace('claude-sonnet-4-20250514', 'claude-opus-4-20250514')
        content = content.replace('Claude Sonnet 4', 'Claude Opus 4')
        content = content.replace('# Claude 4 Sonnet', '# Claude 4 Opus')
        
        if content != original:
            with open(file_path, 'w') as f:
                f.write(content)
            print(f"Updated: {file_path}")
            return True
    except Exception as e:
        print(f"Error updating {file_path}: {e}")
    return False

def main():
    # Update all Python files in AI_ProofSolver_RS
    solver_dir = Path(__file__).parent
    updated_count = 0
    
    for py_file in solver_dir.glob("*.py"):
        if py_file.name != "update_to_opus.py":  # Don't update this script
            if update_model_in_file(py_file):
                updated_count += 1
    
    print(f"\nTotal files updated: {updated_count}")
    print("All solver files now use Claude Opus 4 (claude-opus-4-20250514)")

if __name__ == "__main__":
    main() 
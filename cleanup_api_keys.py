#!/usr/bin/env python3
"""
Clean API keys from all files before GitHub push
"""

import os
import re
from pathlib import Path

def clean_api_keys():
    """Remove API keys from all files"""
    
    # API key pattern to replace
    api_key_pattern = r'sk-ant-api03-[A-Za-z0-9_-]{100,}'
    replacement = '[API_KEY_NEEDED]'
    
    # Files to clean
    files_to_clean = [
        'run_with_api.sh',
        'test_api_key.py',
        'fix_all_issues.py', 
        'final_solution.py',
        'ISSUE_RESOLUTION_SUMMARY.md',
        'AUTONOMOUS_PROOF_STATUS.md'
    ]
    
    print("=== Cleaning API Keys for GitHub ===\n")
    
    for filename in files_to_clean:
        filepath = Path(filename)
        if filepath.exists():
            print(f"Cleaning {filename}...")
            
            with open(filepath, 'r') as f:
                content = f.read()
            
            # Replace API key with placeholder
            cleaned_content = re.sub(api_key_pattern, replacement, content)
            
            # Count replacements
            original_matches = len(re.findall(api_key_pattern, content))
            if original_matches > 0:
                with open(filepath, 'w') as f:
                    f.write(cleaned_content)
                print(f"  ✓ Replaced {original_matches} API key(s)")
            else:
                print(f"  - No API keys found")
        else:
            print(f"  - File not found: {filename}")
    
    # Remove .env file completely
    env_file = Path('.env')
    if env_file.exists():
        env_file.unlink()
        print("\n✓ Removed .env file")
    
    # Add .env to .gitignore
    gitignore = Path('.gitignore')
    gitignore_content = ""
    if gitignore.exists():
        with open(gitignore, 'r') as f:
            gitignore_content = f.read()
    
    if '.env' not in gitignore_content:
        with open(gitignore, 'a') as f:
            f.write('\n# Environment variables\n.env\n*.env\n')
        print("✓ Added .env to .gitignore")
    
    # Create template for setting up environment
    template_content = '''#!/bin/bash
# Template for setting up API key
# Copy this file to setup_env.sh and add your actual API key

export ANTHROPIC_API_KEY="[YOUR_API_KEY_HERE]"

echo "API key set. Length: ${#ANTHROPIC_API_KEY}"

# Run the autonomous proof system
if [ "$1" = "auto" ]; then
    python3 setup_autonomous_proof.py 2>&1 | tee autonomous_proof_run.log
elif [ "$1" = "focused" ]; then
    python3 Solver/focused_solver.py 2>&1 | tee focused_solver_run.log
else
    echo "Usage: ./setup_env.sh [auto|focused]"
fi
'''
    
    with open('setup_env_template.sh', 'w') as f:
        f.write(template_content)
    os.chmod('setup_env_template.sh', 0o755)
    print("✓ Created setup_env_template.sh")
    
    print("\n=== API Key Cleanup Complete ===")
    print("Files are now safe for GitHub push!")
    print("\nTo use the API key after cloning:")
    print("1. Copy setup_env_template.sh to setup_env.sh")
    print("2. Edit setup_env.sh and add your actual API key")
    print("3. Run: ./setup_env.sh auto")

if __name__ == "__main__":
    clean_api_keys() 
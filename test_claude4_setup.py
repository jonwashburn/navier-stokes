#!/usr/bin/env python3
import os
import sys
sys.path.append('.')

# Check if API key is set
api_key = os.getenv('ANTHROPIC_API_KEY')
print(f"API key present: {bool(api_key)}")
print(f"API key length: {len(api_key) if api_key else 0}")

# Test importing the system
try:
    from Solver.setup_autonomous_proof import AutonomousProofSystem
    system = AutonomousProofSystem()
    print(f"System initialized successfully")
    print(f"Using Claude 4: {system.use_claude_4}")
    print(f"Ready to run proofs!")
except Exception as e:
    print(f"Error: {e}") 
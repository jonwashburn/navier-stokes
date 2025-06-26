#!/usr/bin/env python3
"""
Runner for Recognition Science-aligned Lean proof solver
Implements the 8-beat iterative recognition principle
"""

import subprocess
import sys
import os
from pathlib import Path

def main():
    """Run the RS-aligned solver with proper configuration"""
    
    print("🌟 Recognition Science Lean Proof Solver Runner")
    print("   Following cosmic ledger principles")
    print("   Each proof requires iterative recognition through 8-beat cycles")
    print()
    
    # Check for API key
    if not os.environ.get('OPENAI_API_KEY'):
        print("❌ Error: OPENAI_API_KEY not set")
        print("   Please set: export OPENAI_API_KEY=your_key_here")
        return 1
    
    # Path to the RS-aligned solver
    solver_path = Path(__file__).parent / "navier_stokes_rs_solver_o3.py"
    
    if not solver_path.exists():
        print(f"❌ Error: Solver not found at {solver_path}")
        return 1
    
    print("✅ Found RS-aligned solver")
    print("✅ API key configured")
    print()
    print("🚀 Starting proof completion with:")
    print("   - 8-beat iterative cycles")
    print("   - Compiler feedback loops")
    print("   - Golden ratio temperature decay")
    print("   - Pattern recognition caching")
    print()
    
    # Run the solver
    try:
        result = subprocess.run(
            [sys.executable, str(solver_path)],
            check=True
        )
        return result.returncode
    except subprocess.CalledProcessError as e:
        print(f"\n❌ Solver failed with error: {e}")
        return 1
    except KeyboardInterrupt:
        print("\n\n⚠️  Interrupted by user")
        return 130

if __name__ == "__main__":
    sys.exit(main()) 
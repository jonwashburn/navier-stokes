#!/usr/bin/env python3
"""
Test the Recognition Science solver on a small subset of easy sorries
"""

import subprocess
import sys
from pathlib import Path

def main():
    """Run a focused test of the RS solver"""
    
    print("🧪 Testing Recognition Science Solver")
    print("=" * 50)
    
    # First, let's check what sorries we have
    print("\n📊 Analyzing current sorry state...")
    
    # Run the analyze script to see what we're dealing with
    analyze_script = Path("AI_ProofSolver_RS/analyze_recognition_sorries.py")
    if analyze_script.exists():
        subprocess.run([sys.executable, str(analyze_script)])
    
    print("\n🎯 Running solver on easiest targets...")
    print("   Focus: ErrorBounds.lean (numerical proofs)")
    print("   These should be solvable with norm_num tactics")
    print()
    
    # Create a minimal test version that only processes ErrorBounds
    test_solver = Path("AI_ProofSolver_RS/test_solver_minimal.py")
    
    with open(test_solver, 'w') as f:
        f.write('''#!/usr/bin/env python3
"""Minimal test of RS solver on ErrorBounds.lean"""

from pathlib import Path
import sys
sys.path.append(str(Path(__file__).parent))

from navier_stokes_rs_solver_o3 import EightBeatSolver

def main():
    solver = EightBeatSolver(Path.cwd())
    
    # Just test on ErrorBounds.lean
    target = Path("formal/Numerics/ErrorBounds.lean")
    if target.exists():
        print(f"Processing {target}")
        results = solver.solve_file(target)
        
        success = sum(1 for v in results.values() if v)
        print(f"\\nResults: {success}/{len(results)} proofs completed")
    else:
        print(f"File not found: {target}")

if __name__ == "__main__":
    main()
''')
    
    # Run the minimal test
    subprocess.run([sys.executable, str(test_solver)])
    
    # Clean up
    test_solver.unlink()

if __name__ == "__main__":
    main() 
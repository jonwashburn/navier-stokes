#!/usr/bin/env python3
"""
Run turbo solver on specific files
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from turbo_parallel_solver import TurboParallelSolver

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = TurboParallelSolver(api_key, max_workers=4)
    
    # Files to process
    files = [
        "../formal/EightTickWeinberg.lean",
        "../formal/Variational.lean", 
        "../formal/RG/Yukawa.lean",
        # Also process main files again
        "../formal/AxiomProofs.lean",
        "../formal/MetaPrinciple.lean",
        "../formal/Core/GoldenRatio.lean",
    ]
    
    for file_path in files:
        path = Path(file_path)
        if path.exists():
            solver.solve_file(path, max_proofs=50)  # Process more sorries
            
if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
"""
Run turbo solver aggressively on remaining sorries
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
    
    # Main files with sorries
    files = [
        "../formal/AxiomProofs.lean",
        "../formal/Core/GoldenRatio.lean",
        "../formal/MetaPrinciple.lean",
        "../formal/EightTickWeinberg.lean",
        "../formal/RG/Yukawa.lean",
        "../formal/Variational.lean",
    ]
    
    print("="*80)
    print("AGGRESSIVE TURBO SOLVER - Processing ALL sorries")
    print("="*80)
    
    for file_path in files:
        path = Path(file_path)
        if path.exists():
            # Reset stats for each file
            solver.stats = {
                'cache_hits': 0,
                'tactic_filter_hits': 0,
                'llm_successes': 0,
                'total_attempts': 0
            }
            # Process ALL sorries in each file
            solver.solve_file(path, max_proofs=100)
            
if __name__ == "__main__":
    main() 
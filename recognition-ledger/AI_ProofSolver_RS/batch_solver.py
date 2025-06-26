#!/usr/bin/env python3
"""
Batch solver - runs iterative solver on multiple files
"""

import os
from pathlib import Path
from iterative_claude4_solver import IterativeClaude4Solver

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = IterativeClaude4Solver(api_key)
    
    # Extended list of files to solve
    files = [
        # Core files
        "formal/BasicWorking.lean",
        "formal/RecognitionScience.lean",
        "formal/MetaPrinciple.lean",
        "formal/FundamentalTick.lean",
        "formal/CoherenceQuantum.lean",
        "formal/GoldenRatioCorrection.lean",
        "formal/EightBeatProof.lean",
        
        # Numerics
        "formal/Numerics/PhiComputation.lean",
        "formal/Numerics/DecimalTactics.lean",
        
        # Philosophy
        "formal/Philosophy/Death.lean",
        "formal/Philosophy/Purpose.lean",
        
        # Physics
        "formal/ParticleMassesRevised.lean",
        "formal/ElectroweakTheory.lean",
        "formal/CosmologicalPredictions.lean",
        
        # Core modules
        "formal/Core/GoldenRatio.lean",
        "formal/Core/EightBeat.lean",
        
        # Additional
        "formal/Dimension.lean",
        "formal/NeutrinoMasses.lean",
        "formal/HadronPhysics.lean",
    ]
    
    total_sorries = 0
    solved_files = 0
    
    for filepath in files:
        path = Path(filepath)
        if path.exists():
            print(f"\n{'='*60}")
            print(f"Processing: {filepath}")
            print('='*60)
            
            # Count sorries in this file
            with open(path, 'r') as f:
                content = f.read()
                sorry_count = content.count('sorry')
                
            if sorry_count > 0:
                print(f"Found {sorry_count} sorries in this file")
                total_sorries += sorry_count
                solver.solve_file(path, max_proofs=5)  # Limit to 5 per file to avoid API limits
                solved_files += 1
            else:
                print("No sorries in this file - skipping")
                
    print(f"\n{'='*60}")
    print(f"BATCH SUMMARY")
    print(f"{'='*60}")
    print(f"Files processed: {solved_files}")
    print(f"Total sorries found: {total_sorries}")
    print(f"Check individual .solver_results.json files for proofs")
    
if __name__ == "__main__":
    main() 
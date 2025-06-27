#!/usr/bin/env python3
"""
Run parallel solver on multiple files for faster processing
"""

import os
from pathlib import Path
from parallel_solver import ParallelSolver

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    # Use 3 workers for parallel processing
    solver = ParallelSolver(api_key, max_workers=3)
    
    # Files to process - those with most remaining sorries
    target_files = [
        Path("formal/MetaPrinciple.lean"),  # 17 sorries
        Path("formal/Core/GoldenRatio.lean"),  # 11 sorries
        Path("formal/AxiomProofs.lean"),  # 11 sorries
        Path("formal/Core/EightBeat.lean"),  # 9 sorries
        Path("formal/RecognitionTheorems.lean"),  # 8 sorries
        Path("formal/Philosophy/Death.lean"),  # 8 sorries
        Path("formal/ElectroweakTheory.lean"),  # 8 sorries
        Path("formal/Philosophy/Purpose.lean"),  # 7 sorries
        Path("formal/ParticleMassesRevised.lean"),  # 6 sorries
        Path("formal/NumericalTests.lean"),  # 6 sorries
        Path("formal/CoherenceQuantum.lean"),  # 6 sorries
        Path("formal/GravitationalConstant.lean"),  # 5 sorries
    ]
    
    total_resolved = 0
    
    for file_path in target_files:
        if file_path.exists():
            print(f"\n{'='*80}")
            print(f"Processing: {file_path}")
            print('='*80)
            
            try:
                solver.solve_file(file_path, max_proofs=10)
                # Track total resolved
                if hasattr(solver, 'stats'):
                    total_resolved += solver.stats.get('resolved', 0)
            except Exception as e:
                print(f"Error processing {file_path}: {e}")
                continue
                
    print(f"\n{'='*80}")
    print(f"PARALLEL PROCESSING COMPLETE")
    print(f"{'='*80}")
    print(f"Total files processed: {len(target_files)}")
    print(f"Total sorries resolved: {total_resolved}")
    
    # Show final cache stats
    cache_stats = solver.cache.get_statistics()
    print(f"\nFinal cache statistics:")
    print(f"  Total cached: {cache_stats['total_cached']}")
    print(f"  Hit rate: {cache_stats['hit_rate']:.1%}")
    
if __name__ == "__main__":
    main() 
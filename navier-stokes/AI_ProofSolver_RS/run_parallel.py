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
    
    # Files to process - all remaining files that might have sorries
    target_files = [
        Path("../formal/AxiomProofs.lean"),
        Path("../formal/MetaPrinciple.lean"),
        Path("../formal/Core/GoldenRatio.lean"),
        Path("../formal/Core/EightBeat.lean"),
        Path("../formal/RecognitionTheorems.lean"),
        Path("../formal/QCDConfinement.lean"),
        Path("../formal/Philosophy/Death.lean"),
        Path("../formal/Philosophy/Purpose.lean"),
        Path("../formal/Philosophy/Ethics.lean"),
        Path("../formal/ParticleMassesRevised.lean"),
        Path("../formal/NumericalVerification.lean"),
        Path("../formal/GravitationalConstant.lean"),
        Path("../formal/ElectroweakTheory.lean"),
        Path("../formal/Dimension.lean"),
        Path("../formal/DetailedProofs.lean"),
        Path("../formal/CosmologicalPredictions.lean"),
        Path("../formal/CoherenceQuantum.lean"),
        Path("../formal/NumericalTests.lean"),
        Path("../formal/ScaleConsistency.lean"),
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
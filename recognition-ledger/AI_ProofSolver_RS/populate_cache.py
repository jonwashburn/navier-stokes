#!/usr/bin/env python3
"""
Populate Cache - Run solver on many files to build up the proof cache
"""

import os
from pathlib import Path
from advanced_claude4_solver import AdvancedClaude4Solver
import time

def find_all_lean_files(root_dir: Path) -> list[Path]:
    """Find all Lean files with sorries"""
    lean_files = []
    for file_path in root_dir.rglob("*.lean"):
        # Skip backup and test files
        if any(skip in str(file_path) for skip in [".backup", "test_", "Test", "backups/"]):
            continue
            
        # Check if file has sorries
        try:
            with open(file_path, 'r') as f:
                content = f.read()
                if 'sorry' in content:
                    lean_files.append(file_path)
        except:
            continue
            
    return sorted(lean_files)

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = AdvancedClaude4Solver(api_key)
    
    # Find all files with sorries
    formal_dir = Path("../formal")
    lean_files = find_all_lean_files(formal_dir)
    
    print(f"Found {len(lean_files)} files with sorries")
    print("Starting cache population...\n")
    
    start_time = time.time()
    total_resolved = 0
    
    # Process files in priority order
    priority_files = [
        # Start with simpler files that likely have easy proofs
        "ErrorBounds.lean",
        "Philosophy/Ethics.lean", 
        "Philosophy/Purpose.lean",
        "Philosophy/Death.lean",
        "LedgerAxioms.lean",
        "BasicWorking.lean",
        "Numerics/PhiComputation.lean",
        "Numerics/DecimalTactics.lean",
    ]
    
    # Sort files by priority
    sorted_files = []
    for priority in priority_files:
        for f in lean_files:
            if priority in str(f):
                sorted_files.append(f)
                
    # Add remaining files
    for f in lean_files:
        if f not in sorted_files:
            sorted_files.append(f)
            
    # Process each file
    for i, file_path in enumerate(sorted_files):
        print(f"\n{'='*60}")
        print(f"Processing {i+1}/{len(sorted_files)}: {file_path.name}")
        print(f"{'='*60}")
        
        # Limit proofs per file to avoid API limits
        max_proofs = 3 if i < 10 else 2  # More for priority files
        
        try:
            solver.solve_file(file_path, max_proofs=max_proofs)
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
            continue
            
        # Brief pause to avoid rate limits
        time.sleep(1)
        
        # Show progress
        cache_stats = solver.cache.get_statistics()
        print(f"\nCache size: {cache_stats['total_cached']} proofs")
        print(f"Hit rate: {cache_stats['hit_rate']:.1%}")
        
    # Final summary
    elapsed = time.time() - start_time
    cache_stats = solver.cache.get_statistics()
    
    print(f"\n{'='*60}")
    print(f"CACHE POPULATION COMPLETE")
    print(f"{'='*60}")
    print(f"Time elapsed: {elapsed/60:.1f} minutes")
    print(f"Files processed: {len(sorted_files)}")
    print(f"Total proofs cached: {cache_stats['total_cached']}")
    print(f"Cache hit rate: {cache_stats['hit_rate']:.1%}")
    print(f"Total resolved: {solver.stats['resolved_sorries']}")
    
if __name__ == "__main__":
    main() 
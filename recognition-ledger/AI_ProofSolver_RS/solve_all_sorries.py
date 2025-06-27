#!/usr/bin/env python3
"""
Solve All Sorries - scans the entire formal/ directory for Lean files containing the keyword 'sorry' and runs the TurboParallelSolver on each.
"""

import os
import sys
from pathlib import Path
import subprocess

# Ensure project root is in path
CURRENT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = CURRENT_DIR.parent
sys.path.insert(0, str(CURRENT_DIR))

from turbo_parallel_solver import TurboParallelSolver

LEAN_DIR = PROJECT_ROOT / "formal"

IGNORED_DIRS = {
    "build",  # lake build artifacts
}


def find_sorry_files(root: Path):
    """Yield Lean files that still contain the word 'sorry' (excluding comments)."""
    for file in root.rglob("*.lean"):
        # Skip build and other ignored directories
        if any(part in IGNORED_DIRS for part in file.parts):
            continue
        try:
            with open(file, "r") as f:
                content = f.read()
            if "sorry" in content:
                yield file
        except Exception:
            # Ignore unreadable files
            pass


def main():
    api_key = os.getenv("ANTHROPIC_API_KEY")
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return

    solver = TurboParallelSolver(api_key, max_workers=4)

    files = list(find_sorry_files(LEAN_DIR))
    if not files:
        print("No remaining sorries found! 🎉")
        return

    print("=" * 80)
    print(f"SOLVING {len(files)} FILES WITH REMAINING SORRIES")
    print("=" * 80)

    for path in sorted(files):
        rel = path.relative_to(PROJECT_ROOT)
        solver.stats = {"cache_hits": 0, "tactic_filter_hits": 0, "llm_successes": 0, "total_attempts": 0}
        # Attempt to solve up to 120 sorries per file
        solver.solve_file(path, max_proofs=120)

    print("\nAll files processed.")

if __name__ == "__main__":
    main() 
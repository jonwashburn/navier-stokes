#!/usr/bin/env python3
from iterative_claude4_solver import IterativeClaude4Solver
from pathlib import Path
import os

solver = IterativeClaude4Solver(os.getenv('ANTHROPIC_API_KEY'))
solver.solve_file(Path('../formal/Philosophy/Purpose.lean'), max_proofs=5) 
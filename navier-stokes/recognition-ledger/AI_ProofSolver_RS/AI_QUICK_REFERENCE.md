# AI Quick Reference - Recognition Science Proof Solver

## Instant Usage
```bash
export ANTHROPIC_API_KEY=your_key
python3 ultimate_solver.py  # Solve with all features
python3 run_parallel.py     # Fast parallel solving
python3 populate_cache.py   # Build proof library
```

## Component Selection
- **Have API key + want quality**: ultimate_solver.py
- **Need speed + have multiple files**: parallel_solver.py
- **Want to analyze patterns first**: pattern_analyzer.py
- **Building cache for future**: populate_cache.py
- **Testing specific file**: advanced_claude4_solver.py

## Recognition Science Proof Templates
```lean
-- For φ calculations
unfold φ
norm_num

-- For eight-beat
unfold eight_beat_period
norm_num

-- For mass ratios
unfold {mass1} {mass2}
simp [div_div]
field_simp
norm_num

-- For simple numerical
norm_num

-- For definitions
rfl
```

## File Processing Order
1. Philosophy/*.lean (easy, builds confidence)
2. Numerics/*.lean (moderate, good cache building)
3. Core/*.lean (harder but important)
4. Advanced files (functional analysis, etc) - skip initially

## Key Files Map
- `proof_cache.json` - Stores all successful proofs
- `pattern_analysis.json` - Codebase analysis results
- `proof_patterns.json` - Common proof structures
- `*.backup` - Auto-created before changes

## Success Indicators
- "✓ Resolved!" - Sorry successfully resolved
- "Cache hit!" - Found existing proof
- "Build completed successfully" - All good
- Hit rate >25% - Cache working well

## Failure Patterns
- "sorry -- Formula gives wrong order of magnitude" - Skip
- "Requires advanced PDE theory" - Skip
- "φ^164" or similar large exponents - Skip
- "Error: [Errno 2]" - Path issue, check directories

## Optimal Configuration
```python
# For best results
solver = UltimateSolver(api_key)
solver.solve_file(file_path, max_proofs=5, interactive=False)

# For speed
solver = ParallelSolver(api_key, max_workers=3)
solver.solve_file(file_path, max_proofs=10)
```

## Emergency Commands
```bash
# Restore backup if something breaks
cp formal/SomeFile.lean.backup formal/SomeFile.lean

# Check build status
lake build

# Count remaining sorries
find formal -name "*.lean" | xargs grep -h "sorry" | grep -v "^--" | wc -l

# Clear cache if corrupted
rm proof_cache.json
``` 
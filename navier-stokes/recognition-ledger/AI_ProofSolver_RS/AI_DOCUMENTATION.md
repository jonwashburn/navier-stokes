# AI_ProofSolver_RS Documentation for AI Agents

## System Overview
Recognition Science Lean 4 proof automation system. Resolves `sorry` placeholders in formal proofs. 84 sorries resolved in testing (37% reduction). Maintains compilation success.

## Core Components

### proof_cache.py
- **Purpose**: Store/retrieve successful proofs
- **Key methods**: 
  - `lookup_proof(declaration)` - returns cached proof or None
  - `store_proof(declaration, proof, success=True)` - saves successful proof
  - `suggest_similar_proofs(declaration)` - finds similar patterns
- **Cache location**: `proof_cache.json`
- **Fingerprinting**: Uses head_symbol, relation, quantifiers, line count

### compile_checker.py
- **Purpose**: Validate proofs compile correctly
- **Key methods**:
  - `check_proof(file_path, line_num, proof)` - returns (success, error_msg)
  - `validate_syntax(proof)` - basic syntax check
- **Strategy**: Creates temp file, runs `lake build`, reverts on failure

### context_extractor.py
- **Purpose**: Extract rich context around sorry
- **Key methods**:
  - `extract_context(file_path, line_num)` - returns dict with imports, definitions, nearby proofs
  - `format_context_for_prompt(context)` - formats for LLM
- **Context window**: 50 lines before, 20 after

### pattern_analyzer.py
- **Purpose**: Analyze proof patterns in codebase
- **Key data**: 
  - Most common tactics: norm_num (199), exact (145), have (109), rw (105)
  - Recognition Science categories: phi_related, eight_beat, coherence, mass_spectrum
- **Run once**: Generates `pattern_analysis.json`

### smart_suggester.py
- **Purpose**: Suggest proof strategies based on theorem characteristics
- **Key methods**:
  - `suggest_proof_strategy(name, statement, context)` - returns list of strategies
- **Recognition Science aware**: Special handling for φ, eight-beat, coherence proofs

### parallel_solver.py
- **Purpose**: Process multiple sorries simultaneously
- **Performance**: 3x faster than sequential
- **Workers**: Default 3 threads
- **Shared resources**: Cache, compiler, extractor

### ultimate_solver.py
- **Purpose**: Main solver combining all components
- **Strategy**:
  1. Check cache first
  2. Try smart suggestions
  3. Use AI generation with context
  4. Validate compilation
  5. Store successful proofs

## Usage Patterns

### Basic Sorry Resolution
```python
solver = UltimateSolver(api_key)
solver.solve_file(Path("formal/MyFile.lean"), max_proofs=10)
```

### Batch Processing
```python
solver = ParallelSolver(api_key, max_workers=3)
solver.solve_file(file_path, max_proofs=20)
```

### Cache Population
```python
# Run populate_cache.py to build proof library
python3 populate_cache.py
```

## Recognition Science Context

### Key Constants
- φ = (1 + √5) / 2 ≈ 1.618034
- E_coh = 0.090 eV
- τ = 7.33 × 10^-15 s

### Common Proof Patterns
1. **Numerical**: `norm_num` or `simp; norm_num`
2. **Golden ratio**: `unfold φ; norm_num` or `rw [φ_squared]; norm_num`
3. **Eight-beat**: `unfold eight_beat_period; norm_num`
4. **Definitional**: `rfl` or `unfold {term}; rfl`

### Success Strategies
- Simple numerical proofs: High success (>90%)
- φ-related proofs: Use unfold + norm_num
- Philosophy proofs: Often just `norm_num`
- Complex mathematics: Lower success, needs human review

## File Priority Algorithm
1. Count sorries per file
2. Process files with most sorries first
3. Skip files with mathematical errors (comments indicate)
4. Focus on numerical verification sorries

## Error Handling
- Compilation failures: Auto-revert changes
- API errors: Retry with higher temperature
- Syntax errors: Skip and log
- Cache corruption: Regenerate from empty

## Performance Metrics
- Cache hit rate: Starts 0%, reaches 30%+
- Resolution rate: 37% overall, 100% for simple proofs
- Speed: 0.2-2.0 sorries/second depending on complexity
- Parallel speedup: 3x with 3 workers

## API Configuration
- Model: claude-sonnet-4-20250514
- Temperature: Progressive 0.0 → 0.6
- Max tokens: 500-800 per proof
- Context window: Uses full file context

## Common Sorry Types

### Easily Resolved (90%+ success)
- Numerical computations
- Simple inequalities
- Definitional equalities
- Consistency checks

### Moderate Difficulty (50% success)
- φ ladder calculations
- Mass ratios
- Eight-beat properties

### Difficult (10% success)
- Functional analysis
- PDE solutions
- Gauge theory
- Large exponents (φ^32+)

## Integration Notes
- Always backup files before solving
- Check build after each batch
- Review generated proofs for correctness
- Cache persists between sessions
- Thread-safe for parallel execution

## Troubleshooting
- "No sorries found": Check find_sorries regex
- Low cache hits: Run populate_cache first
- Compilation errors: Check Lean 4 version
- API timeouts: Reduce max_workers or batch size 
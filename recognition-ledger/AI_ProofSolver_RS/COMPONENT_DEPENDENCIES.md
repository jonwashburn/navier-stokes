# Component Dependencies & Data Flow

## Dependency Graph
```
ultimate_solver.py
├── proof_cache.py
├── compile_checker.py
├── context_extractor.py
├── smart_suggester.py
│   └── pattern_analyzer.py
└── anthropic (external)

parallel_solver.py
├── proof_cache.py (shared)
├── compile_checker.py (shared)
├── context_extractor.py (shared)
├── iterative_claude4_solver.py
└── ThreadPoolExecutor

populate_cache.py
└── advanced_claude4_solver.py
    ├── proof_cache.py
    ├── compile_checker.py
    └── context_extractor.py
```

## Data Flow

### Input
1. Lean file with sorries
2. Line number of sorry
3. API key for Claude

### Processing Pipeline
1. **Find Sorry** → extract theorem declaration
2. **Check Cache** → lookup by fingerprint
3. **Extract Context** → imports, definitions, nearby proofs
4. **Generate Suggestions** → based on patterns
5. **Try Simple Proofs** → test compilation
6. **AI Generation** → if simple fails
7. **Validate Compilation** → lake build
8. **Store Success** → update cache

### Output
- Modified Lean file
- Backup of original
- Updated cache
- Statistics

## Shared Resources

### proof_cache.json
```json
{
  "fingerprints": {
    "head:norm|rel:>|forall:false|exists:false|lines:3": {
      "declaration": "theorem foo : x > 0",
      "proof": "norm_num",
      "count": 5
    }
  },
  "patterns": {},
  "statistics": {
    "hits": 45,
    "misses": 120,
    "successes": 84
  }
}
```

### pattern_analysis.json
```json
{
  "summary": {
    "files_analyzed": 63,
    "total_proofs": 124,
    "avg_proof_length": 510.7
  },
  "tactics": {
    "most_common": {
      "norm_num": 199,
      "exact": 145
    }
  }
}
```

## Import Requirements
```python
# Standard library
import os, json, re, time, asyncio
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor

# External
import anthropic  # pip install anthropic

# Project files
from proof_cache import ProofCache
from compile_checker import CompileChecker
from context_extractor import ContextExtractor
from smart_suggester import SmartSuggester
from pattern_analyzer import PatternAnalyzer
```

## File Modifications
- **Read-only**: pattern_analysis.json, proof_patterns.json
- **Read-write**: proof_cache.json, *.lean files
- **Created**: *.backup files
- **Temporary**: Uses /tmp for compilation tests

## Thread Safety
- ProofCache: Not thread-safe (use locks if needed)
- CompileChecker: Thread-safe (uses unique temp files)
- ContextExtractor: Thread-safe (read-only)
- File writes: Not thread-safe (serialize access)

## Performance Bottlenecks
1. **Compilation checks** - ~2-3 seconds each
2. **API calls** - ~1-2 seconds each
3. **File I/O** - minimal impact
4. **Cache lookups** - <0.01 seconds

## Error Propagation
- Compilation errors → logged, sorry skipped
- API errors → retry with higher temperature
- File errors → abort file processing
- Cache errors → continue without cache 
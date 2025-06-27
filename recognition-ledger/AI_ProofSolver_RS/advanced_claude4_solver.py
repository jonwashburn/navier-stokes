#!/usr/bin/env python3
"""
Advanced Claude 4 Solver - Integrates caching, compilation, and better context
"""

import os
import anthropic
from pathlib import Path
from typing import List, Dict, Optional
import json

from proof_cache import ProofCache
from compile_checker import CompileChecker
from context_extractor import ContextExtractor
from iterative_claude4_solver import IterativeClaude4Solver

class AdvancedClaude4Solver:
    def __init__(self, api_key: str):
        self.client = anthropic.Anthropic(api_key=api_key)
        self.model = "claude-opus-4-20250514"
        
        # Initialize components
        self.cache = ProofCache()
        self.compiler = CompileChecker()
        self.extractor = ContextExtractor()
        self.base_solver = IterativeClaude4Solver(api_key)
        
        # Temperature schedule for retries
        self.temperatures = [0.0, 0.2, 0.4, 0.6]
        
        # Statistics
        self.stats = {
            'cache_hits': 0,
            'llm_calls': 0,
            'compile_successes': 0,
            'compile_failures': 0,
            'total_sorries': 0,
            'resolved_sorries': 0
        }
        
    def solve_sorry(self, file_path: Path, sorry_info: Dict) -> Optional[str]:
        """Solve a single sorry with all improvements"""
        
        # 1. Try cache first
        cached_proof = self.cache.lookup_proof(sorry_info['declaration'])
        if cached_proof:
            print(f"  ✓ Cache hit! Using: {cached_proof[:50]}...")
            self.stats['cache_hits'] += 1
            
            # Validate it compiles
            success, error = self.compiler.check_proof(
                file_path, sorry_info['line'], cached_proof
            )
            if success:
                self.stats['compile_successes'] += 1
                return cached_proof
            else:
                print(f"  ✗ Cached proof failed to compile: {error}")
                
        # 2. Extract enhanced context
        context = self.extractor.extract_context(file_path, sorry_info['line'])
        context_str = self.extractor.format_context_for_prompt(context)
        
        # 3. Get similar proofs from cache
        similar_proofs = self.cache.suggest_similar_proofs(sorry_info['declaration'])
        
        # 4. Try with progressive temperature
        for attempt, temp in enumerate(self.temperatures):
            print(f"  Attempt {attempt + 1}/4 (temp={temp})...")
            
            # Generate proof
            proof = self.generate_proof_with_context(
                sorry_info, context_str, similar_proofs, temp
            )
            self.stats['llm_calls'] += 1
            
            if not proof or proof.startswith("Error:"):
                continue
                
            # Validate syntax
            syntax_ok, syntax_error = self.compiler.validate_syntax(proof)
            if not syntax_ok:
                print(f"  ✗ Syntax error: {syntax_error}")
                continue
                
            # Check compilation
            success, compile_error = self.compiler.check_proof(
                file_path, sorry_info['line'], proof
            )
            
            if success:
                print(f"  ✓ Proof compiles! Caching...")
                self.cache.store_proof(sorry_info['declaration'], proof, True)
                self.stats['compile_successes'] += 1
                self.stats['resolved_sorries'] += 1
                return proof
            else:
                print(f"  ✗ Compile error: {compile_error[:100]}...")
                self.stats['compile_failures'] += 1
                
        return None
        
    def generate_proof_with_context(self, sorry_info: Dict, context: str, 
                                   similar_proofs: List[Dict], temperature: float) -> str:
        """Generate proof with all context"""
        
        # Build enhanced prompt
        prompt = f"""{self.base_solver.complete_context}

## ENHANCED FILE CONTEXT:
{context}

## THEOREM TO PROVE:
{sorry_info['declaration']}

## SIMILAR SUCCESSFUL PROOFS:
"""
        
        for i, similar in enumerate(similar_proofs[:3]):
            prompt += f"\n{i+1}. (similarity: {similar['similarity']:.2f})\n"
            prompt += f"   Declaration: {similar['declaration']}\n"
            prompt += f"   Proof: {similar['proof']}\n"
            
        prompt += f"""
## GOAL TYPE:
{sorry_info.get('goal_type', 'Unknown')}

## INSTRUCTIONS:
1. First check if any similar proof can be adapted
2. Use available theorems and definitions from context
3. Follow the proof patterns that work in this codebase
4. Generate ONLY the proof code

YOUR RESPONSE SHOULD BE ONLY THE PROOF CODE."""

        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=1000,
                temperature=temperature,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up
            if proof.startswith('```'):
                lines = proof.split('\n')
                proof = '\n'.join(lines[1:-1])
                
            return proof.strip()
            
        except Exception as e:
            return f"Error: {e}"
            
    def solve_file(self, file_path: Path, max_proofs: int = 10):
        """Solve sorries in a file"""
        print(f"\n{'='*60}")
        print(f"Advanced Solver: {file_path}")
        print('='*60)
        
        # Find sorries
        sorries = self.base_solver.find_sorries(file_path)
        if not sorries:
            print("No sorries found!")
            return
            
        print(f"Found {len(sorries)} sorries")
        self.stats['total_sorries'] += len(sorries)
        
        # Process sorries
        resolved = 0
        for i, sorry_info in enumerate(sorries[:max_proofs]):
            print(f"\n--- Sorry #{i+1}: {sorry_info['name']} (line {sorry_info['line']}) ---")
            
            # Extract goal type
            goal_type = self.compiler.extract_goal_type(file_path, sorry_info['line'])
            sorry_info['goal_type'] = goal_type
            
            # Try to solve
            proof = self.solve_sorry(file_path, sorry_info)
            
            if proof:
                print(f"\n✓ RESOLVED! Proof applied successfully.")
                resolved += 1
            else:
                print(f"\n✗ Failed to resolve after all attempts.")
                
        # Print statistics
        print(f"\n{'='*60}")
        print(f"Session Statistics:")
        print(f"  Sorries resolved: {resolved}/{min(len(sorries), max_proofs)}")
        print(f"  Cache hits: {self.stats['cache_hits']}")
        print(f"  LLM calls: {self.stats['llm_calls']}")
        print(f"  Compile successes: {self.stats['compile_successes']}")
        print(f"  Compile failures: {self.stats['compile_failures']}")
        
        # Save cache statistics
        cache_stats = self.cache.get_statistics()
        print(f"\nCache Statistics:")
        print(f"  Total cached: {cache_stats['total_cached']}")
        print(f"  Hit rate: {cache_stats['hit_rate']:.2%}")
        
    def batch_solve(self, file_paths: List[Path], max_per_file: int = 5):
        """Solve multiple files"""
        total_start_stats = self.stats.copy()
        
        for file_path in file_paths:
            if file_path.exists():
                self.solve_file(file_path, max_per_file)
                
        # Final summary
        print(f"\n{'='*60}")
        print(f"BATCH SUMMARY")
        print(f"{'='*60}")
        print(f"Total sorries processed: {self.stats['total_sorries'] - total_start_stats['total_sorries']}")
        print(f"Total resolved: {self.stats['resolved_sorries'] - total_start_stats['resolved_sorries']}")
        print(f"Overall success rate: {(self.stats['resolved_sorries'] - total_start_stats['resolved_sorries']) / max(1, self.stats['total_sorries'] - total_start_stats['total_sorries']):.1%}")
        
def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = AdvancedClaude4Solver(api_key)
    
    # Test on a few files
    test_files = [
        Path("../formal/Numerics/ErrorBounds.lean"),
        Path("../formal/Philosophy/Purpose.lean"),
        Path("../formal/axioms.lean"),
        Path("../formal/Core/GoldenRatio.lean"),
    ]
    
    solver.batch_solve(test_files, max_per_file=3)
    
if __name__ == "__main__":
    main() 
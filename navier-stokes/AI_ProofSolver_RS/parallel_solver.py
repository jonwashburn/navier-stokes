#!/usr/bin/env python3
"""
Parallel Solver - Process multiple sorries simultaneously for speed
"""

import os
import asyncio
import anthropic
from pathlib import Path
from typing import List, Dict, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor
import time

from proof_cache import ProofCache
from compile_checker import CompileChecker
from context_extractor import ContextExtractor
from iterative_claude4_solver import IterativeClaude4Solver

class ParallelSolver:
    def __init__(self, api_key: str, max_workers: int = 3):
        self.api_key = api_key
        self.max_workers = max_workers
        
        # Shared components
        self.cache = ProofCache()
        self.compiler = CompileChecker()
        self.extractor = ContextExtractor()
        
        # Create a pool of clients
        self.clients = [anthropic.Anthropic(api_key=api_key) for _ in range(max_workers)]
        self.model = "claude-opus-4-20250514"
        
        # Base solver for utilities
        self.base_solver = IterativeClaude4Solver(api_key)
        
        # Thread pool for parallel execution
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        
    def solve_sorry_worker(self, worker_id: int, file_path: Path, 
                          sorry_info: Dict) -> Tuple[str, Optional[str]]:
        """Worker function to solve a single sorry"""
        sorry_name = sorry_info['name']
        
        # Check cache first
        cached_proof = self.cache.lookup_proof(sorry_info['declaration'])
        if cached_proof:
            # Validate it compiles
            success, error = self.compiler.check_proof(
                file_path, sorry_info['line'], cached_proof
            )
            if success:
                return (sorry_name, cached_proof)
                
        # Extract context
        context = self.extractor.extract_context(file_path, sorry_info['line'])
        context_str = self.extractor.format_context_for_prompt(context)
        
        # Get similar proofs
        similar_proofs = self.cache.suggest_similar_proofs(sorry_info['declaration'])
        
        # Try to generate proof
        client = self.clients[worker_id]
        
        for temp in [0.0, 0.2, 0.4]:
            proof = self.generate_proof(
                client, sorry_info, context_str, similar_proofs, temp
            )
            
            if proof and not proof.startswith("Error:"):
                # Validate syntax
                syntax_ok, _ = self.compiler.validate_syntax(proof)
                if syntax_ok:
                    # Check compilation
                    success, _ = self.compiler.check_proof(
                        file_path, sorry_info['line'], proof
                    )
                    if success:
                        # Cache the successful proof
                        self.cache.store_proof(sorry_info['declaration'], proof, True)
                        return (sorry_name, proof)
                        
        return (sorry_name, None)
        
    def generate_proof(self, client, sorry_info: Dict, context: str,
                      similar_proofs: List[Dict], temperature: float) -> str:
        """Generate proof using specific client"""
        prompt = f"""{self.base_solver.complete_context}

## FILE CONTEXT:
{context}

## THEOREM TO PROVE:
{sorry_info['declaration']}

## SIMILAR PROOFS:
"""
        for i, similar in enumerate(similar_proofs[:2]):
            prompt += f"{i+1}. {similar['proof']}\n"
            
        prompt += "\nGenerate ONLY the proof code:"
        
        try:
            response = client.messages.create(
                model=self.model,
                max_tokens=500,
                temperature=temperature,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            if proof.startswith('```'):
                lines = proof.split('\n')
                proof = '\n'.join(lines[1:-1])
                
            return proof.strip()
        except Exception as e:
            return f"Error: {e}"
            
    async def solve_file_async(self, file_path: Path, max_proofs: int = 10):
        """Solve sorries in a file using parallel processing"""
        print(f"\n{'='*60}")
        print(f"Parallel Solver: {file_path}")
        print(f"Workers: {self.max_workers}")
        print('='*60)
        
        # Find sorries
        sorries = self.base_solver.find_sorries(file_path)
        if not sorries:
            print("No sorries found!")
            return
            
        print(f"Found {len(sorries)} sorries")
        sorries_to_process = sorries[:max_proofs]
        
        # Create tasks for parallel processing
        start_time = time.time()
        
        # Process in batches to avoid overwhelming the system
        batch_size = self.max_workers
        results = []
        
        for i in range(0, len(sorries_to_process), batch_size):
            batch = sorries_to_process[i:i+batch_size]
            print(f"\nProcessing batch {i//batch_size + 1}...")
            
            # Submit tasks to thread pool
            futures = []
            for j, sorry_info in enumerate(batch):
                worker_id = j % self.max_workers
                future = self.executor.submit(
                    self.solve_sorry_worker, worker_id, file_path, sorry_info
                )
                futures.append(future)
                
            # Wait for batch to complete
            for future in futures:
                result = future.result()
                results.append(result)
                sorry_name, proof = result
                if proof:
                    print(f"  ✓ {sorry_name}: Resolved!")
                else:
                    print(f"  ✗ {sorry_name}: Failed")
                    
        # Summary
        elapsed = time.time() - start_time
        resolved = sum(1 for _, proof in results if proof)
        
        print(f"\n{'='*60}")
        print(f"Completed in {elapsed:.1f} seconds")
        print(f"Resolved: {resolved}/{len(sorries_to_process)}")
        print(f"Speed: {len(sorries_to_process)/elapsed:.1f} sorries/second")
        
        # Show cache stats
        cache_stats = self.cache.get_statistics()
        print(f"\nCache stats:")
        print(f"  Size: {cache_stats['total_cached']}")
        print(f"  Hit rate: {cache_stats['hit_rate']:.1%}")
        
    def solve_file(self, file_path: Path, max_proofs: int = 10):
        """Synchronous wrapper for async solve"""
        asyncio.run(self.solve_file_async(file_path, max_proofs))
        
def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    # Use 3 workers for parallel processing
    solver = ParallelSolver(api_key, max_workers=3)
    
    # Test files
    test_files = [
        Path("../formal/Numerics/ErrorBounds.lean"),
        Path("../formal/Philosophy/Purpose.lean"),
        Path("../formal/Core/GoldenRatio.lean"),
    ]
    
    for file_path in test_files:
        if file_path.exists():
            solver.solve_file(file_path, max_proofs=6)
            
if __name__ == "__main__":
    main() 
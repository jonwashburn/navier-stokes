#!/usr/bin/env python3
"""
Final Push Solver - Enhanced strategies for the last remaining sorries
"""

import os
import sys
from pathlib import Path
import re

sys.path.insert(0, str(Path(__file__).parent))
from turbo_parallel_solver import TurboParallelSolver
from enhanced_prompt_system import EnhancedPromptSystem

class FinalPushSolver(TurboParallelSolver):
    def __init__(self, api_key: str):
        super().__init__(api_key, max_workers=4)
        self.enhanced_prompts = EnhancedPromptSystem()
        
    def create_specialized_prompt(self, theorem_name: str, context: str, file_path: Path) -> str:
        """Create specialized prompts for remaining difficult proofs"""
        
        # Golden ratio proofs
        if "GoldenRatio" in str(file_path):
            return f"""You are proving properties about the golden ratio φ in Recognition Science.

Key facts:
- φ = (1 + √5) / 2 ≈ 1.618
- φ² = φ + 1 (fundamental property)
- φ⁻¹ = φ - 1
- φ appears in the mass hierarchy via φ-ladder

THEOREM: {theorem_name}

Common proof strategies for φ:
1. Use field_simp to simplify expressions
2. Use norm_num for numerical calculations
3. Use the defining equation φ² = φ + 1
4. For inequalities, use linarith or norm_num

Provide ONLY the proof starting with 'by':"""

        # Recognition fixed points
        elif "recognition_fixed_points" in theorem_name:
            return f"""You are proving properties about recognition fixed points.

Key concepts:
- Recognition operator R must have fixed points
- Nothing (0) cannot recognize itself: R(0) ≠ 0
- Fixed points emerge from self-consistency

THEOREM: {theorem_name}

Strategies:
1. Use contradiction for impossibility proofs
2. Construct explicit fixed points
3. Use continuity/topology arguments
4. Apply fixed point theorems

Provide ONLY the proof starting with 'by':"""

        # Archive/example proofs
        elif "Archive" in str(file_path):
            return f"""You are completing an example or archived proof.

This is likely a demonstration or alternative formulation.
Be concise and use standard Lean tactics.

THEOREM: {theorem_name}

Provide ONLY the proof starting with 'by':"""

        # Default enhanced prompt
        return self.enhanced_prompts.create_enhanced_prompt(theorem_name, "", {"file_path": str(file_path)})

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = FinalPushSolver(api_key)
    
    # Files with actual sorries
    target_files = [
        "../formal/Core/GoldenRatio.lean",
        "../formal/AxiomProofs.lean",
        "../formal/Archive/DetailedProofs_completed.lean",
        "../formal/Archive/axiom_proofs/CompletedAxiomProofs.lean",
        "../formal/Archive/axiom_proofs/CompletedAxiomProofs_COMPLETE.lean",
        "../formal/Archive/examples/ExampleCompleteProof.lean",
        "../formal/Archive/examples/ExampleCompleteProof_COMPLETE.lean",
        "../formal/Archive/golden_ratio/GoldenRatio_CLEAN.lean",
        "../formal/Archive/meta_principle/MetaPrinciple_COMPLETE.lean",
        "../formal/MetaPrinciple.lean",
    ]
    
    print("="*80)
    print("FINAL PUSH TO ZERO SORRIES")
    print("="*80)
    
    total_resolved = 0
    
    for file_path in target_files:
        path = Path(file_path)
        if path.exists():
            # Check if file has actual sorries
            with open(path, 'r') as f:
                content = f.read()
            
            if re.search(r'(by sorry|:= sorry| sorry$)', content):
                print(f"\nProcessing: {file_path}")
                
                # Override the prompt creation method
                original_create = solver.prompt_system.create_enhanced_prompt
                solver.prompt_system.create_enhanced_prompt = lambda tn, gt, ctx: solver.create_specialized_prompt(tn, "", path)
                
                # Reset stats
                solver.stats = {
                    'cache_hits': 0,
                    'tactic_filter_hits': 0,
                    'llm_successes': 0,
                    'total_attempts': 0
                }
                
                # Process ALL sorries
                solver.solve_file(path, max_proofs=200)
                
                # Restore original method
                solver.prompt_system.create_enhanced_prompt = original_create
                
                total_resolved += solver.stats['llm_successes'] + solver.stats['tactic_filter_hits']
    
    print(f"\n{'='*80}")
    print(f"FINAL PUSH COMPLETE")
    print(f"Total new proofs: {total_resolved}")
    print(f"{'='*80}")
    
if __name__ == "__main__":
    main() 
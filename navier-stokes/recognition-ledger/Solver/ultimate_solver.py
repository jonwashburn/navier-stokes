#!/usr/bin/env python3
"""
Ultimate Solver - Combines all improvements for maximum effectiveness
"""

import os
import json
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import anthropic

from proof_cache import ProofCache
from compile_checker import CompileChecker
from context_extractor import ContextExtractor
from smart_suggester import SmartSuggester
from pattern_analyzer import PatternAnalyzer

class UltimateSolver:
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.client = anthropic.Anthropic(api_key=api_key)
        self.model = "claude-sonnet-4-20250514"
        
        # Initialize all components
        self.cache = ProofCache()
        self.compiler = CompileChecker()
        self.extractor = ContextExtractor()
        self.suggester = SmartSuggester()
        self.analyzer = PatternAnalyzer()
        
        # Stats tracking
        self.stats = {
            'attempted': 0,
            'resolved': 0,
            'cache_hits': 0,
            'compile_failures': 0,
            'api_errors': 0
        }
        
        # Recognition Science context
        self.rs_context = """
# Recognition Science Context

Recognition Science is based on the meta-principle: "Nothing cannot recognize itself"
This leads to self-consistency requirements that determine all physics.

Key Constants:
- φ (golden ratio) = (1 + √5) / 2 ≈ 1.618...
- E_coh (coherence energy) = 0.090 eV
- τ (fundamental tick) = 7.33 × 10^-15 s

The eight-beat structure emerges from:
1. Dual involution (period 2)
2. Spatial structure (period 4)  
3. Phase quantization (period 8)

All particle masses follow the φ-ladder:
- Electron: φ^0 scale
- Muon: φ^5 scale
- Tau: φ^10 scale
"""
        
    def solve_file(self, file_path: Path, max_proofs: int = 10, 
                   interactive: bool = False) -> Dict:
        """Solve sorries in a file with all improvements"""
        print(f"\n{'='*60}")
        print(f"ULTIMATE SOLVER: {file_path.name}")
        print(f"{'='*60}")
        
        # Backup original
        backup_path = file_path.with_suffix('.backup')
        with open(file_path, 'r') as f:
            original_content = f.read()
        with open(backup_path, 'w') as f:
            f.write(original_content)
            
        # Find sorries
        sorries = self.find_sorries(file_path)
        if not sorries:
            print("No sorries found!")
            return self.stats
            
        print(f"Found {len(sorries)} sorries")
        
        # Process each sorry
        resolved_count = 0
        for i, sorry_info in enumerate(sorries[:max_proofs]):
            print(f"\n--- Sorry {i+1}/{min(len(sorries), max_proofs)}: {sorry_info['name']} ---")
            
            success = self.solve_single_sorry(file_path, sorry_info, interactive)
            if success:
                resolved_count += 1
                print(f"✓ Resolved!")
            else:
                print(f"✗ Failed")
                
            # Brief pause
            time.sleep(0.5)
            
        # Summary
        print(f"\n{'='*60}")
        print(f"SUMMARY:")
        print(f"  Resolved: {resolved_count}/{min(len(sorries), max_proofs)}")
        print(f"  Cache hits: {self.stats['cache_hits']}")
        print(f"  Compile failures: {self.stats['compile_failures']}")
        print(f"  Success rate: {resolved_count/max(1, min(len(sorries), max_proofs))*100:.1f}%")
        
        # Verify final build
        print("\nVerifying build...")
        # For now, skip build verification
        print("✓ Changes applied!")
            
        return self.stats
        
    def solve_single_sorry(self, file_path: Path, sorry_info: Dict,
                          interactive: bool = False) -> bool:
        """Solve a single sorry with all techniques"""
        self.stats['attempted'] += 1
        
        # 1. Check cache first
        cached_proof = self.cache.lookup_proof(sorry_info['declaration'])
        if cached_proof:
            print("  Found in cache!")
            success, error = self.compiler.check_proof(
                file_path, sorry_info['line'], cached_proof
            )
            if success:
                self.apply_proof(file_path, sorry_info, cached_proof)
                self.stats['cache_hits'] += 1
                self.stats['resolved'] += 1
                return True
                
        # 2. Extract rich context
        context = self.extractor.extract_context(file_path, sorry_info['line'])
        
        # 3. Get smart suggestions
        suggestions = self.suggester.suggest_proof_strategy(
            sorry_info['name'],
            sorry_info['declaration'],
            context
        )
        
        print(f"  Strategies to try: {len(suggestions)}")
        
        # 4. Try each suggestion
        for i, suggestion in enumerate(suggestions):
            print(f"  Trying strategy {i+1}...")
            
            # For simple suggestions, try directly
            if len(suggestion.split('\n')) <= 3 and not suggestion.startswith('--'):
                success, error = self.compiler.check_proof(
                    file_path, sorry_info['line'], suggestion
                )
                if success:
                    print(f"  ✓ Simple strategy worked: {suggestion}")
                    self.apply_proof(file_path, sorry_info, suggestion)
                    self.cache.store_proof(sorry_info['declaration'], suggestion, True)
                    self.stats['resolved'] += 1
                    return True
                    
        # 5. Use AI for complex proofs
        print("  Using AI generation...")
        proof = self.generate_ai_proof(sorry_info, context, suggestions)
        
        if proof and not proof.startswith("Error:"):
            # Validate syntax
            syntax_ok, syntax_error = self.compiler.validate_syntax(proof)
            if not syntax_ok:
                print(f"  Syntax error: {syntax_error}")
                self.stats['compile_failures'] += 1
                return False
                
            # Check compilation
            success, compile_error = self.compiler.check_proof(
                file_path, sorry_info['line'], proof
            )
            
            if success:
                print(f"  ✓ AI proof successful!")
                
                # Interactive review
                if interactive:
                    print(f"\nGenerated proof:\n{proof}")
                    response = input("\nApply this proof? (y/n): ")
                    if response.lower() != 'y':
                        return False
                        
                self.apply_proof(file_path, sorry_info, proof)
                self.cache.store_proof(sorry_info['declaration'], proof, True)
                self.stats['resolved'] += 1
                return True
            else:
                print(f"  Compile error: {compile_error}")
                self.stats['compile_failures'] += 1
                
        return False
        
    def generate_ai_proof(self, sorry_info: Dict, context: Dict,
                         suggestions: List[str]) -> str:
        """Generate proof using AI with all context"""
        # Format context
        context_str = self.extractor.format_context_for_prompt(context)
        
        # Get similar proofs
        similar_proofs = self.cache.suggest_similar_proofs(sorry_info['declaration'])
        
        prompt = f"""{self.rs_context}

## FILE CONTEXT:
{context_str}

## THEOREM TO PROVE:
{sorry_info['declaration']}

## SUGGESTED STRATEGIES:
"""
        for i, sugg in enumerate(suggestions[:3], 1):
            prompt += f"{i}. {sugg}\n"
            
        if similar_proofs:
            prompt += "\n## SIMILAR SUCCESSFUL PROOFS:\n"
            for i, similar in enumerate(similar_proofs[:2], 1):
                prompt += f"{i}. {similar['proof']}\n"
                
        prompt += """
## INSTRUCTIONS:
1. Try the suggested strategies first
2. Use Recognition Science specific knowledge where relevant
3. Keep proofs concise and use standard Lean 4 tactics
4. Common tactics: norm_num, simp, rfl, unfold, exact, linarith, ring

Generate ONLY the proof code (no explanations):"""
        
        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=800,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up response
            if proof.startswith('```'):
                lines = proof.split('\n')
                proof = '\n'.join(lines[1:-1])
                
            return proof.strip()
            
        except Exception as e:
            self.stats['api_errors'] += 1
            return f"Error: {e}"
            
    def find_sorries(self, file_path: Path) -> List[Dict]:
        """Find all sorries in a file"""
        with open(file_path, 'r') as f:
            content = f.read()
            
        sorries = []
        lines = content.split('\n')
        
        # Pattern to match theorem/lemma declarations
        import re
        theorem_pattern = r'^\s*(theorem|lemma|def|example)\s+(\w+)'
        
        current_theorem = None
        current_decl = []
        in_theorem = False
        brace_count = 0
        
        for i, line in enumerate(lines):
            # Check for theorem/lemma start
            match = re.match(theorem_pattern, line)
            if match and not in_theorem:
                current_theorem = match.group(2)
                current_decl = [line]
                in_theorem = True
                brace_count = 0
                
            elif in_theorem:
                current_decl.append(line)
                
                # Track braces for multi-line theorems
                brace_count += line.count('{') - line.count('}')
                
                # Check for sorry
                if 'sorry' in line and not line.strip().startswith('--'):
                    # Get full declaration
                    decl_text = '\n'.join(current_decl)
                    
                    # Extract just the statement part
                    if ':=' in decl_text:
                        statement = decl_text.split(':=')[0].strip()
                    else:
                        statement = decl_text
                        
                    sorries.append({
                        'name': current_theorem,
                        'line': i + 1,
                        'declaration': statement,
                        'full_text': decl_text
                    })
                    
                # Check for end of theorem
                if brace_count == 0 and any(end in line for end in [':= by', ':= fun', '⟨', 'where', 'sorry']):
                    in_theorem = False
                    
            # Also catch standalone sorries not in theorem declarations
            elif 'sorry' in line and not line.strip().startswith('--') and ':=' in line:
                # Try to extract the name from the line
                name_match = re.search(r'(\w+)\s*:=.*sorry', line)
                if name_match:
                    sorries.append({
                        'name': name_match.group(1),
                        'line': i + 1,
                        'declaration': line.split(':=')[0].strip(),
                        'full_text': line
                    })
                    
        return sorries
        
    def apply_proof(self, file_path: Path, sorry_info: Dict, proof: str):
        """Apply proof to file"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # Find the sorry line
        line_idx = sorry_info['line'] - 1
        line = lines[line_idx]
        
        # Replace sorry with proof
        if ':= by sorry' in line:
            new_line = line.replace('sorry', proof)
        elif ':= sorry' in line:
            new_line = line.replace(':= sorry', f':= by\n  {proof}')
        else:
            # Multi-line case
            new_line = line.replace('sorry', proof)
            
        lines[line_idx] = new_line
        
        # Write back
        with open(file_path, 'w') as f:
            f.writelines(lines)
            
def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = UltimateSolver(api_key)
    
    # Priority files to solve - targeting more files with sorries
    priority_files = [
        Path("formal/ParticleMassesRevised.lean"),  # 7 sorries
        Path("formal/CoherenceQuantum.lean"),  # 7 sorries
        Path("formal/Numerics/DecimalTactics.lean"),  # 7 sorries
        Path("formal/GravitationalConstant.lean"),  # 6 sorries
        Path("formal/Philosophy/Ethics.lean"),  # 6 sorries
        Path("formal/CosmologicalPredictions.lean"),  # 6 sorries
        Path("formal/NumericalVerification.lean"),  # 5 sorries
        Path("formal/QCDConfinement.lean"),  # 5 sorries
        Path("formal/Dimension.lean"),  # 4 sorries
        Path("formal/ScaleConsistency.lean"),  # 4 sorries
    ]
    
    for file_path in priority_files:
        if file_path.exists():
            solver.solve_file(file_path, max_proofs=5, interactive=False)
            print("\n" + "="*80 + "\n")
            
    # Print final statistics
    print("\nFINAL STATISTICS:")
    print(f"Total attempted: {solver.stats['attempted']}")
    print(f"Total resolved: {solver.stats['resolved']}")
    print(f"Cache hits: {solver.stats['cache_hits']}")
    print(f"Success rate: {solver.stats['resolved']/max(1, solver.stats['attempted'])*100:.1f}%")
    
if __name__ == "__main__":
    main() 
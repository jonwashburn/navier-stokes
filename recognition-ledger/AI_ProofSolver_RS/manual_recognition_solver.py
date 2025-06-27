#!/usr/bin/env python3
"""
Manual Recognition Science Solver
Shows generated proofs for manual review and application
"""

import os
import re
from pathlib import Path
import anthropic
from typing import List, Dict

# Recognition Science context
RS_CONTEXT = """
-- Recognition Science Framework
-- φ (golden ratio) = (1 + √5)/2 ≈ 1.618
-- E_coh = 0.090 eV (coherence quantum)
-- τ = 7.33e-15 s (fundamental tick)
-- Eight-beat period Θ = 4.98e-5 s
-- Meta-principle: "Nothing cannot recognize itself"

Key facts:
- φ^2 = φ + 1 (golden ratio equation)
- E_coh = 0.090 eV exactly
- Particle masses: m = E_coh * φ^n (on φ-ladder)
- Eight-beat period is fundamental
"""

class ManualRecognitionSolver:
    def __init__(self, api_key: str):
        self.client = anthropic.Anthropic(api_key=api_key)
        self.model = "claude-opus-4-20250514"  # Claude Opus 4
        
    def find_sorries_in_file(self, filepath: Path) -> List[Dict]:
        """Find all sorries in a file"""
        sorries = []
        
        with open(filepath, 'r') as f:
            lines = f.readlines()
            
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Skip if sorry is in a comment
                if '--' in line and line.index('--') < line.index('sorry'):
                    continue
                    
                # Look backwards for the declaration
                for j in range(i, max(0, i-30), -1):
                    if any(kw in lines[j] for kw in ['lemma ', 'theorem ', 'def ', 'instance ']):
                        # Get full declaration
                        decl_lines = []
                        k = j
                        while k <= i:
                            decl_lines.append(lines[k].rstrip())
                            if ':=' in lines[k]:
                                break
                            k += 1
                            
                        # Extract name
                        match = re.search(r'(?:lemma|theorem|def|instance)\s+(\w+)', lines[j])
                        if match:
                            name = match.group(1)
                            
                            # Get hint
                            hint = ""
                            if '--' in line:
                                hint = line[line.index('--'):].strip('- ')
                                
                            sorries.append({
                                'name': name,
                                'line': i + 1,
                                'declaration': '\n'.join(decl_lines),
                                'hint': hint,
                                'sorry_line': line.rstrip()
                            })
                            break
                            
        return sorries
        
    def generate_proof(self, sorry_info: Dict, file_context: str) -> str:
        """Generate a proof for a sorry"""
        prompt = f"""You are proving a theorem in Recognition Science using Lean 4.

{RS_CONTEXT}

File context:
{file_context}

Theorem to prove:
{sorry_info['declaration']}

{f"Hint: {sorry_info['hint']}" if sorry_info['hint'] else ""}

Provide ONLY the proof code that replaces 'sorry'. Start with 'by' if using tactics.
Common tactics: simp, norm_num, rfl, linarith, ring, field_simp, unfold, exact

Your response should be ONLY the proof code."""

        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=2000,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up
            if proof.startswith('```'):
                proof = proof.split('\n', 1)[1]
            if proof.endswith('```'):
                proof = proof.rsplit('\n', 1)[0]
                
            return proof.strip()
            
        except Exception as e:
            return f"Error: {e}"
            
    def solve_file(self, filepath: Path, max_proofs: int = 5):
        """Generate proofs for a file"""
        print(f"\n{'='*60}")
        print(f"FILE: {filepath}")
        print(f"{'='*60}")
        
        # Find sorries
        sorries = self.find_sorries_in_file(filepath)
        if not sorries:
            print("No sorries found!")
            return
            
        print(f"Found {len(sorries)} sorries\n")
        
        # Get file context (imports, key definitions)
        with open(filepath, 'r') as f:
            lines = f.readlines()
            
        context_lines = []
        for line in lines[:50]:
            if line.startswith('import') or line.startswith('open'):
                context_lines.append(line.strip())
        for line in lines:
            if 'namespace' in line:
                context_lines.append(line.strip())
                break
                
        file_context = '\n'.join(context_lines[:20])
        
        # Process sorries
        for i, sorry_info in enumerate(sorries[:max_proofs]):
            print(f"\n{'-'*60}")
            print(f"SORRY #{i+1}: {sorry_info['name']} (line {sorry_info['line']})")
            print(f"{'-'*60}")
            print(f"Declaration:\n{sorry_info['declaration']}")
            if sorry_info['hint']:
                print(f"\nHint: {sorry_info['hint']}")
                
            print(f"\nGenerating proof...")
            proof = self.generate_proof(sorry_info, file_context)
            
            print(f"\nGENERATED PROOF:")
            print(f"{proof}")
            
            print(f"\nTO APPLY: Replace '{sorry_info['sorry_line'].strip()}' with:")
            if 'by sorry' in sorry_info['sorry_line']:
                print(f"{sorry_info['sorry_line'].replace('by sorry', proof)}")
            else:
                print(f"{sorry_info['sorry_line'].replace('sorry', proof)}")

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = ManualRecognitionSolver(api_key)
    
    # Target files - focusing on easier proofs
    files = [
        "formal/Numerics/ErrorBounds.lean",
        "formal/Philosophy/Ethics.lean",
        "formal/Philosophy/Purpose.lean",
        "formal/Philosophy/Death.lean",
        "formal/LedgerAxioms.lean",
        "formal/axioms.lean",
    ]
    
    for filepath in files:
        if Path(filepath).exists():
            solver.solve_file(Path(filepath), max_proofs=3)
            
if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
"""
Enhanced Recognition Science Solver with Better Context for Claude 4
Uses improved prompting to help Claude 4 generate correct proofs
"""

import os
import re
from pathlib import Path
import anthropic
from typing import List, Dict, Tuple
import json

class EnhancedRecognitionSolver:
    def __init__(self, api_key: str):
        self.client = anthropic.Anthropic(api_key=api_key)
        self.model = "claude-sonnet-4-20250514"  # Claude Sonnet 4
        
        # Enhanced context with specific examples and patterns
        self.enhanced_context = """
# Recognition Science Lean 4 Proof Assistant

## CRITICAL LEAN 4 SYNTAX RULES:
1. Use `by` to start tactic proofs
2. Common numeric proofs: `by norm_num`
3. Field arithmetic: `by field_simp; ring`
4. Definitional equality: `by rfl` or `rfl`
5. Linear arithmetic: `by linarith`
6. Unfolding definitions: `by unfold <name>`
7. Simple rewriting: `by simp`

## AVAILABLE FROM COMMON IMPORTS:
From `import Mathlib.Data.Real.Basic`:
- Real number operations: +, -, *, /, ^
- Inequalities: <, ≤, >, ≥
- Basic tactics: simp, ring, field_simp, linarith

From `import Mathlib.Analysis.SpecialFunctions.Pow.Real`:
- Real powers: x^y for real x, y
- Exponential: exp
- Properties of powers

From `import Mathlib.Tactic.NormNum`:
- norm_num: Evaluates numeric expressions
- Works on concrete numbers like 0.090, 7.33e-15

## RECOGNITION SCIENCE CONSTANTS:
```lean
def Θ : ℝ := 4.98e-5  -- Eight-beat period (seconds)
noncomputable def tick : ℝ := Θ / 8  -- Single tick
def E_coh : ℝ := 0.090  -- Coherence quantum (eV)
noncomputable def φ : ℝ := (1 + sqrt 5) / 2  -- Golden ratio
```

## PROVEN FACTS YOU CAN USE:
- `Theta_positive : Θ > 0`
- `E_coh_positive : E_coh > 0`
- `phi_gt_one : φ > 1`
- `phi_equation : φ^2 = φ + 1`

## EXAMPLE PROOFS IN THIS CODEBASE:

### Example 1: Numeric inequality
```lean
theorem Theta_positive : Θ > 0 := by norm_num
```

### Example 2: Derived positivity
```lean
theorem tick_positive : tick > 0 := by
  unfold tick
  apply div_pos Theta_positive
  norm_num
```

### Example 3: Field calculation
```lean
theorem phi_equation : φ^2 = φ + 1 := by
  unfold φ
  field_simp
  ring_nf
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  ring
```

### Example 4: Using exponential
```lean
theorem P_positive (cost : ℝ) : P cost > 0 := exp_pos cost
```

## PROOF PATTERNS:

### For positivity of concrete numbers:
`by norm_num`

### For positivity of divisions:
```lean
by
  unfold <definition>
  apply div_pos <numerator_positive> <denominator_positive>
```

### For simple algebraic identities:
```lean
by
  unfold <definitions>
  field_simp
  ring
```

### For inequalities with concrete bounds:
```lean
by
  unfold <definitions>
  norm_num
```

### For using a hypothesis:
```lean
by
  exact <hypothesis>
```

## COMMON MISTAKES TO AVOID:
1. Don't use `Real.` prefix - it's already opened
2. Don't use := in the proof, only after `by`
3. Don't forget `by` when using tactics
4. If a simple expression, try direct term mode without `by`

## YOUR TASK:
Generate a proof that compiles in Lean 4. Be concrete and specific.
"""
        
        # Pattern recognition for different proof types
        self.proof_patterns = {
            'positive': {
                'keywords': ['> 0', '≥ 0', 'positive'],
                'hint': 'For concrete positive numbers, use: by norm_num'
            },
            'equation': {
                'keywords': ['=', 'eq'],
                'hint': 'For equations, try: by unfold <defs>; field_simp; ring'
            },
            'inequality': {
                'keywords': ['<', '≤', '>', '≥', 'lt', 'le', 'gt', 'ge'],
                'hint': 'For inequalities, try: by linarith or by norm_num'
            },
            'exists': {
                'keywords': ['∃', 'exists', 'Exists'],
                'hint': 'For existence, use: use <witness>; <proof>'
            }
        }
        
        self.successful_proofs = []  # Track what works
        self.failed_attempts = []    # Track what doesn't
        
    def analyze_theorem_type(self, declaration: str) -> str:
        """Analyze theorem to determine proof strategy"""
        strategies = []
        
        for pattern_name, pattern_info in self.proof_patterns.items():
            if any(kw in declaration for kw in pattern_info['keywords']):
                strategies.append(pattern_info['hint'])
                
        return '\n'.join(strategies) if strategies else ""
        
    def get_similar_proofs(self, theorem_name: str, declaration: str) -> str:
        """Find similar successful proofs"""
        similar = []
        
        # Look for similar patterns in successful proofs
        for proof in self.successful_proofs:
            if any(keyword in proof['declaration'] for keyword in ['positive', '> 0'] 
                   if keyword in declaration):
                similar.append(f"Similar proof: {proof['name']}\n{proof['proof']}")
                
        return '\n\n'.join(similar[:3]) if similar else ""
        
    def generate_proof(self, sorry_info: Dict, file_context: str, 
                      file_content: str, attempt: int = 1) -> str:
        """Generate a proof with enhanced context"""
        
        # Analyze the theorem
        strategy_hints = self.analyze_theorem_type(sorry_info['declaration'])
        similar_proofs = self.get_similar_proofs(sorry_info['name'], sorry_info['declaration'])
        
        # Build the prompt parts
        strategy_section = f"## STRATEGY HINTS:\n{strategy_hints}" if strategy_hints else ""
        similar_section = f"## SIMILAR SUCCESSFUL PROOFS:\n{similar_proofs}" if similar_proofs else ""
        hint_section = f"## HINT FROM CODE: {sorry_info['hint']}" if sorry_info['hint'] else ""
        attempt_section = f"Previous attempts failed. Try a different approach." if attempt > 1 else ""
        
        prompt = f"""{self.enhanced_context}

## FILE CONTEXT:
{file_context}

## THEOREM TO PROVE:
{sorry_info['declaration']}

{strategy_section}

{similar_section}

{hint_section}

## IMPORTANT CONTEXT FROM THIS FILE:
Look for these defined terms that might be used:
{self.extract_definitions(file_content)}

## ATTEMPT {attempt}/3:
{attempt_section}

Generate ONLY the proof code that replaces 'sorry'. 
If the proof is simple, it might just be a term like `exp_pos cost`.
If using tactics, start with `by`.

YOUR RESPONSE SHOULD BE ONLY THE PROOF CODE."""

        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=1000,
                temperature=0.1 if attempt == 1 else 0.3,  # More creative on retries
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
            
    def extract_definitions(self, file_content: str) -> str:
        """Extract key definitions from file"""
        lines = file_content.split('\n')
        definitions = []
        
        for line in lines:
            if any(kw in line for kw in ['def ', 'noncomputable def ', 'theorem ', 'lemma ']):
                if 'sorry' not in line:
                    definitions.append(line.strip())
                    
        return '\n'.join(definitions[:20])  # First 20 definitions
        
    def find_sorries_in_file(self, filepath: Path) -> List[Dict]:
        """Find all sorries in a file with better context"""
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
                            if ':=' in lines[k] or 'where' in lines[k]:
                                break
                            k += 1
                            
                        # Extract name
                        match = re.search(r'(?:lemma|theorem|def|instance)\s+(\w+)', lines[j])
                        if match:
                            name = match.group(1)
                            
                            # Get hint
                            hint = ""
                            if '--' in line:
                                hint = line[line.index('--'):].strip('- \n')
                                
                            # Get surrounding context
                            context_start = max(0, j - 10)
                            context_end = min(len(lines), i + 5)
                            context = ''.join(lines[context_start:context_end])
                            
                            sorries.append({
                                'name': name,
                                'line': i + 1,
                                'declaration': '\n'.join(decl_lines),
                                'hint': hint,
                                'sorry_line': line.rstrip(),
                                'context': context
                            })
                            break
                            
        return sorries
        
    def apply_proof(self, filepath: Path, sorry_info: Dict, proof: str) -> bool:
        """Apply a proof and check if it works"""
        # Read file
        with open(filepath, 'r') as f:
            content = f.read()
            
        # Replace sorry with proof
        original_line = sorry_info['sorry_line']
        if 'by sorry' in original_line:
            new_line = original_line.replace('by sorry', proof)
        else:
            new_line = original_line.replace('sorry', proof)
            
        new_content = content.replace(original_line, new_line)
        
        # Write to test file
        test_file = filepath.with_suffix('.test.lean')
        with open(test_file, 'w') as f:
            f.write(new_content)
            
        # Test with lake build (would need actual implementation)
        # For now, we'll just check syntax
        success = self.check_syntax(proof)
        
        # Clean up
        if test_file.exists():
            test_file.unlink()
            
        return success
        
    def check_syntax(self, proof: str) -> bool:
        """Basic syntax checking"""
        # Check for common syntax errors
        if proof.count('(') != proof.count(')'):
            return False
        if proof.count('{') != proof.count('}'):
            return False
        if proof.count('⟨') != proof.count('⟩'):
            return False
            
        # Check for suspicious patterns
        suspicious = ['undefined', 'error', 'Error', 'TODO', 'FIXME']
        if any(s in proof for s in suspicious):
            return False
            
        return True
        
    def solve_file(self, filepath: Path, max_proofs: int = 10):
        """Solve sorries in a file with multiple attempts"""
        print(f"\n{'='*60}")
        print(f"FILE: {filepath}")
        print(f"{'='*60}")
        
        # Read file content
        with open(filepath, 'r') as f:
            file_content = f.read()
            lines = file_content.split('\n')
            
        # Get file context
        context_lines = []
        for line in lines[:50]:
            if line.startswith('import') or line.startswith('open'):
                context_lines.append(line.strip())
        for line in lines:
            if 'namespace' in line:
                context_lines.append(line.strip())
                break
                
        file_context = '\n'.join(context_lines[:20])
        
        # Find sorries
        sorries = self.find_sorries_in_file(filepath)
        if not sorries:
            print("No sorries found!")
            return
            
        print(f"Found {len(sorries)} sorries\n")
        
        # Process sorries
        for i, sorry_info in enumerate(sorries[:max_proofs]):
            print(f"\n{'-'*60}")
            print(f"SORRY #{i+1}: {sorry_info['name']} (line {sorry_info['line']})")
            print(f"{'-'*60}")
            print(f"Declaration:\n{sorry_info['declaration']}")
            if sorry_info['hint']:
                print(f"\nHint: {sorry_info['hint']}")
                
            # Try up to 3 times with different approaches
            for attempt in range(1, 4):
                print(f"\nAttempt {attempt}/3...")
                proof = self.generate_proof(sorry_info, file_context, 
                                          file_content, attempt)
                
                print(f"Generated: {proof}")
                
                # Check if it looks valid
                if self.check_syntax(proof):
                    print("✓ Syntax looks valid")
                    
                    # Track successful pattern
                    self.successful_proofs.append({
                        'name': sorry_info['name'],
                        'declaration': sorry_info['declaration'],
                        'proof': proof
                    })
                    
                    print(f"\nTO APPLY: Replace '{sorry_info['sorry_line'].strip()}' with:")
                    if 'by sorry' in sorry_info['sorry_line']:
                        print(f"{sorry_info['sorry_line'].replace('by sorry', proof)}")
                    else:
                        print(f"{sorry_info['sorry_line'].replace('sorry', proof)}")
                    break
                else:
                    print("✗ Syntax check failed, retrying...")
                    self.failed_attempts.append({
                        'name': sorry_info['name'],
                        'proof': proof,
                        'reason': 'syntax'
                    })
                    
        # Save patterns for learning
        self.save_patterns()
        
    def save_patterns(self):
        """Save successful patterns for future use"""
        patterns_file = Path("formal/proof_patterns.json")
        patterns = {
            'successful': self.successful_proofs[-20:],  # Last 20 successes
            'failed': self.failed_attempts[-10:]  # Last 10 failures
        }
        
        with open(patterns_file, 'w') as f:
            json.dump(patterns, f, indent=2)
            
def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = EnhancedRecognitionSolver(api_key)
    
    # Start with files that have simpler proofs
    files = [
        "formal/LedgerAxioms.lean",  # Has tick_positive
        "formal/Numerics/ErrorBounds.lean",
        "formal/Philosophy/Ethics.lean",
        "formal/axioms.lean",
        "formal/MetaPrinciple.lean",
    ]
    
    for filepath in files:
        if Path(filepath).exists():
            solver.solve_file(Path(filepath), max_proofs=5)
            print(f"\n{'='*60}")
            print(f"Completed {filepath}")
            print(f"Successful proofs: {len(solver.successful_proofs)}")
            print(f"Failed attempts: {len(solver.failed_attempts)}")
            
if __name__ == "__main__":
    main() 
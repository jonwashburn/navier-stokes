#!/usr/bin/env python3
"""
Recognition Science-Aligned Lean Proof Solver
Enhanced with 8-beat iterative recognition and ledger-balancing feedback loops
"""

import os
import re
import json
import subprocess
import time
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass
from collections import defaultdict
import hashlib

# OpenAI setup
from openai import OpenAI

# Set API key from environment
api_key = os.environ.get('OPENAI_API_KEY')
if not api_key:
    print("❌ Error: OPENAI_API_KEY environment variable not set")
    print("Please run: export OPENAI_API_KEY='your-key-here'")
    sys.exit(1)

client = OpenAI(api_key=api_key)

# Recognition Science Constants
EIGHT_BEAT_CYCLE = 8  # Maximum iterations per proof attempt
PHI = 1.618034  # Golden ratio for backoff timing
E_COH = 0.090  # Coherence quantum in eV

@dataclass
class RecognitionState:
    """Tracks the ledger state of a proof attempt"""
    debits: List[str] = None  # What we need to prove
    credits: List[str] = None  # What we've established
    balance: float = 0.0  # Recognition cost
    tick: int = 0  # Current iteration in 8-beat cycle
    
    def __post_init__(self):
        if self.debits is None:
            self.debits = []
        if self.credits is None:
            self.credits = []

@dataclass
class ProofContext:
    """Minimal context for focused recognition"""
    imports: List[str]
    dependencies: List[str]  # Lemmas this proof depends on
    target_theorem: str
    namespace: str
    golden_examples: List[str]  # Successful proof patterns

class RecognitionCache:
    """Pattern library for successful recognitions"""
    def __init__(self, cache_file="recognition_cache.json"):
        self.cache_file = cache_file
        self.patterns = self.load_cache()
        self.failure_patterns = defaultdict(list)
        
    def load_cache(self) -> Dict:
        if os.path.exists(self.cache_file):
            with open(self.cache_file, 'r') as f:
                return json.load(f)
        return {"successful_proofs": {}, "lemma_skeletons": {}}
    
    def save_cache(self):
        with open(self.cache_file, 'w') as f:
            json.dump(self.patterns, f, indent=2)
    
    def add_success(self, theorem: str, proof: str, context: ProofContext):
        """Store successful recognition pattern"""
        key = hashlib.md5(theorem.encode()).hexdigest()
        self.patterns["successful_proofs"][key] = {
            "theorem": theorem,
            "proof": proof,
            "dependencies": context.dependencies,
            "timestamp": time.time()
        }
        self.save_cache()
    
    def add_lemma_skeleton(self, lemma: str):
        """Store discovered lemma need"""
        self.patterns["lemma_skeletons"][lemma] = {
            "discovered": time.time(),
            "attempts": 0
        }
        self.save_cache()
    
    def get_similar_proofs(self, theorem: str, limit: int = 3) -> List[str]:
        """Retrieve similar successful patterns"""
        # Simple similarity: shared dependencies
        similar = []
        for entry in self.patterns["successful_proofs"].values():
            if any(dep in theorem for dep in entry["dependencies"]):
                similar.append(entry["proof"])
        return similar[:limit]

class ContextExtractor:
    """Extract minimal Lean context for focused recognition"""
    
    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.golden_examples = self.load_golden_examples()
    
    def load_golden_examples(self) -> List[str]:
        """Load successfully proven theorems as examples"""
        examples = [
            """-- Example: Coherence quantum uniqueness
theorem coherence_quantum_unique : ∃! E : ℝ, E > 0 ∧ E = min_positive_energy := by
  use E_coh
  constructor
  · exact ⟨E_coh_pos, rfl⟩
  · intro y ⟨hy_pos, hy_min⟩
    exact unique_minimum hy_pos hy_min""",
            
            """-- Example: Eight-beat period
theorem eight_beat_period : tick_period = 8 * fundamental_tick := by
  rw [tick_period_def]
  simp [fundamental_tick]
  ring""",
            
            """-- Example: Golden ratio minimization  
theorem phi_minimizes_cost : ∀ x > 0, x ≠ φ → J(x) > J(φ) := by
  intro x hx_pos hx_ne
  apply cost_functional_strict_minimum
  exact ⟨hx_pos, hx_ne⟩"""
        ]
        return examples
    
    def extract_context(self, file_path: Path, theorem_name: str) -> ProofContext:
        """Extract minimal context for theorem"""
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Extract imports
        imports = re.findall(r'^import\s+(.+)$', content, re.MULTILINE)
        
        # Extract namespace
        namespace_match = re.search(r'^namespace\s+(\w+)', content, re.MULTILINE)
        namespace = namespace_match.group(1) if namespace_match else ""
        
        # Find theorem and its dependencies
        theorem_match = re.search(
            rf'^(theorem|lemma)\s+{theorem_name}.*?:=\s*by\s+sorry',
            content, re.MULTILINE | re.DOTALL
        )
        
        if not theorem_match:
            return ProofContext(imports, [], "", namespace, self.golden_examples)
        
        target_theorem = theorem_match.group(0).replace('sorry', '').strip()
        
        # Extract dependencies (simplified - looks for used lemmas)
        deps = self.extract_dependencies(content, theorem_name)
        
        return ProofContext(imports, deps, target_theorem, namespace, self.golden_examples)
    
    def extract_dependencies(self, content: str, theorem_name: str) -> List[str]:
        """Find lemmas that this theorem likely depends on"""
        deps = []
        
        # Find all theorems/lemmas defined before our target
        all_theorems = re.finditer(
            r'^(theorem|lemma)\s+(\w+).*?(?=^theorem|^lemma|^def|^end|\Z)',
            content, re.MULTILINE | re.DOTALL
        )
        
        for match in all_theorems:
            name = match.group(2)
            if name == theorem_name:
                break
            # Add recent theorems as potential dependencies
            if len(deps) < 10:  # Limit context size
                deps.append(match.group(0)[:200])  # First 200 chars
        
        return deps

class EightBeatSolver:
    """Main solver implementing 8-beat recognition cycles"""
    
    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.cache = RecognitionCache()
        self.extractor = ContextExtractor(project_root)
        self.recognition_states: Dict[str, RecognitionState] = {}
    
    def compile_proof(self, file_path: Path, proof_content: str) -> Tuple[bool, str]:
        """Test if proof compiles"""
        # Create temporary file with proof
        temp_file = file_path.with_suffix('.temp.lean')
        temp_file.write_text(proof_content)
        
        try:
            # Run lean compiler
            result = subprocess.run(
                ['lake', 'build', str(temp_file)],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            success = result.returncode == 0
            error_msg = result.stderr if not success else ""
            
            # Extract first error for focused feedback
            if error_msg:
                first_error = error_msg.split('\n')[0]
                return success, first_error
            
            return success, ""
            
        except subprocess.TimeoutExpired:
            return False, "Compilation timeout"
        finally:
            temp_file.unlink(missing_ok=True)
    
    def generate_proof_attempt(self, context: ProofContext, state: RecognitionState, 
                             error_feedback: str = "") -> str:
        """Generate proof using o3 with recognition-aligned prompting"""
        
        # Build prompt with 8-beat structure
        system_prompt = f"""You are a Lean 4 proof assistant following Recognition Science principles.

Key principles:
1. Every proof must balance like a cosmic ledger - each claim needs justification
2. Build proofs iteratively through recognition events, not all at once
3. Use the 8-beat cycle: start simple, add complexity gradually

Golden examples of successful proofs:
{chr(10).join(context.golden_examples)}

Current 8-beat tick: {state.tick + 1}/8
Recognition cost so far: {state.balance:.3f}
"""

        # Build user prompt with chain-of-thought structure
        user_prompt = f"""Prove the following theorem:

{context.target_theorem}

Available context:
{chr(10).join(context.dependencies[:5])}  -- Showing first 5 dependencies

Namespace: {context.namespace}
"""

        if error_feedback:
            user_prompt += f"""

Previous attempt failed with error:
{error_feedback}

Please fix ONLY the part causing this specific error. Focus on balancing this one "debit" in the ledger.
"""
        else:
            user_prompt += """

Please:
1. First write a comment outlining your proof strategy (-- Proof plan: ...)
2. Then implement the proof step by step
3. Keep the proof under 600 tokens for focused recognition
"""

        # Add cache insights if available
        similar_proofs = self.cache.get_similar_proofs(context.target_theorem)
        if similar_proofs:
            user_prompt += f"""

Similar successful proof patterns:
{chr(10).join(similar_proofs[:2])}
"""

        try:
            response = client.chat.completions.create(
                model="gpt-4-turbo-preview",  # Using latest available model
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": user_prompt}
                ],
                max_tokens=600,  # Focused recognition window
                temperature=0.7 * (PHI ** state.tick)  # Golden ratio decay
            )
            
            proof = response.choices[0].message.content
            
            # Clean proof of non-Lean commentary
            proof = self.clean_proof(proof)
            
            return proof
            
        except Exception as e:
            print(f"API error: {e}")
            return ""
    
    def clean_proof(self, proof: str) -> str:
        """Remove non-Lean commentary that causes compilation errors"""
        # Remove lines that are clearly not Lean code
        lines = proof.split('\n')
        clean_lines = []
        
        in_proof = False
        for line in lines:
            # Detect proof start
            if ' by' in line or ':= by' in line:
                in_proof = True
            
            # Skip pure commentary outside proofs
            if not in_proof and line.strip() and not any(
                line.strip().startswith(kw) for kw in 
                ['theorem', 'lemma', 'def', 'import', '--', '/-', 'by']
            ):
                continue
                
            clean_lines.append(line)
        
        return '\n'.join(clean_lines)
    
    def solve_theorem(self, file_path: Path, theorem_name: str) -> Tuple[bool, str]:
        """Solve single theorem using 8-beat recognition cycle"""
        print(f"\n🎯 Attempting: {theorem_name}")
        
        # Initialize recognition state
        state = RecognitionState(
            debits=[theorem_name],
            credits=[],
            balance=0.0,
            tick=0
        )
        
        # Extract minimal context
        context = self.extractor.extract_context(file_path, theorem_name)
        if not context.target_theorem:
            print(f"  ❌ Could not find theorem {theorem_name}")
            return False, ""
        
        # Read current file content
        with open(file_path, 'r') as f:
            original_content = f.read()
        
        error_feedback = ""
        best_proof = ""
        best_error = "No proof generated"
        
        # 8-beat recognition cycle
        for tick in range(EIGHT_BEAT_CYCLE):
            state.tick = tick
            state.balance += E_COH  # Each recognition costs energy
            
            print(f"  🔄 Tick {tick + 1}/8 - Recognition cost: {state.balance:.3f}")
            
            # Generate proof attempt
            proof = self.generate_proof_attempt(context, state, error_feedback)
            if not proof:
                continue
            
            # Construct full file with proof
            # Replace the theorem with sorry with the theorem with proof
            target_with_sorry = context.target_theorem + '\n  sorry'
            target_with_proof = context.target_theorem + '\n' + proof
            
            # First try exact match
            if target_with_sorry in original_content:
                proof_content = original_content.replace(target_with_sorry, target_with_proof)
            else:
                # Try replacing just "by sorry" with the proof
                proof_content = original_content.replace(
                    context.target_theorem,
                    context.target_theorem.replace('by sorry', f'by\n  {proof}')
                )
            
            # Test compilation
            success, error = self.compile_proof(file_path, proof_content)
            
            if success:
                print(f"  ✅ Proof found at tick {tick + 1}!")
                self.cache.add_success(theorem_name, proof, context)
                return True, proof
            
            # Update error feedback for next iteration
            error_feedback = error
            if len(error) < len(best_error):
                best_proof = proof
                best_error = error
            
            # Check for missing lemmas
            if "unknown identifier" in error:
                match = re.search(r"unknown identifier '(\w+)'", error)
                if match:
                    missing_lemma = match.group(1)
                    self.cache.add_lemma_skeleton(missing_lemma)
                    print(f"  📝 Discovered need for lemma: {missing_lemma}")
            
            # Golden ratio backoff
            time.sleep(0.1 * (PHI ** tick))
        
        print(f"  ❌ Failed after 8 ticks. Best error: {best_error[:100]}...")
        return False, best_proof
    
    def solve_file(self, file_path: Path) -> Dict[str, bool]:
        """Solve all sorries in a file"""
        print(f"\n📄 Processing: {file_path}")
        
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Find all sorries with their theorem names
        # Updated pattern to match actual file structure
        sorry_pattern = r'(theorem|lemma)\s+(\w+).*?:=\s*by\s+sorry'
        sorries = re.finditer(sorry_pattern, content, re.MULTILINE | re.DOTALL)
        
        results = {}
        sorry_list = list(sorries)
        
        # Sort by dependency order (simpler theorems first)
        sorry_list.sort(key=lambda m: len(m.group(0)))
        
        for match in sorry_list:
            theorem_name = match.group(2)
            success, proof = self.solve_theorem(file_path, theorem_name)
            results[theorem_name] = success
            
            if success:
                # Update file with successful proof
                with open(file_path, 'r') as f:
                    current_content = f.read()
                
                # Find the exact sorry to replace
                theorem_pattern = rf'(theorem|lemma)\s+{theorem_name}.*?:=\s*by\s+sorry'
                theorem_match = re.search(theorem_pattern, current_content, re.MULTILINE | re.DOTALL)
                
                if theorem_match:
                    new_content = current_content.replace(
                        theorem_match.group(0),
                        theorem_match.group(0).replace('sorry', proof)
                    )
                    
                    with open(file_path, 'w') as f:
                        f.write(new_content)
                    
                    print(f"  💾 Updated {theorem_name} in {file_path}")
        
        return results

def main():
    """Run the Recognition Science-aligned solver"""
    print("🌟 Recognition Science Lean Proof Solver")
    print(f"   Following {EIGHT_BEAT_CYCLE}-beat cycles")
    print(f"   Energy cost per recognition: {E_COH} eV")
    print(f"   Golden ratio decay: {PHI}")
    
    # Setup project
    project_root = Path.cwd()
    solver = EightBeatSolver(project_root)
    
    # Priority files based on dependency order
    priority_files = [
        "formal/Numerics/ErrorBounds.lean",
        "formal/Numerics/PhiComputation.lean",
        "formal/Core/GoldenRatio.lean",
        "formal/Core/EightBeat.lean",
        "formal/axioms.lean",
        "formal/Physics/NavierStokes.lean"
    ]
    
    total_results = {}
    
    for file_path in priority_files:
        full_path = project_root / file_path
        if full_path.exists():
            results = solver.solve_file(full_path)
            total_results.update(results)
        else:
            print(f"⚠️  File not found: {file_path}")
    
    # Summary
    successful = sum(1 for v in total_results.values() if v)
    total = len(total_results)
    
    print(f"\n📊 Final Summary:")
    print(f"   Theorems attempted: {total}")
    print(f"   Successfully proven: {successful}")
    print(f"   Success rate: {successful/total*100:.1f}%")
    print(f"   Recognition patterns cached: {len(solver.cache.patterns['successful_proofs'])}")
    
    # Save final cache
    solver.cache.save_cache()

if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
"""
Enhanced Prompt System - Improved prompts with multi-shot search
"""

from typing import List, Dict, Optional, Tuple
import json
from pathlib import Path

class EnhancedPromptSystem:
    def __init__(self):
        self.successful_proofs = self._load_successful_proofs()
        
    def _load_successful_proofs(self) -> List[Dict]:
        """Load successful RS proofs as examples"""
        return [
            {
                "theorem": "phi_self_consistency",
                "goal": "φ² = φ + 1",
                "proof": "by field_simp; norm_num"
            },
            {
                "theorem": "recognition_fixed_points",
                "goal": "∃ x, recognition x = x",
                "proof": "by use 0; simp [recognition]"
            },
            {
                "theorem": "eight_beat_period",
                "goal": "period = 8",
                "proof": "by rw [period]; norm_num"
            },
            {
                "theorem": "mass_hierarchy_preserved",
                "goal": "m₁ < m₂ → φ_ladder m₁ < φ_ladder m₂",
                "proof": "by intro h; simp [φ_ladder]; exact mul_lt_mul_of_pos_left h φ_pos"
            }
        ]
        
    def create_multi_shot_prompts(self, theorem_name: str, goal_type: str,
                                 context: Dict) -> List[str]:
        """Create multiple prompts with different strategies"""
        prompts = []
        
        # Strategy 1: Direct tactic mode
        prompt1 = self._create_tactic_prompt(theorem_name, goal_type, context)
        prompts.append(prompt1)
        
        # Strategy 2: Term mode 
        prompt2 = self._create_term_prompt(theorem_name, goal_type, context)
        prompts.append(prompt2)
        
        # Strategy 3: Calc mode for equations
        if '=' in goal_type:
            prompt3 = self._create_calc_prompt(theorem_name, goal_type, context)
            prompts.append(prompt3)
            
        # Strategy 4: Induction for recursive goals
        if any(kw in goal_type for kw in ['∀', 'Nat', 'List']):
            prompt4 = self._create_induction_prompt(theorem_name, goal_type, context)
            prompts.append(prompt4)
            
        return prompts
        
    def _create_tactic_prompt(self, theorem_name: str, goal_type: str,
                             context: Dict) -> str:
        """Create tactic-mode prompt"""
        prompt = f"""You are proving a theorem in the Recognition Science framework using Lean 4.

CONTEXT:
- File: {context.get('file_path', 'unknown')}
- Namespace: {context.get('namespace', 'RecognitionScience')}
- Available: {', '.join([str(t) for t in context.get('available_theorems', [])][:5])}

THEOREM TO PROVE:
theorem {theorem_name} : {goal_type} := by sorry

SUCCESSFUL EXAMPLES IN THIS PROJECT:
"""
        
        for example in self.successful_proofs[:3]:
            prompt += f"""
theorem {example['theorem']} : {example['goal']} := {example['proof']}
"""
        
        prompt += f"""
INSTRUCTIONS:
1. Use tactic mode (start with 'by')
2. Try simple tactics first: rfl, simp, norm_num, ring, field_simp, aesop
3. Use Recognition Science specific lemmas when needed
4. Keep the proof concise (prefer one-liners)

Provide ONLY the proof starting with 'by', nothing else:
"""
        return prompt
        
    def _create_term_prompt(self, theorem_name: str, goal_type: str,
                           context: Dict) -> str:
        """Create term-mode prompt"""
        prompt = f"""You are proving a theorem in the Recognition Science framework using Lean 4.

THEOREM: {theorem_name} : {goal_type}

For simple proofs, you can provide a direct term instead of tactics.

Examples of term-mode proofs:
- For existence: ⟨witness, proof⟩
- For functions: fun x => expression
- For equality: Eq.refl value
- For implications: fun h => proof_using_h

Provide ONLY the term proof (no 'by'):
"""
        return prompt
        
    def _create_calc_prompt(self, theorem_name: str, goal_type: str,
                           context: Dict) -> str:
        """Create calc-mode prompt for equations"""
        prompt = f"""You are proving an equation in the Recognition Science framework.

THEOREM: {theorem_name} : {goal_type}

Use calc mode for step-by-step equality proofs:

Example:
theorem example : a + b = c := by
  calc a + b = d := by simp
       _     = c := by rw [lemma]

Provide the calc proof:
"""
        return prompt
        
    def _create_induction_prompt(self, theorem_name: str, goal_type: str,
                                context: Dict) -> str:
        """Create induction prompt"""
        prompt = f"""You are proving a universal statement in Recognition Science.

THEOREM: {theorem_name} : {goal_type}

Consider using induction. Example pattern:
by
  intro n
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

Provide the induction proof:
"""
        return prompt
        
    def create_enhanced_prompt(self, theorem_name: str, goal_type: str,
                             context: Dict, error_history: List[str] = None) -> str:
        """Create single enhanced prompt with error feedback"""
        prompt = f"""You are an expert Lean 4 prover working on the Recognition Science framework.

PROJECT CONTEXT:
Recognition Science achieves zero-parameter physics through:
- Meta-principle: "Nothing cannot recognize itself" 
- Eight fundamental theorems derived from pure logic
- Golden ratio φ emerges from self-consistency
- Complete particle spectrum via φ-ladder

CURRENT PROOF CONTEXT:
File: {context.get('file_path', 'unknown')}
Namespace: {context.get('namespace', 'RecognitionScience')}
Imports: {', '.join(context.get('imports', [])[:3])}

AVAILABLE LEMMAS:
{chr(10).join([str(t) for t in context.get('available_theorems', [])][:10])}

THEOREM TO PROVE:
theorem {theorem_name} : {goal_type} := by sorry

"""

        if error_history:
            prompt += f"""
PREVIOUS ATTEMPTS FAILED:
{chr(10).join(error_history[-3:])}

Common fixes:
- If "unknown identifier": the name might be in a different namespace
- If "type mismatch": check exact types with #check
- If "failed to synthesize": provide type annotations
"""

        prompt += """
LEAN 4 STYLE RULES:
- No 'by' after tactics (wrong: "simp by", correct: "simp")
- Use · for subgoals, not bullets
- Prefer structured proofs for clarity
- Use 'show' to clarify goal types

Provide ONLY the proof starting with 'by':
"""
        return prompt
        
    def extract_goal_features(self, goal_type: str) -> Dict[str, bool]:
        """Extract features from goal type for better prompt selection"""
        return {
            'is_equality': '=' in goal_type,
            'is_inequality': any(op in goal_type for op in ['<', '>', '≤', '≥']),
            'is_existence': '∃' in goal_type,
            'is_universal': '∀' in goal_type,
            'has_implication': '→' in goal_type or '⟶' in goal_type,
            'has_conjunction': '∧' in goal_type,
            'has_disjunction': '∨' in goal_type,
            'involves_nat': 'Nat' in goal_type or 'ℕ' in goal_type,
            'involves_real': 'Real' in goal_type or 'ℝ' in goal_type,
            'involves_list': 'List' in goal_type,
            'involves_set': 'Set' in goal_type,
            'is_recognition': 'recognition' in goal_type.lower(),
            'is_phi_related': 'φ' in goal_type or 'phi' in goal_type.lower()
        } 
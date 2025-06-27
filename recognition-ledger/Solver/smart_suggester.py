#!/usr/bin/env python3
"""
Smart Suggester - Uses pattern analysis to suggest the most appropriate proof strategies
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from pattern_analyzer import PatternAnalyzer

class SmartSuggester:
    def __init__(self):
        # Load pattern analysis
        self.patterns = self.load_patterns()
        self.analyzer = PatternAnalyzer()
        
        # Proof templates based on common patterns
        self.templates = {
            'numerical_simple': "norm_num",
            'numerical_with_simp': "simp\nnorm_num", 
            'numerical_with_unfold': "unfold {terms}\nnorm_num",
            'definitional_rfl': "rfl",
            'definitional_unfold': "unfold {term}\nrfl",
            'calc_chain': "calc {lhs}\n  _ = {step1} := by {proof1}\n  _ = {rhs} := by {proof2}",
            'constructor_simple': "constructor\n· {proof1}\n· {proof2}",
            'exact_value': "exact {value}",
            'have_then_exact': "have h : {statement} := {proof}\nexact h",
            'ring_norm': "ring_nf\nnorm_num",
            'simp_linarith': "simp\nlinarith"
        }
        
        # Recognition Science specific strategies
        self.rs_strategies = {
            'phi_computation': [
                "unfold φ",
                "norm_num", 
                "simp [φ_def]",
                "rw [φ_squared]"
            ],
            'eight_beat': [
                "unfold eight_beat_period",
                "norm_num",
                "simp [period_def]"
            ],
            'coherence_energy': [
                "unfold E_coh",
                "norm_num",
                "simp [energy_def]"
            ],
            'mass_ratio': [
                "unfold {mass1} {mass2}",
                "simp [div_div]",
                "field_simp",
                "norm_num"
            ],
            'ledger_state': [
                "unfold ledger_state",
                "constructor",
                "simp"
            ]
        }
        
    def load_patterns(self) -> Dict:
        """Load pattern analysis results"""
        pattern_file = Path("pattern_analysis.json")
        if pattern_file.exists():
            with open(pattern_file, 'r') as f:
                return json.load(f)
        return {}
        
    def suggest_proof_strategy(self, theorem_name: str, theorem_statement: str,
                             context: Dict) -> List[str]:
        """Suggest proof strategies based on theorem characteristics"""
        suggestions = []
        
        # Analyze theorem characteristics
        is_numerical = self.is_numerical_theorem(theorem_statement)
        is_equality = '=' in theorem_statement and not '≠' in theorem_statement
        is_inequality = any(op in theorem_statement for op in ['<', '>', '≤', '≥'])
        has_phi = any(term in theorem_statement.lower() for term in ['φ', 'phi', 'golden'])
        has_mass = 'mass' in theorem_statement.lower() or '_m' in theorem_name.lower()
        
        # Get RS category
        rs_category = self.analyzer.categorize_rs_proof(
            theorem_name, theorem_statement, ""
        )
        
        # Numerical proofs
        if is_numerical:
            if has_phi:
                suggestions.extend([
                    "unfold φ\nnorm_num",
                    "simp [φ_def]\nnorm_num",
                    "rw [φ_squared]\nnorm_num"
                ])
            else:
                suggestions.extend([
                    "norm_num",
                    "simp\nnorm_num",
                    "ring_nf\nnorm_num"
                ])
                
        # Equality proofs
        if is_equality:
            if self.is_definitional(theorem_name, theorem_statement):
                suggestions.extend([
                    "rfl",
                    "unfold {term}\nrfl",
                    "simp"
                ])
            elif has_mass and 'ratio' in theorem_statement:
                suggestions.append(self.rs_strategies['mass_ratio'][0])
                
        # Inequality proofs
        if is_inequality:
            suggestions.extend([
                "norm_num",
                "linarith", 
                "simp\nlinarith"
            ])
            
        # Recognition Science specific
        if rs_category in self.rs_strategies:
            suggestions.extend(self.rs_strategies[rs_category])
            
        # Look for similar proven theorems
        similar_proofs = self.find_similar_proofs(theorem_name, theorem_statement)
        for proof in similar_proofs[:2]:
            suggestions.append(f"-- Similar to {proof['name']}\n{proof['proof']}")
            
        # Remove duplicates while preserving order
        seen = set()
        unique_suggestions = []
        for s in suggestions:
            if s not in seen:
                seen.add(s)
                unique_suggestions.append(s)
                
        return unique_suggestions[:5]  # Return top 5 suggestions
        
    def is_numerical_theorem(self, statement: str) -> bool:
        """Check if theorem involves numerical computation"""
        numerical_indicators = [
            r'\d+\.?\d*',  # Numbers
            r'sqrt|abs|pow|exp|log',  # Math functions
            r'[+\-*/]',  # Arithmetic operators
            'Real', 'Nat', 'Int', 'ℝ', 'ℕ', 'ℤ'  # Number types
        ]
        
        for indicator in numerical_indicators:
            if re.search(indicator, statement):
                return True
        return False
        
    def is_definitional(self, name: str, statement: str) -> bool:
        """Check if theorem is likely definitional"""
        # Definitional theorems often have these patterns
        definitional_patterns = [
            r'_def$',  # Ends with _def
            r'^def_',  # Starts with def_
            r'unfold',  # Mentions unfolding
            r':=.*=',  # Definition followed by equality
        ]
        
        for pattern in definitional_patterns:
            if re.search(pattern, name) or re.search(pattern, statement):
                return True
                
        # Very short statements are often definitional
        if len(statement.strip()) < 50 and '=' in statement:
            return True
            
        return False
        
    def find_similar_proofs(self, name: str, statement: str) -> List[Dict]:
        """Find similar proven theorems"""
        similar = []
        
        # Extract key terms
        key_terms = set(re.findall(r'\b\w{4,}\b', statement.lower()))
        
        # Search through cached patterns
        for pattern_type, patterns in self.patterns.get('proof_patterns', {}).items():
            if isinstance(patterns, list):
                for p in patterns:
                    if isinstance(p, dict) and 'name' in p:
                        p_terms = set(re.findall(r'\b\w{4,}\b', p['name'].lower()))
                        overlap = len(key_terms & p_terms)
                        if overlap > 1:
                            similar.append({
                                'name': p['name'],
                                'proof': p.get('proof', ''),
                                'similarity': overlap
                            })
                            
        # Sort by similarity
        similar.sort(key=lambda x: x['similarity'], reverse=True)
        return similar
        
    def format_suggestion(self, suggestion: str, context: Dict) -> str:
        """Format suggestion with context-specific values"""
        # Replace placeholders
        if '{terms}' in suggestion:
            # Extract likely terms to unfold from context
            terms = []
            if 'definitions' in context:
                terms = list(context['definitions'].keys())[:3]
            suggestion = suggestion.replace('{terms}', ' '.join(terms))
            
        if '{term}' in suggestion:
            # Pick most relevant term
            if 'definitions' in context and context['definitions']:
                term = list(context['definitions'].keys())[0]
                suggestion = suggestion.replace('{term}', term)
                
        # Add more sophisticated replacements as needed
        
        return suggestion
        
def main():
    """Test the smart suggester"""
    suggester = SmartSuggester()
    
    # Test cases
    test_cases = [
        ("phi_squared", "φ ^ 2 = φ + 1"),
        ("mass_ratio_correct", "m_muon / m_electron = φ^5"),
        ("eight_beat_period", "eight_beat_period = 8"),
        ("coherence_positive", "E_coh > 0"),
        ("ledger_state_valid", "valid_state s → valid_state (update s)")
    ]
    
    for name, statement in test_cases:
        print(f"\nTheorem: {name}")
        print(f"Statement: {statement}")
        print("Suggestions:")
        
        suggestions = suggester.suggest_proof_strategy(name, statement, {})
        for i, sugg in enumerate(suggestions, 1):
            print(f"\n{i}. {sugg}")
        print("-" * 50)
        
if __name__ == "__main__":
    main() 
#!/usr/bin/env python3
"""
Proof Cache - Store and retrieve successful proof patterns
"""

import json
import hashlib
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import re

class ProofCache:
    def __init__(self, cache_file: Path = Path("proof_cache.json")):
        self.cache_file = cache_file
        self.cache = self.load_cache()
        
    def load_cache(self) -> Dict:
        """Load cache from file"""
        if self.cache_file.exists():
            with open(self.cache_file, 'r') as f:
                return json.load(f)
        return {
            "fingerprints": {},
            "patterns": {},
            "statistics": {
                "hits": 0,
                "misses": 0,
                "successes": 0
            }
        }
        
    def save_cache(self):
        """Save cache to file"""
        with open(self.cache_file, 'w') as f:
            json.dump(self.cache, f, indent=2)
            
    def fingerprint_goal(self, declaration: str) -> Dict:
        """Create a fingerprint from a theorem declaration"""
        # Extract key features
        features = {
            "head_symbol": None,
            "relation": None,
            "has_forall": "∀" in declaration or "forall" in declaration,
            "has_exists": "∃" in declaration or "exists" in declaration,
            "has_equality": "=" in declaration,
            "has_inequality": any(op in declaration for op in [">", "<", "≥", "≤"]),
            "has_implication": "→" in declaration or "->" in declaration,
            "num_lines": declaration.count('\n') + 1
        }
        
        # Extract relation
        if features["has_equality"]:
            features["relation"] = "="
        elif ">" in declaration:
            features["relation"] = ">"
        elif "<" in declaration:
            features["relation"] = "<"
        elif "≥" in declaration:
            features["relation"] = "≥"
        elif "≤" in declaration:
            features["relation"] = "≤"
            
        # Extract head symbol (first meaningful identifier after theorem name)
        theorem_match = re.search(r'theorem\s+\w+\s*:\s*(.+)', declaration, re.DOTALL)
        if theorem_match:
            goal_text = theorem_match.group(1)
            # Look for first identifier
            id_match = re.search(r'\b([a-zA-Z_]\w*)\b', goal_text)
            if id_match:
                features["head_symbol"] = id_match.group(1)
                
        return features
        
    def fingerprint_to_key(self, fingerprint: Dict) -> str:
        """Convert fingerprint to cache key"""
        # Create a deterministic string representation
        parts = [
            f"head:{fingerprint.get('head_symbol', 'none')}",
            f"rel:{fingerprint.get('relation', 'none')}",
            f"forall:{fingerprint.get('has_forall', False)}",
            f"exists:{fingerprint.get('has_exists', False)}",
            f"lines:{fingerprint.get('num_lines', 0)}"
        ]
        return "|".join(parts)
        
    def lookup_proof(self, declaration: str) -> Optional[str]:
        """Look up a proof for a similar declaration"""
        fingerprint = self.fingerprint_goal(declaration)
        key = self.fingerprint_to_key(fingerprint)
        
        # Exact match
        if key in self.cache["fingerprints"]:
            self.cache["statistics"]["hits"] += 1
            return self.cache["fingerprints"][key]["proof"]
            
        # Try pattern matching
        for pattern_key, pattern_data in self.cache["patterns"].items():
            if self.matches_pattern(fingerprint, pattern_data["fingerprint"]):
                self.cache["statistics"]["hits"] += 1
                return pattern_data["proof"]
                
        self.cache["statistics"]["misses"] += 1
        return None
        
    def matches_pattern(self, fingerprint1: Dict, fingerprint2: Dict) -> bool:
        """Check if two fingerprints match closely enough"""
        # Must have same relation
        if fingerprint1.get("relation") != fingerprint2.get("relation"):
            return False
            
        # Similar structure
        structure_match = (
            fingerprint1.get("has_forall") == fingerprint2.get("has_forall") and
            fingerprint1.get("has_exists") == fingerprint2.get("has_exists")
        )
        
        return structure_match
        
    def store_proof(self, declaration: str, proof: str, success: bool = True):
        """Store a successful proof"""
        if not success:
            return
            
        fingerprint = self.fingerprint_goal(declaration)
        key = self.fingerprint_to_key(fingerprint)
        
        # Store exact match
        self.cache["fingerprints"][key] = {
            "declaration": declaration,
            "proof": proof,
            "fingerprint": fingerprint,
            "count": self.cache["fingerprints"].get(key, {}).get("count", 0) + 1
        }
        
        # Extract and store patterns
        self.extract_patterns(declaration, proof, fingerprint)
        
        self.cache["statistics"]["successes"] += 1
        self.save_cache()
        
    def extract_patterns(self, declaration: str, proof: str, fingerprint: Dict):
        """Extract reusable patterns from successful proofs"""
        # Pattern: simple positivity proofs
        if fingerprint.get("relation") == ">" and "0" in declaration:
            pattern_key = "positivity"
            self.cache["patterns"][pattern_key] = {
                "fingerprint": {"relation": ">", "has_zero": True},
                "proof": proof,
                "template": "by norm_num"
            }
            
        # Pattern: division positivity
        if "div_pos" in proof:
            pattern_key = "div_positivity"
            self.cache["patterns"][pattern_key] = {
                "fingerprint": {"has_division": True, "relation": ">"},
                "proof": proof,
                "template": "by\n  unfold {definition}\n  apply div_pos {num_pos} {denom_pos}"
            }
            
        # Pattern: field equations
        if "field_simp" in proof and "ring" in proof:
            pattern_key = "field_equation"
            self.cache["patterns"][pattern_key] = {
                "fingerprint": {"relation": "=", "has_field_ops": True},
                "proof": proof,
                "template": "by field_simp; ring"
            }
            
    def get_statistics(self) -> Dict:
        """Get cache statistics"""
        stats = self.cache["statistics"].copy()
        stats["total_cached"] = len(self.cache["fingerprints"])
        stats["patterns"] = len(self.cache["patterns"])
        stats["hit_rate"] = stats["hits"] / max(1, stats["hits"] + stats["misses"])
        return stats
        
    def suggest_similar_proofs(self, declaration: str, limit: int = 3) -> List[Dict]:
        """Suggest similar proofs from cache"""
        fingerprint = self.fingerprint_goal(declaration)
        suggestions = []
        
        # Find proofs with similar fingerprints
        for key, data in self.cache["fingerprints"].items():
            similarity = self.compute_similarity(fingerprint, data["fingerprint"])
            if similarity > 0.5:
                suggestions.append({
                    "proof": data["proof"],
                    "similarity": similarity,
                    "declaration": data["declaration"][:100] + "..." if len(data["declaration"]) > 100 else data["declaration"]
                })
                
        # Sort by similarity and return top matches
        suggestions.sort(key=lambda x: x["similarity"], reverse=True)
        return suggestions[:limit]
        
    def compute_similarity(self, fp1: Dict, fp2: Dict) -> float:
        """Compute similarity between two fingerprints"""
        score = 0.0
        total = 0.0
        
        # Relation match is most important
        if fp1.get("relation") == fp2.get("relation"):
            score += 3.0
        total += 3.0
        
        # Structure matches
        for key in ["has_forall", "has_exists", "has_equality", "has_inequality"]:
            if fp1.get(key) == fp2.get(key):
                score += 1.0
            total += 1.0
            
        # Head symbol match
        if fp1.get("head_symbol") == fp2.get("head_symbol") and fp1.get("head_symbol") is not None:
            score += 2.0
        total += 2.0
        
        return score / total if total > 0 else 0.0 
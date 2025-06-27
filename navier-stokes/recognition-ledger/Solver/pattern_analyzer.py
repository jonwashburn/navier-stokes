#!/usr/bin/env python3
"""
Pattern Analyzer - Identify common proof patterns in Recognition Science
"""

import re
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict, Counter
import json

class PatternAnalyzer:
    def __init__(self):
        self.patterns = {
            'numerical': [],
            'definitional': [],
            'inductive': [],
            'by_cases': [],
            'contradiction': [],
            'simp_based': [],
            'calc_based': [],
            'recognition_specific': []
        }
        
        # Recognition Science specific patterns
        self.rs_patterns = {
            'phi_related': r'φ|phi|golden|fibonacci',
            'eight_beat': r'eight|beat|period|tick',
            'coherence': r'coherence|E_coh|energy',
            'ledger': r'ledger|state|recognition',
            'meta_principle': r'nothing|cannot|recognize|itself',
            'mass_spectrum': r'mass|particle|electron|muon',
            'gauge': r'gauge|symmetry|SU|U\(1\)',
            'cosmological': r'dark|energy|hubble|cosmological'
        }
        
    def analyze_file(self, file_path: Path) -> Dict:
        """Analyze a single file for proof patterns"""
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Find all completed proofs
        proof_pattern = r'theorem\s+(\w+)[^:]*:([^:=]+):=\s*by\s+([^⊢]+?)(?=theorem|lemma|def|end|\Z)'
        proofs = re.findall(proof_pattern, content, re.DOTALL | re.MULTILINE)
        
        file_patterns = {
            'total_proofs': len(proofs),
            'tactics_used': Counter(),
            'proof_lengths': [],
            'rs_categories': Counter(),
            'common_sequences': []
        }
        
        for name, statement, proof in proofs:
            # Skip if contains sorry
            if 'sorry' in proof:
                continue
                
            # Analyze tactics used
            tactics = self.extract_tactics(proof)
            file_patterns['tactics_used'].update(tactics)
            
            # Proof length
            file_patterns['proof_lengths'].append(len(proof.strip()))
            
            # RS category
            category = self.categorize_rs_proof(name, statement, proof)
            if category:
                file_patterns['rs_categories'][category] += 1
                
            # Store pattern
            self.store_pattern(name, statement, proof, tactics)
            
        return file_patterns
        
    def extract_tactics(self, proof: str) -> List[str]:
        """Extract tactics from a proof"""
        # Common Lean 4 tactics
        tactic_pattern = r'\b(simp|rfl|norm_num|linarith|ring|exact|apply|intro|cases|induction|contradiction|unfold|rw|calc|have|show|use|exists|constructor|trivial|decide|omega)\b'
        
        tactics = re.findall(tactic_pattern, proof)
        return tactics
        
    def categorize_rs_proof(self, name: str, statement: str, proof: str) -> str:
        """Categorize proof by Recognition Science domain"""
        full_text = f"{name} {statement} {proof}".lower()
        
        for category, pattern in self.rs_patterns.items():
            if re.search(pattern, full_text, re.IGNORECASE):
                return category
                
        return 'general'
        
    def store_pattern(self, name: str, statement: str, proof: str, tactics: List[str]):
        """Store proof pattern for later analysis"""
        # Determine pattern type
        if 'norm_num' in tactics and len(tactics) <= 3:
            self.patterns['numerical'].append({
                'name': name,
                'proof': proof.strip(),
                'tactics': tactics
            })
        elif 'unfold' in tactics or 'rfl' in tactics:
            self.patterns['definitional'].append({
                'name': name,
                'proof': proof.strip(),
                'tactics': tactics
            })
        elif 'induction' in tactics:
            self.patterns['inductive'].append({
                'name': name,
                'proof': proof.strip(),
                'tactics': tactics
            })
        elif 'calc' in proof:
            self.patterns['calc_based'].append({
                'name': name,
                'proof': proof.strip(),
                'tactics': tactics
            })
            
    def analyze_directory(self, dir_path: Path) -> Dict:
        """Analyze all Lean files in directory"""
        all_patterns = {
            'files_analyzed': 0,
            'total_proofs': 0,
            'tactics_frequency': Counter(),
            'rs_categories': Counter(),
            'avg_proof_length': 0,
            'common_patterns': []
        }
        
        proof_lengths = []
        
        for file_path in dir_path.rglob("*.lean"):
            # Skip backups and tests
            if any(skip in str(file_path) for skip in ['backup', 'test_', 'Test']):
                continue
                
            try:
                file_patterns = self.analyze_file(file_path)
                all_patterns['files_analyzed'] += 1
                all_patterns['total_proofs'] += file_patterns['total_proofs']
                all_patterns['tactics_frequency'].update(file_patterns['tactics_used'])
                all_patterns['rs_categories'].update(file_patterns['rs_categories'])
                proof_lengths.extend(file_patterns['proof_lengths'])
            except:
                continue
                
        # Calculate averages
        if proof_lengths:
            all_patterns['avg_proof_length'] = sum(proof_lengths) / len(proof_lengths)
            
        # Find common tactic sequences
        all_patterns['common_patterns'] = self.find_common_sequences()
        
        return all_patterns
        
    def find_common_sequences(self) -> List[Dict]:
        """Find common tactic sequences across all patterns"""
        sequences = []
        
        # Analyze numerical proofs
        if len(self.patterns['numerical']) > 3:
            common_tactics = Counter()
            for p in self.patterns['numerical']:
                common_tactics.update(p['tactics'])
            sequences.append({
                'type': 'numerical',
                'common_tactics': common_tactics.most_common(5),
                'example': self.patterns['numerical'][0]['proof']
            })
            
        # Analyze definitional proofs
        if len(self.patterns['definitional']) > 3:
            common_tactics = Counter()
            for p in self.patterns['definitional']:
                common_tactics.update(p['tactics'])
            sequences.append({
                'type': 'definitional', 
                'common_tactics': common_tactics.most_common(5),
                'example': self.patterns['definitional'][0]['proof']
            })
            
        return sequences
        
    def generate_report(self, output_path: Path = Path("pattern_analysis.json")):
        """Generate analysis report"""
        formal_dir = Path("../formal")
        analysis = self.analyze_directory(formal_dir)
        
        # Create readable report
        report = {
            'summary': {
                'files_analyzed': analysis['files_analyzed'],
                'total_proofs': analysis['total_proofs'],
                'avg_proof_length': round(analysis['avg_proof_length'], 1)
            },
            'tactics': {
                'most_common': dict(analysis['tactics_frequency'].most_common(15)),
                'total_unique': len(analysis['tactics_frequency'])
            },
            'recognition_science': {
                'categories': dict(analysis['rs_categories']),
                'patterns': self.rs_patterns
            },
            'proof_patterns': {
                'numerical': len(self.patterns['numerical']),
                'definitional': len(self.patterns['definitional']),
                'inductive': len(self.patterns['inductive']),
                'calc_based': len(self.patterns['calc_based'])
            },
            'common_sequences': analysis['common_patterns']
        }
        
        # Save report
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
            
        # Print summary
        print(f"\nPattern Analysis Complete!")
        print(f"{'='*50}")
        print(f"Files analyzed: {report['summary']['files_analyzed']}")
        print(f"Total proofs: {report['summary']['total_proofs']}")
        print(f"Average proof length: {report['summary']['avg_proof_length']} chars")
        print(f"\nMost common tactics:")
        for tactic, count in list(report['tactics']['most_common'].items())[:10]:
            print(f"  {tactic}: {count}")
        print(f"\nRecognition Science categories:")
        for cat, count in report['recognition_science']['categories'].items():
            print(f"  {cat}: {count}")
            
        return report
        
def main():
    analyzer = PatternAnalyzer()
    analyzer.generate_report()
    
if __name__ == "__main__":
    main() 
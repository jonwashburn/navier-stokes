#!/usr/bin/env python3
"""
Context Extractor - Extract relevant context for proof generation
"""

import re
from pathlib import Path
from typing import List, Dict, Set, Tuple

class ContextExtractor:
    def __init__(self):
        self.theorem_pattern = re.compile(r'(?:theorem|lemma)\s+(\w+).*?:=', re.DOTALL)
        self.def_pattern = re.compile(r'(?:def|instance)\s+(\w+).*?:=', re.DOTALL)
        self.import_pattern = re.compile(r'^import\s+(.+)$', re.MULTILINE)
        self.open_pattern = re.compile(r'^open\s+(.+)$', re.MULTILINE)
        
    def extract_context(self, file_path: Path, sorry_line: int) -> Dict:
        """Extract comprehensive context around a sorry"""
        with open(file_path, 'r') as f:
            content = f.read()
            lines = content.split('\n')
            
        context = {
            'imports': self.extract_imports(content),
            'opens': self.extract_opens(content),
            'namespace': self.extract_namespace(content),
            'available_theorems': [],
            'available_defs': [],
            'local_context': [],
            'goal_type': None,
            'nearby_proofs': []
        }
        
        # Extract theorem/lemma we're proving
        theorem_info = self.find_current_theorem(lines, sorry_line)
        if theorem_info:
            context['current_theorem'] = theorem_info
            context['goal_type'] = self.extract_goal_type(theorem_info['declaration'])
            
        # Find available theorems and definitions
        context['available_theorems'] = self.find_available_theorems(content, sorry_line)
        context['available_defs'] = self.find_available_defs(content, sorry_line)
        
        # Extract local context (20 lines before and after)
        start = max(0, sorry_line - 20)
        end = min(len(lines), sorry_line + 20)
        context['local_context'] = lines[start:end]
        
        # Find nearby successful proofs as examples
        context['nearby_proofs'] = self.find_nearby_proofs(content, sorry_line)
        
        # Extract variables and hypotheses
        context['variables'] = self.extract_variables(lines, sorry_line)
        
        return context
        
    def extract_imports(self, content: str) -> List[str]:
        """Extract import statements"""
        imports = []
        for match in self.import_pattern.finditer(content):
            imports.append(match.group(1).strip())
        return imports
        
    def extract_opens(self, content: str) -> List[str]:
        """Extract open statements"""
        opens = []
        for match in self.open_pattern.finditer(content):
            opens.append(match.group(1).strip())
        return opens
        
    def extract_namespace(self, content: str) -> str:
        """Extract current namespace"""
        namespace_match = re.search(r'namespace\s+(\S+)', content)
        if namespace_match:
            return namespace_match.group(1)
        return ""
        
    def find_current_theorem(self, lines: List[str], sorry_line: int) -> Dict:
        """Find the theorem containing the sorry"""
        # Look backwards for theorem/lemma declaration
        for i in range(sorry_line - 1, max(0, sorry_line - 50), -1):
            line = lines[i]
            if any(kw in line for kw in ['theorem ', 'lemma ']):
                # Extract full declaration
                decl_lines = []
                j = i
                while j < len(lines) and ':=' not in lines[j]:
                    decl_lines.append(lines[j])
                    j += 1
                if j < len(lines):
                    decl_lines.append(lines[j])
                    
                declaration = '\n'.join(decl_lines)
                
                # Extract name
                match = re.search(r'(?:theorem|lemma)\s+(\w+)', declaration)
                if match:
                    return {
                        'name': match.group(1),
                        'start_line': i,
                        'declaration': declaration
                    }
        return None
        
    def extract_goal_type(self, declaration: str) -> str:
        """Extract the goal type from a theorem declaration"""
        # Find the type after : and before :=
        match = re.search(r':\s*(.+?)\s*:=', declaration, re.DOTALL)
        if match:
            return match.group(1).strip()
        return ""
        
    def find_available_theorems(self, content: str, before_line: int) -> List[Dict]:
        """Find theorems available before the current line"""
        theorems = []
        lines = content.split('\n')
        
        for match in self.theorem_pattern.finditer(content):
            name = match.group(1)
            # Find which line this theorem is on
            theorem_text = match.group(0)
            for i, line in enumerate(lines):
                if theorem_text.startswith(line.strip()) and i < before_line:
                    theorems.append({
                        'name': name,
                        'line': i,
                        'declaration': theorem_text
                    })
                    break
                    
        return theorems[-20:]  # Return last 20 theorems
        
    def find_available_defs(self, content: str, before_line: int) -> List[Dict]:
        """Find definitions available before the current line"""
        defs = []
        lines = content.split('\n')
        
        for match in self.def_pattern.finditer(content):
            name = match.group(1)
            def_text = match.group(0)
            for i, line in enumerate(lines):
                if def_text.startswith(line.strip()) and i < before_line:
                    defs.append({
                        'name': name,
                        'line': i,
                        'declaration': def_text[:200]  # First 200 chars
                    })
                    break
                    
        return defs[-10:]  # Return last 10 definitions
        
    def find_nearby_proofs(self, content: str, around_line: int) -> List[Dict]:
        """Find successfully proven theorems near the current line"""
        proofs = []
        lines = content.split('\n')
        
        # Look for theorems with actual proofs (not sorry)
        for i in range(max(0, around_line - 50), min(len(lines), around_line + 50)):
            line = lines[i]
            if any(kw in line for kw in ['theorem ', 'lemma ']):
                # Check if this has a real proof
                j = i
                while j < len(lines) and ':=' not in lines[j]:
                    j += 1
                    
                if j < len(lines):
                    # Look for the proof
                    proof_start = j
                    proof_lines = []
                    brace_count = 0
                    k = j
                    
                    while k < len(lines):
                        proof_line = lines[k]
                        if 'sorry' in proof_line:
                            break  # Skip sorries
                            
                        proof_lines.append(proof_line)
                        
                        # Simple heuristic to find end of proof
                        if 'by' in proof_line:
                            # Continue until we find a line that starts a new declaration
                            k += 1
                            while k < len(lines) and not any(kw in lines[k] for kw in ['theorem ', 'lemma ', 'def ', '#']):
                                proof_lines.append(lines[k])
                                k += 1
                            break
                        k += 1
                        
                    if proof_lines and 'sorry' not in ' '.join(proof_lines):
                        match = re.search(r'(?:theorem|lemma)\s+(\w+)', line)
                        if match:
                            proofs.append({
                                'name': match.group(1),
                                'declaration': lines[i:j+1],
                                'proof': proof_lines[:10]  # First 10 lines of proof
                            })
                            
        return proofs[:5]  # Return up to 5 examples
        
    def extract_variables(self, lines: List[str], before_line: int) -> List[str]:
        """Extract variable declarations"""
        variables = []
        for i in range(max(0, before_line - 50), before_line):
            line = lines[i]
            if 'variable' in line:
                variables.append(line.strip())
        return variables
        
    def format_context_for_prompt(self, context: Dict) -> str:
        """Format extracted context for LLM prompt"""
        parts = []
        
        # Imports and opens
        if context['imports']:
            parts.append(f"Imports: {', '.join(context['imports'][:5])}")
        if context['opens']:
            parts.append(f"Open: {', '.join(context['opens'])}")
        if context['namespace']:
            parts.append(f"Namespace: {context['namespace']}")
            
        # Available theorems
        if context['available_theorems']:
            theorem_names = [t['name'] for t in context['available_theorems'][-10:]]
            parts.append(f"\nAvailable theorems: {', '.join(theorem_names)}")
            
        # Available definitions
        if context['available_defs']:
            def_names = [d['name'] for d in context['available_defs'][-5:]]
            parts.append(f"Available definitions: {', '.join(def_names)}")
            
        # Variables
        if context['variables']:
            parts.append(f"\nVariables:\n" + '\n'.join(context['variables'][:5]))
            
        # Nearby successful proofs
        if context['nearby_proofs']:
            parts.append("\nExample proofs nearby:")
            for proof in context['nearby_proofs'][:2]:
                parts.append(f"\n{proof['name']}:")
                parts.append('\n'.join(proof['proof'][:5]))
                
        return '\n'.join(parts) 
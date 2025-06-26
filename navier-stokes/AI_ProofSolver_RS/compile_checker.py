#!/usr/bin/env python3
"""
Compile Checker - Validate generated proofs by compiling
"""

import subprocess
import tempfile
from pathlib import Path
from typing import Tuple, Optional
import shutil
import re

class CompileChecker:
    def __init__(self, lake_path: str = "lake"):
        self.lake_path = lake_path
        
    def check_proof(self, file_path: Path, sorry_line: int, 
                   new_proof: str, original_content: str = None) -> Tuple[bool, Optional[str]]:
        """
        Check if a proof compiles by replacing sorry and building
        Returns (success, error_message)
        """
        # Read original file if not provided
        if original_content is None:
            with open(file_path, 'r') as f:
                original_content = f.read()
                
        # Create a backup
        backup_path = file_path.with_suffix('.backup')
        backup_created = False
        try:
            shutil.copy(file_path, backup_path)
            backup_created = True
        except Exception:
            # If backup fails, we can still try the proof
            pass
        
        try:
            # Replace the sorry with the new proof
            lines = original_content.split('\n')
            
            # Find the line with sorry
            if sorry_line <= len(lines):
                line = lines[sorry_line - 1]
                
                # Replace sorry with the proof
                if 'by sorry' in line:
                    new_line = line.replace('by sorry', new_proof)
                else:
                    new_line = line.replace('sorry', new_proof)
                    
                lines[sorry_line - 1] = new_line
                
                # Write modified content
                new_content = '\n'.join(lines)
                with open(file_path, 'w') as f:
                    f.write(new_content)
                    
                # Try to compile
                result = self.compile_file(file_path)
                
                if result[0]:
                    # Success! Keep the change
                    return (True, None)
                else:
                    # Failed - restore original
                    if backup_created and backup_path.exists():
                        shutil.copy(backup_path, file_path)
                    return (False, result[1])
            else:
                return (False, f"Line {sorry_line} out of range")
                
        except Exception as e:
            # Restore on any error
            if backup_created and backup_path.exists():
                shutil.copy(backup_path, file_path)
            return (False, str(e))
            
        finally:
            # Clean up backup
            if backup_created and backup_path.exists():
                try:
                    backup_path.unlink()
                except Exception:
                    # Ignore cleanup errors
                    pass
                
    def compile_file(self, file_path: Path) -> Tuple[bool, Optional[str]]:
        """
        Compile a single Lean file
        Returns (success, error_message)
        """
        try:
            # Run lake build on the specific file
            cmd = [self.lake_path, "build"]
            
            # Find project root (where lakefile.lean is)
            project_root = file_path.parent
            while project_root.parent != project_root:
                if (project_root / "lakefile.lean").exists():
                    break
                project_root = project_root.parent
                
            result = subprocess.run(
                cmd,
                cwd=project_root,  # Run from project root
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                return (True, None)
            else:
                # Extract error message
                error_msg = result.stderr
                if not error_msg:
                    error_msg = result.stdout
                    
                # Try to extract the most relevant error
                error_lines = error_msg.split('\n')
                relevant_errors = []
                
                for line in error_lines:
                    if 'error:' in line.lower():
                        relevant_errors.append(line)
                    elif file_path.name in line:
                        relevant_errors.append(line)
                        
                if relevant_errors:
                    return (False, '\n'.join(relevant_errors[:5]))  # First 5 errors
                else:
                    return (False, error_msg[:500])  # First 500 chars
                    
        except subprocess.TimeoutExpired:
            return (False, "Compilation timed out")
        except Exception as e:
            return (False, f"Compilation error: {str(e)}")
            
    def extract_goal_type(self, file_path: Path, line_num: int) -> Optional[str]:
        """
        Extract the goal type at a specific line
        This is a simplified version - full implementation would use Lean server
        """
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # Look backwards from the sorry to find the theorem declaration
        for i in range(line_num - 1, max(0, line_num - 30), -1):
            line = lines[i]
            if any(kw in line for kw in ['theorem ', 'lemma ', 'def ']):
                # Extract the type signature
                decl_lines = []
                j = i
                while j < len(lines) and ':=' not in lines[j]:
                    decl_lines.append(lines[j].strip())
                    j += 1
                    
                declaration = ' '.join(decl_lines)
                
                # Extract goal after :
                match = re.search(r':\s*(.+?)(?:\s*:=|$)', declaration, re.DOTALL)
                if match:
                    return match.group(1).strip()
                    
        return None
        
    def validate_syntax(self, proof: str) -> Tuple[bool, Optional[str]]:
        """
        Basic syntax validation before attempting compilation
        """
        # Check balanced parentheses
        if proof.count('(') != proof.count(')'):
            return (False, "Unbalanced parentheses")
            
        if proof.count('{') != proof.count('}'):
            return (False, "Unbalanced braces")
            
        if proof.count('⟨') != proof.count('⟩'):
            return (False, "Unbalanced angle brackets")
            
        # Check for common syntax errors
        if 'by by' in proof:
            return (False, "Double 'by' keyword")
            
        if proof.strip().endswith(','):
            return (False, "Trailing comma")
            
        # Check for undefined references (heuristic)
        suspicious_patterns = [
            # r'\b[a-z]_\w+',  # Too strict - many valid names match this
            r'undefined',
            r'TODO',
            r'FIXME'
        ]
        
        for pattern in suspicious_patterns:
            if re.search(pattern, proof, re.IGNORECASE):
                return (False, f"Suspicious pattern: {pattern}")
                
        return (True, None) 
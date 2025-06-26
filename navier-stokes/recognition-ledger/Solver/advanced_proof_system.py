#!/usr/bin/env python3
"""
Advanced Proof System for Navier-Stokes
- Better proof extraction with Lean syntax validation
- Careful application with incremental testing
- Optimized Claude 4 prompting
"""

import os
import re
import json
import subprocess
import shutil
import asyncio
import logging
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional, Tuple
import anthropic

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class LeanProofValidator:
    """Validates Lean proof syntax before application"""
    
    def __init__(self):
        self.lean_keywords = {'by', 'sorry', 'exact', 'apply', 'intro', 'simp', 'norm_num', 
                             'rfl', 'constructor', 'unfold', 'rw', 'have', 'show', 'use',
                             'left', 'right', 'cases', 'induction', 'trivial'}
    
    def validate_proof_syntax(self, proof: str) -> Tuple[bool, str]:
        """Validate basic Lean proof syntax"""
        proof = proof.strip()
        
        # Check for empty proof
        if not proof:
            return False, "Empty proof"
        
        # Check for 'sorry' in proof
        if 'sorry' in proof.lower() and not proof.endswith('-- TODO'):
            return False, "Contains sorry"
        
        # Check for random text/comments that aren't valid proofs
        if any(phrase in proof for phrase in ['Looking at', 'I need to', 'Based on', '```']):
            return False, "Contains natural language instead of proof"
        
        # Check for isolated numbers
        if re.match(r'^\d+$', proof.strip()):
            return False, "Invalid proof: just a number"
        
        # For 'by' proofs, ensure valid tactics follow
        if proof.startswith('by'):
            tactics_part = proof[2:].strip()
            if not tactics_part:
                return False, "Empty tactics after 'by'"
            
            # Check first word is a valid tactic
            first_word = tactics_part.split()[0] if tactics_part.split() else ""
            if first_word and first_word not in self.lean_keywords and not first_word.startswith('{'):
                return False, f"Invalid tactic: {first_word}"
        
        # Check parentheses/brackets balance
        if proof.count('(') != proof.count(')'):
            return False, "Unbalanced parentheses"
        if proof.count('[') != proof.count(']'):
            return False, "Unbalanced brackets"
        if proof.count('{') != proof.count('}'):
            return False, "Unbalanced braces"
        
        return True, "Valid"

class ProofExtractor:
    """Extracts proofs from logs with validation"""
    
    def __init__(self, validator: LeanProofValidator):
        self.validator = validator
    
    def extract_from_log(self, log_file: str) -> Dict[str, str]:
        """Extract valid proofs from log files"""
        proofs = {}
        
        if not Path(log_file).exists():
            return proofs
        
        with open(log_file, 'r') as f:
            content = f.read()
        
        # Pattern to find lemma proofs in logs
        pattern = r'Verifying proof for (\w+).*?(?:Proof verified|Successfully applied) for \1'
        
        for match in re.finditer(pattern, content, re.DOTALL):
            lemma_name = match.group(1)
            
            # Extract the proof between these markers
            section = match.group(0)
            
            # Look for actual proof content
            proof_patterns = [
                r'proof:\s*```lean\s*(.*?)\s*```',
                r'proof:\s*by\s+(.*?)(?:\n|$)',
                r'Generated proof:\s*(.*?)(?:\n|$)',
            ]
            
            for pp in proof_patterns:
                proof_match = re.search(pp, section, re.DOTALL)
                if proof_match:
                    proof = proof_match.group(1).strip()
                    valid, reason = self.validator.validate_proof_syntax(proof)
                    if valid:
                        proofs[lemma_name] = proof
                    break
        
        return proofs

class Claude4ProofGenerator:
    """Generates proofs using Claude 4 with optimized prompting"""
    
    def __init__(self, api_key: str):
        self.client = anthropic.Anthropic(api_key=api_key)
        self.model = "claude-sonnet-4-20250514"
    
    def create_optimized_prompt(self, lemma_name: str, lemma_statement: str, context: str) -> str:
        """Create an optimized prompt for Claude 4"""
        return f"""You are a Lean 4 theorem prover. Your task is to provide a complete, valid proof for the following lemma.

Context (definitions and imports):
```lean
{context}
```

Lemma to prove:
```lean
{lemma_statement}
```

Instructions:
1. Provide ONLY the proof term or tactic sequence that replaces 'sorry'
2. Do NOT include any explanation or comments
3. Do NOT include the lemma declaration itself
4. The proof should compile in Lean 4
5. Use appropriate tactics like: intro, apply, exact, simp, norm_num, rfl, unfold, constructor
6. For numerical proofs, try norm_num first
7. For definitional equality, try rfl
8. For simple logical proofs, try simp or trivial

Your response should be ONLY the proof, starting with 'by' if using tactics, or a direct term if not.
"""
    
    def generate_proof(self, lemma_name: str, lemma_statement: str, context: str) -> Optional[str]:
        """Generate a proof using Claude 4"""
        try:
            prompt = self.create_optimized_prompt(lemma_name, lemma_statement, context)
            
            response = self.client.messages.create(
                model=self.model,
                max_tokens=1000,
                temperature=0.2,  # Lower temperature for more deterministic proofs
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up the proof
            if proof.startswith('```lean'):
                proof = proof[7:]
            if proof.endswith('```'):
                proof = proof[:-3]
            proof = proof.strip()
            
            return proof
            
        except Exception as e:
            logger.error(f"Error generating proof for {lemma_name}: {e}")
            return None

class AdvancedProofApplicator:
    """Applies proofs with careful validation and testing"""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.validator = LeanProofValidator()
        self.backup_dir = None
        self.applied_proofs = []
        self.failed_proofs = []
    
    def create_backup(self) -> Path:
        """Create timestamped backup"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = self.project_root / f"backups/advanced_{timestamp}"
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        # Copy all Lean files
        for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
            for file in self.project_root.glob(pattern):
                rel_path = file.relative_to(self.project_root)
                backup_path = self.backup_dir / rel_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, backup_path)
        
        logger.info(f"Created backup at {self.backup_dir}")
        return self.backup_dir
    
    def find_lemma_in_file(self, filepath: Path, lemma_name: str) -> Optional[Dict]:
        """Find lemma declaration and extract info"""
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Pattern to match lemma/theorem declarations (including multi-line with content before sorry)
        pattern = rf'(lemma|theorem)\s+{re.escape(lemma_name)}\s*([^:]*?):\s*(.*?)\s*:=\s*by\s*(.*?)sorry'
        match = re.search(pattern, content, re.DOTALL | re.MULTILINE)
        
        if match:
            return {
                'keyword': match.group(1),
                'params': match.group(2).strip(),
                'statement': match.group(3).strip(),
                'full_match': match.group(0),
                'content': content
            }
        
        return None
    
    def test_file_syntax(self, filepath: Path) -> bool:
        """Test if a file has valid syntax"""
        try:
            result = subprocess.run(
                ['lake', 'env', 'lean', '--only-export', str(filepath)],
                capture_output=True,
                text=True,
                timeout=10
            )
            return result.returncode == 0
        except:
            return False
    
    def apply_single_proof(self, filepath: Path, lemma_name: str, proof: str) -> bool:
        """Apply a single proof with validation"""
        # Validate proof syntax first
        valid, reason = self.validator.validate_proof_syntax(proof)
        if not valid:
            logger.warning(f"Invalid proof syntax for {lemma_name}: {reason}")
            return False
        
        # Find the lemma
        lemma_info = self.find_lemma_in_file(filepath, lemma_name)
        if not lemma_info:
            return False
        
        # Create temp backup
        temp_backup = str(filepath) + '.temp'
        shutil.copy2(filepath, temp_backup)
        
        try:
            # Apply the proof (replacing everything after 'by' including sorry)
            new_content = lemma_info['content'].replace(
                lemma_info['full_match'],
                f"{lemma_info['keyword']} {lemma_name} {lemma_info['params']}: {lemma_info['statement']} := {proof}"
            )
            
            with open(filepath, 'w') as f:
                f.write(new_content)
            
            # Test syntax
            if self.test_file_syntax(filepath):
                os.remove(temp_backup)
                logger.info(f"✅ Applied proof for {lemma_name}")
                return True
            else:
                # Restore from backup
                shutil.copy2(temp_backup, filepath)
                os.remove(temp_backup)
                logger.warning(f"❌ Syntax check failed for {lemma_name}")
                return False
                
        except Exception as e:
            # Restore from backup
            if os.path.exists(temp_backup):
                shutil.copy2(temp_backup, filepath)
                os.remove(temp_backup)
            logger.error(f"Error applying proof for {lemma_name}: {e}")
            return False
    
    def run_incremental_build(self) -> bool:
        """Run build and check for errors"""
        try:
            result = subprocess.run(
                ['lake', 'build'],
                capture_output=True,
                text=True,
                timeout=60
            )
            return result.returncode == 0
        except:
            return False

class AdvancedProofSystem:
    """Main system orchestrating all components"""
    
    def __init__(self, api_key: Optional[str] = None):
        self.applicator = AdvancedProofApplicator()
        self.extractor = ProofExtractor(self.applicator.validator)
        self.generator = Claude4ProofGenerator(api_key) if api_key else None
    
    async def process_file_with_claude4(self, filepath: Path, max_proofs: int = 5):
        """Process a single file with Claude 4"""
        if not self.generator:
            logger.error("No API key provided for Claude 4")
            return
        
        logger.info(f"Processing {filepath} with Claude 4")
        
        # Find sorries in file
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Extract context (imports and definitions)
        context_lines = []
        lines = content.split('\n')
        for i, line in enumerate(lines):
            if line.startswith('import') or line.startswith('open'):
                context_lines.append(line)
            elif any(kw in line for kw in ['def', 'structure', 'inductive', 'class', 'noncomputable def']):
                # Include the whole definition
                context_lines.append(line)
                # Add lines until we find an empty line or a new definition
                j = i + 1
                while j < len(lines) and lines[j].strip() and not any(kw in lines[j] for kw in ['def', 'lemma', 'theorem']):
                    context_lines.append(lines[j])
                    j += 1
        
        # Also include namespace
        for line in lines[:50]:  # Check first 50 lines
            if line.startswith('namespace'):
                context_lines.append(line)
                break
        
        # Make sure to include the specific definitions needed for this file
        # Find C_star and φ definitions
        for i, line in enumerate(lines):
            if 'def φ' in line or 'def C_star' in line:
                context_lines.append(line)
        
        context = '\n'.join(context_lines[:50])  # Increase context size
        logger.info(f"Context has {len(context_lines)} lines, using first 50")
        
        # Find lemmas with sorry (including multi-line with content before sorry)
        lemma_pattern = r'(lemma|theorem)\s+(\w+)\s*([^:]*?):\s*(.*?)\s*:=\s*by\s*(.*?)sorry'
        matches = list(re.finditer(lemma_pattern, content, re.DOTALL | re.MULTILINE))
        
        proofs_generated = 0
        for match in matches[:max_proofs]:
            lemma_name = match.group(2)
            lemma_params = match.group(3).strip()
            lemma_statement = match.group(4).strip()
            full_statement = f"lemma {lemma_name} {lemma_params}: {lemma_statement} := by sorry"
            
            logger.info(f"Generating proof for {lemma_name}")
            
            proof = self.generator.generate_proof(lemma_name, full_statement, context)
            if proof:
                logger.info(f"Generated proof: {proof[:100]}...")  # Log first 100 chars
                valid, reason = self.applicator.validator.validate_proof_syntax(proof)
                if valid:
                    if self.applicator.apply_single_proof(filepath, lemma_name, proof):
                        proofs_generated += 1
                        logger.info(f"✅ Successfully applied {lemma_name}")
                    else:
                        logger.warning(f"Failed to apply {lemma_name}")
                else:
                    logger.warning(f"Invalid proof for {lemma_name}: {reason}")
                    logger.warning(f"Proof was: {proof}")
        
        return proofs_generated
    
    def extract_and_apply_from_logs(self, log_files: List[str]):
        """Extract proofs from logs and apply them"""
        all_proofs = {}
        
        for log_file in log_files:
            logger.info(f"Extracting from {log_file}")
            proofs = self.extractor.extract_from_log(log_file)
            all_proofs.update(proofs)
        
        logger.info(f"Extracted {len(all_proofs)} valid proofs")
        
        # Apply proofs
        for lemma_name, proof in all_proofs.items():
            # Search for the lemma in all files
            for pattern in ["NavierStokesLedger/*.lean", "NavierStokesLedger/*/*.lean"]:
                for filepath in Path(".").glob(pattern):
                    if self.applicator.find_lemma_in_file(filepath, lemma_name):
                        if self.applicator.apply_single_proof(filepath, lemma_name, proof):
                            self.applicator.applied_proofs.append(lemma_name)
                        else:
                            self.applicator.failed_proofs.append(lemma_name)
                        break
    
    async def run_targeted_proof_campaign(self, target_files: List[str], proofs_per_file: int = 5):
        """Run Claude 4 on specific files"""
        if not self.generator:
            logger.error("No API key for Claude 4")
            return
        
        # Create backup first
        self.applicator.create_backup()
        
        total_proofs = 0
        for filepath in target_files:
            path = Path(filepath)
            if path.exists():
                proofs = await self.process_file_with_claude4(path, proofs_per_file)
                total_proofs += proofs
                
                # Run incremental build check
                if total_proofs > 0 and total_proofs % 10 == 0:
                    logger.info("Running incremental build check...")
                    if not self.applicator.run_incremental_build():
                        logger.warning("Build failed, stopping")
                        break
        
        # Final summary
        logger.info(f"\n{'='*50}")
        logger.info(f"Total proofs generated: {total_proofs}")
        logger.info(f"Successfully applied: {len(self.applicator.applied_proofs)}")
        logger.info(f"Failed: {len(self.applicator.failed_proofs)}")
        
        # Final build
        logger.info("\nRunning final build...")
        if self.applicator.run_incremental_build():
            logger.info("✅ Build successful!")
        else:
            logger.info("❌ Build failed")
            logger.info(f"Backup available at: {self.applicator.backup_dir}")

async def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Advanced Proof System for Navier-Stokes')
    parser.add_argument('--extract-logs', nargs='+', help='Extract proofs from log files')
    parser.add_argument('--target-files', nargs='+', help='Target files for Claude 4')
    parser.add_argument('--api-key', help='Anthropic API key for Claude 4')
    parser.add_argument('--proofs-per-file', type=int, default=5, help='Max proofs per file')
    
    args = parser.parse_args()
    
    # Get API key from env if not provided
    api_key = args.api_key or os.getenv('ANTHROPIC_API_KEY')
    
    system = AdvancedProofSystem(api_key)
    
    if args.extract_logs:
        system.extract_and_apply_from_logs(args.extract_logs)
    
    if args.target_files and api_key:
        await system.run_targeted_proof_campaign(args.target_files, args.proofs_per_file)
    elif args.target_files and not api_key:
        logger.error("API key required for Claude 4 proof generation")
    
    if not args.extract_logs and not args.target_files:
        # Default: try to extract from recent logs
        log_files = ['autonomous_proof_claude4.log', 'big_batch_run.log', 'turbo_run.log']
        existing_logs = [f for f in log_files if Path(f).exists()]
        if existing_logs:
            system.extract_and_apply_from_logs(existing_logs)
        else:
            logger.info("No action specified. Use --extract-logs or --target-files")

if __name__ == "__main__":
    asyncio.run(main()) 
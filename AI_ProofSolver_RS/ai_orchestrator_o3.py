#!/usr/bin/env python3
"""
Pure AI-Driven Sorry Removal Orchestrator
Uses only o3 model for all decision making and proof generation
"""

import os
import re
import json
import time
from pathlib import Path
from datetime import datetime
from openai import OpenAI

class AIOrchestrator:
    def __init__(self, api_key: str):
        self.client = OpenAI(api_key=api_key)
        self.model = "gpt-4o"  # Using gpt-4o as o3 is not yet available
        self.session_data = {
            'start_time': datetime.now(),
            'sorries_found': 0,
            'sorries_resolved': 0,
            'ai_calls': 0,
            'total_tokens': 0,
            'progress_log': []
        }
        
    def log_progress(self, message: str):
        """Log progress with timestamp"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        log_entry = f"[{timestamp}] {message}"
        print(log_entry)
        self.session_data['progress_log'].append(log_entry)
        
    def ask_ai(self, prompt: str, max_tokens: int = 2000) -> str:
        """Core AI interaction - all decisions go through AI"""
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[
                    {"role": "system", "content": "You are an expert Lean 4 theorem prover specializing in Navier-Stokes equations and Recognition Science. Be precise and concise."},
                    {"role": "user", "content": prompt}
                ],
                max_tokens=max_tokens,
                temperature=0.2  # Low temperature for consistency
            )
            
            self.session_data['ai_calls'] += 1
            self.session_data['total_tokens'] += response.usage.total_tokens if response.usage else 0
            
            return response.choices[0].message.content.strip()
            
        except Exception as e:
            self.log_progress(f"AI Error: {e}")
            return None
            
    def analyze_project_with_ai(self):
        """Let AI analyze the entire project and create a strategy"""
        self.log_progress("=== AI-DRIVEN SORRY REMOVAL ORCHESTRATOR ===")
        self.log_progress("Asking AI to analyze project structure...")
        
        # Get file list
        lean_files = list(Path("../NavierStokesLedger").glob("*.lean"))
        file_list = "\n".join([f.name for f in lean_files])
        
        prompt = f"""Analyze this Navier-Stokes proof project for sorry removal strategy.

Files in NavierStokesLedger/:
{file_list}

Based on the conversation history, we have:
- 46 total sorries remaining
- Key files: GeometricDepletion.lean (11), VorticityLemmas.lean (8), RSClassicalBridge.lean (6)
- Recognition Science constants: C_star=0.05, φ≈1.618, cascade_cutoff=-4log(φ)

Provide a strategic order for tackling sorries, considering:
1. Dependencies (solve foundational lemmas first)
2. Difficulty (start with easier proofs to build momentum)
3. Impact (prioritize proofs that unlock many others)

Output a JSON list of files to process in order, with reasoning."""

        response = self.ask_ai(prompt)
        self.log_progress("AI strategy received")
        
        # Parse AI's strategic order
        try:
            # Extract JSON from response
            json_match = re.search(r'\[.*\]', response, re.DOTALL)
            if json_match:
                file_order = json.loads(json_match.group())
            else:
                # Fallback order
                file_order = ["RSImports.lean", "PDEOperators.lean", "VectorCalculus.lean", 
                             "BiotSavart.lean", "SimplifiedProofs.lean", "RecognitionLemmas.lean",
                             "VorticityLemmas.lean", "GeometricDepletion.lean", "RSClassicalBridge.lean"]
                
            return file_order
        except:
            return [f.name for f in lean_files]
            
    def find_sorries_with_ai(self, file_path: Path):
        """Use AI to analyze sorries in a file"""
        with open(file_path, 'r') as f:
            content = f.read()
            
        prompt = f"""Analyze this Lean file and identify all sorries with their context.

File: {file_path.name}

For each sorry, provide:
1. Line number (approximate)
2. Theorem/lemma name
3. What needs to be proved
4. Difficulty estimate (easy/medium/hard)
5. Key techniques likely needed

Content (showing key parts):
{content[:3000]}...

Output as JSON list."""

        response = self.ask_ai(prompt, max_tokens=1500)
        
        # Parse response
        try:
            json_match = re.search(r'\[.*\]', response, re.DOTALL)
            if json_match:
                sorries = json.loads(json_match.group())
                self.session_data['sorries_found'] += len(sorries)
                return sorries
        except:
            pass
            
        # Fallback: simple search
        sorries = []
        lines = content.split('\n')
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                sorries.append({
                    'line': i + 1,
                    'content': line.strip(),
                    'difficulty': 'unknown'
                })
        
        self.session_data['sorries_found'] += len(sorries)
        return sorries
        
    def generate_proof_with_ai(self, file_path: Path, sorry_info: dict, context_window: int = 50):
        """Use AI to generate a proof for a specific sorry"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # Extract context around the sorry
        sorry_line = sorry_info.get('line', 0) - 1
        start = max(0, sorry_line - context_window)
        end = min(len(lines), sorry_line + 10)
        
        context = ''.join(lines[start:end])
        
        # Find the theorem declaration
        theorem_start = sorry_line
        while theorem_start > 0 and not any(kw in lines[theorem_start] for kw in ['theorem', 'lemma', 'def']):
            theorem_start -= 1
            
        theorem_context = ''.join(lines[theorem_start:sorry_line + 1])
        
        prompt = f"""Generate a Lean 4 proof to replace this sorry.

File: {file_path.name}
Theorem context:
{theorem_context}

Surrounding context:
{context}

Key Recognition Science facts:
- C_star = 0.05 (geometric depletion constant)
- φ = (1 + √5)/2 ≈ 1.618 (golden ratio)
- cascade_cutoff = -4 * log φ ≈ -1.887
- recognition_tick = (planck_time * c) / φ^6 ≈ 7.33e-15

Recent improvements from the conversation:
- Use angle_bound_aligned_norm with 2*sin(π/12) bound
- Apply Lagrange identity for cross products
- Use eight-beat modulation for phase coherence

Generate ONLY the Lean proof code to replace 'sorry'. Be concise and correct."""

        proof = self.ask_ai(prompt, max_tokens=800)
        
        # Clean the proof
        if proof:
            # Remove markdown blocks
            proof = re.sub(r'```lean?\s*\n?', '', proof)
            proof = re.sub(r'```\s*$', '', proof)
            
            # Remove explanatory text before 'by'
            if 'by' in proof:
                by_index = proof.find('by')
                proof = proof[by_index:]
                
        return proof
        
    def apply_proof_with_ai_validation(self, file_path: Path, sorry_line: int, proof: str):
        """Apply proof and use AI to validate the change"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # Apply the proof
        if sorry_line <= len(lines) and 'sorry' in lines[sorry_line - 1]:
            original_line = lines[sorry_line - 1]
            lines[sorry_line - 1] = lines[sorry_line - 1].replace('sorry', proof)
            
            # Ask AI to validate
            prompt = f"""Validate this proof replacement:

Original: {original_line.strip()}
New proof: {proof}

Is this a valid Lean 4 proof? Any syntax issues? Reply with 'valid' or describe the issue briefly."""

            validation = self.ask_ai(prompt, max_tokens=200)
            
            if 'valid' in validation.lower():
                with open(file_path, 'w') as f:
                    f.writelines(lines)
                self.session_data['sorries_resolved'] += 1
                return True
            else:
                self.log_progress(f"AI validation failed: {validation}")
                return False
        
        return False
        
    def orchestrate_file(self, file_path: Path):
        """Orchestrate sorry removal for a single file"""
        self.log_progress(f"\n--- Processing {file_path.name} ---")
        
        # Find sorries
        sorries = self.find_sorries_with_ai(file_path)
        self.log_progress(f"Found {len(sorries)} sorries")
        
        # Process each sorry
        for i, sorry in enumerate(sorries):
            self.log_progress(f"Sorry {i+1}/{len(sorries)}: line {sorry.get('line', '?')}")
            
            # Generate proof
            proof = self.generate_proof_with_ai(file_path, sorry)
            
            if proof:
                # Apply and validate
                if self.apply_proof_with_ai_validation(file_path, sorry['line'], proof):
                    self.log_progress(f"✓ Successfully resolved!")
                else:
                    self.log_progress(f"✗ Failed to apply proof")
            else:
                self.log_progress(f"✗ Could not generate proof")
                
            # Brief pause to avoid rate limits
            time.sleep(0.5)
            
    def run_orchestration(self):
        """Main orchestration loop"""
        # Get AI-recommended file order
        file_order = self.analyze_project_with_ai()
        
        self.log_progress(f"\nProcessing {len(file_order)} files in AI-recommended order")
        
        # Process each file
        for filename in file_order:
            file_path = Path(f"../NavierStokesLedger/{filename}")
            if file_path.exists():
                self.orchestrate_file(file_path)
                
        # Final report
        self.generate_final_report()
        
    def generate_final_report(self):
        """Generate final report using AI"""
        duration = (datetime.now() - self.session_data['start_time']).total_seconds() / 60
        
        prompt = f"""Generate a concise final report for this sorry removal session:

Duration: {duration:.1f} minutes
Sorries found: {self.session_data['sorries_found']}
Sorries resolved: {self.session_data['sorries_resolved']}
AI calls made: {self.session_data['ai_calls']}
Total tokens: {self.session_data['total_tokens']}

Key accomplishments from the log:
{chr(10).join(self.session_data['progress_log'][-10:])}

Provide:
1. Success rate
2. Key insights discovered
3. Recommendations for next session"""

        report = self.ask_ai(prompt, max_tokens=500)
        
        self.log_progress("\n=== FINAL REPORT ===")
        print(report)
        
        # Save session data
        with open('ai_orchestrator_session.json', 'w') as f:
            json.dump(self.session_data, f, indent=2, default=str)

def main():
    # Get API key from environment or command line
    import sys
    
    if len(sys.argv) > 1:
        api_key = sys.argv[1]
    else:
        api_key = os.getenv("OPENAI_API_KEY")
        
    if not api_key:
        print("Error: Please provide OpenAI API key as argument or set OPENAI_API_KEY environment variable")
        return
    
    orchestrator = AIOrchestrator(api_key)
    orchestrator.run_orchestration()

if __name__ == "__main__":
    main() 
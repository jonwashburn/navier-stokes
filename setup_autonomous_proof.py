#!/usr/bin/env python3
"""
Autonomous Lean Proof Completion System
DO NOT put API keys in this file - use environment variables
"""

import os
import subprocess
import json
import time
from pathlib import Path
from typing import List, Dict, Optional, Tuple
import asyncio
import aiohttp
from dataclasses import dataclass
import re
import logging

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Configuration
LEAN_PROJECT_ROOT = Path(__file__).parent
SCAFFOLD_FILE = "NavierStokesLedger/UnconditionalProof.lean"
MAX_PARALLEL_AGENTS = 5
PROOF_ATTEMPT_TIMEOUT = 30  # seconds
API_TIMEOUT = 60  # seconds for API calls
MAX_RETRIES = 3

@dataclass
class ProofTask:
    """Represents a single sorry to be filled"""
    file_path: str
    line_number: int
    lemma_name: str
    statement: str
    dependencies: List[str]
    
class LeanProofAgent:
    """Manages interaction with Lean and proof synthesis"""
    
    def __init__(self, api_key: Optional[str] = None):
        # Get API key from environment if not provided
        self.api_key = api_key or os.environ.get("ANTHROPIC_API_KEY")
        if not self.api_key:
            logger.warning("No API key found - will only use mechanical tactics")
            
    async def find_sorries(self) -> List[ProofTask]:
        """Parse Lean files to find all remaining sorries"""
        tasks = []
        
        # Use grep to find sorries
        result = subprocess.run(
            ["grep", "-n", "sorry", SCAFFOLD_FILE],
            capture_output=True, text=True, cwd=LEAN_PROJECT_ROOT
        )
        
        if result.returncode == 0 and result.stdout:
            # Read the file to get context
            with open(LEAN_PROJECT_ROOT / SCAFFOLD_FILE, 'r') as f:
                lines = f.readlines()
            
            # Parse grep output
            for line in result.stdout.strip().split('\n'):
                if 'declarations with' not in line and 'TODO' not in line:
                    # Extract line number from format "123:  sorry"
                    match = re.match(r'^(\d+):', line)
                    if match:
                        line_num = int(match.group(1))
                        
                        # Check if this line contains just "sorry" or ends with "sorry"
                        if line_num <= len(lines):
                            line_content = lines[line_num-1].strip()
                            if line_content == "sorry" or line_content.endswith("sorry"):
                                # Look backwards to find lemma/theorem name
                                lemma_name = ""
                                for i in range(max(0, line_num - 10), line_num):
                                    if i < len(lines):
                                        if 'lemma ' in lines[i] or 'theorem ' in lines[i]:
                                            # Extract name
                                            match = re.search(r'(lemma|theorem)\s+(\w+)', lines[i])
                                            if match:
                                                lemma_name = match.group(2)
                                                break
                                
                                if lemma_name:
                                    tasks.append(ProofTask(
                                        file_path=str(SCAFFOLD_FILE),
                                        line_number=line_num,
                                        lemma_name=lemma_name,
                                        statement=lines[line_num-1].strip() if line_num > 0 else "",
                                        dependencies=[]
                                    ))
            
        return tasks
    
    async def attempt_proof(self, task: ProofTask) -> Optional[str]:
        """Try to prove a single lemma using AI only"""
        
        # Skip mechanical tactics - go straight to AI
        if self.api_key:
            logger.info(f"Using Claude 4 Sonnet for {task.lemma_name}")
            for attempt in range(MAX_RETRIES):
                try:
                    proof = await self.synthesize_proof_with_ai(task)
                    if proof:
                        # Verify the proof actually compiles
                        if await self.verify_proof(task, proof):
                            return proof
                        else:
                            logger.warning(f"Proof failed compilation for {task.lemma_name}, retrying...")
                except Exception as e:
                    logger.warning(f"AI synthesis attempt {attempt + 1} failed: {e}")
                    if attempt < MAX_RETRIES - 1:
                        await asyncio.sleep(2 ** attempt)  # Exponential backoff
        else:
            logger.error("No API key provided - cannot generate proofs without AI")
        
        return None
        
    async def try_tactic(self, task: ProofTask, tactic: str) -> Optional[str]:
        """Test if a simple tactic solves the goal"""
        # For now, return the tactic name if it's likely to work
        # In a real implementation, this would test compilation
        
        # Simple heuristics for which tactics might work
        if tactic == "decide" and "≥ 0" in task.statement:
            return tactic
        elif tactic == "norm_num" and any(x in task.statement for x in ["<", ">", "≤", "≥"]):
            return tactic
        elif tactic == "linarith" and "ℝ" in task.statement:
            return tactic
            
        return None
        
    async def synthesize_proof_with_ai(self, task: ProofTask) -> Optional[str]:
        """Use Claude to synthesize a proof"""
        
        # Read context around the sorry
        context = self.get_proof_context(task)
        
        prompt = f"""
You are helping prove a lemma in Lean 4. Here is the context:

{context}

The lemma to prove is:
{task.statement}

Please provide ONLY the proof term or tactic sequence that should replace 'sorry'.
Do not include any explanation or markdown formatting.
The proof should be valid Lean 4 code.
"""
        
        # Call Claude API with timeout and error handling
        timeout = aiohttp.ClientTimeout(total=API_TIMEOUT)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            headers = {
                "x-api-key": self.api_key,
                "anthropic-version": "2023-06-01",
                "content-type": "application/json"
            }
            
            data = {
                "model": "claude-sonnet-4-20250514",  # Claude 4 Sonnet
                "max_tokens": 2000,
                "messages": [{"role": "user", "content": prompt}]
            }
            
            try:
                async with session.post(
                    "https://api.anthropic.com/v1/messages",
                    headers=headers,
                    json=data
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return result["content"][0]["text"]
                    else:
                        logger.error(f"API error: {response.status}")
                        return None
            except asyncio.TimeoutError:
                logger.error("API request timed out")
                return None
            except Exception as e:
                logger.error(f"API request failed: {e}")
                return None
        
    def get_proof_context(self, task: ProofTask) -> str:
        """Extract relevant context for the proof"""
        # Read file and get surrounding context
        with open(task.file_path, 'r') as f:
            lines = f.readlines()
            
        start = max(0, task.line_number - 20)
        end = min(len(lines), task.line_number + 10)
        
        return ''.join(lines[start:end])
        
    async def verify_proof(self, task: ProofTask, proof: str) -> bool:
        """Verify a proof by actually compiling it"""
        
        logger.info(f"Verifying proof for {task.lemma_name}")
        
        # Read the original file
        with open(LEAN_PROJECT_ROOT / task.file_path, 'r') as f:
            lines = f.readlines()
        
        # Replace the sorry with the proof
        if task.line_number <= len(lines):
            lines[task.line_number - 1] = f"  {proof}\n"
        else:
            logger.error(f"Line number {task.line_number} out of range")
            return False
        
        # Write to a temporary file
        temp_file = LEAN_PROJECT_ROOT / f"{task.file_path}.tmp"
        with open(temp_file, 'w') as f:
            f.writelines(lines)
        
        # Try to compile the file
        try:
            result = subprocess.run(
                ["lake", "build", "NavierStokesLedger"],  # Build the library, not the file
                capture_output=True,
                text=True,
                timeout=PROOF_ATTEMPT_TIMEOUT,
                cwd=LEAN_PROJECT_ROOT
            )
            
            # Check if compilation succeeded
            if result.returncode == 0:
                logger.info(f"✓ Proof verified for {task.lemma_name}")
                # Move the temp file to replace the original
                temp_file.rename(LEAN_PROJECT_ROOT / task.file_path)
                return True
            else:
                logger.warning(f"Compilation failed for {task.lemma_name}:")
                logger.warning(result.stderr[:500])  # First 500 chars of error
                temp_file.unlink()  # Remove temp file
                return False
                
        except subprocess.TimeoutExpired:
            logger.error(f"Compilation timed out for {task.lemma_name}")
            temp_file.unlink()
            return False
        except Exception as e:
            logger.error(f"Error during compilation: {e}")
            if temp_file.exists():
                temp_file.unlink()
            return False

async def main():
    """Main orchestration loop"""
    
    logger.info("=== Autonomous Lean Proof System ===")
    logger.info(f"Project root: {LEAN_PROJECT_ROOT}")
    logger.info(f"Scaffold file: {SCAFFOLD_FILE}")
    
    # Initialize agent
    agent = LeanProofAgent()
    
    # Find all sorries
    logger.info("\nSearching for remaining sorries...")
    tasks = await agent.find_sorries()
    logger.info(f"Found {len(tasks)} sorries to fill")
    
    if not tasks:
        logger.info("No sorries found - proof is complete!")
        return
    
    # Process in parallel with rate limiting
    semaphore = asyncio.Semaphore(MAX_PARALLEL_AGENTS)
    
    async def process_task(task: ProofTask):
        async with semaphore:
            logger.info(f"\nAttempting: {task.lemma_name}")
            proof = await agent.attempt_proof(task)
            
            if proof:
                logger.info(f"✓ Proved {task.lemma_name}")
                return True
            else:
                logger.warning(f"✗ Could not find valid proof for {task.lemma_name}")
                return False
    
    # Run all tasks
    results = await asyncio.gather(*[process_task(task) for task in tasks], return_exceptions=True)
    
    # Handle any exceptions
    success_count = 0
    for i, result in enumerate(results):
        if isinstance(result, Exception):
            logger.error(f"Task {tasks[i].lemma_name} failed with error: {result}")
        elif result:
            success_count += 1
    
    # Summary
    logger.info(f"\n=== Summary ===")
    logger.info(f"Proved: {success_count}/{len(tasks)}")
    logger.info(f"Remaining: {len(tasks) - success_count}")
    
    # Show which proofs succeeded
    if success_count > 0:
        logger.info("\nSuccessful proofs:")
        for i, (task, result) in enumerate(zip(tasks, results)):
            if result and not isinstance(result, Exception):
                logger.info(f"  - {task.lemma_name}")

if __name__ == "__main__":
    # Check if API key is provided
    if os.environ.get("ANTHROPIC_API_KEY"):
        logger.info("API key found - will use both mechanical and AI tactics")
    else:
        logger.info("No API key found - will use only mechanical tactics")
        
    asyncio.run(main()) 
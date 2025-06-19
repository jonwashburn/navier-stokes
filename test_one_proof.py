#!/usr/bin/env python3
"""
Test script to prove just one lemma
"""

import os
import asyncio
import logging
from setup_autonomous_proof import LeanProofAgent, ProofTask

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

async def test_single_proof():
    """Test proving a single lemma"""
    
    # Check API key
    if not os.environ.get("ANTHROPIC_API_KEY"):
        logger.error("Please set ANTHROPIC_API_KEY environment variable")
        return
    
    # Create agent
    agent = LeanProofAgent()
    
    # Create a test task for covering_multiplicity (should be easy)
    task = ProofTask(
        file_path="NavierStokesLedger/UnconditionalProof.lean",
        line_number=78,  # The line with decide
        lemma_name="covering_multiplicity",
        statement="∀ (t : ℝ), (7 : ℕ) ≥ 0",
        dependencies=[]
    )
    
    logger.info(f"Testing proof for: {task.lemma_name}")
    logger.info(f"Statement: {task.statement}")
    
    # Get the proof directly to see what Claude generates
    proof = await agent.synthesize_proof_with_ai(task)
    logger.info(f"Claude generated proof: {proof}")
    
    # Now try the full attempt with verification
    proof = await agent.attempt_proof(task)
    
    if proof:
        logger.info(f"Successfully proved {task.lemma_name}!")
        logger.info(f"Final proof: {proof}")
    else:
        logger.error(f"Failed to prove {task.lemma_name}")

if __name__ == "__main__":
    asyncio.run(test_single_proof()) 
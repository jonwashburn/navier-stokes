#!/usr/bin/env python3
"""
Progressive Navier-Stokes Solver
Tracks attempted proofs and progressively moves to harder ones
"""

import asyncio
import os
import sys
import json
from pathlib import Path
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from enhanced_navier_solver import EnhancedNavierStokesProofCompleter
import logging

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class ProgressiveProofSolver:
    def __init__(self, api_key: str):
        self.completer = EnhancedNavierStokesProofCompleter(api_key, apply_proofs=False)
        self.attempted_file = Path("Solver/attempted_proofs.json")
        self.attempted_proofs = self.load_attempted()
        
    def load_attempted(self):
        """Load list of already attempted proofs"""
        if self.attempted_file.exists():
            with open(self.attempted_file, 'r') as f:
                return set(json.load(f))
        return set()
    
    def save_attempted(self):
        """Save list of attempted proofs"""
        with open(self.attempted_file, 'w') as f:
            json.dump(list(self.attempted_proofs), f)
    
    async def run_progressive_batch(self, batch_size=50):
        """Run a batch, skipping already-attempted proofs"""
        logger.info("=== PROGRESSIVE Navier-Stokes Proof Completion ===")
        logger.info(f"📊 Already attempted: {len(self.attempted_proofs)} proofs")
        
        # Find all sorries
        sorries = await self.completer.find_all_sorries()
        logger.info(f"Found {len(sorries)} total sorries")
        
        # Filter out already attempted
        new_sorries = [s for s in sorries if s.lemma_name not in self.attempted_proofs]
        logger.info(f"New sorries to attempt: {len(new_sorries)}")
        
        # Show difficulty breakdown
        easy = sum(1 for s in new_sorries if s.difficulty == 1)
        medium = sum(1 for s in new_sorries if s.difficulty == 2)
        hard = sum(1 for s in new_sorries if s.difficulty == 3)
        logger.info(f"Difficulty breakdown: {easy} easy, {medium} medium, {hard} hard")
        
        if not new_sorries:
            logger.info("No new sorries to attempt!")
            return
        
        # Process batch
        completed = 0
        failed = 0
        batch_targets = new_sorries[:batch_size]
        
        logger.info(f"\n🎯 Targeting {len(batch_targets)} new proofs...")
        
        for i, sorry in enumerate(batch_targets):
            logger.info(f"\n[{i+1}/{len(batch_targets)}] Working on {sorry.lemma_name} (difficulty: {sorry.difficulty})")
            
            # Mark as attempted
            self.attempted_proofs.add(sorry.lemma_name)
            
            success, proof = await self.completer.complete_sorry(sorry)
            
            if success:
                completed += 1
                logger.info(f"✅ Success #{completed}: {sorry.lemma_name}")
            else:
                failed += 1
                logger.warning(f"❌ Failed: {sorry.lemma_name}")
            
            # Progress update every 10
            if (i + 1) % 10 == 0:
                logger.info(f"\nProgress: {i+1}/{len(batch_targets)} ({(i+1)/len(batch_targets)*100:.1f}%)")
                logger.info(f"Success rate: {completed/(completed+failed)*100:.1f}%")
                # Save progress
                self.save_attempted()
        
        # Final summary
        logger.info(f"\n{'='*60}")
        logger.info(f"BATCH COMPLETE")
        logger.info(f"✅ Completed: {completed}/{completed + failed} proofs")
        logger.info(f"📈 Success rate: {completed/(completed+failed)*100:.1f}%")
        logger.info(f"📊 Total attempted so far: {len(self.attempted_proofs)}")
        
        # Save final state
        self.save_attempted()
        
        # Show what's next
        remaining_new = len(new_sorries) - len(batch_targets)
        if remaining_new > 0:
            logger.info(f"\n🔥 {remaining_new} new proofs remaining")
            next_5 = new_sorries[batch_size:batch_size+5]
            if next_5:
                logger.info("Next targets:")
                for s in next_5:
                    logger.info(f"  - {s.lemma_name} ({s.category}, difficulty: {s.difficulty})")

async def main():
    api_key = os.environ.get('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY")
        return
    
    solver = ProgressiveProofSolver(api_key)
    await solver.run_progressive_batch(50)

if __name__ == "__main__":
    asyncio.run(main()) 
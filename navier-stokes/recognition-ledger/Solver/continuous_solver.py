#!/usr/bin/env python3
"""
Continuous Navier-Stokes Proof Solver
Runs multiple batches automatically to make systematic progress
"""

import asyncio
import os
import re
import json
import time
from pathlib import Path
import logging
from enhanced_navier_solver import EnhancedNavierStokesProofCompleter

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

class ContinuousProofSolver:
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.session_stats = {
            'total_attempts': 0,
            'total_successes': 0,
            'start_time': time.time(),
            'proofs_by_category': {},
            'proof_data': []
        }
    
    async def run_batch(self, batch_size: int = 15) -> dict:
        """Run a single batch of proof attempts"""
        completer = EnhancedNavierStokesProofCompleter(self.api_key, apply_proofs=False)
        
        # Find sorries
        sorries = await completer.find_all_sorries()
        
        # Filter for easy ones we haven't completed yet
        easy_targets = [
            s for s in sorries 
            if s.difficulty == 1 and s.category in ['numerical', 'golden_ratio', 'definition', 'tactic_proof']
        ]
        
        # Take next batch
        batch = easy_targets[:batch_size]
        
        batch_results = {
            'batch_size': len(batch),
            'successes': 0,
            'failures': 0,
            'proofs': []
        }
        
        for sorry in batch:
            success, proof = await completer.complete_sorry(sorry)
            
            self.session_stats['total_attempts'] += 1
            
            if success:
                self.session_stats['total_successes'] += 1
                batch_results['successes'] += 1
                
                # Track by category
                cat = sorry.category
                if cat not in self.session_stats['proofs_by_category']:
                    self.session_stats['proofs_by_category'][cat] = 0
                self.session_stats['proofs_by_category'][cat] += 1
                
                # Store proof data
                proof_data = {
                    'lemma': sorry.lemma_name,
                    'file': sorry.file,
                    'line': sorry.line,
                    'proof': proof,
                    'category': sorry.category,
                    'difficulty': sorry.difficulty
                }
                batch_results['proofs'].append(proof_data)
                self.session_stats['proof_data'].append(proof_data)
                
            else:
                batch_results['failures'] += 1
            
            # Small delay between proofs
            await asyncio.sleep(0.5)
        
        return batch_results
    
    def save_session_data(self):
        """Save current session progress"""
        with open('continuous_solver_session.json', 'w') as f:
            json.dump(self.session_stats, f, indent=2)
        
        # Also save just the proofs for easy application
        if self.session_stats['proof_data']:
            with open('ready_to_apply_proofs.json', 'w') as f:
                json.dump({
                    'timestamp': time.time(),
                    'total_proofs': len(self.session_stats['proof_data']),
                    'proofs': self.session_stats['proof_data']
                }, f, indent=2)
    
    def print_session_summary(self):
        """Print current session statistics"""
        elapsed = time.time() - self.session_stats['start_time']
        success_rate = (self.session_stats['total_successes'] / 
                       max(1, self.session_stats['total_attempts']) * 100)
        
        logger.info("\n" + "="*60)
        logger.info("📊 CONTINUOUS SOLVER SESSION SUMMARY")
        logger.info("="*60)
        logger.info(f"⏱️  Runtime: {elapsed/60:.1f} minutes")
        logger.info(f"🎯 Success Rate: {success_rate:.1f}% ({self.session_stats['total_successes']}/{self.session_stats['total_attempts']})")
        logger.info(f"⚡ Proofs/minute: {self.session_stats['total_successes']/(elapsed/60):.1f}")
        
        logger.info("\n📋 Proofs by Category:")
        for cat, count in sorted(self.session_stats['proofs_by_category'].items()):
            logger.info(f"   {cat}: {count}")
        
        logger.info(f"\n💾 Total Proofs Ready to Apply: {len(self.session_stats['proof_data'])}")
    
    async def run_continuous_session(self, max_batches: int = 5, batch_size: int = 15):
        """Run multiple batches continuously"""
        logger.info("🚀 Starting Continuous Proof Solver Session")
        logger.info(f"Target: {max_batches} batches of {batch_size} proofs each")
        
        for batch_num in range(1, max_batches + 1):
            logger.info(f"\n🔄 === BATCH {batch_num}/{max_batches} ===")
            
            try:
                batch_results = await self.run_batch(batch_size)
                
                logger.info(f"✅ Batch {batch_num} Complete:")
                logger.info(f"   Successes: {batch_results['successes']}")
                logger.info(f"   Failures: {batch_results['failures']}")
                logger.info(f"   Success Rate: {batch_results['successes']/batch_results['batch_size']*100:.1f}%")
                
                # Save progress after each batch
                self.save_session_data()
                
                # Brief pause between batches
                if batch_num < max_batches:
                    logger.info("⏸️  Brief pause before next batch...")
                    await asyncio.sleep(2)
                
            except Exception as e:
                logger.error(f"❌ Batch {batch_num} failed: {e}")
                continue
        
        # Final summary
        self.print_session_summary()
        
        # Save final state
        self.save_session_data()
        
        logger.info("\n🎉 Continuous session complete!")
        logger.info("📄 Results saved to:")
        logger.info("   - continuous_solver_session.json (full session data)")
        logger.info("   - ready_to_apply_proofs.json (proofs ready to apply)")

async def main():
    api_key = os.environ.get('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY")
        return
    
    solver = ContinuousProofSolver(api_key)
    
    # Run 3 batches of 15 proofs each (45 total proof attempts)
    await solver.run_continuous_session(max_batches=3, batch_size=15)
    
    # Show final recommendations
    logger.info("\n🔧 NEXT STEPS:")
    logger.info("1. Review generated proofs in ready_to_apply_proofs.json")
    logger.info("2. Use mass_proof_applicator.py to apply them safely")
    logger.info("3. Run lake build to verify compilation")
    logger.info("4. Continue with harder proof categories")

if __name__ == "__main__":
    asyncio.run(main()) 
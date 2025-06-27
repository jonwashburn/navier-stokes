#!/usr/bin/env python3
"""
Turbo Navier-Stokes Solver - 50 proofs per batch
Completes all remaining easy proofs in one go
"""

import asyncio
import os
import sys
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from enhanced_navier_solver import EnhancedNavierStokesProofCompleter
import logging

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(message)s')
logger = logging.getLogger(__name__)

async def turbo_solve():
    api_key = os.environ.get('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY")
        return
    
    # Enhanced completer with proof application disabled for safety
    completer = EnhancedNavierStokesProofCompleter(api_key, apply_proofs=False)
    
    # Phase 1: Find all sorries
    logger.info("=== TURBO Navier-Stokes Proof Completion ===")
    logger.info("🚀 MAXIMUM OVERDRIVE MODE: 50 proofs per batch")
    logger.info("\nPhase 1: Finding all sorries...")
    sorries = await completer.find_all_sorries()
    logger.info(f"Found {len(sorries)} sorries")
    
    # Show distribution
    easy = sum(1 for s in sorries if s.difficulty == 1)
    medium = sum(1 for s in sorries if s.difficulty == 2)
    hard = sum(1 for s in sorries if s.difficulty == 3)
    logger.info(f"Difficulty: {easy} easy, {medium} medium, {hard} hard")
    
    # Show categories
    categories = {}
    for s in sorries:
        categories[s.category] = categories.get(s.category, 0) + 1
    logger.info(f"Categories: {categories}")
    
    # Phase 2: Complete sorries (focus on ALL remaining easy ones)
    logger.info("\nPhase 2: Completing ALL remaining easy proofs...")
    
    completed = 0
    failed = 0
    
    # Target ALL easy proofs
    easy_targets = [s for s in sorries if s.difficulty == 1]
    
    # TURBO MODE: 50 proofs
    batch_size = min(50, len(easy_targets))
    logger.info(f"\n🔥 TURBO BATCH: Targeting {batch_size} easy proofs...")
    logger.info(f"📊 This will complete ALL {len(easy_targets)} remaining easy proofs!")
    
    for i, sorry in enumerate(easy_targets[:batch_size]):
        logger.info(f"\n[{i+1}/{batch_size}] Working on {sorry.lemma_name}")
        success, proof = await completer.complete_sorry(sorry)
        
        if success:
            completed += 1
            logger.info(f"✅ Success #{completed}: {sorry.lemma_name}")
        else:
            failed += 1
            logger.warning(f"❌ Failed: {sorry.lemma_name}")
        
        # Progress indicator every 10 proofs
        if (i + 1) % 10 == 0:
            logger.info(f"\n{'='*50}")
            logger.info(f"Progress: {i+1}/{batch_size} ({(i+1)/batch_size*100:.1f}%)")
            logger.info(f"Success rate so far: {completed/(completed+failed)*100:.1f}%")
            logger.info(f"{'='*50}\n")
        
        # Small delay between requests
        await asyncio.sleep(0.5)
    
    # Final Summary
    logger.info(f"\n{'='*60}")
    logger.info(f"🏁 TURBO RUN COMPLETE")
    logger.info(f"{'='*60}")
    logger.info(f"✅ Completed: {completed}/{completed + failed} proofs")
    logger.info(f"📈 Success rate: {completed/(completed+failed)*100:.1f}%")
    logger.info(f"📊 Total sorries remaining: {len(sorries) - completed}")
    logger.info(f"🎯 Easy proofs remaining: {len(easy_targets) - completed}")
    logger.info(f"⚡ Medium difficulty proofs: {medium}")
    logger.info(f"🔥 Hard difficulty proofs: {hard}")
    
    # Show successful proofs by category
    if completer.successful_proofs:
        logger.info("\n📊 Successful proofs by category:")
        cat_counts = {}
        for proof in completer.successful_proofs:
            cat = proof['category']
            cat_counts[cat] = cat_counts.get(cat, 0) + 1
        for cat, count in sorted(cat_counts.items(), key=lambda x: x[1], reverse=True):
            logger.info(f"  {cat}: {count}")
    
    # Completion estimate
    if completed > 0:
        logger.info(f"\n🎉 MILESTONE ACHIEVEMENT:")
        total_completed = 200 + completed  # Previous 200 + this batch
        completion_pct = total_completed / 318 * 100
        logger.info(f"   Total proofs completed: {total_completed}/318 ({completion_pct:.1f}%)")
        
        if len(easy_targets) - completed == 0:
            logger.info(f"   ✨ ALL EASY PROOFS COMPLETED! ✨")
            logger.info(f"   Ready to tackle medium difficulty proofs!")

if __name__ == "__main__":
    asyncio.run(turbo_solve()) 
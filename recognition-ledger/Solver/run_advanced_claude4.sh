#!/bin/bash
# Run the advanced proof system with Claude 4

export ANTHROPIC_API_KEY="${ANTHROPIC_API_KEY}"

# Run the advanced proof system
echo "Starting advanced proof system with Claude 4..."
python3 Solver/advanced_proof_system.py 2>&1 | tee advanced_claude4_run.log

# Show summary
echo ""
echo "=== RUN COMPLETE ==="
echo "Counting remaining sorries..."
grep -r "sorry" NavierStokesLedger/*.lean | wc -l

# Show which files still have sorries
echo ""
echo "Files with sorries:"
grep -c "sorry" NavierStokesLedger/*.lean | grep -v ":0$" | sort -t: -k2 -n 
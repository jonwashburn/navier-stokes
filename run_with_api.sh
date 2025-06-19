#!/bin/bash
# Set the API key properly
export ANTHROPIC_API_KEY="[API_KEY_NEEDED]"

echo "API key set. Length: ${#ANTHROPIC_API_KEY}"

# Run the autonomous proof system
if [ "$1" = "auto" ]; then
    python3 setup_autonomous_proof.py 2>&1 | tee autonomous_proof_run.log
elif [ "$1" = "focused" ]; then
    python3 Solver/focused_solver.py 2>&1 | tee focused_solver_run.log
elif [ "$1" = "incremental" ]; then
    python3 Solver/incremental_solver.py 2>&1 | tee incremental_solver_run.log
else
    echo "Usage: ./run_with_api.sh [auto|focused|incremental]"
fi

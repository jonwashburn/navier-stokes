#!/bin/bash
# Template for setting up API key
# Copy this file to setup_env.sh and add your actual API key

export ANTHROPIC_API_KEY="[YOUR_API_KEY_HERE]"

echo "API key set. Length: ${#ANTHROPIC_API_KEY}"

# Run the autonomous proof system
if [ "$1" = "auto" ]; then
    python3 setup_autonomous_proof.py 2>&1 | tee autonomous_proof_run.log
elif [ "$1" = "focused" ]; then
    python3 Solver/focused_solver.py 2>&1 | tee focused_solver_run.log
else
    echo "Usage: ./setup_env.sh [auto|focused]"
fi

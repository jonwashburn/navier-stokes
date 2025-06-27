#!/bin/bash
# Run the Navier-Stokes AI proof completion system

echo "Navier-Stokes Lean Proof Completion System"
echo "=========================================="
echo "Adapted from Yang-Mills solver for Navier-Stokes proofs"
echo ""

# Check for API key
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Error: ANTHROPIC_API_KEY not set"
    echo "Please run: export ANTHROPIC_API_KEY='your-key-here'"
    exit 1
fi

# Create backup
echo "Creating backup of current state..."
backup_dir="backups/NavierStokes_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$backup_dir"
cp -r NavierStokesLedger "$backup_dir/" 2>/dev/null || true

echo ""
echo "Starting Navier-Stokes proof completion..."
echo "Features:"
echo "  ✓ Difficulty-based prioritization (easy numerical proofs first)"
echo "  ✓ Category-specific prompting (golden ratio, vorticity, etc.)"
echo "  ✓ Multiple attempt strategy"
echo "  ✓ Focus on axiom-free proofs"
echo ""

# Ensure we have anthropic installed
if ! python3 -c "import anthropic" 2>/dev/null; then
    echo "Installing anthropic library..."
    pip3 install anthropic
fi

python3 Solver/navier_stokes_solver.py

echo ""
echo "Navier-Stokes completion finished!"
echo "Backup saved in: $backup_dir" 
#!/bin/bash
# Setup script for autonomous Lean proof completion

set -e

echo "=== Navier-Stokes Autonomous Proof Setup ==="

# Check if we're in the right directory
if [ ! -f "lakefile.lean" ]; then
    echo "Error: Run this script from the navier-stokes project root"
    exit 1
fi

# Install Python dependencies
echo "Installing Python dependencies..."
pip3 install --user aiohttp asyncio dataclasses

# Build Lean project and cache mathlib
echo "Building Lean project..."
lake update
lake exe cache get
lake build

# Create .env file template if it doesn't exist
if [ ! -f ".env" ]; then
    echo "Creating .env template..."
    cat > .env << 'EOF'
# DO NOT COMMIT THIS FILE
# Add your API key here:
export ANTHROPIC_API_KEY='your-key-here'

# Optional configuration
export MAX_PARALLEL_AGENTS=5
export PROOF_TIMEOUT=30
EOF
    echo "Please edit .env and add your Anthropic API key"
fi

# Create monitoring script
cat > monitor_progress.sh << 'EOF'
#!/bin/bash
# Monitor proof completion progress

echo "=== Proof Progress ==="
echo "Remaining sorries:"
grep -n "sorry" NavierStokesLedger/UnconditionalProof.lean | wc -l

echo -e "\nDetailed sorry locations:"
lake exe sorry_finder

echo -e "\nGit status:"
git status --short

echo -e "\nLast 5 commits:"
git log --oneline -5
EOF

chmod +x monitor_progress.sh

# Create run script
cat > run_autonomous_proof.sh << 'EOF'
#!/bin/bash
# Run the autonomous proof system

# Load environment
if [ -f ".env" ]; then
    source .env
else
    echo "Error: .env file not found. Run setup_environment.sh first"
    exit 1
fi

# Check API key
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Error: ANTHROPIC_API_KEY not set in .env"
    exit 1
fi

# Run the autonomous system
python3 setup_autonomous_proof.py
EOF

chmod +x run_autonomous_proof.sh

echo "=== Setup Complete ==="
echo ""
echo "Next steps:"
echo "1. Edit .env and add your Anthropic API key"
echo "2. Run: ./run_autonomous_proof.sh"
echo "3. Monitor progress: ./monitor_progress.sh"
echo ""
echo "The system will:"
echo "- Find all remaining sorries in UnconditionalProof.lean"
echo "- Try mechanical tactics first (simp, aesop, norm_num, etc.)"
echo "- Use Claude for complex proofs"
echo "- Automatically commit successful proofs" 
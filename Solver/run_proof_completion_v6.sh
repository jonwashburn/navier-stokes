#!/bin/bash
# Run the v6 AI proof completion system

echo "Yang-Mills Lean Proof Completion System V6"
echo "=========================================="
echo "Targeted approach with difficulty assessment"
echo ""

# Check for API key
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Error: ANTHROPIC_API_KEY not set"
    exit 1
fi

# Create backup
echo "Creating backup of current state..."
backup_dir="backups/YangMillsProof_v6_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$backup_dir"
cp -r YangMillsProof/* "$backup_dir/"

echo ""
echo "Starting v6 proof completion..."
echo "Features:"
echo "  ✓ Difficulty-based prioritization (easy first)"
echo "  ✓ Real compilation testing"
echo "  ✓ Category-specific prompting"
echo "  ✓ Working build environment"
echo ""

python3 lean_ai_agents_v6.py

echo ""
echo "V6 completion finished!"
echo "Backup saved in: $backup_dir" 
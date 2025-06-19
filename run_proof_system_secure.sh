#!/bin/bash
# Secure runner for autonomous proof system
# API key is only passed via environment variable, never written to disk

set -euo pipefail

echo "=== Secure Autonomous Proof Runner ==="
echo "This script will:"
echo "1. Prompt for your API key (hidden input)"
echo "2. Run the proof system with the key in memory only"
echo "3. Clear the key from memory when done"
echo ""

# Function to securely read API key
read_api_key() {
    echo -n "Enter your Anthropic API key (input hidden): "
    read -s ANTHROPIC_API_KEY
    echo ""  # New line after hidden input
    
    # Validate key format (basic check)
    if [[ ! "$ANTHROPIC_API_KEY" =~ ^sk-ant-api[0-9]{2}- ]]; then
        echo "Warning: API key doesn't match expected format (sk-ant-api...)"
        echo -n "Continue anyway? (y/N): "
        read -r response
        if [[ ! "$response" =~ ^[Yy]$ ]]; then
            echo "Aborted."
            exit 1
        fi
    fi
}

# Function to run the proof system
run_proof_system() {
    echo ""
    echo "Starting proof system..."
    echo "Using mechanical tactics first, then AI synthesis if needed."
    echo ""
    
    # Export the API key for this subprocess only
    export ANTHROPIC_API_KEY
    
    # Run the Python script
    python3 setup_autonomous_proof.py
    
    # Clear the API key from environment
    unset ANTHROPIC_API_KEY
}

# Main execution
main() {
    # Check Python dependencies
    echo "Checking dependencies..."
    if ! python3 -c "import aiohttp" 2>/dev/null; then
        echo "Error: aiohttp not installed. Run: pip3 install aiohttp"
        exit 1
    fi
    
    # Check if we're in the right directory
    if [ ! -f "lakefile.lean" ]; then
        echo "Error: Run this script from the navier-stokes project root"
        exit 1
    fi
    
    # Read API key securely
    read_api_key
    
    # Run the proof system
    run_proof_system
    
    echo ""
    echo "Done! API key has been cleared from memory."
}

# Trap to ensure cleanup on exit
trap 'unset ANTHROPIC_API_KEY' EXIT

# Run main function
main 
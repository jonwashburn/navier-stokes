#!/bin/bash
set -e

# Development Watch Script
# Continuously compiles files as you save them

echo "👀 Starting development watch mode..."

# Get optimal worker count (usually cores - 1 for dev work)
CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo "4")
WORKERS=$((CORES > 1 ? CORES - 1 : 1))

echo "🏃 Using $WORKERS workers for watch mode"
echo "💡 Tip: Save any .lean file and it will auto-compile"
echo "🛑 Press Ctrl+C to stop watching"

# Check if lake has built-in watch support
if lake --help | grep -q "watch"; then
    echo "📁 Using lake's built-in watch with optimizations..."
    lake watch
else
    echo "📁 Using file system watch fallback..."
    # Fallback using fswatch (install with: brew install fswatch)
    if command -v fswatch &> /dev/null; then
        fswatch -r NavierStokesLedger/ | while read file; do
            echo "🔄 File changed: $file"
            echo "🔨 Rebuilding..."
            lake build
        done
    else
        echo "❌ No watch capability found."
        echo "💡 Install fswatch: brew install fswatch"
        echo "🔄 Falling back to manual build mode..."
        lake build
    fi
fi 
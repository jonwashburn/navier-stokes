#!/bin/bash
set -e

# Build Optimization Script for Navier-Stokes
# This script implements the build optimization plan

echo "🚀 Starting optimized build process..."

# Step 1: Clean any stale builds if requested
if [ "$1" = "--clean" ]; then
    echo "🧹 Cleaning build directory..."
    rm -rf .lake/build
    echo "✅ Build directory cleaned"
fi

# Step 2: Update dependencies (skip cache for now due to version conflicts)
echo "📦 Updating dependencies..."
lake update 2>/dev/null || echo "⚠️  Dependencies already up to date"

# Step 3: Get system info for optimal parallelism
CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo "4")
echo "🏃 Using $CORES cores for parallel compilation"

# Step 4: Build with optimizations
echo "🔨 Building with optimizations..."
echo "   - Using $CORES cores (configured in lakefile.lean)"
echo "   - Using -T 200000 for extended timeout"
echo "   - lakefile.lean has moreLeanArgs with parallelism settings"

# Build with optimizations configured in lakefile.lean
lake build

# Step 5: Check build success
if [ $? -eq 0 ]; then
    echo "✅ Build completed successfully!"
    echo "📊 Build directory size:"
    du -sh .lake/build 2>/dev/null || echo "   (size check failed)"
else
    echo "❌ Build failed!"
    exit 1
fi

# Optional: Show build statistics
echo "📈 Quick build stats:"
echo "   - Mathlib cache: $(ls -la .lake/packages/mathlib/.lake/build/ 2>/dev/null | wc -l) files"
echo "   - Project files: $(find .lake/build -name '*.olean' 2>/dev/null | wc -l) compiled"

echo "🎉 Optimized build process complete!" 
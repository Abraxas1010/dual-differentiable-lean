#!/usr/bin/env bash
set -euo pipefail

echo "=== Dual-Differentiable Verification ==="
echo ""

cd "$(dirname "$0")/.."

# Check for sorry/admit
echo "Checking for sorry/admit..."
if grep -rn "sorry\|admit" HeytingLean/*.lean HeytingLean/**/*.lean 2>/dev/null | grep -v "-- sorry"; then
    echo "ERROR: Found sorry/admit in codebase"
    exit 1
fi
echo "✓ No sorry/admit found"
echo ""

# Build
echo "Building library..."
lake build --wfail
echo "✓ Library build successful"
echo ""

# Build executable
echo "Building executable..."
lake build differential_sky_demo
echo "✓ Executable build successful"
echo ""

# Run demo
echo "Running demo..."
lake exe differential_sky_demo
echo ""
echo "✓ Demo execution successful"
echo ""

echo "=== All checks passed ==="

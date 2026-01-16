# Reproducibility Guide

## Requirements

- **Lean 4**: version 4.24.0 (specified in `lean-toolchain`)
- **Mathlib**: version 4.24.0 (specified in `lakefile.lean`)
- **Operating System**: Linux, macOS, or Windows with WSL

## Build Instructions

### 1. Install Lean 4

```bash
# Using elan (recommended)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

### 2. Clone Repository

```bash
git clone https://github.com/Abraxas1010/dual-differentiable-lean.git
cd dual-differentiable-lean/RESEARCHER_BUNDLE
```

### 3. Fetch Dependencies

```bash
lake update
```

This downloads Mathlib and all transitive dependencies. First build may take 15-30 minutes.

### 4. Build Library

```bash
lake build
```

### 5. Build and Run Demo

```bash
lake build differential_sky_demo
lake exe differential_sky_demo
```

## Verification

Run the verification script to confirm no `sorry`/`admit` and successful build:

```bash
./scripts/verify_differential.sh
```

Expected output:
```
=== Dual-Differentiable Verification ===

Checking for sorry/admit...
✓ No sorry/admit found

Building library...
✓ Library build successful

Building executable...
✓ Executable build successful

Running demo...
[differential_sky_demo] compute-backend demo (Rat coefficients)
x = [(1)·Y]
target y = [(2)·(K Y), (1)·(S Y)]
learned w = [(2)·K, (1)·S]
loss(w) = 0
stepSum((K (K S) Y)) = [(1)·(K S)]

✓ Demo execution successful

=== All checks passed ===
```

## Troubleshooting

### "mathlib not found"

Run `lake update` to fetch dependencies.

### Build takes too long

First build downloads and compiles Mathlib (~15-30 min). Subsequent builds are incremental.

### Memory issues

Mathlib requires ~8GB RAM. If build fails with OOM, try:
```bash
lake build -j1  # Single-threaded build
```

## Pinned Versions

The `lake-manifest.json` pins exact dependency versions for reproducibility. To update:
```bash
lake update
lake build
```

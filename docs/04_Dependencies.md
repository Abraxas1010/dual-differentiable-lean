# Dependencies

## Direct Dependencies

| Package | Version | Purpose |
|---------|---------|---------|
| Lean 4 | 4.24.0 | Language runtime |
| Mathlib | v4.24.0 | Mathematical library |

## Mathlib Imports Used

### Linear Algebra

- `Mathlib.LinearAlgebra.BilinearMap` — Bilinear maps for `appBilin`
- `Mathlib.LinearAlgebra.Finsupp.LSum` — Linear sums over Finsupp
- `Mathlib.LinearAlgebra.Prod` — Product spaces for Jacobians

### Data Structures

- `Mathlib.Data.Finset.Basic` — Finite sets for `stepEdges`
- `Mathlib.Data.Finsupp.Defs` — `Finsupp` (functions with finite support)

## No External Runtime Dependencies

The `differential_sky_demo` executable:
- Uses only Lean's standard library at runtime
- All Mathlib usage is compile-time only
- No FFI or native code dependencies

## Dependency Graph

```
dual-differentiable
       │
       └── mathlib4 (v4.24.0)
              │
              ├── Qq
              ├── Aesop
              ├── Batteries
              └── (transitive deps)
```

## Updating Dependencies

To update to newer Mathlib:

1. Edit `lakefile.lean`:
   ```lean
   require mathlib from git
     "https://github.com/leanprover-community/mathlib4" @ "vX.Y.Z"
   ```

2. Run:
   ```bash
   lake update
   lake build
   ```

3. Fix any API changes (rare for stable Mathlib releases)

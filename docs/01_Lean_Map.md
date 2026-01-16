# Lean Module Map

## Module Hierarchy

```
HeytingLean/
├── LoF/
│   ├── HoTT/
│   │   └── Identity.lean          # HoTT-style identity types (Id, FormId)
│   └── Combinators/
│       ├── SKY.lean               # Core SKY combinators and Step relation
│       ├── SKYMultiway.lean       # Multiway enumeration of rewrite edges
│       └── Differential/
│           ├── VectorSpace.lean   # FormalSum abbrev, single, l2NormSq
│           ├── LinearComb.lean    # Bilinear application, stepSum
│           ├── Derivative.lean    # Dual numbers, chain rule
│           ├── Exponential.lean   # Exp V (bang modality)
│           ├── Codereliction.lean # Linear increment lemma
│           ├── Loss.lean          # IOExample, coordinate gradients
│           ├── GradientDescent.lean # GDConfig, synthesize
│           ├── NucleusDifferential.lean # Nucleus projection
│           ├── SKYDerivatives.lean # K/S/Y Jacobians
│           ├── Compute.lean       # Executable runtime (Rat)
│           ├── Tests.lean         # Compile-time sanity
│           └── Demo.lean          # Demo configuration
└── CLI/
    └── DifferentialSKYDemoMain.lean # Executable demo
```

## Import Dependencies

```
Identity.lean
    ↓
SKY.lean
    ↓
SKYMultiway.lean
    ↓
VectorSpace.lean → LinearComb.lean → Derivative.lean
                         ↓                    ↓
                    Exponential.lean    Codereliction.lean
                         ↓
                      Loss.lean → GradientDescent.lean
                                        ↓
                               DifferentialSKYDemoMain.lean
```

## Key Namespaces

- `HeytingLean.LoF.HoTT` — Identity type infrastructure
- `HeytingLean.LoF.Comb` — SKY combinator syntax
- `HeytingLean.LoF.Combinators.Differential` — DiLL semantics
- `HeytingLean.LoF.Combinators.Differential.Compute` — Runtime backend

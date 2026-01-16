# Proof Index

## Core Theorems

### Identity (HoTT Foundation)

| Name | Type | File:Line |
|------|------|-----------|
| `Id.refl` | `Id x x` | `Identity.lean:50` |
| `Id.symm` | `Id x y → Id y x` | `Identity.lean:53` |
| `Id.trans` | `Id x y → Id y z → Id x z` | `Identity.lean:58` |

### SKY Combinators

| Name | Type | File:Line |
|------|------|-----------|
| `K_normal` | `Normal Comb.K` | `SKY.lean:55` |
| `S_normal` | `Normal Comb.S` | `SKY.lean:60` |
| `Y_normal` | `Normal Comb.Y` | `SKY.lean:65` |
| `I_reduces` | `Steps (Comb.app I t) t` | `SKY.lean:101` |

### Multiway System

| Name | Type | File:Line |
|------|------|-----------|
| `rootStep?_sound` | step from rootStep? is valid | `SKYMultiway.lean:63` |
| `stepEdgesList_sound` | enumerated edges are Steps | `SKYMultiway.lean:146` |
| `stepEdges_complete` | all Steps are enumerated | `SKYMultiway.lean:286` |

### Differential Layer

| Name | Type | File:Line |
|------|------|-----------|
| `app_single_single` | basis · basis = basis | `LinearComb.lean:37` |
| `chainRule` | composition derivative rule | `Derivative.lean:101` |
| `codereliction_linear_increment` | DiLL codereliction | `Exponential.lean:40` |
| `codereliction_is_derivative` | codereliction = derivative | `Codereliction.lean:50` |
| `nucleusLinear_idempotent` | nucleus preserves idempotence | `NucleusDifferential.lean:32` |

## Key Definitions

### Types

| Name | Definition | File:Line |
|------|------------|-----------|
| `Comb` | inductive K \| S \| Y \| app | `SKY.lean:16` |
| `Step` | one-step reduction | `SKY.lean:27` |
| `FormalSum K` | `Comb →₀ K` | `VectorSpace.lean` |
| `Dual V` | structure {base, tangent} | `Derivative.lean:29` |
| `Exp V` | `ℕ →₀ V` (bang modality) | `Exponential.lean:26` |
| `IOExample` | input/expected pair | `Loss.lean:31` |
| `GDConfig` | gradient descent config | `GradientDescent.lean:26` |
| `GDState` | optimization state | `GradientDescent.lean:32` |

### Functions

| Name | Signature | File:Line |
|------|-----------|-----------|
| `FormalSum.app` | bilinear application | `LinearComb.lean:31` |
| `FormalSum.stepSum` | superposition of successors | `LinearComb.lean:62` |
| `dualApp` | dual-number application | `Derivative.lean:61` |
| `S_derivative` | Jacobian of S combinator | `Derivative.lean:81` |
| `totalLoss` | loss with regularization | `Loss.lean:52` |
| `totalGrad` | coordinate gradient | `Loss.lean:77` |
| `gradientDescentLoop` | optimization loop | `GradientDescent.lean:66` |
| `synthesize` | full synthesis pipeline | `GradientDescent.lean:81` |

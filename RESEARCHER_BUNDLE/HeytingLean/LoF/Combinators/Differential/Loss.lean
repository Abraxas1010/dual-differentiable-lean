import HeytingLean.LoF.Combinators.Differential.LinearComb
import HeytingLean.LoF.Combinators.Differential.Compute

/-!
# Differential combinators: loss functions (coordinate gradients)

The DiLL inspiration treats proofs/terms as “vectorized” objects and differentiates through their
combinator structure. For a runnable synthesis loop we additionally need a *computable* loss and
gradient. In this codebase we provide:

* Library layer (`FormalSum K`): noncomputable coordinate gradients parameterized by a finite basis.
* Runtime layer (`Compute.FSum`): fully computable `Rat` coordinate gradients used by executables.

The coordinate-gradient approach matches the demo in `HeytingLean.CLI.DifferentialSKYDemoMain`:
we only learn coefficients for a fixed list of “parameter terms” (a finite basis).
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

/-! ## Library layer: `FormalSum` losses -/

namespace Loss

structure IOExample (K : Type*) [Zero K] where
  input : FormalSum K
  expected : FormalSum K

section FormalSumLoss

variable {K : Type*} [CommRing K]

def error (w : FormalSum K) (ex : IOExample K) : FormalSum K :=
  FormalSum.app (K := K) w ex.input - ex.expected

def singleIOLoss (w : FormalSum K) (ex : IOExample K) : K :=
  FormalSum.l2NormSq (K := K) (error (K := K) w ex)

def ioLoss (w : FormalSum K) (examples : List (IOExample K)) : K :=
  examples.foldl (fun acc ex => acc + singleIOLoss (K := K) w ex) 0

/-- L2 regularization (squared norm). -/
def l2Reg (w : FormalSum K) : K :=
  FormalSum.l2NormSq (K := K) w

def totalLoss (regularization : K) (w : FormalSum K) (examples : List (IOExample K)) : K :=
  ioLoss (K := K) w examples + regularization * l2Reg (K := K) w

/-- Coordinate gradient of `singleIOLoss` over a finite list of basis terms. -/
def ioLossCoordGrad (params : List LoF.Comb) (w : FormalSum K) (ex : IOExample K) : FormalSum K :=
  let err := error (K := K) w ex
  params.foldl
    (fun g t =>
      let phi := FormalSum.app (K := K) (single (K := K) t) ex.input
      let gc : K := (2 : K) * FormalSum.dot (K := K) err phi
      g + gc • single (K := K) t)
    0

def ioLossCoordGradDataset (params : List LoF.Comb) (w : FormalSum K) (examples : List (IOExample K)) :
    FormalSum K :=
  examples.foldl (fun g ex => g + ioLossCoordGrad (K := K) params w ex) 0

/-!
`ioLossGradient` is a convenience wrapper: it chooses the current support as the coordinate basis.
This is not a “true” Fréchet gradient on an infinite-dimensional space; it is the most convenient
noncomputable finite approximation compatible with the rest of this file.
-/
def ioLossGradient (w : FormalSum K) (examples : List (IOExample K)) : FormalSum K :=
  ioLossCoordGradDataset (K := K) (w.support.toList) w examples

def totalGrad (params : List LoF.Comb) (regularization : K) (w : FormalSum K) (examples : List (IOExample K)) :
    FormalSum K :=
  ioLossCoordGradDataset (K := K) params w examples + ((2 : K) * regularization) • w

/-! ### Optional extensions (placeholders for the aspirational spec) -/

/-- A placeholder “type loss” hook: currently zero (no type constraints enforced here). -/
def typeLoss (_w _targetType : FormalSum K) : K :=
  0

/-- A simple complexity proxy: L2 regularization. -/
def complexityLoss (w : FormalSum K) : K :=
  l2Reg (K := K) w

end FormalSumLoss

end Loss

/-! ## Runtime layer: `Compute.FSum` losses -/

namespace Compute

open HeytingLean.LoF.Combinators.Differential.Compute

structure IOExample where
  input : FSum
  expected : FSum

def error (w : FSum) (ex : IOExample) : FSum :=
  sub (app w ex.input) ex.expected

def singleIOLoss (w : FSum) (ex : IOExample) : Rat :=
  l2NormSq (error w ex)

def ioLoss (w : FSum) (examples : List IOExample) : Rat :=
  examples.foldl (fun acc ex => acc + singleIOLoss w ex) 0

def l2Reg (w : FSum) : Rat :=
  l2NormSq w

def totalLoss (regularization : Rat) (w : FSum) (examples : List IOExample) : Rat :=
  ioLoss w examples + regularization * l2Reg w

/-- Coordinate gradient of `singleIOLoss` over a finite list of basis terms. -/
def ioLossCoordGrad (params : List Comb) (w : FSum) (ex : IOExample) : FSum :=
  let err := error w ex
  params.foldl
    (fun g t =>
      let phi := app (single t) ex.input
      let gc := (2 : Rat) * dot err phi
      add g (single t gc))
    []

def ioLossCoordGradDataset (params : List Comb) (w : FSum) (examples : List IOExample) : FSum :=
  examples.foldl (fun g ex => add g (ioLossCoordGrad params w ex)) []

def paramsOfWeights (w : FSum) : List Comb :=
  (w.map (fun tc => tc.1)).eraseDups

def ioLossGradient (w : FSum) (examples : List IOExample) : FSum :=
  ioLossCoordGradDataset (paramsOfWeights w) w examples

def totalGrad (params : List Comb) (regularization : Rat) (w : FSum) (examples : List IOExample) : FSum :=
  add (ioLossCoordGradDataset params w examples) (smul ((2 : Rat) * regularization) w)

/-- A placeholder “type loss” hook: currently zero (no type constraints enforced here). -/
def typeLoss (_w _targetType : FSum) : Rat :=
  0

/-- A simple complexity proxy: L2 regularization. -/
def complexityLoss (w : FSum) : Rat :=
  l2Reg w

end Compute

end Differential
end Combinators
end LoF
end HeytingLean

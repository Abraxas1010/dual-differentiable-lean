import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LSum
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.Combinators.Differential.VectorSpace

/-!
# Differential combinators: linear extension of application and stepping

This file provides:
- `app`      : bilinear extension of `Comb.app` to formal sums.
- `appBilin` : the same operation bundled as a bilinear `LinearMap`.
- `stepSum`  : formal superposition of one-step successors, via `Comb.stepEdgesList`.
- `steps`    : linear extension of `stepSum` to formal sums.
- bounded iterates / reachability operators (useful as a runtime approximation).
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

namespace FormalSum

variable {K : Type*} [Semiring K]

/-- Bilinear extension of syntactic application: distribute over formal sums. -/
def app (v w : FormalSum K) : FormalSum K :=
  v.sum (fun t a => w.sum (fun u b => Finsupp.single (LoF.Comb.app t u) (a * b)))

infixl:70 " ⬝ " => app

@[simp]
theorem app_single_single (t u : LoF.Comb) :
    (single (K := K) t) ⬝ (single (K := K) u) = single (K := K) (LoF.Comb.app t u) := by
  classical
  simp [app, single, Finsupp.sum_single_index]

end FormalSum

namespace FormalSum

variable {K : Type*} [CommSemiring K]

noncomputable def appRight (t : LoF.Comb) : FormalSum K →ₗ[K] FormalSum K :=
  Finsupp.lsum K (fun u => (Finsupp.lsingle (LoF.Comb.app t u) : K →ₗ[K] FormalSum K))

noncomputable def appBilin : FormalSum K →ₗ[K] FormalSum K →ₗ[K] FormalSum K :=
  Finsupp.lsum K (fun t =>
    ((LinearMap.lsmul K (FormalSum K →ₗ[K] FormalSum K)).flip (appRight (K := K) t)))

end FormalSum

namespace FormalSum

variable {K : Type*} [Semiring K]

/-- Formal sum of one-step successors of a term, with coefficient `1` for each enumerated edge. -/
def stepSum (t : LoF.Comb) : FormalSum K :=
  (LoF.Comb.stepEdgesList t).foldl (fun acc e => acc + Finsupp.single e.2 1) 0

/-- Linear extension of one-step reduction to formal sums. -/
def steps (v : FormalSum K) : FormalSum K :=
  v.sum (fun t a => a • stepSum (K := K) t)

def stepsIter : Nat → FormalSum K → FormalSum K
  | 0, v => v
  | Nat.succ n, v => steps (K := K) (stepsIter n v)

def reachabilityBounded (fuel : Nat) (v : FormalSum K) : FormalSum K :=
  (Finset.range (fuel + 1)).sum (fun n => stepsIter (K := K) n v)

end FormalSum

end Differential
end Combinators
end LoF
end HeytingLean

import HeytingLean.LoF.Combinators.SKYMultiway

/-!
# Differential combinators: small computable “formal sum” backend (Rat coefficients)

Mathlib's `Finsupp` API is extremely convenient for *library* work, but many constructors are
noncomputable because they avoid requiring decidable equality on coefficients.

For executables we provide a tiny, fully computable backend:

`FSum := List (Comb × Rat)`

with normalization-by-insertion to combine like terms and drop zero coefficients. This is meant
only for demos and runtime sanity checks.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential
namespace Compute

open HeytingLean.LoF

abbrev FSum := List (Comb × Rat)

def addTerm (t : Comb) (c : Rat) : FSum → FSum
  | [] =>
      if c = 0 then [] else [(t, c)]
  | (t', c') :: rest =>
      if t' = t then
        let c'' := c' + c
        if c'' = 0 then rest else (t, c'') :: rest
      else
        (t', c') :: addTerm t c rest

def normalize (v : FSum) : FSum :=
  v.foldl (fun acc tc => addTerm tc.1 tc.2 acc) []

def add (a b : FSum) : FSum :=
  b.foldl (fun acc tc => addTerm tc.1 tc.2 acc) a

def neg (v : FSum) : FSum :=
  v.map (fun tc => (tc.1, -tc.2))

def sub (a b : FSum) : FSum :=
  add a (neg b)

def smul (r : Rat) (v : FSum) : FSum :=
  normalize <| v.map (fun tc => (tc.1, r * tc.2))

def coeff (t : Comb) : FSum → Rat
  | [] => 0
  | (t', c) :: rest => if t' = t then c else coeff t rest

def dot (a b : FSum) : Rat :=
  a.foldl (fun acc tc => acc + tc.2 * coeff tc.1 b) 0

def l2NormSq (v : FSum) : Rat :=
  dot v v

def single (t : Comb) (c : Rat := 1) : FSum :=
  if c = 0 then [] else [(t, c)]

def app (f x : FSum) : FSum :=
  f.foldl
    (fun acc tc =>
      x.foldl
        (fun acc' uc => addTerm (Comb.app tc.1 uc.1) (tc.2 * uc.2) acc')
        acc)
    []

def stepSum (t : Comb) : FSum :=
  (Comb.stepEdgesList t).foldl (fun acc e => addTerm e.2 1 acc) []

def steps (v : FSum) : FSum :=
  v.foldl (fun acc tc => add acc (smul tc.2 (stepSum tc.1))) []

def stepsIter : Nat → FSum → FSum
  | 0, v => v
  | Nat.succ n, v => steps (stepsIter n v)

def reachabilityBounded (fuel : Nat) (v : FSum) : FSum :=
  (List.range (fuel + 1)).foldl (fun acc n => add acc (stepsIter n v)) []

def showFSum (v : FSum) : String :=
  let parts :=
    v.map (fun tc =>
      let tStr := reprStr tc.1
      let cStr := toString tc.2
      s!"({cStr})·{tStr}")
  "[" ++ String.intercalate ", " parts ++ "]"

end Compute
end Differential
end Combinators
end LoF
end HeytingLean

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The interaction distribution of the tri-molecular CRN

An *interaction event* of the CRN `Tri` draws an unordered triple of the `n`
molecules uniformly at random. Such a triple has one of exactly four
compositions, recorded by `TripleKind`, and the number of triples of each
composition is given by `TripleKind.weight`.

The resulting distribution `interactionPMF` is a genuine `PMF` precisely because
of `Tri.choose_three_split`, proved in `Tri.Basic` — the four composition counts
sum to `C(n,3)`. That is the whole content of the normalization obligation, and
it is discharged here once.

Two of the four compositions are *productive*: `xxy` triggers reaction (1)
(`X+X+Y → X+X+X`, so `y` decreases by one) and `xyy` triggers reaction (2)
(`X+Y+Y → Y+Y+Y`, so `y` increases by one). The homogeneous compositions `xxx`
and `yyy` leave the configuration unchanged. `TripleKind.delta` records this as
the change in the count of `X`.

## Main definitions

* `TripleKind` — the four compositions of an unordered triple.
* `TripleKind.weight x y` — how many triples have each composition.
* `interactionPMF` — the uniform-triple distribution over compositions.
* `TripleKind.delta` — the change in the `X`-count caused by a composition.

## Main results

* `sum_weight` — the four weights sum to `C(x+y,3)` (restatement of
  `choose_three_split` in the form the `PMF` constructor needs).
* `interactionPMF_apply` — the mass of each composition.
* `productive_weight` — the combined weight of the two productive compositions,
  in the subtraction-free form supplied by `Tri.productive_two_mul`.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Figure 1 and Section 2.1.
-/

namespace Tri

open scoped ENNReal

/-- The four possible compositions of an unordered triple drawn from a mixture
of species `X` and `Y`. `xxy` triggers reaction (1) and `xyy` triggers
reaction (2); `xxx` and `yyy` are unproductive. -/
inductive TripleKind
  | xxx
  | xxy
  | xyy
  | yyy
  deriving DecidableEq, Fintype, Repr

namespace TripleKind

/-- The number of unordered triples of each composition, in a mixture with `x`
molecules of `X` and `y` of `Y`. -/
def weight (x y : ℕ) : TripleKind → ℕ
  | .xxx => Nat.choose x 3
  | .xxy => Nat.choose x 2 * y
  | .xyy => x * Nat.choose y 2
  | .yyy => Nat.choose y 3

/-- The change in the count of `X` caused by a triple of the given composition.
Reaction (1) converts one `Y` into an `X`; reaction (2) converts one `X` into a
`Y`; homogeneous triples change nothing. -/
def delta : TripleKind → ℤ
  | .xxx => 0
  | .xxy => 1
  | .xyy => -1
  | .yyy => 0

/-- A composition is *productive* when it triggers one of the two reactions. -/
def IsProductive : TripleKind → Prop
  | .xxx => False
  | .xxy => True
  | .xyy => True
  | .yyy => False

instance : DecidablePred IsProductive := by
  intro k; cases k <;> unfold IsProductive <;> infer_instance

@[simp] theorem delta_xxx : delta .xxx = 0 := rfl
@[simp] theorem delta_xxy : delta .xxy = 1 := rfl
@[simp] theorem delta_xyy : delta .xyy = -1 := rfl
@[simp] theorem delta_yyy : delta .yyy = 0 := rfl

/-- A composition changes the configuration exactly when it is productive. -/
theorem delta_ne_zero_iff (k : TripleKind) : k.delta ≠ 0 ↔ k.IsProductive := by
  cases k <;> simp [delta, IsProductive]

end TripleKind

/-- The four composition counts sum to the total number of unordered triples.
This is `Tri.choose_three_split`, arranged as the normalization hypothesis
required by `PMF.ofFintype`. -/
theorem sum_weight (x y : ℕ) :
    ∑ k : TripleKind, TripleKind.weight x y k = Nat.choose (x + y) 3 := by
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  simp [TripleKind.weight, choose_three_split]
  ring

/-- The combined weight of the two productive compositions, in subtraction-free
form. Together with `sum_weight` this is what yields the closed form
`q = 3xy/(n(n-1))` for the probability that an interaction event is
productive. -/
theorem productive_weight (x y : ℕ) :
    2 * (TripleKind.weight x y .xxy + TripleKind.weight x y .xyy) + 2 * (x * y)
      = x * y * (x + y) :=
  productive_two_mul x y

/-- The distribution of the composition of a uniformly drawn unordered triple,
in a mixture of `x` molecules of `X` and `y` of `Y` with `3 ≤ x + y`. -/
noncomputable def interactionPMF (x y : ℕ) (h : 3 ≤ x + y) : PMF TripleKind :=
  PMF.ofFintype
    (fun k => (TripleKind.weight x y k : ℝ≥0∞) / (Nat.choose (x + y) 3 : ℝ≥0∞))
    (by
      have hpos : 0 < Nat.choose (x + y) 3 := choose_three_pos h
      have hne : ((Nat.choose (x + y) 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop : ((Nat.choose (x + y) 3 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [show ∑ k : TripleKind, ((TripleKind.weight x y k : ℕ) : ℝ≥0∞)
            = ((∑ k : TripleKind, TripleKind.weight x y k : ℕ) : ℝ≥0∞) by push_cast; rfl]
      rw [sum_weight, ← div_eq_mul_inv]
      exact ENNReal.div_self hne htop)

@[simp] theorem interactionPMF_apply (x y : ℕ) (h : 3 ≤ x + y) (k : TripleKind) :
    interactionPMF x y h k
      = (TripleKind.weight x y k : ℝ≥0∞) / (Nat.choose (x + y) 3 : ℝ≥0∞) :=
  rfl

section Sanity

/-! Guards: the weights must be the composition counts, not a mis-transcription. -/

example : TripleKind.weight 5 4 .xxy = Nat.choose 5 2 * 4 := rfl
example : TripleKind.weight 5 4 .xyy = 5 * Nat.choose 4 2 := rfl
example : ∑ k : TripleKind, TripleKind.weight 5 4 k = Nat.choose 9 3 := by decide

/-- At consensus every triple is homogeneous, so nothing is productive. -/
example : TripleKind.weight 9 0 .xxy = 0 ∧ TripleKind.weight 9 0 .xyy = 0 := by
  constructor <;> rfl

end Sanity

end Tri

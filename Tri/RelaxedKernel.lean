/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Step

/-!
# The unequal-rate interaction kernel (Theorem 3)

The rate of `X + X + Y → X + X + X` is `α ≤ 1`; the reverse-direction
reaction keeps rate one.  A sampled `xxy` triple therefore has two distinct
outcomes: the reaction fires with mass `α`, or the interaction is a self-loop
with mass `1 - α`.  Keeping that latter outcome explicit is essential: the raw
interaction chain is not the productive-reaction chain.
-/

namespace Tri

open scoped ENNReal

/-- A physical rate in the normalization used by the paper.

The firing and idle weights are carried separately.  This keeps truncated
subtraction out of the model and makes their sum-to-one law an explicit
invariant. -/
structure RelaxedRate where
  fire : NNReal
  idle : NNReal
  add_eq_one : fire + idle = 1

/-- The five outcomes of one unequal-rate unordered triple interaction. -/
inductive RelaxedTripleKind
  | xxx
  | xxyFire
  | xxyIdle
  | xyyFire
  | yyy
  deriving DecidableEq, Fintype, Repr

namespace RelaxedTripleKind

/-- Unnormalized mass of an unequal-rate interaction outcome. -/
noncomputable def weight (r : RelaxedRate) (x y : ℕ) :
  RelaxedTripleKind → ℝ≥0∞
  | .xxx => Nat.choose x 3
  | .xxyFire => (r.fire : ℝ≥0∞) * (Nat.choose x 2 * y : ℕ)
  | .xxyIdle => (r.idle : ℝ≥0∞) * (Nat.choose x 2 * y : ℕ)
  | .xyyFire => x * Nat.choose y 2
  | .yyy => Nat.choose y 3

/-- The resulting `X` count.  The idle `xxy` outcome is a genuine self-loop. -/
def nextX (x : ℕ) : RelaxedTripleKind → ℕ
  | .xxx | .xxyIdle | .yyy => x
  | .xxyFire => x + 1
  | .xyyFire => x - 1

end RelaxedTripleKind

/-- Splitting `xxy` into firing and idle outcomes preserves the total triple
mass. -/
theorem relaxed_sum_weight (r : RelaxedRate) (x y : ℕ) :
    ∑ k : RelaxedTripleKind, k.weight r x y =
      (Nat.choose (x + y) 3 : ℝ≥0∞) := by
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  simp [RelaxedTripleKind.weight]
  have hsplit : (r.fire : ℝ≥0∞) + (r.idle : ℝ≥0∞) = 1 := by
    exact_mod_cast r.add_eq_one
  calc
    (Nat.choose x 3 : ℝ≥0∞) +
          ((r.fire : ℝ≥0∞) * (((Nat.choose x 2 : ℕ) : ℝ≥0∞) * y) +
          ((r.idle : ℝ≥0∞) * (((Nat.choose x 2 : ℕ) : ℝ≥0∞) * y) +
          ((x : ℝ≥0∞) * Nat.choose y 2 + Nat.choose y 3)))
      = (Nat.choose x 3 : ℝ≥0∞) +
          (((r.fire : ℝ≥0∞) + (r.idle : ℝ≥0∞)) *
              (((Nat.choose x 2 : ℕ) : ℝ≥0∞) * y) +
          ((x : ℝ≥0∞) * Nat.choose y 2 + Nat.choose y 3)) := by ring
    _ = (Nat.choose x 3 : ℝ≥0∞) +
          (((Nat.choose x 2 : ℕ) : ℝ≥0∞) * y +
          ((x : ℝ≥0∞) * Nat.choose y 2 + Nat.choose y 3)) := by
          rw [hsplit, one_mul]
    _ = (Nat.choose (x + y) 3 : ℝ≥0∞) := by
          have hnat :
              Nat.choose x 3 +
                  (Nat.choose x 2 * y + (x * Nat.choose y 2 + Nat.choose y 3)) =
                Nat.choose (x + y) 3 := by
            simpa [Nat.add_assoc] using (choose_three_split x y).symm
          exact_mod_cast hnat

/-- The normalized five-outcome interaction distribution. -/
noncomputable def relaxedInteractionPMF
    (r : RelaxedRate) (x y : ℕ) (h : 3 ≤ x + y) :
    PMF RelaxedTripleKind :=
  PMF.ofFintype
    (fun k => k.weight r x y / (Nat.choose (x + y) 3 : ℝ≥0∞))
    (by
      have hpos : 0 < Nat.choose (x + y) 3 := choose_three_pos h
      have hne : ((Nat.choose (x + y) 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop : ((Nat.choose (x + y) 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [relaxed_sum_weight, ← div_eq_mul_inv]
      exact ENNReal.div_self hne htop)

@[simp] theorem relaxedInteractionPMF_apply
    (r : RelaxedRate) (x y : ℕ) (h : 3 ≤ x + y)
    (k : RelaxedTripleKind) :
    relaxedInteractionPMF r x y h k =
      k.weight r x y / (Nat.choose (x + y) 3 : ℝ≥0∞) :=
  rfl

/-- One unequal-rate interaction, represented by the resulting `X` count. -/
noncomputable def relaxedTriStep
    (r : RelaxedRate) (x y : ℕ) (h : 3 ≤ x + y) : PMF ℕ :=
  (relaxedInteractionPMF r x y h).map (RelaxedTripleKind.nextX x)

end Tri

#print axioms Tri.relaxed_sum_weight

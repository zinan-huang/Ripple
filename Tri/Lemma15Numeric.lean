/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Window

/-!
# Lemma 15's scalar endgame: optimising `λ` against the telescope

`urn_window_ville_exp` leaves the bound as

```text
ofReal (exp (λ²/8 · urnA (ν−1) − (|λ| δ + λ²/8 · urnA u)))
```

Everything remaining is scalar. Two steps:

1. **Carry the variance increment as a budget.** The exponent needs
   `urnA (ν−1) − urnA u`, which is a subtraction and so cannot appear in a
   statement. Carry a budget `A` with the hypothesis

   ```text
   urnA (ν−1) ≤ A + urnA u
   ```

   The orientation matters: this says the ACTUAL increment is at most `A`,
   which is what an upper-tail bound needs. The reverse would be useless.

2. **Optimise.** At `λ = 4δ/A` the exponent is exactly `−2δ²/A`.

The budget itself comes from `urnA_add_tail_antitone`, the telescope already
proved for Lemma 14. Parametrising the window by `u + k + 1 = ν` — `u+1` is
the pool remaining at the window's end, `k` the number of reveals in it — the
telescope gives

```text
A = 2k / ((u+1) · ν)
```

and the optimised exponent becomes `−δ² · ν · (u+1) / k`, which is the shape
Lemma 16 consumes.
-/

open scoped ENNReal

namespace Tri

/-- **The telescope, in budget form.**  The variance increment across a window
of `k` reveals ending with `u+1` in the pool is at most `2k/((u+1)ν)`.

Stated subtraction-free by putting `urnA u` on the right. -/
theorem urn_telescope_budget (u k R B : ℕ) (hν : u + k + 1 = R + B) :
    urnA (R + B - 1)
      ≤ 2 * (k : ℝ) / (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ))) + urnA u := by
  have hle : u ≤ R + B - 1 := by omega
  have htel := urnA_add_tail_antitone hle
  -- `((R+B-1 : ℕ) : ℝ) + 1 = (R:ℝ) + (B:ℝ)`, since `1 ≤ R + B`
  have hcast : ((R + B - 1 : ℕ) : ℝ) + 1 = (R : ℝ) + (B : ℝ) := by
    have h1 : 1 ≤ R + B := by omega
    have : ((R + B - 1 : ℕ) : ℝ) = ((R : ℝ) + (B : ℝ)) - 1 := by
      have : (R + B - 1 : ℕ) + 1 = R + B := by omega
      have hc : (((R + B - 1 : ℕ) + 1 : ℕ) : ℝ) = ((R + B : ℕ) : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
      push_cast at hc
      linarith
    rw [this]; ring
  rw [hcast] at htel
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hRB : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    have : 1 ≤ R + B := by omega
    have : (1 : ℝ) ≤ (R : ℝ) + (B : ℝ) := by exact_mod_cast this
    linarith
  -- `2/(u+1) − 2/ν = 2k/((u+1)ν)` given `u + k + 1 = ν`
  have hk : (R : ℝ) + (B : ℝ) = (u : ℝ) + (k : ℝ) + 1 := by
    have : ((u + k + 1 : ℕ) : ℝ) = ((R + B : ℕ) : ℝ) :=
      congrArg (Nat.cast : ℕ → ℝ) hν
    push_cast at this
    linarith
  have hsplit : 2 * (k : ℝ) / (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ)))
      = 2 / ((u : ℝ) + 1) - 2 / ((R : ℝ) + (B : ℝ)) := by
    field_simp
    rw [hk]; ring
  rw [hsplit]
  linarith

/-- **The optimised exponent.**  With the variance increment bounded by `A`
and the tilt taken at `λ = 4δ/A`, the Ville exponent is at most `−2δ²/A`.

This is a pure real inequality; the `ENNReal` layer is peeled by the caller. -/
theorem urn_exponent_optimised (δ A : ℝ) (u ν : ℕ)
    (hA : 0 < A) (hδ : 0 ≤ δ)
    (hbudget : urnA ν ≤ A + urnA u) :
    (4 * δ / A) ^ 2 / 8 * urnA ν
        - (|4 * δ / A| * δ + (4 * δ / A) ^ 2 / 8 * urnA u)
      ≤ -(2 * δ ^ 2 / A) := by
  set lam : ℝ := 4 * δ / A with hlam
  have hlam0 : 0 ≤ lam := by
    rw [hlam]; positivity
  have habs : |lam| = lam := abs_of_nonneg hlam0
  have hcoef : 0 ≤ lam ^ 2 / 8 := by positivity
  -- the variance part is at most `lam²/8 · A`
  have hvar : lam ^ 2 / 8 * urnA ν - lam ^ 2 / 8 * urnA u ≤ lam ^ 2 / 8 * A := by
    have : lam ^ 2 / 8 * urnA ν ≤ lam ^ 2 / 8 * (A + urnA u) :=
      mul_le_mul_of_nonneg_left hbudget hcoef
    nlinarith [this]
  -- and `lam²/8 · A − lam·δ = −2δ²/A` exactly
  have hexact : lam ^ 2 / 8 * A - lam * δ = -(2 * δ ^ 2 / A) := by
    rw [hlam]
    field_simp
    ring
  rw [habs]
  nlinarith [hvar, hexact]

/-- The same optimized exponent with the negative tilt, used when the adverse
colour is the second urn coordinate. -/
theorem urn_exponent_optimised_neg (δ A : ℝ) (u ν : ℕ)
    (hA : 0 < A) (hδ : 0 ≤ δ)
    (hbudget : urnA ν ≤ A + urnA u) :
    (- (4 * δ / A)) ^ 2 / 8 * urnA ν
        - (|- (4 * δ / A)| * δ +
          (- (4 * δ / A)) ^ 2 / 8 * urnA u)
      ≤ -(2 * δ ^ 2 / A) := by
  have hsq :
      (- (4 * δ / A)) ^ 2 = (4 * δ / A) ^ 2 := by
    ring
  rw [hsq, abs_neg]
  exact urn_exponent_optimised δ A u ν hA hδ hbudget

/-- **Lemma 15's windowed tail, optimised.**

The maximal deviation bound over every prefix of a window, at the optimal
tilt, with the budget carried subtraction-free.  This is the statement the
Lemma 16 assembly consumes. -/
theorem urn_window_tail (δ A : ℝ) (u R B : ℕ)
    (hA : 0 < A) (hδ : 0 ≤ δ)
    (hbudget : urnA (R + B - 1) ≤ A + urnA u) :
    ⨆ T : ℕ,
        hitProb (UrnWindowBad ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ (4 * δ / A) u)
          urnStopped T (R, B)
      ≤ ENNReal.ofReal (Real.exp (-(2 * δ ^ 2 / A))) := by
  refine le_trans (urn_window_ville_exp δ (4 * δ / A) u R B) ?_
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (urn_exponent_optimised δ A u (R + B - 1) hA hδ hbudget))

/-- Optimized maximal window tail with the negative tilt. -/
theorem urn_window_tail_neg (δ A : ℝ) (u R B : ℕ)
    (hA : 0 < A) (hδ : 0 ≤ δ)
    (hbudget : urnA (R + B - 1) ≤ A + urnA u) :
    ⨆ T : ℕ,
        hitProb
          (UrnWindowBad
            ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
            δ (- (4 * δ / A)) u)
          urnStopped T (R, B)
      ≤ ENNReal.ofReal (Real.exp (-(2 * δ ^ 2 / A))) := by
  refine le_trans
    (urn_window_ville_exp δ (- (4 * δ / A)) u R B) ?_
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr
      (urn_exponent_optimised_neg
        δ A u (R + B - 1) hA hδ hbudget))

/-- **The two combined**: the tail at the telescope's own budget, in terms of
the window's length `k` and the pool sizes.

The exponent is `−δ² ν (u+1) / k`, which is what the paper's parameters get
substituted into. -/
theorem urn_window_tail_telescope (δ : ℝ) (u k R B : ℕ)
    (hδ : 0 ≤ δ) (hν : u + k + 1 = R + B) (hk : 0 < k) :
    ⨆ T : ℕ,
        hitProb
          (UrnWindowBad ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ
            (4 * δ / (2 * (k : ℝ) / (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ))))) u)
          urnStopped T (R, B)
      ≤ ENNReal.ofReal (Real.exp
          (-(2 * δ ^ 2
              / (2 * (k : ℝ) / (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ))))))) := by
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hRB : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    have h1 : 1 ≤ R + B := by omega
    have : (1 : ℝ) ≤ (R : ℝ) + (B : ℝ) := by exact_mod_cast h1
    linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hA : 0 < 2 * (k : ℝ) / (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ))) := by
    positivity
  exact urn_window_tail δ _ u R B hA hδ (urn_telescope_budget u k R B hν)

/-- Telescope form of the negative-tilt maximal tail. -/
theorem urn_window_tail_telescope_neg
    (δ : ℝ) (u k R B : ℕ)
    (hδ : 0 ≤ δ) (hν : u + k + 1 = R + B)
    (hk : 0 < k) :
    ⨆ T : ℕ,
        hitProb
          (UrnWindowBad
            ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
            δ
            (- (4 * δ /
              (2 * (k : ℝ) /
                (((u : ℝ) + 1) *
                  ((R : ℝ) + (B : ℝ)))))) u)
          urnStopped T (R, B)
      ≤ ENNReal.ofReal (Real.exp
          (-(2 * δ ^ 2
              / (2 * (k : ℝ) /
                (((u : ℝ) + 1) *
                  ((R : ℝ) + (B : ℝ))))))) := by
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hRB : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    have h1 : 1 ≤ R + B := by omega
    have : (1 : ℝ) ≤ (R : ℝ) + (B : ℝ) := by
      exact_mod_cast h1
    linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hA :
      0 < 2 * (k : ℝ) /
        (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ))) := by
    positivity
  exact urn_window_tail_neg δ _ u R B hA hδ
    (urn_telescope_budget u k R B hν)

end Tri

#print axioms Tri.urn_telescope_budget
#print axioms Tri.urn_exponent_optimised
#print axioms Tri.urn_exponent_optimised_neg
#print axioms Tri.urn_window_tail
#print axioms Tri.urn_window_tail_neg
#print axioms Tri.urn_window_tail_telescope
#print axioms Tri.urn_window_tail_telescope_neg

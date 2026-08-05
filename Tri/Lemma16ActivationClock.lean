/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationBudget
import Tri.Lemma16Exponent

/-!
# Lemma 16's epidemic deadline

The existing budgeted early-activation ladder already supplies the epidemic
clock needed by Lemma 16.  Running its dyadic rungs from one active molecule
with confidence budget `2q` costs at most `640 q n` raw interactions and has
failure at most `exp (-q)`.

The checkpoint is `a ≤ active`, rather than exact equality: one raw
interaction can activate two molecules.
-/

namespace Tri

open scoped ENNReal

/-- Number of dyadic early-activation rungs from one active molecule. -/
noncomputable def lemma16ActivationStages (n : ℕ) : ℕ :=
  infectionEarlyStages n 1 (by omega)

/-- Exact heterogeneous horizon of Lemma 16's budgeted activation ladder. -/
noncomputable def lemma16ActivationHorizon
    (n q : ℕ) : ℕ :=
  infectionEarlyBudgetHorizon n 1 (2 * q)
    (lemma16ActivationStages n)

/-- Exact union-bound error of Lemma 16's budgeted activation ladder. -/
noncomputable def lemma16ActivationExactError
    (n q : ℕ) : ℝ≥0∞ :=
  infectionEarlyBudgetError (2 * q)
    (lemma16ActivationStages n)

/-- The exact budgeted ladder reaches every threshold in the first quarter. -/
theorem infectionActivation_one_to_threshold_exact
    (n q a : ℕ)
    (h3 : 3 ≤ n)
    (hquarter : 4 * a ≤ n) :
    Reaches
      (infectionStateStep n h3)
      (lemma16ActivationHorizon n q)
      (fun s : InfectionState n => 1 ≤ s.1.active)
      (fun s => a ≤ s.1.active)
      (lemma16ActivationExactError n q) := by
  let k := lemma16ActivationStages n
  have hvalid :
      ∀ j < k, 4 * infectionEarlyLevel 1 j ≤ n := by
    intro j hj
    exact infectionEarlyStages_valid n 1 (by omega) j
      (by simpa [k, lemma16ActivationStages] using hj)
  have hfinal :
      n ≤ 4 * infectionEarlyLevel 1 k := by
    simpa [k, lemma16ActivationStages] using
      infectionEarlyStages_quarter n 1 (by omega)
  have haLevel : a ≤ infectionEarlyLevel 1 k := by
    omega
  have hladder :=
    infectionActivation_early_budget_ladder
      n 1 (2 * q) k h3 (by omega) hvalid
  have htarget := hladder.mono_post
    (fun s hs => haLevel.trans hs)
  simpa [lemma16ActivationHorizon,
    lemma16ActivationExactError, k] using htarget

/-- The confidence-`2q` early ladder fits inside `640 q n` raw steps. -/
theorem lemma16ActivationHorizon_le
    (n q : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q) :
    lemma16ActivationHorizon n q ≤ 640 * q * n := by
  let k := lemma16ActivationStages n
  have hklog : k ≤ Nat.log 2 n := by
    simpa [k, lemma16ActivationStages] using
      infectionEarlyStages_le_log n 1 (by omega) (by omega)
  have hkq : k ≤ q := hklog.trans hlog
  calc
    lemma16ActivationHorizon n q
        ≤ 128 * n * (2 * (2 * q) + k) := by
          simpa [lemma16ActivationHorizon, k] using
            infectionEarlyBudgetHorizon_le n 1 (2 * q) k (by omega)
    _ ≤ 128 * n * (5 * q) := by
          exact Nat.mul_le_mul_left (128 * n) (by omega)
    _ = 640 * q * n := by ring

/-- Scalar absorption of the ladder's `k exp(-2q)` error into `exp(-q)`. -/
theorem early_ladder_real_error_le
    (k q : ℕ) (hkq : k ≤ q) :
    (k : ℝ) * Real.exp (-((2 * q : ℕ) : ℝ)) ≤
      Real.exp (-(q : ℝ)) := by
  have hkR : (k : ℝ) ≤ (q : ℝ) := by exact_mod_cast hkq
  have hqexp : (q : ℝ) ≤ Real.exp (q : ℝ) := by
    have h := Real.add_one_le_exp (q : ℝ)
    linarith
  calc
    (k : ℝ) * Real.exp (-((2 * q : ℕ) : ℝ))
        ≤ (q : ℝ) * Real.exp (-((2 * q : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hkR (Real.exp_nonneg _)
    _ ≤ Real.exp (q : ℝ) *
          Real.exp (-((2 * q : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hqexp (Real.exp_nonneg _)
    _ = Real.exp (-(q : ℝ)) := by
          rw [← Real.exp_add]
          push_cast
          congr 1
          ring

/-- The exact early-ladder union bound is at most Lemma 16's normalized
epidemic error. -/
theorem lemma16ActivationExactError_le
    (n q : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q) :
    lemma16ActivationExactError n q ≤
      lemma16EpidemicError q := by
  let k := lemma16ActivationStages n
  have hklog : k ≤ Nat.log 2 n := by
    simpa [k, lemma16ActivationStages] using
      infectionEarlyStages_le_log n 1 (by omega) (by omega)
  have hkq : k ≤ q := hklog.trans hlog
  unfold lemma16ActivationExactError
    infectionEarlyBudgetError infectionStageBudgetError
    lemma16EpidemicError
  rw [show (lemma16ActivationStages n : ℝ≥0∞) =
      ENNReal.ofReal (lemma16ActivationStages n : ℝ) by
    exact (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (early_ladder_real_error_le k q (by simpa [k] using hkq))

/-- Lemma 16's epidemic deadline from one active molecule.  The target is a
first-crossing inequality, so two-activation overshoot is handled exactly. -/
theorem infectionActivation_lemma16_deadline
    (n q a cStar : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter : 4 * a ≤ n)
    (hcStar : 640 ≤ cStar) :
    Reaches
      (infectionStateStep n h3)
      (cStar * q * n)
      (fun s : InfectionState n => 1 ≤ s.1.active)
      (fun s => a ≤ s.1.active)
      (lemma16EpidemicError q) := by
  have hexact :=
    infectionActivation_one_to_threshold_exact
      n q a h3 hquarter
  have hshort :
      lemma16ActivationHorizon n q ≤ 640 * q * n :=
    lemma16ActivationHorizon_le n q h3 hlog
  have hdeadline : 640 * q * n ≤ cStar * q * n := by
    have h := Nat.mul_le_mul_right (q * n) hcStar
    simpa [Nat.mul_assoc] using h
  have hpadded :=
    hexact.mono_horizon_of_closed
      (hshort.trans hdeadline)
      (fun s hs V z hz =>
        infectionStateStep_iter_target h3 s z hs hz)
  exact hpadded.mono_error
    (lemma16ActivationExactError_le n q h3 hlog)

end Tri

#print axioms Tri.infectionActivation_one_to_threshold_exact
#print axioms Tri.lemma16ActivationHorizon_le
#print axioms Tri.early_ladder_real_error_le
#print axioms Tri.lemma16ActivationExactError_le
#print axioms Tri.infectionActivation_lemma16_deadline

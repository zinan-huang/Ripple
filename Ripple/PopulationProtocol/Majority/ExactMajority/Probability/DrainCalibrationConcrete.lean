/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete drain calibration — calibrated horizon and per-level budget discharge

The honest drain slots (1/5/6/7/8 in `DrainEngine.lean`) carry the per-level budget hypothesis

  `hpt : ∀ m ∈ Finset.Icc 1 M₀, (qHat E n m) ^ (tWin m) ≤ (budgetNN M₀ n : ℝ≥0∞)`

This file provides the CONCRETE `tWin` that discharges it:

* `calibratedHorizon E n := ⌈3·n·(n−1)·log n / E⌉₊` — the uniform horizon across all levels.
* `levelRate_eq_ofReal` — bridge: `levelRate E n m = ENNReal.ofReal (1 − E/(n(n−1)))`.
* `levelRate_pow_le_budgetNN` — per-level budget at `levelRate` and calibrated horizon.
* `qHat_calibrated_hpt` — the ready-to-plug `hpt` at `tWin _ := calibratedHorizon E n`.

## Key insight

`levelRate E n m = 1 − ofReal(E/(n(n−1)))` is CONSTANT in `m`, so the horizon
`T ≥ (3/α)·(n/m)·log n` (from `rect_pow_le_budget`) simplifies — by choosing
`α := E/(m·(n−1))` at each level — to `T ≥ 3·n·(n−1)·log(n)/E`, independent of `m`.
Therefore `tWin` is a constant function.

## Proof route (per level `m ∈ Icc 1 M₀`)

1. Rewrite `qHat E n m` → `levelRate E n m` → `ENNReal.ofReal q_r` where `q_r = 1 − E/(n(n−1))`.
2. Set `α := E/(m·(n−1))`, giving `q_r ≤ 1 − α·m/n` (exact equality).
3. Apply `rect_pow_le_budget_enn` at `α`, `q_r`, `T = calibratedHorizon E n`.
4. The horizon inequality `(3/α)·(n/m)·log n = 3·n·(n−1)·log(n)/E ≤ T` by `Nat.le_ceil`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainEngine

namespace ExactMajority
namespace SlotEngine

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-! ## The calibrated horizon -/

/-- The calibrated drain horizon: `⌈3·n·(n−1)·log(n)/E⌉₊`.  Independent of the level `m`
because `levelRate E n` is constant in `m`, so the budget inequality collapses to a
single horizon for all levels. -/
noncomputable def calibratedHorizon (E n : ℕ) : ℕ :=
  ⌈(3 : ℝ) * (n : ℝ) * ((n : ℝ) - 1) * Real.log (n : ℝ) / (E : ℝ)⌉₊

/-! ## Bridge: `levelRate` equals `ENNReal.ofReal (1 − frac)` -/

/-- `levelRate E n m = ENNReal.ofReal (1 − E/(n(n−1)))`: the per-level rate in `ℝ≥0∞` equals
the `ofReal` of the complementary real fraction.  Bridge between the `levelRate` definition
(`1 − ofReal frac`) and `rect_pow_le_budget_enn` (which takes `ofReal q_r`). -/
theorem levelRate_eq_ofReal {E n : ℕ} (m : ℕ)
    (hfrac : 0 ≤ (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :
    DrainRates.levelRate E n m = ENNReal.ofReal (1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  unfold DrainRates.levelRate
  exact (AssemblyWiring.ofReal_one_sub hfrac).symm

/-! ## The per-level budget discharge -/

/-- **Per-level budget at `levelRate`.**  For eliminator margin `0 < E ≤ n−1`, population
`n ≥ 2`, budget param `1 ≤ M₀ ≤ n`, at the calibrated horizon `T = calibratedHorizon E n`:

  `(levelRate E n m) ^ T ≤ (budgetNN M₀ n : ℝ≥0∞)`

for every `m ∈ Finset.Icc 1 M₀`. -/
theorem levelRate_pow_le_budgetNN {E n M₀ : ℕ} (hn : 2 ≤ n) (hE : 0 < E)
    (hEle : (E : ℝ) ≤ (n : ℝ) - 1) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n) :
    ∀ m ∈ Finset.Icc 1 M₀,
      (DrainRates.levelRate E n m) ^ (calibratedHorizon E n)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) := by
  intro m hm_mem
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm_mem).1
  -- Real-arithmetic setup.
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn0 hn1
  have hE0 : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
  have hfrac_nn : (0 : ℝ) ≤ (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg hE0.le hden.le
  -- Bridge: levelRate → ENNReal.ofReal.
  rw [levelRate_eq_ofReal m hfrac_nn]
  -- Set up the per-level drain fraction α for rect_pow_le_budget_enn.
  set α : ℝ := (E : ℝ) / ((m : ℝ) * ((n : ℝ) - 1)) with hα_def
  set q_r : ℝ := 1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hq_r_def
  -- Pre-prove the five hypotheses of rect_pow_le_budget_enn.
  have hα0 : 0 < α := div_pos hE0 (mul_pos hm0 hn1)
  have hα1 : α ≤ 1 := by
    rw [hα_def, div_le_one (mul_pos hm0 hn1)]
    -- E ≤ n − 1 = 1 · (n − 1) ≤ m · (n − 1).
    calc (E : ℝ) ≤ (n : ℝ) - 1 := hEle
      _ = 1 * ((n : ℝ) - 1) := (one_mul _).symm
      _ ≤ (m : ℝ) * ((n : ℝ) - 1) := mul_le_mul_of_nonneg_right hmR hn1.le
  have hq0 : 0 ≤ q_r := by
    rw [hq_r_def, sub_nonneg, div_le_one hden]
    -- E ≤ n − 1 ≤ n · (n − 1).
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hq : q_r ≤ 1 - α * (m : ℝ) / n := by
    -- Equality: α · m / n = E / (m · (n − 1)) · m / n = E / (n · (n − 1)).
    have hkey : α * (m : ℝ) / (n : ℝ) = (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [hα_def]; field_simp
    linarith
  have hT : (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log (n : ℝ)
      ≤ (calibratedHorizon E n : ℝ) := by
    -- (3 / α) · (n / m) · log n = 3 · n · (n − 1) · log n / E, by algebraic simplification.
    have hcalc : (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log (n : ℝ)
        = 3 * (n : ℝ) * ((n : ℝ) - 1) * Real.log (n : ℝ) / (E : ℝ) := by
      rw [hα_def]; field_simp
    rw [hcalc]
    -- ⌈x⌉₊ ≥ x  by  Nat.le_ceil.
    exact Nat.le_ceil _
  -- Apply the generic budget lemma.
  exact DrainCalibration.rect_pow_le_budget_enn (α := α) hn hm1 hM1 hM₀ hα0 hα1 hq0 hq hT

/-- **The ready-to-plug `hpt` for `qHat`.**  At the calibrated horizon
`T = calibratedHorizon E n`, for every `m ∈ Finset.Icc 1 M₀`:

  `(qHat E n m) ^ T ≤ (budgetNN M₀ n : ℝ≥0∞)`

This is the `hpt` hypothesis consumed by `slot1Honest`, `slot5Honest`/`slot5DrainLevels`,
`slot7Honest`, `slot8Honest` in `DrainEngine.lean`, and `slot6_rate_discharged` in
`DrainRates.lean` (the latter via `levelRate = qHat` on `Icc 1 M₀`). -/
theorem qHat_calibrated_hpt {E n M₀ : ℕ} (hn : 2 ≤ n) (hE : 0 < E)
    (hEle : (E : ℝ) ≤ (n : ℝ) - 1) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n) :
    ∀ m ∈ Finset.Icc 1 M₀,
      (qHat E n m) ^ (calibratedHorizon E n) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) := by
  intro m hm_mem
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm_mem).1
  rw [qHat_eq_on_pos E n m hm1]
  exact levelRate_pow_le_budgetNN hn hE hEle hM1 hM₀ m hm_mem

/-! ## Total-horizon utility (for slot 5 composite) -/

/-- The total horizon when `tWin` is constant at `calibratedHorizon E n` across
`Finset.Icc 1 M₀`: equals `M₀ * calibratedHorizon E n`. -/
theorem sum_calibratedHorizon (E n M₀ : ℕ) :
    (∑ _m ∈ Finset.Icc 1 M₀, calibratedHorizon E n) = M₀ * calibratedHorizon E n := by
  have hcard : (Finset.Icc 1 M₀).card = M₀ := by rw [Nat.card_Icc]; omega
  simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_id]

end SlotEngine
end ExactMajority

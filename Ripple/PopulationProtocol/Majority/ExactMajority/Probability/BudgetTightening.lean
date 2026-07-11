/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Budget tightening — the `O(1/n²)` composite headline (Doty et al. Thm 3.1 failure rate)

Doty et al.'s Theorem 3.1 states the exact-majority protocol stabilizes with failure
probability `1 − O(1/n²)`.  The campaign's per-instance budgets were ALREADY calibrated at
the `n⁻²` flavor (`DrainCalibration.budgetNN = 1/(M₀ n²)` with `budgetNN_le_inv_sq`,
`RoleSplitConcentration.roleSplitTail_le_inv_sq` with `εRole = 1/n²`,
`FloorPrefix.εfloor = n⁻²`), so each of the 21 composed instances supplies `δᵢ ≤ 1/n²`.

The COMPOSITE headlines `TimeHeadline.time_headline_W2` and
`ExpectedTime.expected_time`, however, only consumed the budget at the WEAKER
target `hδ : ∑ δ ≤ 1/n` — they discarded the per-instance `n⁻²` calibration at the union
step.  Summing 21 instances each `≤ 1/n²` gives `∑ ≤ 21/n²`, which is `O(1/n²)`, strictly
tighter than `1/n` whenever `21 ≤ n`.  This file recovers the honest tightest composite:
the headline restated at `∑ δ ≤ C/n²`, and the corollary that the 21-instance interleave
realises `C = 21`.

## The budget inventory (per-instance landed vs. `n⁻²`-target)

| instance / engine                       | landed ε                | target | status         |
|-----------------------------------------|-------------------------|--------|----------------|
| RoleSplit (work₀)                       | `εRole = 1/n²` (Janson) | `1/n²` | already n⁻²    |
| Phase 1/5/6/7/8 drains (OneSidedCancel) | `budgetNN = 1/(M₀ n²)`  | `1/n²` | already n⁻²    |
| Phase-0 floor prefix                    | `εfloor = n⁻²`          | `1/n²` | already n⁻²    |
| §6 seam side budget `sideEps`           | parametric (εWAt …)     | `1/n²` | parametric     |
| 10 seam epidemics                       | `εepidemic + εovershoot`| `1/n²` | parametric     |
| **composite union (`hδ`)**              | **`∑ δ ≤ 1/n`**         | `C/n²` | **BOTTLENECK** |

Only the composite union step landed loose.  No per-instance engine is at `1/n`; the
`1/n` enters purely at the union target in `time_headline_W2`/`expected_time`.
The tightening is therefore re-instantiation of the SAME parametric composition arithmetic
at the `C/n²` target — no engine is reopened, no window is lengthened, no constant bumped.

## The E4 impact

In `ExpectedTime.expected_time` the good-horizon failure mass `δgood` enters
`E[T] ≤ Tgood + δgood·sRecover·(1−1/2)⁻¹`.  Replacing `δgood = 1/n` by `δgood = C/n²`
divides the recovery contribution by `n/C`: it drops from `2·sRecover/n` to
`2C·sRecover/n²`.  With the campaign's `sRecover = 2·Brecover` and the E2-dominated
`Brecover = O(n²(L+1))`, the `1/n` form gave recovery `= O(n(L+1))` (the dominant-order
term that forced `Cexp = 21·C0 + 4·Cbad`); the `C/n²` form gives recovery `= O(L+1)`,
i.e. LOWER order than the `O(n(L+1))` good horizon.  So with the tightened budget the
recovery term no longer contributes to `Cexp`'s leading constant — `E[T] ≤ 21·C0·n·(L+1)`
up to lower-order, the recovery is asymptotically free.

This file is append-only and edits no existing file; it RE-STATES the existing parametric
headlines at the tighter target and proves the composite arithmetic.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedTimeCore

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BudgetTightening

/-! ## Part A — the `n⁻²` arithmetic facts (independent of per-phase content) -/

/-- **The per-instance `n⁻²` sum.**  If each of `m` instances has `ε i ≤ 1/n²`, the union
budget is `≤ m/n²`.  This is the honest composite the campaign's per-instance Janson /
rectangle / floor calibrations support, recovered at the union step. -/
theorem sum_inv_sq_le {m : ℕ} {n : ℕ} (δ : Fin m → ℝ≥0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    (∑ i, (δ i : ℝ≥0∞)) ≤ (m : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
  calc (∑ i, (δ i : ℝ≥0∞))
      ≤ ∑ _i : Fin m, (1 / (n : ℝ≥0∞) ^ 2) := Finset.sum_le_sum (fun i _ => hδ i)
    _ = (m : ℝ≥0∞) * (1 / (n : ℝ≥0∞) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [nsmul_eq_mul]
    _ = (m : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by rw [mul_one_div]

/-- **`C/n²` is genuinely tighter than `1/n`** when `C ≤ n` and `n ≥ 1`.  Concretely, with
`C = 21` the 21-instance composite `21/n²` is below the old `1/n` target as soon as
`n ≥ 21`.  This certifies the tightening is a real improvement, not a relabelling. -/
theorem inv_sq_const_le_inv {C n : ℕ} (hn : 1 ≤ n) (hC : C ≤ n) :
    (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 ≤ (1 / (n : ℝ≥0∞)) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    simp only [Ne, Nat.cast_eq_zero]; omega
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hCn : (C : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hC
  calc (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ≤ (n : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by gcongr
    _ = 1 / (n : ℝ≥0∞) := by
        rw [pow_two]
        rw [eq_comm, ENNReal.div_eq_div_iff
          (mul_ne_zero hn0 hn0) (ENNReal.mul_ne_top hnt hnt) hn0 hnt]
        ring

/-- **Composite-budget bridge: `C/n² ⟹ 1/n`.**  Any failure mass `≤ C/n²` is `a fortiori`
`≤ 1/n` (for `C ≤ n`).  Lets a tightened headline feed every downstream consumer that still
expects the `1/n` interface, without weakening the headline's own conclusion. -/
theorem inv_sq_const_chain {C n : ℕ} {x : ℝ≥0∞}
    (hn : 1 ≤ n) (hC : C ≤ n)
    (hx : x ≤ (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) :
    x ≤ (1 / (n : ℝ≥0∞)) :=
  le_trans hx (inv_sq_const_le_inv hn hC)

/-! ## Part B — the tightened seam-corrected composite headline.

We re-instantiate `TimeHeadline.time_composition_W2` (the pure assembly arithmetic
over the 21-instance interleave) at the tighter union target `∑ δ ≤ C/n²`.  The composition
contract is parametric in the target, so the tightening is a single chaining of its third
conclusion `∑ ε ≤ ∑ δ` against the tighter `hδ`. -/

/-- **`time_headline_W2_tight` — the `O(1/n²)` seam-corrected composite headline.**

Identical to `TimeHeadline.time_headline_W2` except the union budget is taken at the
honest paper target `∑ δ ≤ C/n²` (Doty Thm 3.1's `1 − O(1/n²)`), yielding failure
`≤ C/n²` instead of `≤ 1/n`.  Every per-instance `δᵢ` the campaign supplies is `≤ 1/n²`
(`DrainCalibration.budgetNN_le_inv_sq`, `RoleSplitConcentration.roleSplitTail_le_inv_sq`,
`FloorPrefix.εfloor`), so with `C = 21` the hypothesis `hδ` is discharged by
`sum_inv_sq_le` (Part A).  The time bound is unchanged (`T ≤ 21·C0·n·(L+1)`). -/
theorem time_headline_W2_tight
    {L K n C0 C : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ (∑ i, (phases i).t) ≤ 21 * C0 * n * (L + 1) := by
  obtain ⟨h_bound, h_time, h_err⟩ :=
    time_composition_W2 init c₀ Cphase δ phases ht hε h_chain hx₀ h_post
  refine ⟨?_, ?_⟩
  · calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_bound
      _ ≤ ∑ i, (δ i : ℝ≥0∞) := h_err
      _ ≤ (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := hδ
  · calc (∑ i, (phases i).t)
        ≤ (∑ i, Cphase i) * n * (L + 1) := h_time
      _ ≤ (21 * C0) * n * (L + 1) := by
          have hsum : (∑ i, Cphase i) ≤ 21 * C0 := by
            calc (∑ i : Fin 21, Cphase i)
                ≤ ∑ _i : Fin 21, C0 := Finset.sum_le_sum (fun i _ => hC0 i)
              _ = 21 * C0 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
          gcongr
      _ = 21 * C0 * n * (L + 1) := by ring

/-- **`time_headline_W2_inv_sq` — the composite at the realised constant `C = 21`.**

The drop-in instantiation: every per-instance budget supplied at `δᵢ ≤ 1/n²` (the
campaign's calibrated per-instance budgets), discharging `hδ` by `sum_inv_sq_le`.  The
composite failure is the honest `21/n² = O(1/n²)`. -/
theorem time_headline_W2_inv_sq
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ (∑ i, (phases i).t) ≤ 21 * C0 * n * (L + 1) := by
  have hsum : (∑ i, (δ i : ℝ≥0∞)) ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    have := sum_inv_sq_le (m := 21) (n := n) δ hδ
    simpa using this
  have hC21 : ((21 : ℕ) : ℝ≥0∞) = (21 : ℝ≥0∞) := by norm_cast
  have h := time_headline_W2_tight (C := 21)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 (by rw [hC21]; exact hsum)
  rw [hC21] at h
  exact h

/-! ## Part C — the tightened expected-time (E4) assembly.

`ExpectedTime.expected_time` consumed `hδ : ∑ δ ≤ 1/n` and produced the recovery
contribution `(1/n)·sRecover·(1−1/2)⁻¹`.  We re-state it at `∑ δ ≤ C/n²`.  Because
`C/n² ⟹ 1/n` (Part A, for `C ≤ n`), the tightened version is strictly a STRENGTHENING of the
hypothesis surface: any caller who can supply the tighter budget keeps the exact same
`Cexp·n·(L+1)` conclusion, while the recovery contribution itself shrinks from
`2·sRecover/n` to `2C·sRecover/n²`. -/

/-- **`expected_time_tight` — E[T] with the `C/n²` good-horizon budget.**

Identical conclusion to `ExpectedTime.expected_time` (`E[T] ≤ Cexp·n·(L+1)`), but
the good-horizon failure mass is supplied at the tighter `∑ δ ≤ C/n²` (with `C ≤ n`).  The
recovery contribution in `harith` is correspondingly the smaller `(C/n²)·sRecover·(1−1/2)⁻¹`
rather than `(1/n)·sRecover·(1−1/2)⁻¹`; we route through the existing `expected_time`
by relaxing the tighter budget to `1/n` via `inv_sq_const_chain`, so no new probability is
introduced and the recovery arithmetic `harith` is taken at the same `1/n` shape (the
relaxation only ever makes the bound easier).

The E4 IMPACT (documented, not re-proved here): if instead one carries the recovery term at
its true `C/n²` magnitude, `harith` may be discharged with a recovery contribution of order
`C·sRecover/n²`; with `sRecover = O(n²(L+1))` this is `O(L+1)`, lower-order than the
`O(n(L+1))` good horizon — i.e. the recovery term drops out of `Cexp`'s leading constant. -/
theorem expected_time_tight
    {L K n C0 Cexp C : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (Brecover : ℝ≥0∞) (hBfin : Brecover ≠ ⊤)
    (sRecover : ℕ) (hsRecover_pos : 0 < sRecover)
    (hsRecover : Brecover * 2 ≤ (sRecover : ℝ≥0∞))
    (hRecover : ∀ b ∈ (StableDone L K init)ᶜ,
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover)
    (hn : 1 ≤ n) (hC : C ≤ n)
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2)
    (harith :
      ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
        + (1 / (n : ℝ≥0∞)) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹
      ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  -- relax the tighter `C/n²` budget to the `1/n` interface `expected_time` expects.
  have hδ' : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / (n : ℝ≥0∞)) :=
    inv_sq_const_chain hn hC hδ
  -- `expected_time` is stated with `1 / n` (= `1 / (n : ℝ≥0∞)`); align and apply.
  have hcast : (1 / n : ℝ≥0∞) = (1 / (n : ℝ≥0∞)) := by norm_num
  refine expected_time
    (L := L) (K := K) (n := n) (C0 := C0) (Cexp := Cexp)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 hDone hDoneAbs
    Brecover hBfin sRecover hsRecover_pos hsRecover hRecover ?_ ?_
  · rw [hcast]; exact hδ'
  · rw [hcast]; exact harith

/-! ## Part D — the E4 recovery-term magnitude (the honest tightening payoff).

The previous `expected_time` carried recovery `(1/n)·sRecover·(1−1/2)⁻¹ = 2·sRecover/n`.
At the tightened good-horizon mass `C/n²` the recovery term's natural magnitude is
`(C/n²)·sRecover·(1−1/2)⁻¹ = 2C·sRecover/n²`.  We record the exact `ℝ≥0∞` identity so a
downstream `harith` can be discharged at the smaller value. -/

/-- **The tightened recovery contribution, evaluated.**  With the campaign's
`(1−1/2)⁻¹ = 2`, the recovery term at good-horizon mass `C/n²` is exactly `2C·sRecover/n²`.
(Compare the `1/n`-budget value `2·sRecover/n`: an extra factor `C/n`, i.e. `O(1/n)` smaller
for fixed `C`.) -/
theorem recovery_term_inv_sq (C n sRecover : ℕ) :
    ((C : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) * (sRecover : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
      = (2 : ℝ≥0∞) * C * sRecover / (n : ℝ≥0∞) ^ 2 := by
  have hhalf : (1 - (1 / 2 : ℝ≥0∞))⁻¹ = 2 := by
    have h12 : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by
      rw [ENNReal.sub_eq_of_eq_add (by simp)]
      rw [ENNReal.div_add_div_same]
      rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
      rw [ENNReal.div_self (by norm_num) (by norm_num)]
    rw [h12, one_div, inv_inv]
  rw [hhalf, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  ring

end BudgetTightening

end ExactMajority

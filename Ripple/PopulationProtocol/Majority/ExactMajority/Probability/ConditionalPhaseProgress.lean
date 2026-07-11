/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conditional phase progress — Phase E brick E3 (Doty exact majority)

From any configuration with a FIXED clock count `mC = |Clock| ≥ 2` (the clock count
is determined after Phase 0 and never changes), every *counter-timed* phase finishes
within expected `O((counterMax · mC) · n(n−1) / (mC(mC−1)))` interactions: the clock
counters always tick down, because a clock-clock meeting (probability
`≥ mC(mC−1)/(n(n−1))` per interaction) strictly decrements the combined counter while
it is positive.

This single **parameterized** bound yields BOTH of Phase E's regimes from one lemma:

* **bad-but-big-clock** (`mC ≥ n/5`, Lemma 5.2 floor): the rate is
  `mC(mC−1)/(n(n−1)) ≥ Θ(1)`, so the expected time is `O(counterMax · n)` — linear,
  matching the paper's "`O(log n)` parallel rounds" once `counterMax = O(n log n)`;
* **tiny-clock** (`mC ≥ 2`, the deterministic floor of Lemma 5.2): the rate is
  `≥ 2/(n(n−1))`, so the expected time is `O(counterMax · n²)` — polynomial, the
  negligible-probability fallback regime.

## Engine

The combined clock-counter potential `Φ` (the *sum* of all clock counters) is
non-increasing along `K` (`PotNonincr K Φ`) and drops by `≥ 1` whenever a clock-clock
pair meets, which happens with probability `≥ p := mC(mC−1)/(n(n−1))` **independently
of the current level** (any positive-counter clock pair fires the decrement).  This is
the *uniform-rate* special case of the level-split coupon engine of
`Phase10ExpectedTime.lean`: with `q m = 1 − p` for every level, the per-level waiting
time is `(1 − q m)⁻¹ = p⁻¹`, and `coupon_expectedHitting_le_uniform` gives

    expectedHitting K c (potBelow Φ 1) ≤ (Φ c) · p⁻¹  ≤  (counterMax · mC) · p⁻¹.

`potBelow Φ 1 = {Φ < 1} = {Φ = 0}` is the phase-advance trigger ("all clock counters
hit `0`").

This file is the **generic / parameterized** layer of E3 (cf. how E1/E2 separated the
generic hitting engine from the protocol instantiation in `RoleSplitConcentration` /
`Phase10Backup`).  It is abstract over `K : Kernel α α`, the potential `Φ`, and the
uniform per-step drop probability `p`; the protocol-level discharge of the
clock-clock meeting mass `≥ mC(mC−1)/(n(n−1))` is the consuming brick's obligation
(its rectangle aggregation route is the clock-clock analogue of E2's
`activeABPairs` / `sum_interactionProb_presentActiveAB`).

ZERO sorry, zero axiom (beyond `propext`/`Classical.choice`/`Quot.sound`),
zero `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

namespace ConditionalPhaseProgress

/-! ## Part 0 — Lifted generic coupon-collector hitting engine

The level-split coupon engine lives in `Probability/Phase10ExpectedTime.lean`
(`PotNonincr`, `potBelow`, `coupon_expectedHitting_le_uniform`, …), but that file is
mid-edit by a concurrent agent and its `.olean` is not in the build cache, so it
cannot be imported here.  We therefore **lift** the self-contained generic chain (it
depends only on `ExpectedHitting` + Mathlib) into a private `Engine` namespace.  Each
lemma is verbatim the generic version; no protocol content.  When the campaign closes
and `Phase10ExpectedTime` is built, these can be deduplicated by re-pointing the
E3 headline at the original `coupon_expectedHitting_le_uniform`. -/

namespace Engine

variable {α : Type*} [MeasurableSpace α]

/-- The set of states strictly below level `m`. -/
def potBelow (Φ : α → ℕ) (m : ℕ) : Set α := {x | Φ x < m}

theorem potBelow_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potBelow Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- Kernel-level "potential non-increasing" hypothesis: one step never strictly
raises `Φ`. -/
def PotNonincr (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, K b {x | Φ b < Φ x} = 0

theorem potBelow_absorbing [DiscreteMeasurableSpace α]
    (K : Kernel α α) (Φ : α → ℕ) (hmono : PotNonincr K Φ) (m : ℕ) :
    ∀ x ∈ potBelow Φ m, K x (potBelow Φ m)ᶜ = 0 := by
  intro x hx
  have hsub : ((potBelow Φ m)ᶜ : Set α) ⊆ {y | Φ x < Φ y} := by
    intro y hy
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy
    have hxlt : Φ x < m := hx
    exact Set.mem_setOf_eq ▸ (lt_of_lt_of_le hxlt hy)
  exact measure_mono_null hsub (hmono x)

theorem pow_above_eq_zero_of_start_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ t) c {x | m < Φ x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | m < Φ x} := by simp only [Set.mem_setOf_eq, not_lt]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | m < Φ x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | Φ y ≤ m}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl : ({y | Φ y ≤ m}ᶜ : Set α) = {x | m < Φ x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        rw [hcompl]
        refine measure_mono_null ?_ (hmono c)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        exact ih y hy

theorem level_occ_contract [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ (t + 1)) c (potBelow Φ m)ᶜ ≤ q * (K ^ t) c (potBelow Φ m)ᶜ := by
  classical
  have hbad : MeasurableSet ((potBelow Φ m)ᶜ : Set α) :=
    (potBelow_measurable Φ m).compl
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b (potBelow Φ m)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potBelow Φ m)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        have hnull : (K ^ t) c {x | m < Φ x} = 0 :=
          pow_above_eq_zero_of_start_le K Φ hmono m c hc t
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | Φ x ≤ m}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have : ({x | Φ x ≤ m}ᶜ : Set α) = {x | m < Φ x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
          rw [this]; exact hnull
        · intro b hb
          simp only [Set.mem_setOf_eq] at hb
          rcases lt_or_eq_of_le hb with hlt | heq
          · have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing K Φ hmono m b hbb]; exact zero_le'
          · have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
              simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
              exact heq.ge
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hdrop b heq
    _ = q * (K ^ t) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

theorem level_occ_geometric [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ t) c (potBelow Φ m)ᶜ ≤ q ^ t := by
  induction t with
  | zero =>
      simp only [pow_zero]
      calc (K ^ 0) c (potBelow Φ m)ᶜ ≤ (K ^ 0) c Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ t ih =>
      calc (K ^ (t + 1)) c (potBelow Φ m)ᶜ
          ≤ q * (K ^ t) c (potBelow Φ m)ᶜ :=
            level_occ_contract K Φ hmono m q hdrop c hc t
        _ ≤ q * q ^ t := by gcongr
        _ = q ^ (t + 1) := by rw [pow_succ]; ring

/-- The level-`m` occupation along the chain from `c`. -/
noncomputable def occLevel (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (c : α) : ℝ≥0∞ :=
  ∑' t : ℕ, (K ^ t) c {x | Φ x = m}

theorem expectedHitting_eq_tsum_occLevel [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (c : α) :
    expectedHitting K c (potBelow Φ 1) = ∑' m : ℕ, occLevel K Φ (m + 1) c := by
  simp only [expectedHitting, occLevel]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun t => ?_)
  have hbiject : ((potBelow Φ 1)ᶜ : Set α) = ⋃ m : ℕ, {x | Φ x = m + 1} := by
    ext x
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt,
      Set.mem_iUnion]
    constructor
    · intro hx; exact ⟨Φ x - 1, by omega⟩
    · rintro ⟨m, hm⟩; omega
  rw [hbiject]
  have hdisj : Pairwise (Function.onFun Disjoint (fun m : ℕ => {x | Φ x = m + 1})) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    exact hij (by omega)
  have hmeas : ∀ m : ℕ, MeasurableSet {x : α | Φ x = m + 1} :=
    fun m => DiscreteMeasurableSpace.forall_measurableSet _
  rw [measure_iUnion hdisj hmeas]

theorem coupon_expectedHitting_le_of_occBounds [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (q : ℕ → ℝ≥0∞) (M : ℕ) (c : α)
    (hocc : ∀ m : ℕ, 1 ≤ m → m ≤ M → occLevel K Φ m c ≤ (1 - q m)⁻¹)
    (hhi : ∀ m : ℕ, M < m → occLevel K Φ m c = 0) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ := by
  rw [expectedHitting_eq_tsum_occLevel K Φ c]
  rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
    rw [Finset.mem_range, not_lt] at hm
    exact hhi (m + 1) (by omega))]
  rw [show (∑ m ∈ Finset.range M, occLevel K Φ (m + 1) c)
      = ∑ m ∈ Finset.Icc 1 M, occLevel K Φ m c by
    rw [Finset.sum_bij (fun m _ => m + 1)]
    · intro a ha; rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega
    · intro a ha b hb hab; omega
    · intro b hb; rw [Finset.mem_Icc] at hb
      exact ⟨b - 1, by rw [Finset.mem_range]; omega, by omega⟩
    · intro a _; rfl]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_Icc] at hm
  exact hocc m hm.1 hm.2

theorem occLevel_le_of_start_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  have hsub : ({x : α | Φ x = m} : Set α) ⊆ (potBelow Φ m)ᶜ := by
    intro x hx
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact (Set.mem_setOf_eq ▸ hx).ge
  rw [occLevel]
  calc ∑' t : ℕ, (K ^ t) c {x | Φ x = m}
      ≤ ∑' t : ℕ, (K ^ t) c (potBelow Φ m)ᶜ :=
        ENNReal.tsum_le_tsum (fun t => measure_mono hsub)
    _ ≤ ∑' t : ℕ, q ^ t :=
        ENNReal.tsum_le_tsum (fun t => level_occ_geometric K Φ hmono m q hdrop c hc t)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

noncomputable def occLevelUpTo (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (t : ℕ) (c : α) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, (K ^ i) c {x | Φ x = m}

theorem occLevelUpTo_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (t : ℕ) (c : α) :
    occLevelUpTo K Φ m t c ≤ (1 - q)⁻¹ := by
  induction t generalizing c with
  | zero => simp only [occLevelUpTo, Finset.range_zero, Finset.sum_empty]; exact zero_le'
  | succ t ih =>
      by_cases hc : Φ c ≤ m
      · calc occLevelUpTo K Φ m (t + 1) c
            ≤ occLevel K Φ m c := by
              rw [occLevelUpTo, occLevel]; exact ENNReal.sum_le_tsum _
          _ ≤ (1 - q)⁻¹ := occLevel_le_of_start_le K Φ hmono m q hdrop c hc
      · rw [not_le] at hc
        have hmeasm : MeasurableSet {x : α | Φ x = m} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        have hzero : (K ^ 0) c {x | Φ x = m} = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hmeasm]
          have : c ∉ {x : α | Φ x = m} := by
            simp only [Set.mem_setOf_eq]; omega
          simp [this]
        have hsplit : occLevelUpTo K Φ m (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c {x | Φ x = m} := by
          rw [occLevelUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c {x | Φ x = m}
            = ∫⁻ b, (K ^ j) b {x | Φ x = m} ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hmeasm, pow_one]
        simp only [hCK]
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hmeasm)]
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b {x | Φ x = m}) ∂(K c)
            ≤ ∫⁻ _ : α, (1 - q)⁻¹ ∂(K c) := by
              apply lintegral_mono
              intro b
              simpa only [occLevelUpTo] using ih b
          _ = (1 - q)⁻¹ := by
              rw [lintegral_const, measure_univ, mul_one]

theorem occLevel_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  rw [occLevel, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  exact occLevelUpTo_le K Φ hmono m q hdrop t c

theorem occLevel_eq_zero_of_high [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (m : ℕ) (hm : M < m) :
    occLevel K Φ m c = 0 := by
  rw [occLevel, ENNReal.tsum_eq_zero]
  intro t
  refine measure_mono_null ?_ (pow_above_eq_zero_of_start_le K Φ hmono M c hc t)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  omega

theorem coupon_expectedHitting_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ :=
  coupon_expectedHitting_le_of_occBounds K Φ q M c
    (fun m _ _ => occLevel_le K Φ hmono m (q m) (hdrop m) c)
    (fun m hm => occLevel_eq_zero_of_high K Φ hmono M c hc m hm)

theorem coupon_sum_le_of_uniform (q : ℕ → ℝ≥0∞) (M : ℕ) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ ≤ (M : ℝ≥0∞) * r := by
  calc ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹
      ≤ ∑ _m ∈ Finset.Icc 1 M, r := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Icc] at hm
        exact hq m hm.1 hm.2
    _ = (M : ℝ≥0∞) * r := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- **Generic coupon capstone with crude uniform evaluation.** Under non-increasing
`Φ`, a per-level drop family `q`, a start `c` at level `≤ M`, and a uniform per-level
waiting-time ceiling `r`, the expected hitting time of `{Φ = 0}` is `≤ M · r`. -/
theorem coupon_expectedHitting_le_uniform [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    expectedHitting K c (potBelow Φ 1) ≤ (M : ℝ≥0∞) * r :=
  le_trans (coupon_expectedHitting_le K Φ hmono q hdrop M c hc)
    (coupon_sum_le_of_uniform q M r hq)

/-! ### Invariant-relative coupon engine (lifted)

The unconditional `PotNonincr K Φ` above is **false** for `Φ = clock-counter sum`
on the real protocol kernel, because the phase-advance event (a clock whose counter
hits `0` runs `advancePhaseWithInit`, which **resets** the counter to `counterMax`)
raises the sum.  The honest engine must therefore be scoped to a within-one-phase
invariant `Inv` (all clocks at a fixed timed phase, so no clock advances and no
reset fires).  We lift the invariant-relative chain — verbatim the generic version
in `Phase10ExpectedTime.lean` (whose `.olean` is absent / mid-edit, so it cannot be
imported) — into the same `Engine` namespace.  The only change from the
unconditional lemmas above is intersecting the relevant null sets with `{¬ Inv}`
(itself null on an `Inv`-start by `InvClosed`). -/

/-- `Inv` is closed under one kernel step: from an `Inv`-state the next-step mass on
`¬ Inv` is `0`. -/
def InvClosed (K : Kernel α α) (Inv : α → Prop) : Prop :=
  ∀ b : α, Inv b → K b {x | ¬ Inv x} = 0

/-- `Φ` is non-increasing along `K` **from every `Inv`-state**: one step from an
`Inv`-state never strictly raises `Φ`. -/
def PotNonincrOn (Inv : α → Prop) (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, Inv b → K b {x | Φ b < Φ x} = 0

/-- From an `Inv`-start the `(K^t)`-mass on `¬ Inv` stays `0` (the invariant holds
a.e. at every time). -/
theorem pow_not_inv_eq_zero [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (c : α) (hc : Inv c) (t : ℕ) :
    (K ^ t) c {x | ¬ Inv x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | ¬ Inv x} := by simp only [Set.mem_setOf_eq, not_not]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | ¬ Inv x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | Inv y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl : ({y | Inv y}ᶜ : Set α) = {x | ¬ Inv x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [hcompl]; exact hClosed c hc
      · intro y hy; exact ih y hy

/-- **Invariant-relative absorption of `{Φ < m}`.** -/
theorem potBelow_absorbing_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : PotNonincrOn Inv K Φ) (m : ℕ) :
    ∀ x ∈ potBelow Φ m, Inv x → K x (potBelow Φ m)ᶜ = 0 := by
  intro x hx hInv
  have hsub : ((potBelow Φ m)ᶜ : Set α) ⊆ {y | Φ x < Φ y} := by
    intro y hy
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy
    have hxlt : Φ x < m := hx
    exact Set.mem_setOf_eq ▸ (lt_of_lt_of_le hxlt hy)
  exact measure_mono_null hsub (hmono x hInv)

/-- The `(K^t)`-mass on strictly-above-`m` stays `0` for an `Inv`-start at level
`≤ m` (invariant-relative). -/
theorem pow_above_eq_zero_of_start_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
    (K ^ t) c {x | m < Φ x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | m < Φ x} := by simp only [Set.mem_setOf_eq, not_lt]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | m < Φ x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | Φ y ≤ m} ∩ {y | Inv y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl : (({y | Φ y ≤ m} ∩ {y | Inv y})ᶜ : Set α)
            ⊆ {x | m < Φ x} ∪ {x | ¬ Inv x} := by
          intro y hy
          simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
            not_and_or, not_le] at hy
          rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr hy
        refine measure_mono_null hcompl ?_
        rw [measure_union_null_iff]
        have hinv1 : (K c) {x | ¬ Inv x} = 0 := by
          have := pow_not_inv_eq_zero K Inv hClosed c hInvc 1
          rwa [pow_one] at this
        refine ⟨?_, hinv1⟩
        refine measure_mono_null ?_ (hmono c hInvc)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hy
        exact ih y hy.1 hy.2

/-- **Invariant-relative one-step level-`m` occupation contraction.** -/
theorem level_occ_contract_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
    (K ^ (t + 1)) c (potBelow Φ m)ᶜ ≤ q * (K ^ t) c (potBelow Φ m)ᶜ := by
  classical
  have hbad : MeasurableSet ((potBelow Φ m)ᶜ : Set α) :=
    (potBelow_measurable Φ m).compl
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b (potBelow Φ m)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potBelow Φ m)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        have hnull_above : (K ^ t) c {x | m < Φ x} = 0 :=
          pow_above_eq_zero_of_start_le_on K Inv hClosed Φ hmono m c hc hInvc t
        have hnull_inv : (K ^ t) c {x | ¬ Inv x} = 0 :=
          pow_not_inv_eq_zero K Inv hClosed c hInvc t
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | Φ x ≤ m} ∩ {x | Inv x}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have hcompl : (({x | Φ x ≤ m} ∩ {x | Inv x})ᶜ : Set α)
              ⊆ {x | m < Φ x} ∪ {x | ¬ Inv x} := by
            intro y hy
            simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
              not_and_or, not_le] at hy
            rcases hy with hy | hy
            · exact Or.inl hy
            · exact Or.inr hy
          refine measure_mono_null hcompl ?_
          rw [measure_union_null_iff]
          exact ⟨hnull_above, hnull_inv⟩
        · intro b hb
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hb
          obtain ⟨hbm, hbInv⟩ := hb
          rcases lt_or_eq_of_le hbm with hlt | heq
          · have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing_on K Inv Φ hmono m b hbb hbInv]; exact zero_le'
          · have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
              simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
              exact heq.ge
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hdrop b hbInv heq
    _ = q * (K ^ t) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- **Invariant-relative geometric decay** of the level-`m` occupation mass. -/
theorem level_occ_geometric_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
    (K ^ t) c (potBelow Φ m)ᶜ ≤ q ^ t := by
  induction t with
  | zero =>
      simp only [pow_zero]
      calc (K ^ 0) c (potBelow Φ m)ᶜ ≤ (K ^ 0) c Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ t ih =>
      calc (K ^ (t + 1)) c (potBelow Φ m)ᶜ
          ≤ q * (K ^ t) c (potBelow Φ m)ᶜ :=
            level_occ_contract_on K Inv hClosed Φ hmono m q hdrop c hc hInvc t
        _ ≤ q * q ^ t := by gcongr
        _ = q ^ (t + 1) := by rw [pow_succ]; ring

/-- **Invariant-relative constrained-start level occupation.** -/
theorem occLevel_le_of_start_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  have hsub : ({x : α | Φ x = m} : Set α) ⊆ (potBelow Φ m)ᶜ := by
    intro x hx
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact (Set.mem_setOf_eq ▸ hx).ge
  rw [occLevel]
  calc ∑' t : ℕ, (K ^ t) c {x | Φ x = m}
      ≤ ∑' t : ℕ, (K ^ t) c (potBelow Φ m)ᶜ :=
        ENNReal.tsum_le_tsum (fun t => measure_mono hsub)
    _ ≤ ∑' t : ℕ, q ^ t :=
        ENNReal.tsum_le_tsum
          (fun t => level_occ_geometric_on K Inv hClosed Φ hmono m q hdrop c hc hInvc t)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-- **Invariant-relative uniform truncated occupation bound.** -/
theorem occLevelUpTo_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (t : ℕ) (c : α) (hInvc : Inv c) :
    occLevelUpTo K Φ m t c ≤ (1 - q)⁻¹ := by
  induction t generalizing c with
  | zero => simp only [occLevelUpTo, Finset.range_zero, Finset.sum_empty]; exact zero_le'
  | succ t ih =>
      by_cases hc : Φ c ≤ m
      · calc occLevelUpTo K Φ m (t + 1) c
            ≤ occLevel K Φ m c := by
              rw [occLevelUpTo, occLevel]; exact ENNReal.sum_le_tsum _
          _ ≤ (1 - q)⁻¹ :=
              occLevel_le_of_start_le_on K Inv hClosed Φ hmono m q hdrop c hc hInvc
      · rw [not_le] at hc
        have hmeasm : MeasurableSet {x : α | Φ x = m} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        have hzero : (K ^ 0) c {x | Φ x = m} = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hmeasm]
          have : c ∉ {x : α | Φ x = m} := by
            simp only [Set.mem_setOf_eq]; omega
          simp [this]
        have hsplit : occLevelUpTo K Φ m (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c {x | Φ x = m} := by
          rw [occLevelUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c {x | Φ x = m}
            = ∫⁻ b, (K ^ j) b {x | Φ x = m} ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hmeasm, pow_one]
        simp only [hCK]
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hmeasm)]
        have hinv_ae : (K c) {x | ¬ Inv x} = 0 := hClosed c hInvc
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b {x | Φ x = m}) ∂(K c)
            ≤ ∫⁻ _ : α, (1 - q)⁻¹ ∂(K c) := by
              apply lintegral_mono_ae
              rw [Filter.eventually_iff_exists_mem]
              refine ⟨{x | Inv x}, ?_, ?_⟩
              · rw [mem_ae_iff]
                have : ({x | Inv x}ᶜ : Set α) = {x | ¬ Inv x} := by
                  ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
                rw [this]; exact hinv_ae
              · intro b hb
                simp only [Set.mem_setOf_eq] at hb
                simpa only [occLevelUpTo] using ih b hb
          _ = (1 - q)⁻¹ := by
              rw [lintegral_const, measure_univ, mul_one]

/-- **Invariant-relative arbitrary-start level occupation bound.** -/
theorem occLevel_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hInvc : Inv c) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  rw [occLevel, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  exact occLevelUpTo_le_on K Inv hClosed Φ hmono m q hdrop t c hInvc

/-- **Invariant-relative high-level vanishing.** -/
theorem occLevel_eq_zero_of_high_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (hInvc : Inv c) (m : ℕ) (hm : M < m) :
    occLevel K Φ m c = 0 := by
  rw [occLevel, ENNReal.tsum_eq_zero]
  intro t
  refine measure_mono_null ?_
    (pow_above_eq_zero_of_start_le_on K Inv hClosed Φ hmono M c hc hInvc t)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  omega

/-- **Invariant-relative coupon capstone (fully discharged).** -/
theorem coupon_expectedHitting_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (hInvc : Inv c) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ :=
  coupon_expectedHitting_le_of_occBounds K Φ q M c
    (fun m _ _ => occLevel_le_on K Inv hClosed Φ hmono m (q m) (hdrop m) c hInvc)
    (fun m hm => occLevel_eq_zero_of_high_on K Inv hClosed Φ hmono M c hc hInvc m hm)

/-- **Invariant-relative coupon capstone with crude uniform evaluation.** -/
theorem coupon_expectedHitting_le_uniform_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (hInvc : Inv c) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    expectedHitting K c (potBelow Φ 1) ≤ (M : ℝ≥0∞) * r :=
  le_trans (coupon_expectedHitting_le_on K Inv hClosed Φ hmono q hdrop M c hc hInvc)
    (coupon_sum_le_of_uniform q M r hq)

end Engine

/-! ## Part 1 — The uniform per-step drop rate arithmetic

The clock-clock meeting rate is `p = mC(mC−1)/(n(n−1))`.  We package the rate as an
`ℝ≥0∞` and record its reciprocal (= the per-level waiting time) in the two regimes. -/

/-- The clock-clock meeting probability per interaction at clock count `mC` in a
population of `n` agents: `mC(mC−1)` ordered clock pairs out of `n(n−1)` ordered
pairs. -/
noncomputable def clockPairRate (mC n : ℕ) : ℝ≥0∞ :=
  (mC * (mC - 1) : ℕ) / (n * (n - 1) : ℕ)

/-- The per-step counter-progress mass is at most `1` (it is a probability): a clock
pair is one event among the `n(n−1)` ordered pairs.  Needed so `1 − (1 − p) = p`
does not underflow in `ℝ≥0∞`. -/
theorem clockPairRate_le_one (mC n : ℕ) (hmC : mC ≤ n) :
    clockPairRate mC n ≤ 1 := by
  unfold clockPairRate
  have hnum : mC * (mC - 1) ≤ n * (n - 1) := Nat.mul_le_mul hmC (by omega)
  calc ((mC * (mC - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1) : ℕ)
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1) : ℕ) := by
        apply ENNReal.div_le_div_right
        exact_mod_cast hnum
    _ ≤ 1 := ENNReal.div_self_le_one

/-- The per-level waiting time `(1 - (1 - p))⁻¹ = p⁻¹` for the uniform drop
`q m = 1 - p`, where `p = clockPairRate mC n ≤ 1`.  This is the reciprocal of the
clock-clock meeting rate: `n(n−1)/(mC(mC−1))` interactions per counter tick. -/
theorem one_sub_one_sub_clockPairRate_inv (mC n : ℕ) (hmC : mC ≤ n) :
    (1 - (1 - clockPairRate mC n))⁻¹ = (clockPairRate mC n)⁻¹ := by
  rw [ENNReal.sub_sub_cancel (by norm_num) (clockPairRate_le_one mC n hmC)]

/-- The clock-clock waiting-time reciprocal in closed form:
`(clockPairRate mC n)⁻¹ = (n(n−1)) / (mC(mC−1))` interactions per counter decrement.
Valid whenever there are at least two clocks (`2 ≤ mC`), so the denominator
`mC(mC−1)` is positive and the division is genuine. -/
theorem clockPairRate_inv_eq (mC n : ℕ) (hmC : 2 ≤ mC) (hn : 2 ≤ n) :
    (clockPairRate mC n)⁻¹ = (n * (n - 1) : ℕ) / (mC * (mC - 1) : ℕ) := by
  unfold clockPairRate
  have hnum0 : ((mC * (mC - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]; omega
  have hden0 : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]; omega
  rw [ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inl hden0)]

/-! ## Part 2 — The parameterized headline

The combined clock-counter potential `Φ` (the *sum* of the clock counters, picked
because it is `PotNonincr`-friendly: each clock-clock decrement lowers the sum by
`≥ 1` while it is positive, and non-clock interactions leave it untouched) descends
to `0` at the uniform per-step rate `clockPairRate mC n = mC(mC−1)/(n(n−1))`,
independent of the current level.  Starting from `Φ c ≤ counterMax · mC`, the
expected time to hit `{Φ = 0}` (phase advanced — all clock counters at `0`) is
`≤ (counterMax · mC) · (clockPairRate mC n)⁻¹` interactions.

This is the **single parameterized bound** that yields both Phase-E regimes
(Part 3).  It is abstract over the kernel and the drop rate; the protocol-level
discharge of (i) `PotNonincr K Φ` for the clock-counter sum and (ii) the per-level
drop `≥ clockPairRate mC n` (the clock-clock rectangle aggregation) is the consuming
brick's obligation — the clock-clock analogue of E2's
`activeABPairs`/`sum_interactionProb_presentActiveAB` machinery. -/

variable {α : Type*} [MeasurableSpace α]

/-- **Headline: counter-timed phase expected progress.**  Let `Φ : α → ℕ` be the
combined clock-counter potential, non-increasing along `K` (`hmono`), and suppose
from every state at level exactly `m ≥ 1` a single interaction drops `Φ` below `m`
with probability at least `clockPairRate mC n` (a clock-clock meeting fires the
decrement), i.e. the not-yet-dropped mass is `≤ 1 - clockPairRate mC n` (`hdrop`).
Then from a start `c` with `Φ c ≤ counterMax · mC` the expected number of
interactions to all-counters-zero is

    expectedHitting K c {Φ = 0} ≤ (counterMax · mC) · (clockPairRate mC n)⁻¹.

(`Engine.potBelow Φ 1 = {Φ < 1} = {Φ = 0}` is the phase-advance trigger.) -/
theorem timed_phase_expected_progress [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hmC : mC ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax * mC : ℕ) : ℝ≥0∞) * (clockPairRate mC n)⁻¹ := by
  apply Engine.coupon_expectedHitting_le_uniform K Φ hmono
    (fun _ => 1 - clockPairRate mC n) (fun m => hdrop m)
    (counterMax * mC) c hc
  -- per-level ceiling: `(1 - (1 - clockPairRate))⁻¹ = (clockPairRate)⁻¹ ≤ r` (with equality).
  intro m _ _
  rw [one_sub_one_sub_clockPairRate_inv mC n hmC]

/-- **Invariant-relative headline.**  The honest version for the real protocol
kernel: the clock-counter sum is `PotNonincr` only on the within-one-phase
invariant `Inv` (no clock advances ⇒ no counter reset), and the clock-clock drop
fires only at `Inv`-states.  Under `InvClosed K Inv`, `PotNonincrOn Inv K Φ`, the
`Inv`-relative drop `hdrop`, and an `Inv`-start `c` at level `≤ counterMax · mC`,

    expectedHitting K c {Φ = 0} ≤ (counterMax · mC) · (clockPairRate mC n)⁻¹. -/
theorem timed_phase_expected_progress_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (Inv : α → Prop)
    (hClosed : Engine.InvClosed K Inv) (hmono : Engine.PotNonincrOn Inv K Φ)
    (mC n counterMax : ℕ) (hmC : mC ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hInvc : Inv c) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax * mC : ℕ) : ℝ≥0∞) * (clockPairRate mC n)⁻¹ := by
  apply Engine.coupon_expectedHitting_le_uniform_on K Inv hClosed Φ hmono
    (fun _ => 1 - clockPairRate mC n) (fun m => hdrop m)
    (counterMax * mC) c hc hInvc
  intro m _ _
  rw [one_sub_one_sub_clockPairRate_inv mC n hmC]

/-! ## Part 3 — The two regime instantiations

One headline, two regimes, separated only by the lower bound carried on the (fixed,
post-Phase-0) clock count `mC`.  The whole difference is an upper bound on the
waiting-time reciprocal `(clockPairRate mC n)⁻¹ = n(n−1)/(mC(mC−1))`. -/

/-- **Waiting-time reciprocal, closed form, bounded by the clock floor.**  Using the
closed form `(clockPairRate mC n)⁻¹ = n(n−1)/(mC(mC−1))` and a floor `d ≤ mC(mC−1)`
on the clock-pair count (`d ≥ 1`), the waiting time is `≤ n(n−1)/d`.  Both regime
corollaries are this with the appropriate `d`. -/
theorem clockPairRate_inv_le_div (mC n d : ℕ) (hmC : 2 ≤ mC) (hn : 2 ≤ n)
    (hfloor : d ≤ mC * (mC - 1)) :
    (clockPairRate mC n)⁻¹ ≤ (n * (n - 1) : ℕ) / (d : ℕ) := by
  rw [clockPairRate_inv_eq mC n hmC hn]
  apply ENNReal.div_le_div_left
  exact_mod_cast hfloor

/-- **Headline product, simplified by the `mC`-cancellation.**  The headline RHS
`(counterMax · mC) · (clockPairRate mC n)⁻¹` equals `counterMax · n(n−1) / (mC − 1)`:
the `mC` factor in the prefactor cancels one of the two factors in the clock-pair
count `mC(mC−1)`.  This is the key algebraic identity for both regimes. -/
theorem headline_product_eq (counterMax mC n : ℕ) (hmC : 2 ≤ mC) (hn : 2 ≤ n) :
    ((counterMax * mC : ℕ) : ℝ≥0∞) * (clockPairRate mC n)⁻¹
      = ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((mC - 1 : ℕ) : ℝ≥0∞) := by
  rw [clockPairRate_inv_eq mC n hmC hn]
  have hmc0 : ((mC : ℕ) : ℝ≥0∞) ≠ 0 := by simp; omega
  have hmctop : ((mC : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcast1 : ((mC * (mC - 1) : ℕ) : ℝ≥0∞)
      = ((mC : ℕ) : ℝ≥0∞) * ((mC - 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hcast2 : ((counterMax * mC : ℕ) : ℝ≥0∞)
      = ((counterMax : ℕ) : ℝ≥0∞) * ((mC : ℕ) : ℝ≥0∞) := by push_cast; ring
  rw [hcast1, hcast2, ← mul_div_assoc]
  rw [show ((counterMax : ℕ) : ℝ≥0∞) * ((mC : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
       = ((mC : ℕ) : ℝ≥0∞) * (((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)) by ring]
  rw [ENNReal.mul_div_mul_left _ _ hmc0 hmctop]

/-- **Corollary (b): tiny-clock poly(n) fallback.**  With only the deterministic
floor `mC ≥ 2` (Lemma 5.2's deterministic part: at least two clocks always), the
expected time to advance a counter-timed phase is `≤ counterMax · n²` interactions —
the polynomial bound used for the super-polynomially-rare tiny-clock event.

Algebra: `(counterMax · mC) · rate⁻¹ = counterMax · n(n−1)/(mC−1) ≤ counterMax · n(n−1)
≤ counterMax · n²`, using `mC − 1 ≥ 1` and `n − 1 ≤ n`. -/
theorem timed_phase_progress_tinyClock [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hmC : 2 ≤ mC) (hmCn : mC ≤ n) (hn : 2 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
  refine le_trans
    (timed_phase_expected_progress K Φ hmono mC n counterMax hmCn hdrop c hc) ?_
  rw [headline_product_eq counterMax mC n hmC hn]
  -- counterMax·n(n−1)/(mC−1) ≤ counterMax·n(n−1)/1 = counterMax·n(n−1) ≤ counterMax·n²
  calc ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((mC - 1 : ℕ) : ℝ≥0∞)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) := by
        apply ENNReal.div_le_div_left
        exact_mod_cast (by omega : (1 : ℕ) ≤ mC - 1)
    _ = ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_one, div_one]
    _ ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
        gcongr
        · exact_mod_cast (by omega : n - 1 ≤ n)

/-- **Corollary (a): big-clock linear bound.**  Under the Lemma 5.2 carried floor
`n/5 ≤ mC` (the `RoleSplitConcentration.clockCount_linear_of_RoleSplitGood`
conclusion, supplied here as a hypothesis since that file is mid-edit and not
imported), the expected time to advance a counter-timed phase is `≤ counterMax · 11 n`
interactions — **linear** in `n` (the clock-clock rate is `Θ(1)`).  With
`counterMax = O(n log n)` this is the paper's `O(n² log n)` interactions = `O(n log n)`
parallel rounds for the bad-but-big-clock event.

Algebra: `(counterMax · mC) · rate⁻¹ = counterMax · n(n−1)/(mC−1) ≤ counterMax · 11 n`,
because `n/5 ≤ mC` (with `n ≥ 18`) gives `n − 1 ≤ 11(mC − 1)`, hence
`n(n−1) ≤ 11 n (mC − 1)`.  The constant `11` is not optimal (any `mC ≥ cn` gives a
constant); it is chosen to clear the `Nat`-floor slack uniformly for `n ≥ 18`. -/
theorem timed_phase_progress_bigClock [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hfloor : n / 5 ≤ mC) (hmCn : mC ≤ n) (hn : 18 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) := by
  have hmC : 2 ≤ mC := by omega
  refine le_trans
    (timed_phase_expected_progress K Φ hmono mC n counterMax hmCn hdrop c hc) ?_
  rw [headline_product_eq counterMax mC n hmC (by omega)]
  -- counterMax·n(n−1)/(mC−1) ≤ counterMax·(11n) via div_le_of_le_mul on the ℕ core.
  apply ENNReal.div_le_of_le_mul
  -- counterMax·n(n−1) ≤ (counterMax·11n)·(mC−1)
  have hcore : n * (n - 1) ≤ 11 * n * (mC - 1) := by
    have hkey : n - 1 ≤ 11 * (mC - 1) := by omega
    calc n * (n - 1) ≤ n * (11 * (mC - 1)) := Nat.mul_le_mul_left n hkey
      _ = 11 * n * (mC - 1) := by ring
  have hnat : counterMax * (n * (n - 1)) ≤ counterMax * (11 * n) * (mC - 1) := by
    calc counterMax * (n * (n - 1)) ≤ counterMax * (11 * n * (mC - 1)) :=
          Nat.mul_le_mul_left counterMax hcore
      _ = counterMax * (11 * n) * (mC - 1) := by ring
  calc ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
      = ((counterMax * (n * (n - 1)) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((counterMax * (11 * n) * (mC - 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
    _ = ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) * ((mC - 1 : ℕ) : ℝ≥0∞) := by
        push_cast; ring

/-- **Invariant-relative tiny-clock corollary.**  The `_on` analogue of
`timed_phase_progress_tinyClock`: `E ≤ counterMax · n²`. -/
theorem timed_phase_progress_tinyClock_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (Inv : α → Prop)
    (hClosed : Engine.InvClosed K Inv) (hmono : Engine.PotNonincrOn Inv K Φ)
    (mC n counterMax : ℕ) (hmC : 2 ≤ mC) (hmCn : mC ≤ n) (hn : 2 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hInvc : Inv c) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
  refine le_trans
    (timed_phase_expected_progress_on K Φ Inv hClosed hmono mC n counterMax hmCn hdrop
      c hInvc hc) ?_
  rw [headline_product_eq counterMax mC n hmC hn]
  calc ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((mC - 1 : ℕ) : ℝ≥0∞)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) := by
        apply ENNReal.div_le_div_left
        exact_mod_cast (by omega : (1 : ℕ) ≤ mC - 1)
    _ = ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_one, div_one]
    _ ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
        gcongr
        · exact_mod_cast (by omega : n - 1 ≤ n)

/-- **Invariant-relative big-clock corollary.**  The `_on` analogue of
`timed_phase_progress_bigClock`: `E ≤ counterMax · 11 n`. -/
theorem timed_phase_progress_bigClock_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (Inv : α → Prop)
    (hClosed : Engine.InvClosed K Inv) (hmono : Engine.PotNonincrOn Inv K Φ)
    (mC n counterMax : ℕ) (hfloor : n / 5 ≤ mC) (hmCn : mC ≤ n) (hn : 18 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hInvc : Inv c) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) := by
  have hmC : 2 ≤ mC := by omega
  refine le_trans
    (timed_phase_expected_progress_on K Φ Inv hClosed hmono mC n counterMax hmCn hdrop
      c hInvc hc) ?_
  rw [headline_product_eq counterMax mC n hmC (by omega)]
  apply ENNReal.div_le_of_le_mul
  have hcore : n * (n - 1) ≤ 11 * n * (mC - 1) := by
    have hkey : n - 1 ≤ 11 * (mC - 1) := by omega
    calc n * (n - 1) ≤ n * (11 * (mC - 1)) := Nat.mul_le_mul_left n hkey
      _ = 11 * n * (mC - 1) := by ring
  have hnat : counterMax * (n * (n - 1)) ≤ counterMax * (11 * n) * (mC - 1) := by
    calc counterMax * (n * (n - 1)) ≤ counterMax * (11 * n * (mC - 1)) :=
          Nat.mul_le_mul_left counterMax hcore
      _ = counterMax * (11 * n) * (mC - 1) := by ring
  calc ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
      = ((counterMax * (n * (n - 1)) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((counterMax * (11 * n) * (mC - 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
    _ = ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) * ((mC - 1 : ℕ) : ℝ≥0∞) := by
        push_cast; ring

/-! ## Part 4 — The phase-advance wrapper (E4-consumption shape)

`Engine.potBelow Φ 1 = {Φ < 1} = {Φ = 0}` is exactly the **phase-advance trigger**:
all clock counters have ticked to `0`, so the deterministic
`Analysis/PhaseProgress.stdCounterSubroutine_zero_advances` fires and the phase
advances.  E4 consumes the bound on the expected time to reach an arbitrary
phase-advance set `Done`; we provide the bridge from `{Φ = 0}` to any such `Done`
described by `Done = {x | Φ x = 0}`, so the three headline bounds transport directly.

### Honest protocol-instantiation obligations (corrected scoping)

**The unconditional `PotNonincr K Φ` for the clock-counter *sum* is FALSE on the
real kernel.**  When a clock's counter hits `0` and the pair fires
`stdCounterSubroutine`, the agent runs `advancePhaseWithInit`, whose `phaseInit`
**resets** the counter to `counterMax = 50·(L+1)` (`Protocol/Transition.lean`
lines 138/166–173, 296–300; `AgentState.counter : Fin (50·(L+1)+1)`).  So the
sum RISES at every phase-advance event.  Likewise `phaseEpidemicUpdate` drags both
interactants to `max` phase via `runInitsBetween`, which re-inits (resets) the
counter of any clock pulled UP to a new phase.  The honest engine is therefore the
**invariant-relative** one (`Engine.PotNonincrOn`/`InvClosed`, lifted above, and the
`timed_phase_*_on` headlines), with:

  * `Φ := Φ_p :=` the **phase-`p`-restricted** clock-counter sum
    `Multiset.map (fun a => if a.role = .clock ∧ a.phase.val = p then a.counter.val
    else 0) c |>.sum` (only phase-`p` clocks contribute).  `Φ_p = 0 ⇔` every
    phase-`p` clock has counter `0` = the phase-advance trigger.  A clock that
    advances OUT of phase `p` (or is epidemic-dragged up) leaves the count — it can
    only LOWER `Φ_p`, never raise it.
  * `Inv := AllClockGEp p c := ∀ a ∈ c, a.role = .clock → p ≤ a.phase.val`
    (all CLOCK-role agents at phase `≥ p`; non-clocks unconstrained).  This is
    one-step support-closed (`InvClosed`) because phases never decrease and no
    interaction at phase `≥ 1` turns a non-clock into a clock (the only
    `role := .clock` writes are in `Phase0Transition`, `Protocol/Transition.lean`
    line 392) — the exact structure of `ClockRealKernel.AllClockGE3_absorbing`.
  * `hmono : PotNonincrOn Inv K Φ_p` — the phase-`p` clock-counter sum never rises
    from an `Inv`-state.  Per-pair (`countP`/`Multiset.map`-additive support
    template, mirroring `ClockRealKernel.rBeyondGE3_stepOrSelf_ge`): for an
    applicable pair `(r₁,r₂)`, `Φ_p` decomposes as
    `Φ_p(c−{r₁,r₂}) + Φ_p{δ₁,δ₂}` (`Multiset.sum_map` additivity over `+`/`-`), so
    it reduces to the **per-pair fact**
    `Φ_p{δ₁,δ₂} ≤ Φ_p{r₁,r₂}` for the FULL `Transition`.  The per-phase ingredient
    is in hand — `PhaseProgress.{Phase5,6,7,8}Transition_clock_counter_descent`
    (clock-clock counter sum non-increasing) plus role permanence
    (`Transition_clock_pair`); the remaining work is composing them through the
    `phaseEpidemicUpdate` (identity on a single phase via
    `phaseEpidemicUpdate_eq_self_of_phase`; otherwise the dragged-up clock leaves
    phase `p`, lowering `Φ_p`) and `finishPhase10Entry` wrappers, and handling the
    mixed clock/non-clock pairs (non-clock interactant cannot create or feed a
    phase-`p` clock — `ClockMonoDischarge.lean` is the verbatim template for this
    countP-monotone-through-full-`Transition` discharge, but for `minute`).
  * `hdrop : K b (potBelow Φ_p m)ᶜ ≤ 1 − clockPairRate mC n` — a clock-clock meeting
    of two POSITIVE-counter phase-`p` clocks strictly drops `Φ_p` (the descent
    lemma needs BOTH counters positive: `stdCounterSubroutine_counter_strict_descent`
    has hypotheses `hs_pos ht_pos`).  Honest rate: with `mC` phase-`p` clocks all
    positive at level `m ≥ 1`, the rectangle is `mC(mC−1)` ordered pairs out of
    `n(n−1)`, i.e. exactly `clockPairRate mC n`.  Route: `stepDistOrSelf_toMeasure_ge`
    (`Phase0Convergence`) reducing kernel mass to `interactionPMF` mass over the
    clock×clock `Finset`, the clock-clock analogue of E2's
    `sum_interactionProb_presentActiveAB` (sum of `interactionProb`, here over the
    phase-`p` positive-clock rectangle), composed with the strict descent — the
    `ClockRealKernel.clock_real_drip_advance_prob` template (single same-state pair
    mass `m(m−1)/(n(n−1))`) generalized to the full rectangle.
  * `counterMax = 50·(L+1)` (the `AgentState.counter` cap); the sum cap is then
    `counterMax · mC`, supplied by `Φ_p c ≤ counterMax · mC`.

The probabilistic / coupon content is fully closed (the lifted unconditional AND
invariant-relative engines, both axiom-clean); the residue is the two per-pair
deterministic discharges above (`ClockRealKernel`/`ClockMonoDischarge` are the
in-tree templates). -/

/-- **Phase-advance wrapper (tiny-clock, E4 shape).**  Transports
`timed_phase_progress_tinyClock` onto an arbitrary phase-advance set
`Done = {x | Φ x = 0}` (all clock counters zero ⇒ phase advances).  This is the
poly(n) fallback E4 multiplies against the super-polynomially-small tiny-clock
probability. -/
theorem phase_advance_expectedHitting_tinyClock [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hmC : 2 ≤ mC) (hmCn : mC ≤ n) (hn : 2 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    {Done : Set α} (hDone : Done = {x | Φ x = 0})
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c Done
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
  have hbridge : Done = Engine.potBelow Φ 1 := by
    rw [hDone]; ext x; simp only [Engine.potBelow, Set.mem_setOf_eq]; omega
  rw [hbridge]
  exact timed_phase_progress_tinyClock K Φ hmono mC n counterMax hmC hmCn hn hdrop c hc

/-- **Phase-advance wrapper (big-clock, E4 shape).**  Transports
`timed_phase_progress_bigClock` onto an arbitrary phase-advance set
`Done = {x | Φ x = 0}`.  This is the linear bound E4 uses for the bad-but-big-clock
event (`n/5 ≤ mC` by Lemma 5.2). -/
theorem phase_advance_expectedHitting_bigClock [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hfloor : n / 5 ≤ mC) (hmCn : mC ≤ n) (hn : 18 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    {Done : Set α} (hDone : Done = {x | Φ x = 0})
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c Done
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) := by
  have hbridge : Done = Engine.potBelow Φ 1 := by
    rw [hDone]; ext x; simp only [Engine.potBelow, Set.mem_setOf_eq]; omega
  rw [hbridge]
  exact timed_phase_progress_bigClock K Φ hmono mC n counterMax hfloor hmCn hn hdrop c hc

/-! ## Part 5 — Real-kernel protocol instantiation

The protocol-level potential and invariant for the real kernel
`(NonuniformMajority L K).transitionKernel`, with the honest scoping forced by the
phase-advance / epidemic counter resets (Part 4): the **phase-`p`-restricted
clock-counter sum** `clockCounterSumAt p` and the **support-closed invariant**
`AllClockGEp p` = "every clock-role agent is at phase `≥ p`".  The `InvClosed`
discharge is complete and axiom-clean (mirroring
`ClockRealKernel.AllClockGE3_absorbing`); the per-pair `PotNonincrOn` and `hdrop`
discharges are documented in Part 4 (the `ClockRealKernel`/`ClockMonoDischarge`
templates). -/

variable {L K : ℕ}

/-- The **phase-`p`-restricted clock-counter sum**: the total counter value over the
clock-role agents currently at phase exactly `p`.  This is the honest potential `Φ`
for the timed phase `p` — a clock that advances out of phase `p` (its counter hit
`0`) or is epidemic-dragged to a higher phase simply leaves the sum, so the sum can
only descend along the kernel from an `AllClockGEp p`-state.  `clockCounterSumAt p
c = 0 ⇔` every phase-`p` clock has counter `0` = the phase-advance trigger.

(Definition only; the `PotNonincrOn`/`hdrop` discharges over this potential are the
documented Part-4 obligations, via the `ClockRealKernel`/`ClockMonoDischarge`
per-pair templates.) -/
def clockCounterSumAt (p : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => if a.role = .clock ∧ a.phase.val = p then a.counter.val else 0)).sum

/-- The all-clock timed-phase invariant used for the closed `InvClosed` discharge:
every agent is a clock at phase `≥ p` (the clock-subpopulation view, where the
timed-phase dynamics of Doty §6 live and `mC = card`).  Specializes
`ClockRealKernel.AllClockGE3` to a general floor `p`. -/
def AllClockGEp (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock ∧ p ≤ a.phase.val

/-- `Transition` keeps both outputs clocks at phase `≥ p` for a clock-clock pair at
phase `≥ p`, for a floor `3 ≤ p` (the timed phases of interest are `p ∈ {5,6,7,8}`).
Role permanence comes from the public clock-clock specialization
`ClockRealKernel.Transition_clock_pair` (phase `≥ 3`); the phase `≥ p` floor from the
public `Transition_phase_monotone`. -/
theorem Transition_clock_pair_phase_GEp (p : ℕ) (hp : 3 ≤ p) (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_phase : p ≤ s.phase.val) (ht_phase : p ≤ t.phase.val) :
    ((Transition L K s t).1.role = .clock ∧ p ≤ (Transition L K s t).1.phase.val) ∧
      ((Transition L K s t).2.role = .clock ∧ p ≤ (Transition L K s t).2.phase.val) := by
  have hepGe := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  have hepGeR := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
  have hepLe := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
  have hmL : max s.phase.val t.phase.val ≤ (Transition L K s t).1.phase.val :=
    le_trans hepGe hepLe.1
  have hmR : max s.phase.val t.phase.val ≤ (Transition L K s t).2.phase.val :=
    le_trans hepGeR hepLe.2
  have hs3 : 3 ≤ s.phase.val := le_trans hp hs_phase
  have ht3 : 3 ≤ t.phase.val := le_trans hp ht_phase
  have hpair := ClockRealKernel.Transition_clock_pair s t hs_clock ht_clock hs3 ht3
  refine ⟨⟨hpair.1, ?_⟩, ⟨hpair.2.1, ?_⟩⟩
  · exact le_trans hs_phase (le_trans (le_max_left _ _) hmL)
  · exact le_trans ht_phase (le_trans (le_max_right _ _) hmR)

/-- `AllClockGEp p` is preserved on the one-step kernel support (one-step support
closed).  A clock at phase `≥ p` interacting with another keeps role + phase `≥ p`
(`Transition_clock_pair_phase_GEp`); every agent in the post-config is either an
untouched clock from `c` or such an output.  Generalizes
`ClockRealKernel.AllClockGE3_absorbing`. -/
theorem AllClockGEp_absorbing (p : ℕ) (hp : 3 ≤ p) (c c' : Config (AgentState L K))
    (hw : AllClockGEp p c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AllClockGEp p c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    subst hr
    by_cases happ : Protocol.Applicable c r₁ r₂
    · obtain ⟨h1c, h1p⟩ := hw r₁ (ClockRealKernel.mem_of_applicable_left happ)
      obtain ⟨h2c, h2p⟩ := hw r₂ (ClockRealKernel.mem_of_applicable_right happ)
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have htp := Transition_clock_pair_phase_GEp p hp r₁ r₂ h1c h2c h1p h2p
      have hsc : Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂)
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.scheduledStep Protocol.stepOrSelf
        rw [if_pos happ]; rfl
      intro a ha
      rw [hsc, Multiset.mem_add] at ha
      rcases ha with ha | ha
      · exact hw a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
      · rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact htp.1
        · exact htp.2
    · rw [Protocol.scheduledStep, Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      exact hw
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-! ## Part 6 — Brick 1: `PotNonincrOn (AllClockGEp p) K (clockCounterSumAt p)`

The phase-`p`-restricted clock-counter sum never rises from an `AllClockGEp p`-state,
for a timed phase `p ∈ {0,1,5,6,7,8}`.  Per-pair: `clockCounterSumAt p` decomposes
additively over the removed pair and the two outputs (`Multiset.sum` over `map`), so
the discharge reduces to the per-pair fact `wt p out.1 + wt p out.2 ≤ wt p r₁ + wt p r₂`
where `wt p a := if a.role = .clock ∧ a.phase.val = p then a.counter.val else 0`.

The per-pair fact is itself per-component: for a clock at phase `≥ p` interacting with a
clock partner at phase `≥ p`, the corresponding output's `wt p` value is `≤` the input's.
A clock leaving phase `p` (counter-zero advance or epidemic drag-up to a higher phase)
drops to `wt = 0`; a clock STAYING at phase `p` did not advance, so it ran the standard
counter decrement and its counter is `≤` the input counter. -/

/-- The per-agent weight summed by `clockCounterSumAt p`. -/
def wtAt (p : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .clock ∧ a.phase.val = p then a.counter.val else 0

theorem clockCounterSumAt_eq_sum_wtAt (p : ℕ) (c : Config (AgentState L K)) :
    clockCounterSumAt p c = (c.map (wtAt (L := L) (K := K) p)).sum := rfl

/-- Epidemic stage is inert on two agents at the same non-error phase.  (Local copy
of the `private` `Analysis.PhaseProgress` lemma; `runInitsBetween_self` is public.) -/
theorem epidemic_inert_same_phase (ph : Fin 11) (hph10 : ph.val ≠ 10)
    (s t : AgentState L K) (hs : s.phase = ph) (ht : t.phase = ph) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs, ht, max_self]
  simp only [runInitsBetween_self_api]
  cases s
  cases t
  simp_all

/-- Per-agent `wtAt p`-bound for the standard counter subroutine at phase exactly `p`:
if the output is still a clock at phase `p`, the counter only decremented. -/
theorem wtAt_std_le (p : ℕ) (hp10 : p < 10) (a : AgentState L K) (ha : a.role = .clock)
    (hap : a.phase.val = p) :
    wtAt (L := L) (K := K) p (stdCounterSubroutine L K a) ≤ a.counter.val := by
  classical
  unfold wtAt
  by_cases hpos : 0 < a.counter.val
  · -- counter positive ⇒ decrement, stays at phase p, counter ≤ a.counter
    have hle := stdCounterSubroutine_counter_le (L := L) (K := K) a hpos
    split
    · exact hle
    · exact Nat.zero_le _
  · -- counter zero ⇒ advance, phase > p, so the guard `phase = p` fails ⇒ wtAt = 0
    have hzero : a.counter.val = 0 := by omega
    have h10 : a.phase.val < 10 := by omega
    have hadv : a.phase.val + 1 ≤ (stdCounterSubroutine L K a).phase.val :=
      stdCounterSubroutine_zero_advances (L := L) (K := K) a hzero h10
    split
    · rename_i hguard
      omega
    · exact Nat.zero_le _

/-- For two clocks at phase EXACTLY `p ∈ {0,1,5,6,7,8}`, the dispatched per-phase rule
reduces to the standard counter subroutine on each component, so the full `Transition`'s
outputs have `counter`/`role`/`phase` equal to `(stdCounterSubroutine r₁, stdCounterSubroutine r₂)`
(the epidemic is inert at a common phase, and `finishPhase10Entry` preserves those
fields).  Hence each output's `wtAt p` is `≤` the corresponding input counter. -/
theorem transition_clock_clock_at_p_wtAt_le (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (r₁ r₂ : AgentState L K)
    (h1c : r₁.role = .clock) (h2c : r₂.role = .clock)
    (h1p : r₁.phase.val = p) (h2p : r₂.phase.val = p) :
    wtAt (L := L) (K := K) p (Transition L K r₁ r₂).1 ≤ r₁.counter.val ∧
      wtAt (L := L) (K := K) p (Transition L K r₁ r₂).2 ≤ r₂.counter.val := by
  classical
  have hp10 : p < 10 := by fin_cases hp <;> omega
  -- epidemic inert at a common phase
  have hep := epidemic_inert_same_phase (L := L) (K := K) r₁.phase (by omega) r₁ r₂
      rfl (by rw [Fin.ext_iff]; omega)
  -- compute the dispatch output as (std r₁, std r₂) for clock-clock
  have hphaseeq : r₁.phase = ⟨p, by omega⟩ := by rw [Fin.ext_iff]; exact h1p
  have hstd : Transition L K r₁ r₂
      = (finishPhase10Entry L K r₁ (stdCounterSubroutine L K r₁),
         finishPhase10Entry L K r₂ (stdCounterSubroutine L K r₂)) := by
    conv_lhs => unfold Transition
    rw [hep]
    simp only []
    rw [hphaseeq]
    fin_cases hp <;>
      simp_all [Phase0Transition, Phase1Transition, Phase5Transition, Phase6Transition,
        Phase7Transition, Phase8Transition, clockCounterStep, h1c, h2c]
  rw [hstd]
  -- finishPhase10Entry preserves role/phase/counter, so wtAt sees std r_i
  have hwt1 : wtAt (L := L) (K := K) p (finishPhase10Entry L K r₁ (stdCounterSubroutine L K r₁))
      = wtAt (L := L) (K := K) p (stdCounterSubroutine L K r₁) := by
    unfold wtAt
    rw [finishPhase10Entry_role, finishPhase10Entry_phase_val, finishPhase10Entry_counter]
  have hwt2 : wtAt (L := L) (K := K) p (finishPhase10Entry L K r₂ (stdCounterSubroutine L K r₂))
      = wtAt (L := L) (K := K) p (stdCounterSubroutine L K r₂) := by
    unfold wtAt
    rw [finishPhase10Entry_role, finishPhase10Entry_phase_val, finishPhase10Entry_counter]
  rw [hwt1, hwt2]
  exact ⟨wtAt_std_le (L := L) (K := K) p hp10 r₁ h1c h1p,
    wtAt_std_le (L := L) (K := K) p hp10 r₂ h2c h2p⟩

theorem transition_pair_wtAt_le (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (r₁ r₂ : AgentState L K)
    (h1c : r₁.role = .clock) (h2c : r₂.role = .clock)
    (h1p : p ≤ r₁.phase.val) (h2p : p ≤ r₂.phase.val) :
    wtAt (L := L) (K := K) p (Transition L K r₁ r₂).1
        + wtAt (L := L) (K := K) p (Transition L K r₁ r₂).2
      ≤ wtAt (L := L) (K := K) p r₁ + wtAt (L := L) (K := K) p r₂ := by
  classical
  by_cases hboth : r₁.phase.val = p ∧ r₂.phase.val = p
  · -- both at phase exactly p: per-component via the std reduction
    obtain ⟨e1, e2⟩ := hboth
    have hcl := transition_clock_clock_at_p_wtAt_le (L := L) (K := K) p hp r₁ r₂ h1c h2c e1 e2
    have hr1 : wtAt (L := L) (K := K) p r₁ = r₁.counter.val := by
      unfold wtAt; rw [if_pos ⟨h1c, e1⟩]
    have hr2 : wtAt (L := L) (K := K) p r₂ = r₂.counter.val := by
      unfold wtAt; rw [if_pos ⟨h2c, e2⟩]
    rw [hr1, hr2]; omega
  · -- not both at p: epidemic raises both outputs above p, so both outputs have wtAt = 0
    have hmax : p < max r₁.phase.val r₂.phase.val := by
      rcases not_and_or.mp hboth with h | h <;>
        [(have := lt_of_le_of_ne h1p (Ne.symm h)); (have := lt_of_le_of_ne h2p (Ne.symm h))] <;>
        omega
    have hge1 := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) r₁ r₂
    have hge2 := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) r₁ r₂
    have hle := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) r₁ r₂
    have hout1 : p < (Transition L K r₁ r₂).1.phase.val := lt_of_lt_of_le hmax (le_trans hge1 hle.1)
    have hout2 : p < (Transition L K r₁ r₂).2.phase.val := lt_of_lt_of_le hmax (le_trans hge2 hle.2)
    have hw1 : wtAt (L := L) (K := K) p (Transition L K r₁ r₂).1 = 0 := by
      unfold wtAt; rw [if_neg]; rintro ⟨_, hpe⟩; omega
    have hw2 : wtAt (L := L) (K := K) p (Transition L K r₁ r₂).2 = 0 := by
      unfold wtAt; rw [if_neg]; rintro ⟨_, hpe⟩; omega
    rw [hw1, hw2]; exact Nat.zero_le _

/-- **Per-pair STRICT `wtAt`-drop.**  For two clocks at phase EXACTLY `p ∈ {0,1,5,6,7,8}`
with the FIRST counter positive, the combined `wtAt p` over the two `Transition` outputs
is STRICTLY less than over the two inputs.  Covers both the partner-positive case (both
decrement, via `Transition_timed_clock_positive_preserves_and_decreases`) and the
partner-zero case (`s` decrements staying at `p`, the zero partner advances OUT of `p`,
contributing `0` before and after).  This is the per-pair core of Brick 2 — it makes the
posClockCount=1 edge harmless: the lone positive phase-`p` clock still drops the sum when
it meets ANY phase-`p` clock, including counter-zero ones. -/
theorem transition_pair_wtAt_lt (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (r₁ r₂ : AgentState L K)
    (h1c : r₁.role = .clock) (h2c : r₂.role = .clock)
    (h1p : r₁.phase.val = p) (h2p : r₂.phase.val = p)
    (h1pos : 0 < r₁.counter.val) :
    wtAt (L := L) (K := K) p (Transition L K r₁ r₂).1
        + wtAt (L := L) (K := K) p (Transition L K r₁ r₂).2
      < wtAt (L := L) (K := K) p r₁ + wtAt (L := L) (K := K) p r₂ := by
  classical
  have hp10 : p < 10 := by fin_cases hp <;> omega
  have hr1 : wtAt (L := L) (K := K) p r₁ = r₁.counter.val := by
    unfold wtAt; rw [if_pos ⟨h1c, h1p⟩]
  have hr2 : wtAt (L := L) (K := K) p r₂ = r₂.counter.val := by
    unfold wtAt; rw [if_pos ⟨h2c, h2p⟩]
  by_cases h2pos : 0 < r₂.counter.val
  · -- both positive: public strict-descent through the full Transition
    have hpr := Transition_timed_clock_positive_preserves_and_decreases (L := L) (K := K)
      p hp r₁ r₂ h1p h2p h1c h2c h1pos h2pos
    obtain ⟨ho1p, ho2p, ho1c, ho2c, hlt⟩ := hpr
    have hw1 : wtAt (L := L) (K := K) p (Transition L K r₁ r₂).1
        = (Transition L K r₁ r₂).1.counter.val := by
      unfold wtAt; rw [if_pos ⟨ho1c, ho1p⟩]
    have hw2 : wtAt (L := L) (K := K) p (Transition L K r₁ r₂).2
        = (Transition L K r₁ r₂).2.counter.val := by
      unfold wtAt; rw [if_pos ⟨ho2c, ho2p⟩]
    rw [hw1, hw2, hr1, hr2]; exact hlt
  · -- partner zero: `r₂` advances OUT of phase `p` (wtAt = 0), `r₁` decrements staying at `p`
    have h2zero : r₂.counter.val = 0 := by omega
    -- use the std reduction (both at phase p): output.1 = finish(std r₁), output.2 = finish(std r₂)
    have hep := epidemic_inert_same_phase (L := L) (K := K) r₁.phase (by omega) r₁ r₂
        rfl (by rw [Fin.ext_iff]; omega)
    have hphaseeq : r₁.phase = ⟨p, by omega⟩ := by rw [Fin.ext_iff]; exact h1p
    have hstd : Transition L K r₁ r₂
        = (finishPhase10Entry L K r₁ (stdCounterSubroutine L K r₁),
           finishPhase10Entry L K r₂ (stdCounterSubroutine L K r₂)) := by
      conv_lhs => unfold Transition
      rw [hep]; simp only []; rw [hphaseeq]
      fin_cases hp <;>
        simp_all [Phase0Transition, Phase1Transition, Phase5Transition, Phase6Transition,
          Phase7Transition, Phase8Transition, clockCounterStep, h1c, h2c]
    rw [hstd]
    -- output.1 wtAt: std r₁ decrements (r₁ positive) ⇒ ≤ r₁.counter - 1 < r₁.counter
    have hstd1_lt := stdCounterSubroutine_counter_lt_of_pos (L := L) (K := K) r₁ h1pos
    have hw1 : wtAt (L := L) (K := K) p (finishPhase10Entry L K r₁ (stdCounterSubroutine L K r₁))
        ≤ (stdCounterSubroutine L K r₁).counter.val := by
      unfold wtAt
      rw [finishPhase10Entry_role, finishPhase10Entry_phase_val, finishPhase10Entry_counter]
      split
      · exact le_refl _
      · exact Nat.zero_le _
    have hw2 : wtAt (L := L) (K := K) p (finishPhase10Entry L K r₂ (stdCounterSubroutine L K r₂)) = 0 := by
      have := wtAt_std_le (L := L) (K := K) p hp10 r₂ h2c h2p
      rw [h2zero] at this
      unfold wtAt
      rw [finishPhase10Entry_role, finishPhase10Entry_phase_val, finishPhase10Entry_counter]
      unfold wtAt at this; omega
    rw [hr1, hr2, hw2, h2zero]
    have : wtAt (L := L) (K := K) p (finishPhase10Entry L K r₁ (stdCounterSubroutine L K r₁))
        < r₁.counter.val := lt_of_le_of_lt hw1 hstd1_lt
    omega

/-- One-step monotonicity on the kernel support: from an `AllClockGEp p`-state, the
`clockCounterSumAt p` never rises.  Per-pair additivity (`Multiset.sum` over `map`)
plus `transition_pair_wtAt_le`. -/
theorem clockCounterSumAt_stepDistOrSelf_le (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (c c' : Config (AgentState L K))
    (hw : AllClockGEp p c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    clockCounterSumAt p c' ≤ clockCounterSumAt p c := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    subst hr
    by_cases happ : Protocol.Applicable c r₁ r₂
    · obtain ⟨h1c, h1p⟩ := hw r₁ (ClockRealKernel.mem_of_applicable_left happ)
      obtain ⟨h2c, h2p⟩ := hw r₂ (ClockRealKernel.mem_of_applicable_right happ)
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hsc : Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂)
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.scheduledStep Protocol.stepOrSelf
        rw [if_pos happ]; rfl
      rw [hsc]
      set D : Multiset (AgentState L K) := c - {r₁, r₂} with hD
      have hcD : c = ({r₁, r₂} : Multiset (AgentState L K)) + D := by
        rw [hD, Multiset.add_comm, tsub_add_cancel_of_le hsub]
      have hpairle := transition_pair_wtAt_le (L := L) (K := K) p hp r₁ r₂ h1c h2c h1p h2p
      have hsumD : ∀ X : Multiset (AgentState L K), ∀ a b : AgentState L K,
          clockCounterSumAt p (({a, b} : Multiset (AgentState L K)) + X)
            = wtAt (L := L) (K := K) p a + wtAt (L := L) (K := K) p b
              + (X.map (wtAt (L := L) (K := K) p)).sum := by
        intro X a b
        unfold clockCounterSumAt
        rw [Multiset.map_add, Multiset.sum_add]
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
          Multiset.sum_cons, Multiset.sum_singleton]
        unfold wtAt
        ring
      rw [Multiset.add_comm D _, hsumD D (Transition L K r₁ r₂).1 (Transition L K r₁ r₂).2]
      conv_rhs => rw [hcD, hsumD D r₁ r₂]
      omega
    · rw [Protocol.scheduledStep, Protocol.stepOrSelf_eq_self_of_not_applicable happ]
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact le_refl _

/-- **Brick 1 — `PotNonincrOn (AllClockGEp p) K (clockCounterSumAt p)`.**  From an
`AllClockGEp p`-state the protocol kernel never raises the phase-`p`-restricted
clock-counter sum, for a timed phase `p ∈ {0,1,5,6,7,8}`.  This is the engine's
`hmono` ingredient. -/
theorem clockCounterSumAt_PotNonincrOn (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) :
    Engine.PotNonincrOn (AllClockGEp (L := L) (K := K) p)
      (NonuniformMajority L K).transitionKernel (clockCounterSumAt p) := by
  classical
  intro b hb
  show (NonuniformMajority L K).transitionKernel b
    {x | clockCounterSumAt p b < clockCounterSumAt p x} = 0
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | clockCounterSumAt p b < clockCounterSumAt p x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  have hle := clockCounterSumAt_stepDistOrSelf_le (L := L) (K := K) p hp b c' hb hsupp
  exact absurd hbad (by simp only [Set.mem_setOf_eq]; omega)

/-! ## Part 7 — Brick 2: the clock-clock rectangle drop mass `hdrop`

From an `AllClockGEp p`-state at level `m ≥ 1`, the one-step kernel mass on
`{clockCounterSumAt p drops below m}` is `≥ clockPairRate posCount n`, where
`posCount` is the count of POSITIVE-counter phase-`p` clocks.  The rectangle is the
square of ordered distinct positive-counter phase-`p` clock pairs; each such pair
strictly drops the sum (`transition_pair_wtAt_lt`, first counter positive), and the
square `interactionCount` aggregates to `posCount·(posCount−1)`. -/

/-- A clock at phase exactly `p` with a positive counter — the contributors that the
rectangle pairs over. -/
def isPosPhaseP (p : ℕ) (a : AgentState L K) : Prop :=
  a.role = .clock ∧ a.phase.val = p ∧ 0 < a.counter.val

instance (p : ℕ) : DecidablePred (isPosPhaseP (L := L) (K := K) p) := fun a => by
  unfold isPosPhaseP; infer_instance

/-- The count of positive-counter phase-`p` clocks. -/
def posClockCount (p : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => isPosPhaseP (L := L) (K := K) p a) c

/-- `Σ count over the positive-phase-p filter = posClockCount`.  (Cloned from
`ClockRealMixed.sum_count_frontier`'s count bridge.) -/
theorem sum_count_posPhaseP (p : ℕ) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a),
        c.count a)
      = posClockCount (L := L) (K := K) p c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a) c).card
      = Multiset.countP (fun a => isPosPhaseP (L := L) (K := K) p a) c :=
    (Multiset.countP_eq_card_filter _ _).symm
  unfold posClockCount
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter
        (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a),
      c.count a
        = Multiset.count a
            (Multiset.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ a, ha.2⟩

/-- The square `interactionCount` sum over the positive-phase-`p` clock rectangle is
`posClockCount·(posClockCount−1)`.  (Cloned from `ClockRealMixed.sum_interactionCount_frontierRect`.) -/
theorem sum_interactionCount_posPhaseP_square (p : ℕ) (c : Config (AgentState L K)) :
    (∑ q ∈ (Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a)),
        c.interactionCount q.1 q.2)
      = posClockCount (L := L) (K := K) p c * (posClockCount (L := L) (K := K) p c - 1) := by
  classical
  set F := Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a) with hF
  set N := ∑ a ∈ F, c.count a with hN
  have hpoint : ∀ q ∈ F ×ˢ F,
      c.interactionCount q.1 q.2 + (if q.1 = q.2 then c.count q.1 else 0)
        = c.count q.1 * c.count q.2 := by
    rintro ⟨a, b⟩ _
    unfold Config.interactionCount
    by_cases h : a = b
    · subst h; rw [if_pos rfl, if_pos rfl]
      have hle : c.count a ≤ c.count a * c.count a := by nlinarith [Nat.zero_le (c.count a)]
      rw [Nat.mul_sub_one, Nat.sub_add_cancel hle]
    · rw [if_neg h, if_neg h, Nat.add_zero]
  have hsq : (∑ q ∈ F ×ˢ F, c.count q.1 * c.count q.2) = N * N := by
    rw [Finset.sum_product, hN, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _; rw [Finset.mul_sum]
  have hdiag : (∑ q ∈ F ×ˢ F, (if q.1 = q.2 then c.count q.1 else 0)) = N := by
    rw [Finset.sum_product]
    have : ∀ a ∈ F, (∑ b ∈ F, (if a = b then c.count a else 0)) = c.count a := by
      intro a ha
      rw [Finset.sum_ite_eq F a (fun _ => c.count a), if_pos ha]
    rw [Finset.sum_congr rfl this]
  have hadd : (∑ q ∈ F ×ˢ F, c.interactionCount q.1 q.2) + N = N * N := by
    have hcollect : (∑ q ∈ F ×ˢ F, c.interactionCount q.1 q.2)
        + (∑ q ∈ F ×ˢ F, (if q.1 = q.2 then c.count q.1 else 0))
        = ∑ q ∈ F ×ˢ F, c.count q.1 * c.count q.2 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hpoint
    rw [hdiag, hsq] at hcollect; exact hcollect
  have hNval : N = posClockCount (L := L) (K := K) p c := by
    rw [hN, hF]; exact sum_count_posPhaseP p c
  rw [← hNval, Nat.mul_sub_one]
  omega

/-- A pair of distinct present states forms an applicable pair. -/
theorem pair_le_of_mem_ne {α : Type*} {c : Multiset α} {s t : α}
    (hs : s ∈ c) (ht : t ∈ c) (hne : s ≠ t) :
    ({s, t} : Multiset α) ≤ c := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hxs : x = s
  · subst x
    have hs_pos : 0 < Multiset.count s c := (Multiset.count_pos).2 hs
    simp [hne, Nat.succ_le_iff, hs_pos]
  · by_cases hxt : x = t
    · subst x
      have ht_pos : 0 < Multiset.count t c := (Multiset.count_pos).2 ht
      simp [hxs, Nat.succ_le_iff, ht_pos]
    · simp [hxs, hxt]

/-- The drop target at level `m`: configurations whose `clockCounterSumAt p` is `< m`. -/
def dropBelow (p m : ℕ) : Set (Config (AgentState L K)) :=
  {c' | clockCounterSumAt p c' < m}

/-- An APPLICABLE ordered pair of positive-counter phase-`p` clocks, scheduled on an
`AllClockGEp p` config at level `m`, lands in `dropBelow p m`.  Covers both distinct
pairs and the diagonal `(a,a)` with `count ≥ 2` (two copies of the same positive clock
state).  (`transition_pair_wtAt_lt` plus the per-pair additivity of `clockCounterSumAt`.) -/
theorem scheduledStep_posPair_in_dropBelow (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (c : Config (AgentState L K))
    (m : ℕ) (hm : clockCounterSumAt p c = m)
    {a b : AgentState L K}
    (ha : isPosPhaseP (L := L) (K := K) p a) (hb : isPosPhaseP (L := L) (K := K) p b)
    (happ : Protocol.Applicable c a b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈ dropBelow (L := L) (K := K) p m := by
  classical
  have hsub : ({a, b} : Multiset (AgentState L K)) ≤ c := happ
  have hstep : Protocol.scheduledStep (NonuniformMajority L K) c (a, b)
      = c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos happ]; rfl
  simp only [dropBelow, Set.mem_setOf_eq, hstep]
  set D : Multiset (AgentState L K) := c - {a, b} with hD
  have hcD : c = ({a, b} : Multiset (AgentState L K)) + D := by
    rw [hD, Multiset.add_comm, tsub_add_cancel_of_le hsub]
  have hsumD : ∀ X : Multiset (AgentState L K), ∀ u v : AgentState L K,
      clockCounterSumAt p (({u, v} : Multiset (AgentState L K)) + X)
        = wtAt (L := L) (K := K) p u + wtAt (L := L) (K := K) p v
          + (X.map (wtAt (L := L) (K := K) p)).sum := by
    intro X u v
    unfold clockCounterSumAt
    rw [Multiset.map_add, Multiset.sum_add]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    unfold wtAt; ring
  have hlt := transition_pair_wtAt_lt (L := L) (K := K) p hp a b ha.1 hb.1 ha.2.1 hb.2.1 ha.2.2
  rw [Multiset.add_comm D _, hsumD D (Transition L K a b).1 (Transition L K a b).2]
  rw [← hm]
  conv_rhs => rw [hcD, hsumD D a b]
  omega

/-- The positive-phase-`p` clock square rectangle, restricted to actually-present states. -/
def presentPosPairs (p : ℕ) (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  ((Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a))).filter
    (fun q => 1 ≤ c.count q.1 ∧ 1 ≤ c.count q.2)

/-- The `interactionProb`-sum over the present positive-pair square equals
`posClockCount·(posClockCount−1)/totalPairs` (absent pairs carry `interactionCount = 0`). -/
theorem sum_interactionProb_presentPosPairs (p : ℕ) (c : Config (AgentState L K)) :
    (∑ q ∈ presentPosPairs (L := L) (K := K) p c, c.interactionProb q.1 q.2)
      = (↑(posClockCount (L := L) (K := K) p c * (posClockCount (L := L) (K := K) p c - 1)) : ℝ≥0∞)
          / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ q ∈ presentPosPairs (L := L) (K := K) p c, c.interactionProb q.1 q.2)
      = ∑ q ∈ (Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a)) ×ˢ
          (Finset.univ.filter (fun a : AgentState L K => isPosPhaseP (L := L) (K := K) p a)),
          c.interactionProb q.1 q.2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq_in hqnot
    have hqnot' : ¬ (1 ≤ c.count q.1 ∧ 1 ≤ c.count q.2) := by
      intro hpres
      exact hqnot (Finset.mem_filter.mpr ⟨hq_in, hpres⟩)
    rw [not_and_or, not_le, not_le, Nat.lt_one_iff, Nat.lt_one_iff] at hqnot'
    have hcounts : c.count q.1 = 0 ∨ c.count q.2 = 0 := hqnot'
    have hzero : c.interactionCount q.1 q.2 = 0 := by
      unfold Config.interactionCount
      by_cases hqq : q.1 = q.2
      · rw [if_pos hqq]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hqq, h2, Nat.zero_mul]
      · rw [if_neg hqq]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ q : AgentState L K × AgentState L K,
      c.interactionProb q.1 q.2 = (↑(c.interactionCount q.1 q.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro q; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun q _ => heqterm q), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_posPhaseP_square, ← div_eq_mul_inv]

open Classical in
/-- The applicable subset of the present positive-pair square. -/
noncomputable def applicablePosPairs (p : ℕ) (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (presentPosPairs (L := L) (K := K) p c).filter (fun q => Protocol.Applicable c q.1 q.2)

/-- The non-applicable present positive-pairs carry zero `interactionProb`, so the sum over
the applicable subset equals the full present-square sum. -/
theorem sum_interactionProb_applicablePosPairs (p : ℕ) (c : Config (AgentState L K)) :
    (∑ q ∈ applicablePosPairs (L := L) (K := K) p c, c.interactionProb q.1 q.2)
      = (↑(posClockCount (L := L) (K := K) p c * (posClockCount (L := L) (K := K) p c - 1)) : ℝ≥0∞)
          / (c.totalPairs : ℝ≥0∞) := by
  classical
  rw [← sum_interactionProb_presentPosPairs (L := L) (K := K) p c]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq_in hqnot
  -- present but not applicable ⇒ {q.1,q.2} ⊄ c ⇒ q.1 = q.2 ∧ count = 1 ⇒ interactionCount = 0
  have hnotapp : ¬ Protocol.Applicable c q.1 q.2 := by
    intro happ
    exact hqnot (Finset.mem_filter.mpr ⟨hq_in, happ⟩)
  have hpres : 1 ≤ c.count q.1 ∧ 1 ≤ c.count q.2 :=
    (Finset.mem_filter.mp hq_in).2
  -- not applicable with both counts ≥ 1 forces q.1 = q.2 with count = 1
  have hzero : c.interactionCount q.1 q.2 = 0 := by
    by_cases hqq : q.1 = q.2
    · -- diagonal: not applicable ⇒ count q.1 < 2 ⇒ count = 1 ⇒ interactionCount = count·(count-1) = 0
      have hc1 : c.count q.1 ≤ 1 := by
        by_contra hgt
        push_neg at hgt
        refine hnotapp ?_
        show ({q.1, q.2} : Multiset (AgentState L K)) ≤ c
        rw [hqq, Multiset.le_iff_count]
        intro x; by_cases hx : x = q.2
        · subst x
          have hcnt2 : Multiset.count q.2 ({q.2, q.2} : Multiset (AgentState L K)) = 2 := by
            simp [Multiset.insert_eq_cons]
          rw [hcnt2, ← hqq]
          show 2 ≤ c.count q.1
          omega
        · simp [hx]
      have hcnt1 : c.count q.1 = 1 := by omega
      unfold Config.interactionCount; rw [if_pos hqq, hcnt1]
    · -- off-diagonal: both counts ≥ 1 ⇒ applicable, contradicting hnotapp
      exact absurd (pair_le_of_mem_ne (Multiset.count_pos.mp (by omega : 0 < c.count q.1))
        (Multiset.count_pos.mp (by omega : 0 < c.count q.2)) hqq) hnotapp
  unfold Config.interactionProb; rw [hzero]; simp

/-- `clockPairRate` is monotone in the clock count (more positive clocks ⇒ larger rate),
for `mC ≤ d ≤ n`.  Used to lower-bound the drop rate by the carried floor `mC ≤ posClockCount`. -/
theorem clockPairRate_mono_left (mC d n : ℕ) (hmCd : mC ≤ d) :
    clockPairRate mC n ≤ clockPairRate d n := by
  unfold clockPairRate
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul hmCd (by omega)

/-- **Brick 2 — the clock-clock rectangle drop mass.**  From an `AllClockGEp p` config
with `≥ 2` agents at level `clockCounterSumAt p c = m`, the one-step kernel mass on
`{clockCounterSumAt p drops below m}` is `≥ clockPairRate posClockCount n`, where
`posClockCount` counts the positive-counter phase-`p` clocks and `n = c.card`.  Each
applicable ordered pair of positive phase-`p` clocks strictly drops the sum
(`scheduledStep_posPair_in_dropBelow`); the square rectangle aggregates to
`posCount·(posCount−1)/(n(n−1))`. -/
theorem posPair_drop_prob (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card)
    (m : ℕ) (hm : clockCounterSumAt p c = m) :
    (NonuniformMajority L K).transitionKernel c (dropBelow (L := L) (K := K) p m)
      ≥ clockPairRate (posClockCount (L := L) (K := K) p c) c.card := by
  classical
  -- every applicable positive-pair lands in the drop target
  have hgood : ∀ q ∈ applicablePosPairs (L := L) (K := K) p c,
      (NonuniformMajority L K).scheduledStep c q ∈ dropBelow (L := L) (K := K) p m := by
    intro q hq
    rw [applicablePosPairs, Finset.mem_filter, presentPosPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hq
    obtain ⟨⟨⟨⟨_, ha⟩, ⟨_, hb⟩⟩, _⟩, happ⟩ := hq
    exact scheduledStep_posPair_in_dropBelow (L := L) (K := K) p hp c m hm ha hb happ
  -- kernel mass ≥ interactionPMF mass of the good finset (inline reduction)
  have hmeas : MeasurableSet (dropBelow (L := L) (K := K) p m) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hc := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure (dropBelow (L := L) (K := K) p m)
    ≥ _
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        (dropBelow (L := L) (K := K) p m)
      = (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            (dropBelow (L := L) (K := K) p m)) := by
    rw [hstepDist]
    unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hsub : (↑(applicablePosPairs (L := L) (K := K) p c) :
      Set (AgentState L K × AgentState L K))
      ⊆ (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
          (dropBelow (L := L) (K := K) p m) := by
    intro q hq
    rw [Finset.mem_coe] at hq
    exact hgood q hq
  have hmono := measure_mono (μ := (c.interactionPMF hc).toMeasure) hsub
  refine le_trans ?_ hmono
  have hfinset : (c.interactionPMF hc).toMeasure
      (↑(applicablePosPairs (L := L) (K := K) p c) :
        Set (AgentState L K × AgentState L K))
      = ∑ q ∈ applicablePosPairs (L := L) (K := K) p c, c.interactionProb q.1 q.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [hfinset, sum_interactionProb_applicablePosPairs]
  unfold clockPairRate Config.totalPairs
  exact le_refl _

/-! ## Part 8 — Real-kernel E4-ready corollaries

The engine (`timed_phase_progress_{tinyClock,bigClock}_on`) consumes `InvClosed`,
`PotNonincrOn`, and a per-level `hdrop` carrying a UNIFORM rate `clockPairRate mC n`.
We supply `Inv := AllClockGEpCard p n` (`AllClockGEp p` + fixed card `n`), which is
one-step-closed; `hmono := clockCounterSumAt_PotNonincrOn`; and discharge `hdrop` from
`posPair_drop_prob` via the carried floor `mC ≤ posClockCount p b` (the protocol-level
"clock floor", the ONE probabilistic ingredient E4 supplies — `n/5 ≤ mC ≤ posCount`
holds whp while the timed phase runs, not deterministically closed, so it enters as a
hypothesis, NOT through `InvClosed`). -/

/-- The closed engine invariant: all clocks at phase `≥ p`, fixed card `n`. -/
def AllClockGEpCard (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllClockGEp (L := L) (K := K) p c ∧ c.card = n

/-- `AllClockGEpCard p n` is one-step-support-closed (`AllClockGEp_absorbing` + card
preservation). -/
theorem AllClockGEpCard_InvClosed (p n : ℕ) (hp : 3 ≤ p) :
    Engine.InvClosed (NonuniformMajority L K).transitionKernel
      (AllClockGEpCard (L := L) (K := K) p n) := by
  classical
  intro b hb
  obtain ⟨hbGE, hbcard⟩ := hb
  show (NonuniformMajority L K).transitionKernel b
    {x | ¬ AllClockGEpCard (L := L) (K := K) p n x} = 0
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ AllClockGEpCard (L := L) (K := K) p n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  apply hbad
  refine ⟨AllClockGEp_absorbing (L := L) (K := K) p hp b c' hbGE hsupp, ?_⟩
  rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) b c' hsupp]; exact hbcard

/-- **`hdrop` discharge.**  From the carried floor `mC ≤ posClockCount p b` on every
`AllClockGEpCard p n`-state, `posPair_drop_prob` + `clockPairRate` monotonicity give the
engine's per-level drop hypothesis with the UNIFORM rate `clockPairRate mC n`. -/
theorem clockCounterSumAt_hdrop_of_floor (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (mC n : ℕ)
    (hfloor : ∀ b : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n b →
      mC ≤ posClockCount (L := L) (K := K) p b) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n b →
      clockCounterSumAt p b = m →
      (NonuniformMajority L K).transitionKernel b
          (Engine.potBelow (clockCounterSumAt p) m)ᶜ
        ≤ 1 - clockPairRate mC n := by
  classical
  intro m b hb hbm
  have hcard : b.card = n := hb.2
  by_cases hc : 2 ≤ b.card
  · have hdrop := posPair_drop_prob (L := L) (K := K) p hp b hc m hbm
    -- dropBelow p m = potBelow (clockCounterSumAt p) m
    have hset : dropBelow (L := L) (K := K) p m = Engine.potBelow (clockCounterSumAt p) m := by
      unfold dropBelow Engine.potBelow; rfl
    rw [hset] at hdrop
    -- complement mass = 1 - mass; rate floor mC ≤ posCount, n = card
    have hmeas : MeasurableSet (Engine.potBelow (clockCounterSumAt (L := L) (K := K) p) m) :=
      Engine.potBelow_measurable _ _
    rw [MeasureTheory.prob_compl_eq_one_sub hmeas]
    have hmono := clockPairRate_mono_left mC (posClockCount (L := L) (K := K) p b) b.card
      (hfloor b hb)
    -- hmono : clockPairRate mC b.card ≤ clockPairRate posCount b.card
    -- hdrop : kernel ≥ clockPairRate posCount b.card
    have hrate : clockPairRate mC n
        ≤ (NonuniformMajority L K).transitionKernel b
            (Engine.potBelow (clockCounterSumAt p) m) := by
      rw [← hcard]
      exact le_trans hmono hdrop
    exact tsub_le_tsub_left hrate 1
  · -- card < 2: the floor forces mC ≤ posCount ≤ card < 2, so mC ≤ 1 ⇒ rate numerator = 0.
    have hposle : posClockCount (L := L) (K := K) p b ≤ b.card := by
      unfold posClockCount
      exact le_trans (Multiset.countP_le_card _ _) (le_refl _)
    have hmCle : mC ≤ 1 := le_trans (hfloor b hb) (by omega)
    have hzero : clockPairRate mC n = 0 := by
      unfold clockPairRate
      have : mC * (mC - 1) = 0 := by interval_cases mC <;> rfl
      rw [this]; simp
    rw [hzero, tsub_zero]
    exact MeasureTheory.prob_le_one

/-- **Real-kernel tiny-clock corollary (E4-ready).**  On the protocol kernel, from an
`AllClockGEpCard p n`-state at level `≤ counterMax · mC`, with the carried clock floor
`mC ≤ posClockCount p b` on every invariant state (`mC ≥ 2`), the expected number of
interactions to advance the timed phase `p ∈ {0,1,5,6,7,8}` is `≤ counterMax · n²`.

All engine ingredients are discharged here: `InvClosed` (`AllClockGEpCard_InvClosed`),
`PotNonincrOn` (Brick 1), `hdrop` (Brick 2 + floor).  The SINGLE remaining input is the
protocol-level floor `hfloor` (the clock-count lower bound, supplied by E4 / Lemma 5.2). -/
theorem timed_phase_progress_real_tinyClock (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (hp3 : 3 ≤ p)
    (mC n counterMax : ℕ) (hmC : 2 ≤ mC) (hmCn : mC ≤ n) (hn : 2 ≤ n)
    (hfloor : ∀ b : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n b →
      mC ≤ posClockCount (L := L) (K := K) p b)
    (c : Config (AgentState L K)) (hInvc : AllClockGEpCard (L := L) (K := K) p n c)
    (hc : clockCounterSumAt p c ≤ counterMax * mC) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (Engine.potBelow (clockCounterSumAt p) 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) :=
  timed_phase_progress_tinyClock_on (NonuniformMajority L K).transitionKernel
    (clockCounterSumAt p) (AllClockGEpCard (L := L) (K := K) p n)
    (AllClockGEpCard_InvClosed (L := L) (K := K) p n hp3)
    (by
      -- PotNonincrOn for AllClockGEpCard follows from the AllClockGEp version
      intro b hb
      exact clockCounterSumAt_PotNonincrOn (L := L) (K := K) p hp b hb.1)
    mC n counterMax hmC hmCn hn
    (clockCounterSumAt_hdrop_of_floor (L := L) (K := K) p hp mC n hfloor)
    c hInvc hc

/-- **Real-kernel big-clock corollary (E4-ready).**  The linear bound `≤ counterMax · 11 n`
under the Lemma 5.2 big-clock floor `n/5 ≤ mC ≤ posClockCount p b` (`n ≥ 18`).  Same
discharge as the tiny-clock corollary; the only input is the protocol-level floor. -/
theorem timed_phase_progress_real_bigClock (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (hp3 : 3 ≤ p)
    (mC n counterMax : ℕ) (hfloorN : n / 5 ≤ mC) (hmCn : mC ≤ n) (hn : 18 ≤ n)
    (hfloor : ∀ b : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n b →
      mC ≤ posClockCount (L := L) (K := K) p b)
    (c : Config (AgentState L K)) (hInvc : AllClockGEpCard (L := L) (K := K) p n c)
    (hc : clockCounterSumAt p c ≤ counterMax * mC) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (Engine.potBelow (clockCounterSumAt p) 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) :=
  timed_phase_progress_bigClock_on (NonuniformMajority L K).transitionKernel
    (clockCounterSumAt p) (AllClockGEpCard (L := L) (K := K) p n)
    (AllClockGEpCard_InvClosed (L := L) (K := K) p n hp3)
    (by intro b hb; exact clockCounterSumAt_PotNonincrOn (L := L) (K := K) p hp b hb.1)
    mC n counterMax hfloorN hmCn hn
    (clockCounterSumAt_hdrop_of_floor (L := L) (K := K) p hp mC n hfloor)
    c hInvc hc

end ConditionalPhaseProgress

end ExactMajority

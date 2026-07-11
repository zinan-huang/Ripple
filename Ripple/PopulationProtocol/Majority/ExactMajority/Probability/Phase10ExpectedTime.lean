/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-10 Backup Expected Stabilization Time (Doty et al. Lemma 7.7)

The 6-state Phase-10 backup protocol stably computes majority in `O(n log n)`
*parallel* time, both in expectation and with high probability.  This file
formalizes the **expectation** bound.

## Convention (READ THIS)

All time bounds in this file are stated in **interaction counts** (= kernel
steps), NOT parallel time.  Parallel time = interactions / n, so the paper's
`O(n log n)` parallel-time statements become:

  * cancel stage (active B against active A):   `O(n²)` interactions;
  * coupon-collector stages (absorb T, convert passive):  `O(n² log n)` each.

The expected hitting time is the E1 tail-sum `expectedHitting K c Done`
(`= ∑' t, (K^t) c Doneᶜ`), which under the standard identity
`E[T] = ∑_{t≥0} P(T > t)` equals the mean number of interactions to reach the
stable set `Done`.

## Structure (three sequential coupon/cancel stages, majority case WLOG A)

1. All active-B agents cancel against active-A agents (`Phase10Transition`
   cancel reaction): with `b` active-B and `a ≥ b` active-A agents, the per-step
   cancel probability is `≥ a·b / (n·(n−1)) ≥ b / (n·(n−1))`, and the potential
   `b = activeBCount` strictly drops on each cancel.  Harmonic-free here: a crude
   `∑_{b ≤ n} (n·(n−1))/b ≤ (n·(n−1))·(H_n)` interaction bound, dominated by the
   coupon stages.
2. The active-A agents absorb all active-T agents (broadcast A): coupon-collector
   on `wrongACount`, per-step success `≥ wrongACount / (n·(n−1))`, expected
   `≤ (n·(n−1))·H_n = O(n² log n)` interactions.
3. Same shape converting passive agents.

The **generic engine** (`Coupon` section below) is the level-split coupon
bound: a `ℕ`-valued potential `Φ` non-increasing along the kernel, with a
per-level one-step strict-decrease probability `≥ p_lev`, yields
`E[T] ≤ ∑_{m < Φ c₀} (p_lev m)⁻¹` interactions.  This is the harmonic / coupon
sum.  It is built directly on E1's `expectedHitting` toolkit
(`ExpectedHitting.lean`) and the per-step progress technique of
`Phase2TimeConvergence.step_advance_prob` (one useful ordered state pair fires
with probability `interactionCount / totalPairs`).

## Status

The generic coupon engine and the per-stage potential bookkeeping are delivered
and axiom-clean.  The capstone instantiation for the real
`(NonuniformMajority L K).transitionKernel` requires the per-step progress lower
bound to be discharged against the *state-multiplicity* of `AgentState`: an
"active A" is not a single scheduler state `Λ` but a whole class of `AgentState`
records, so the single-useful-pair bound of `step_advance_prob` must be replaced
by a class-aggregated `interactionCount` lower bound.  That bridge is documented
as the remaining blocker at the end of this file (see `phase10_progress_blocker`).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase10Backup
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase0Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## Generic level-split coupon-collector hitting engine

We work over a generic measurable space `α` and a Markov kernel `K`, exactly as
in `ExpectedHitting.lean`, with a `ℕ`-valued potential `Φ`.  `Done = {Φ = 0}`.
-/

section Coupon

variable {α : Type*} [MeasurableSpace α]

/-- The "done" set of a `ℕ`-valued potential: where `Φ` has hit `0`. -/
def potDone (Φ : α → ℕ) : Set α := {x | Φ x = 0}

/-- The "above level `m`" set: where `Φ` still exceeds `m`. -/
def potAbove (Φ : α → ℕ) (m : ℕ) : Set α := {x | m < Φ x}

theorem potDone_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) :
    MeasurableSet (potDone Φ) :=
  DiscreteMeasurableSpace.forall_measurableSet _

theorem potAbove_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potAbove Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- `potDoneᶜ = {0 < Φ} = potAbove Φ 0`. -/
theorem compl_potDone (Φ : α → ℕ) : (potDone Φ)ᶜ = potAbove Φ 0 := by
  ext x; simp only [potDone, potAbove, Set.mem_compl_iff, Set.mem_setOf_eq]; omega

/-! ### Additive stage chaining

The campaign's "chaining lemma": for nested absorbing sets `Done ⊆ Mid` the
expected hitting time of `Done` splits additively into the time to reach `Mid`
plus the residual time spent in `Mid ∖ Done`.  This is the kernel-power form
`(K^t) c Doneᶜ ≤ (K^t) c Midᶜ + (K^t) c (Mid ∩ Doneᶜ)`, summed over `t`.  It lets
a multi-stage potential descent (cancel → absorb-T → convert-passive) be bounded
stage by stage. -/

/-- **Pointwise additive split through an intermediate set.** For any sets
`Done ⊆ Mid`, the not-done mass splits as not-in-`Mid` plus in-`Mid`-not-`Done`. -/
theorem bad_split_through_mid (K : Kernel α α)
    {Done Mid : Set α} (_hsub : Done ⊆ Mid) (c : α) (t : ℕ) :
    (K ^ t) c Doneᶜ ≤ (K ^ t) c Midᶜ + (K ^ t) c (Mid ∩ Doneᶜ) := by
  have hcover : (Doneᶜ : Set α) ⊆ Midᶜ ∪ (Mid ∩ Doneᶜ) := by
    intro x hx
    by_cases hxM : x ∈ Mid
    · exact Or.inr ⟨hxM, hx⟩
    · exact Or.inl hxM
  calc (K ^ t) c Doneᶜ
      ≤ (K ^ t) c (Midᶜ ∪ (Mid ∩ Doneᶜ)) := measure_mono hcover
    _ ≤ (K ^ t) c Midᶜ + (K ^ t) c (Mid ∩ Doneᶜ) := measure_union_le _ _

/-- **Expected-hitting additive split.** `Done ⊆ Mid` gives
`E[hit Done] ≤ E[hit Mid] + ∑ₜ P(in Mid, not Done at t)`. -/
theorem expectedHitting_le_through_mid (K : Kernel α α)
    {Done Mid : Set α} (hsub : Done ⊆ Mid) (c : α) :
    expectedHitting K c Done ≤
      expectedHitting K c Mid + ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) := by
  rw [expectedHitting, expectedHitting, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (fun t => bad_split_through_mid K hsub c t)

/-! ### Level occupation from a constrained start (coupon-collector core)

The single rigorous waiting-time fact behind the coupon sum: if the potential
never increases along `K` and from every state at level exactly `m` (`Φ = m`,
`m ≥ 1`) the one-step probability of dropping to `Φ < m` is at least `1 - q`
(`q < 1`), then starting **at or below level `m`** the expected time to hit
`{Φ < m}` is `≤ (1 - q)⁻¹`.

The trick: starting at `Φ ≤ m`, the chain stays in `{Φ ≤ m}` (`Φ` non-increasing),
so the "not yet below `m`" event coincides with the level-`m` event, on which the
per-step drop hypothesis applies uniformly.  We instantiate E1's
`expectedHitting_one_step_q` with `Done := {Φ < m}` after transporting the start
into `{Φ ≤ m}`. -/

/-- The set of states strictly below level `m`. -/
def potBelow (Φ : α → ℕ) (m : ℕ) : Set α := {x | Φ x < m}

theorem potBelow_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potBelow Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- Kernel-level "potential non-increasing" hypothesis: one step never strictly
raises `Φ` (the mass placed on strictly-higher potential is `0`). -/
def PotNonincr (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, K b {x | Φ b < Φ x} = 0

/-- `{Φ < m}` is absorbing when `Φ` is non-increasing: from a state already below
`m`, one step cannot reach `{Φ ≥ m}`. -/
theorem potBelow_absorbing [DiscreteMeasurableSpace α]
    (K : Kernel α α) (Φ : α → ℕ) (hmono : PotNonincr K Φ) (m : ℕ) :
    ∀ x ∈ potBelow Φ m, K x (potBelow Φ m)ᶜ = 0 := by
  intro x hx
  -- (potBelow Φ m)ᶜ = {Φ ≥ m} ⊆ {Φ > Φ x} since Φ x < m.
  have hsub : ((potBelow Φ m)ᶜ : Set α) ⊆ {y | Φ x < Φ y} := by
    intro y hy
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy
    have hxlt : Φ x < m := hx
    exact Set.mem_setOf_eq ▸ (lt_of_lt_of_le hxlt hy)
  exact measure_mono_null hsub (hmono x)

/-- The `(K^t)`-mass on strictly-above-`m` stays `0` for a start at level `≤ m`. -/
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
        -- complement is {Φ > m}; one step from c (Φ c ≤ m) cannot reach it.
        have hcompl : ({y | Φ y ≤ m}ᶜ : Set α) = {x | m < Φ x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        rw [hcompl]
        refine measure_mono_null ?_ (hmono c)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        exact ih y hy

/-- **One-step level-`m` occupation contraction.** Under non-increasing `Φ` and a
per-step drop hypothesis at level `m` (`∀ b, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q`),
for a start `c` with `Φ c ≤ m` the not-below-`m` mass contracts by `q` each step:
`(K^(t+1)) c (potBelow Φ m)ᶜ ≤ q · (K^t) c (potBelow Φ m)ᶜ`. -/
theorem level_occ_contract [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ (t + 1)) c (potBelow Φ m)ᶜ ≤ q * (K ^ t) c (potBelow Φ m)ᶜ := by
  classical
  have hbad : MeasurableSet ((potBelow Φ m)ᶜ : Set α) :=
    (potBelow_measurable Φ m).compl
  -- Peel last step: (K^(t+1)) c Bᶜ = ∫ b, K b Bᶜ ∂(K^t c).
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  -- The (K^t c)-mass lives on {Φ = m} ∪ {Φ < m}; on {Φ < m}, Bᶜ-reach is 0
  -- (absorbing); on {Φ = m}, K b Bᶜ ≤ q; {Φ > m} carries 0 mass.
  calc ∫⁻ b, K b (potBelow Φ m)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potBelow Φ m)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        -- a.e. b: handle by cases on Φ b vs m, using that {Φ > m} is null.
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
          · -- Φ b < m: b ∈ potBelow, absorbing ⇒ K b Bᶜ = 0 ≤ q·indicator
            have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing K Φ hmono m b hbb]; exact zero_le'
          · -- Φ b = m: b ∉ potBelow (since not < m), so indicator = 1.
            have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
              simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
              exact heq.ge
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hdrop b heq
    _ = q * (K ^ t) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- Geometric decay of the level-`m` occupation mass: `(K^t) c (potBelow Φ m)ᶜ ≤ q^t`
for a start `c` at level `≤ m`. -/
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

/-- **Level-`m` occupation bound (coupon waiting time).** Under non-increasing `Φ`
and a level-`m` per-step drop probability `≥ 1 - q`, a start at level `≤ m` hits
`{Φ < m}` in expected time `≤ (1 - q)⁻¹`:
`expectedHitting K c (potBelow Φ m) ≤ (1 - q)⁻¹`. -/
theorem level_occ_expectedHitting [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) :
    expectedHitting K c (potBelow Φ m) ≤ (1 - q)⁻¹ := by
  rw [expectedHitting]
  calc ∑' t : ℕ, (K ^ t) c (potBelow Φ m)ᶜ
      ≤ ∑' t : ℕ, q ^ t :=
        ENNReal.tsum_le_tsum (fun t => level_occ_geometric K Φ hmono m q hdrop c hc t)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-! ### Full coupon assembly (harmonic sum)

Chaining the per-level occupation bound down the potential ladder gives the total
expected hitting time of `Done = {Φ = 0}` as the sum of the per-level waiting
times `∑_{m=1}^{M} (1 - q_m)⁻¹`.  This is the harmonic / coupon sum: for the
Phase-10 coupon stages `q_m = 1 - m/(n(n−1))`, so `(1-q_m)⁻¹ = n(n−1)/m` and the
sum is `n(n−1)·H_M = O(n² log n)` interactions.

The chaining is downward induction on the level gap, peeling one level per step
via `expectedHitting_le_through_mid`: hitting `{Φ < m}` from a start at level
`≤ M` costs the level-`M` waiting time plus hitting `{Φ < m}` from the next level
down.  We package the per-level drop hypotheses as a single family `q : ℕ → ℝ≥0∞`
with `hdrop : ∀ m b, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m`. -/

/-- The level-`m` occupation along the chain from `c`:
`occLevel K Φ m c = ∑' t, P(Φ = m at time t)`. -/
noncomputable def occLevel (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (c : α) : ℝ≥0∞ :=
  ∑' t : ℕ, (K ^ t) c {x | Φ x = m}

/-- The expected hitting time of `Done = {Φ = 0}` decomposes as the sum of the
per-level occupations over the active levels `1, 2, …`:
`expectedHitting K c (potBelow Φ 1) = ∑' m, occLevel K Φ (m+1) c`.

This is the exact occupation decomposition (`{Φ ≥ 1} = ⨆ₘ {Φ = m+1}` disjointly),
the bookkeeping skeleton of the coupon sum.  Bounding each `occLevel K Φ m c` by
the per-level waiting time `(1 - q m)⁻¹` (the strong-Markov restart, see
`occLevel_le_blocker`) then yields the harmonic bound. -/
theorem expectedHitting_eq_tsum_occLevel [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (c : α) :
    expectedHitting K c (potBelow Φ 1) = ∑' m : ℕ, occLevel K Φ (m + 1) c := by
  simp only [expectedHitting, occLevel]
  -- ∑'_t (K^t)c (potBelow Φ 1)ᶜ  and  ∑'_m ∑'_t (K^t)c {Φ = m+1}
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun t => ?_)
  -- For each t: (K^t)c {Φ ≥ 1} = ∑'_m (K^t)c {Φ = m+1}.
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

/-- **Coupon assembly (modulo the level-occupation bound).**  Given the
per-level occupation bound `hocc : ∀ m, 1 ≤ m → m ≤ M → occLevel K Φ m c ≤ (1-q m)⁻¹`
and that levels above `M` are unreached (`hhi : ∀ m, M < m → occLevel K Φ m c = 0`),
the expected hitting time of `Done` is `≤ ∑_{m=1}^{M} (1-q m)⁻¹`.

This is the pure bookkeeping step: it turns the occupation decomposition into the
finite harmonic sum.  Discharging `hocc` is the remaining strong-Markov restart
(documented as `occLevel_le_blocker`); `hhi` follows from `Φ c ≤ M` +
`pow_above_eq_zero_of_start_le`. -/
theorem coupon_expectedHitting_le_of_occBounds [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (q : ℕ → ℝ≥0∞) (M : ℕ) (c : α)
    (hocc : ∀ m : ℕ, 1 ≤ m → m ≤ M → occLevel K Φ m c ≤ (1 - q m)⁻¹)
    (hhi : ∀ m : ℕ, M < m → occLevel K Φ m c = 0) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ := by
  rw [expectedHitting_eq_tsum_occLevel K Φ c]
  -- ∑'_m occLevel (m+1) = ∑_{m=1}^{M} occLevel m  (tail vanishes by hhi)
  rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
    rw [Finset.mem_range, not_lt] at hm
    exact hhi (m + 1) (by omega))]
  -- reindex range M (m ↦ m+1) to Icc 1 M
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

/-! ### Arbitrary-start level occupation (the strong-Markov restart, formalized)

We now discharge the per-level occupation bound

  `occLevel K Φ m c ≤ (1 - q m)⁻¹`   for **arbitrary** start `c`  (∗)

required by `coupon_expectedHitting_le_of_occBounds`.

The constrained case `Φ c ≤ m` is immediate from `level_occ_geometric`
(`{Φ = m} ⊆ (potBelow Φ m)ᶜ`, geometric decay, geometric series).  The arbitrary
case is the **first-passage restart**: from a start `Φ c > m` the time-0 level-`m`
mass is `0`, and one Chapman-Kolmogorov step pushes the whole occupation onto the
one-step successors, where the bound holds by induction.  We avoid a pathwise
strong-Markov statement by inducting on a **time-truncated** occupation
`∑_{i<t} (K^i) c {Φ = m}` (a uniform-in-`c` bound for every truncation `t`), then
passing to the `tsum` limit.  No measure-theoretic first-passage σ-algebra is
needed — only the kernel Chapman-Kolmogorov identity and a Markov-kernel
`∫ const = const`. -/

/-- **Constrained-start level occupation.** For a start at level `≤ m`, the
level-`m` occupation is bounded by the per-level waiting time `(1 - q)⁻¹`.  Direct
from geometric decay: `{Φ = m} ⊆ (potBelow Φ m)ᶜ` and `(K^t) c (potBelow Φ m)ᶜ ≤ qᵗ`. -/
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

/-- The **time-truncated** level-`m` occupation: the partial sum of the level-`m`
masses over the first `t` steps. -/
noncomputable def occLevelUpTo (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (t : ℕ) (c : α) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, (K ^ i) c {x | Φ x = m}

/-- **Uniform truncated bound (the strong-Markov restart, truncated form).** For
*every* truncation `t` and *every* start `c`, the truncated level-`m` occupation is
`≤ (1 - q)⁻¹`.  Proof by induction on `t`, splitting on `Φ c ≤ m` (constrained
bound, no IH) vs `Φ c > m` (the time-0 term vanishes, then one Chapman-Kolmogorov
step pushes the remaining sum onto successors where the IH applies, integrated
against the Markov kernel `K c`). -/
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
      · -- Constrained start: truncated sum ≤ full occupation ≤ (1-q)⁻¹.
        calc occLevelUpTo K Φ m (t + 1) c
            ≤ occLevel K Φ m c := by
              rw [occLevelUpTo, occLevel]; exact ENNReal.sum_le_tsum _
          _ ≤ (1 - q)⁻¹ := occLevel_le_of_start_le K Φ hmono m q hdrop c hc
      · -- Φ c > m: the i = 0 term is 0; peel it and reindex i ↦ j+1.
        rw [not_le] at hc  -- m < Φ c
        have hmeasm : MeasurableSet {x : α | Φ x = m} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        -- (K^0) c {Φ = m} = 0 since Φ c ≠ m.
        have hzero : (K ^ 0) c {x | Φ x = m} = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hmeasm]
          have : c ∉ {x : α | Φ x = m} := by
            simp only [Set.mem_setOf_eq]; omega
          simp [this]
        -- Truncated sum over range (t+1): drop i=0, reindex i = j+1.
        have hsplit : occLevelUpTo K Φ m (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c {x | Φ x = m} := by
          rw [occLevelUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        -- Chapman-Kolmogorov per term: (K^(j+1)) c S = ∫ b, (K^j) b S ∂(K c).
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c {x | Φ x = m}
            = ∫⁻ b, (K ^ j) b {x | Φ x = m} ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hmeasm, pow_one]
        simp only [hCK]
        -- Pull the finite sum inside the integral: ∑_j ∫ f_j = ∫ ∑_j f_j.
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hmeasm)]
        -- The integrand ∑_{j<t} (K^j) b {Φ = m} = occLevelUpTo … t b ≤ (1-q)⁻¹ (IH),
        -- so the integral is ≤ (1-q)⁻¹ · (K c)(univ) = (1-q)⁻¹ (Markov kernel).
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b {x | Φ x = m}) ∂(K c)
            ≤ ∫⁻ _ : α, (1 - q)⁻¹ ∂(K c) := by
              apply lintegral_mono
              intro b
              simpa only [occLevelUpTo] using ih b
          _ = (1 - q)⁻¹ := by
              rw [lintegral_const, measure_univ, mul_one]

/-- **Arbitrary-start level occupation bound (∗).** For *any* start `c`, the
level-`m` occupation is bounded by the per-level waiting time `(1 - q)⁻¹`.  The
truncated occupations `occLevelUpTo … t c` are uniformly `≤ (1-q)⁻¹`
(`occLevelUpTo_le`) and increase to `occLevel … c` (partial sums of a nonnegative
series), so their `tsum` limit inherits the bound.  This is the strong-Markov
first-passage restart, discharged via the time-truncation + Chapman-Kolmogorov
route, and closes the last brick of the coupon engine. -/
theorem occLevel_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  -- occLevel = tsum = ⨆ truncations; each truncation ≤ (1-q)⁻¹.
  rw [occLevel, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  exact occLevelUpTo_le K Φ hmono m q hdrop t c

/-- High levels carry no occupation from a start at level `≤ M`: for `M < m`,
`occLevel K Φ m c = 0`.  Immediate from `pow_above_eq_zero_of_start_le`
(`{Φ = m} ⊆ {M < Φ}` is null at every time for a start with `Φ c ≤ M`). -/
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

/-- **Generic coupon capstone (fully discharged).** Under non-increasing `Φ`, a
per-level drop family `q : ℕ → ℝ≥0∞` with `K b (potBelow Φ m)ᶜ ≤ q m` at every
level-`m` state, and a start `c` at level `≤ M`, the expected hitting time of
`Done = {Φ < 1} = {Φ = 0}` is bounded by the harmonic coupon sum
`∑_{m=1}^{M} (1 - q m)⁻¹`.

This is `coupon_expectedHitting_le_of_occBounds` with both hypotheses discharged:
`hocc` by the arbitrary-start `occLevel_le` and `hhi` by `occLevel_eq_zero_of_high`.
It is the protocol-agnostic `O(coupon sum)` interaction-count bound; the Phase-10
stages instantiate it with `q m = 1 - m/(n(n-1))`. -/
theorem coupon_expectedHitting_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ :=
  coupon_expectedHitting_le_of_occBounds K Φ q M c
    (fun m _ _ => occLevel_le K Φ hmono m (q m) (hdrop m) c)
    (fun m hm => occLevel_eq_zero_of_high K Φ hmono M c hc m hm)

/-! ### Harmonic / coupon-sum evaluation (generic bookkeeping)

The capstone RHS is the coupon sum `∑_{m=1}^{M} (1 - q m)⁻¹`.  For the Phase-10
shape `(1 - q m)⁻¹ = n(n-1)/m`, the exact value is `n(n-1)·H_M`, but the engine
only needs an upper bound.  We record the crude per-level-uniform bound: if every
active level's waiting time is `≤ r`, the sum is `≤ M·r` (here `r = n(n-1)` since
`n(n-1)/m ≤ n(n-1)` for `m ≥ 1`), which already gives the `O(n²·M)` interaction
count; for the coupon stages `M = O(n)`, i.e. `O(n³)`, dominated by — and in the
paper sharpened to — the `n(n-1)·H_n = O(n² log n)` harmonic form.  The crude
bound is what the chained stage argument consumes; recorded here so the harmonic
constant is not on the critical path. -/

/-- **Crude coupon-sum bound.** If every active-level waiting time `(1 - q m)⁻¹`
(`1 ≤ m ≤ M`) is bounded by a common `r`, then the coupon sum is `≤ M · r`.  Feeds
the capstone RHS with `r = (per-level waiting-time ceiling) = n(n-1)`. -/
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

/-- **Generic coupon capstone with crude harmonic evaluation.** Combines
`coupon_expectedHitting_le` with `coupon_sum_le_of_uniform`: under the engine
hypotheses plus a uniform per-level waiting-time ceiling `r`, the expected hitting
time of `Done = {Φ = 0}` is `≤ M · r` interactions.  For the Phase-10 coupon
stages (`M = O(n)`, `r = n(n-1)`) this is the `O(n³)` crude form; the harmonic
`O(n² log n)` is a constant sharpening orthogonal to the engine. -/
theorem coupon_expectedHitting_le_uniform [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    expectedHitting K c (potBelow Φ 1) ≤ (M : ℝ≥0∞) * r :=
  le_trans (coupon_expectedHitting_le K Φ hmono q hdrop M c hc)
    (coupon_sum_le_of_uniform q M r hq)

/-! ## Invariant-relative coupon engine (Brick B1 generic infrastructure)

The Phase-10 stage potentials (`activeBCount`, `wrongACount`) are **not**
non-increasing on the full `NonuniformMajority` kernel: a pre-phase-10 reaction
(`enterPhase10`, epidemic entry) can create active-B agents or un-A an A.  The
per-pair non-increase holds only when both interacting agents are already in phase
10, i.e. on the **all-phase-10 subdynamics**.

We thread an abstract invariant `Inv : α → Prop` through the engine.  Two abstract
hypotheses suffice and are both discharged for `Inv = Phase10EpidemicPost` by the
existing support-closure machinery:

* **`InvClosed K Inv`** — `Inv` is `K`-support-closed: from an `Inv`-state, one step
  almost surely stays in `Inv` (`K b {¬ Inv} = 0`).  (For the protocol kernel this
  is `Phase10EpidemicPost` preservation: phases only increase and 10 is the max.)
* **`PotNonincrOn Inv K Φ`** — `Φ` is non-increasing from every `Inv`-state:
  `K b {Φ b < Φ x} = 0` for all `b` with `Inv b`.  (The per-pair bound on the
  phase-10-restricted transition.)

Carrying `Inv` a.e. along the kernel powers (every reachable state from an
`Inv`-start satisfies `Inv`), the level-occupation contraction goes through with the
drop hypothesis only required at `Inv`-states.  All engine theorems below mirror
their unconditional counterparts; the proofs differ only by intersecting the
relevant null sets with `{¬ Inv}` (which is itself null). -/

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

/-- **Invariant-relative absorption of `{Φ < m}`.** From an `Inv`-state below level
`m`, one step cannot reach `{Φ ≥ m}` (using the drop hypothesis at that state). -/
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
      -- Stay in {Φ ≤ m} ∩ Inv: one step from an Inv-state at level ≤ m.
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
        -- one step from c (Inv c, Φ c ≤ m) cannot reach {Φ > m}
        refine measure_mono_null ?_ (hmono c hInvc)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hy
        exact ih y hy.1 hy.2

/-- **Invariant-relative one-step level-`m` occupation contraction.** Mirrors
`level_occ_contract`, but the drop hypothesis is only needed at `Inv`-level-`m`
states, and the start must satisfy `Inv`.  The `(K^t c)`-mass lives a.e. on
`{Φ ≤ m} ∩ Inv`: on `{Φ < m} ∩ Inv` the reach of `(potBelow Φ m)ᶜ` is `0`
(invariant-relative absorption); on `{Φ = m} ∩ Inv` it is `≤ q`; the rest
(`{Φ > m}` and `¬ Inv`) carries `0` mass. -/
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
        -- a.e. b lives in {Φ ≤ m} ∩ Inv.
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
          · -- Φ b < m: b ∈ potBelow, Inv b, absorbing ⇒ K b Bᶜ = 0
            have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing_on K Inv Φ hmono m b hbb hbInv]; exact zero_le'
          · -- Φ b = m: b ∉ potBelow, so indicator = 1, and K b Bᶜ ≤ q.
            have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
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

/-- **Invariant-relative constrained-start level occupation.** For an `Inv`-start at
level `≤ m`, the level-`m` occupation is `≤ (1 - q)⁻¹`. -/
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

/-- **Invariant-relative uniform truncated occupation bound.** For *every* truncation
`t` and *every* `Inv`-start `c`, the truncated level-`m` occupation is `≤ (1 - q)⁻¹`.
Mirrors `occLevelUpTo_le`: split on `Φ c ≤ m` (constrained, no IH) vs `Φ c > m`
(time-0 term vanishes, then one Chapman-Kolmogorov step pushes onto successors —
which satisfy `Inv` a.e. by `InvClosed`, so the IH applies under the integral). -/
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
        -- a.e. b under (K c) satisfies Inv (InvClosed); on those the IH applies.
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

/-- **Invariant-relative arbitrary-start level occupation bound.** For any `Inv`-start
`c`, the level-`m` occupation is `≤ (1 - q)⁻¹`.  The truncated occupations are
uniformly bounded and increase to `occLevel`. -/
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

/-- **Invariant-relative high-level vanishing.** For an `Inv`-start at level `≤ M`,
levels above `M` carry no occupation. -/
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

/-- **Invariant-relative coupon capstone (fully discharged).** The all-phase-10
analogue of `coupon_expectedHitting_le`: under `InvClosed K Inv`, `PotNonincrOn Inv
K Φ`, a per-level drop family `q` (required only at `Inv`-states), an `Inv`-start `c`
at level `≤ M`, the expected hitting time of `Done = {Φ = 0}` is `≤
∑_{m=1}^{M} (1 - q m)⁻¹`. -/
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

/-- **Invariant-relative coupon capstone with crude harmonic evaluation.** The
`_on` analogue of `coupon_expectedHitting_le_uniform`: under the invariant-relative
engine hypotheses plus a uniform per-level ceiling `r`, the expected hitting time of
`Done = {Φ = 0}` is `≤ M · r`. -/
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

/-! ### Phase-10 instantiation target

For the real protocol `K := (NonuniformMajority L K).transitionKernel` and the
stage potentials of `Analysis/Phase10Backup.lean`:

* **cancel stage** `Φ := activeBCount` (majority A case): `Done = {activeBCount = 0}`;
* **absorb-T stage** `Φ := wrongACount` after `activeBCount = 0`;
* **convert-passive stage** `Φ := wrongACount` (passive recount).

**Generic engine: fully closed (E2-6/7/8).**  `coupon_expectedHitting_le_uniform`
takes exactly `(PotNonincr K Φ)`, `(hdrop : ∀ m b, Φ b = m → K b (potBelow Φ m)ᶜ ≤
q m)`, `(Φ c ≤ M)`, and a uniform per-level ceiling `r` (`(1 - q m)⁻¹ ≤ r`), and
returns `expectedHitting K c (potBelow Φ 1) ≤ M·r` — no residual hypotheses.  Only
the THREE protocol facts below remain, all in `Analysis/Phase10Backup.lean` land:

1. `PotNonincr K Φ`, i.e. `∀ c, K c {c' | Φ c < Φ c'} = 0`.  Via the established
   support template (`Phase0Convergence.phaseBelowCount_step_le` / `mcrCount_step_le`):
   `c' ∈ (stepDistOrSelf c).support` ⇒ `Protocol.stepDist_support` peels a pair
   `(r₁,r₂)`, `Φ c' = Φ(c-{r₁,r₂}) + Φ{Transition r₁ r₂}` (countP additivity,
   `Multiset.countP_add`), so it reduces to the **per-pair bound**
   `Φ{Transition r₁ r₂} ≤ Φ{r₁,r₂}` (a `Transition_activeBCount_le` /
   `Transition_wrongACount_le`, the analogue of `Transition_phaseBelowCount_le`).
   **SCOPING CAVEAT (precise):** this per-pair bound is FALSE for the *full*
   `NonuniformMajority` kernel — pre-phase-10 reactions (`enterPhase10`, epidemic
   entry) DO create active-B / un-A an A.  So `PotNonincr` holds only on the
   **phase-10-restricted** subdynamics.  The honest discharge is either (a) run the
   stages on the absorbed/restricted kernel where every reachable config satisfies
   the all-phase-10 invariant (`backupSignal_of_all_phase10` regime), proving the
   per-pair bound under `IsActiveX`-typed hypotheses on `r₁,r₂`; or (b) thread an
   all-phase-10 invariant `J` through a `PotNonincr`-relative-to-`J` variant of the
   engine.  This invariant-threading is the first genuine instantiation brick.
2. the per-level drop `K c (potBelow Φ m)ᶜ ≤ q m` with `q m = 1 - m/(n(n−1))`.  The
   useful-interaction probability is `≥ (class interactionCount)/(n(n−1))`; with `m`
   active-B and `≥ 1` active-A (from `exists_activeA_of_phase10ActiveSignedSum_pos`
   in the majority-A case), the class count is `≥ m`.  **State-multiplicity subtlety
   (precise):** `step_advance_prob` is proven over `Bool` for a single fixed pair
   `(true,false)`; here "active A" / "active B" are *classes* of `AgentState`
   records, so the single-pair mass bound must be aggregated over the
   active-A × active-B class.  This needs (i) the real-kernel analogue of
   `step_advance_prob` (the `interactionPMF (r₁,r₂)` mass lower bound for an
   applicable `AgentState` pair, following the `stepDist = map scheduledStep
   interactionPMF` route used in `ClockOLogN`/`ClockFaithful`), and (ii) summing
   that mass over the `Finset` of present useful pairs via `interactionPMF`/`countP`
   additivity to reach `≥ m/(n(n−1))`.  This is the second (largest) brick.
3. the harmonic evaluation — DONE generically: `coupon_sum_le_of_uniform` gives the
   crude `M·r = O(n³)`; the sharp `n(n−1)·H_n = O(n² log n)` is a constant
   refinement of the same Icc sum (`∑ 1/m`), orthogonal to the engine.

The three stages are then chained by `expectedHitting_le_through_mid`
(majority/tie case split via `Phase10Backup.backupSignal` sign), giving the
Lemma 7.7 expectation bound in interaction counts.  Remaining work = bricks 1 and 2
above (invariant-threading + class-aggregated probability), both PURELY protocol
instantiation; the probability/coupon engine carries no further obligation. -/

end Coupon

/-! ## Phase-10 per-level drop probability (Brick B2)

We instantiate the per-level drop hypothesis of the invariant-relative engine for
the real kernel `K = (NonuniformMajority L K).transitionKernel` and `Φ =
activeBCount` on the all-phase-10 invariant `Inv = Phase10EpidemicPost`.

The route is the one used by `Invariants.phase10_descent_prob`: the public helper
`Phase0Convergence.stepDistOrSelf_toMeasure_ge` reduces a kernel-mass lower bound on
a target set to the `interactionPMF` mass of a `good` Finset of ordered pairs that
land in the target.  Each ordered pair `(a, b)` with `a` active-A and `b` active-B
fires the Phase-10 cancel reaction, which strictly lowers `activeBCount` (so it
lands in the drop target).  Aggregating over the `m` distinct active-B agents
(paired with one fixed active-A) gives mass `≥ m / (n(n−1))`. -/

namespace Phase10Drop

open MeasureTheory ProbabilityTheory

variable {L K : ℕ}

/-- The drop target set for a potential `Φ` at a base configuration `c`:
configurations whose `Φ`-value is strictly smaller than `Φ c`. -/
def dropTarget (Φ : Config (AgentState L K) → ℕ) (c : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {c' | Φ c' < Φ c}

/-- Re-derivation of applicability from membership + distinctness (the public
analogue of the `Analysis`-private `applicable_of_mem_ne'`). -/
theorem applicable_of_mem_ne {c : Config (AgentState L K)} {a b : AgentState L K}
    (ha : a ∈ c) (hb : b ∈ c) (hne : a ≠ b) :
    Protocol.Applicable c a b := by
  have hnot : a ∉ ({b} : Multiset (AgentState L K)) := by simp [hne]
  change a ::ₘ ({b} : Multiset (AgentState L K)) ≤ c
  rw [Multiset.cons_le_of_notMem hnot]
  exact ⟨ha, Multiset.singleton_le.2 hb⟩

/-- The `activeBCount` of the post-cancel configuration is strictly below the base
`activeBCount`, for an active-A / active-B ordered pair on an all-phase-10 config.
Re-derived in-file from the public output characterization
`Phase10Transition_activeA_activeB_outputs_T`. -/
theorem activeBCount_post_cancel_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveB b) :
    activeBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeBCount c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .B := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  -- activeBCount {a,b} = 1 (only b is active-B).
  have hpair_before :
      Multiset.countP IsActiveB ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveB (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad
      have : a.output = .B := hbad.2
      rw [ha.2] at this; exact absurd this (by decide)
  -- both outputs become T after cancel, so activeBCount of the pair becomes 0.
  have hlocal :=
    Phase10Transition_activeA_activeB_outputs_T
      (L := L) (K := K) a b ha.1 hb.1 ha.2 hb.2
  have hpair_after :
      Multiset.countP IsActiveB
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out, _h1full, _h2full⟩
    change Multiset.countP IsActiveB
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        have : (Phase10Transition L K a b).2.output = .B := hbad.2
        rw [h2out] at this; exact absurd this (by decide)
    · intro hbad
      have : (Phase10Transition L K a b).1.output = .B := hbad.2
      rw [h1out] at this; exact absurd this (by decide)
  have hres :
      Multiset.countP IsActiveB (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP IsActiveB c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveB
    rw [hsub, hpair_before]
  have hpos_old : 0 < Multiset.countP IsActiveB c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb
  unfold activeBCount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- A single active-A / active-B ordered pair, scheduled on an all-phase-10
configuration, lands in the `activeBCount`-drop target. -/
theorem scheduledStep_activeA_activeB_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveB b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (activeBCount (L := L) (K := K)) c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .B := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact activeBCount_post_cancel_lt c hphase ha_mem hb_mem ha hb

/-- The active-A × active-B rectangle of ordered pairs. -/
def activeABPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveA a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => IsActiveB a))

/-- The total `interactionCount` over the active-A × active-B rectangle equals
`activeACount c · activeBCount c`.  Active-A and active-B states are disjoint
classes, so the cross-rectangle identity `sum_interactionCount_cross_disjoint`
applies, and each row/column sum of `count` is the respective `countP`. -/
theorem sum_interactionCount_activeAB (c : Config (AgentState L K)) :
    (∑ p ∈ activeABPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeACount c * activeBCount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    have : a.output = .B := hb.2.2
    rw [ha.2.2] at this; exact absurd this (by decide)
  rw [activeABPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a), c.count a)
      = Multiset.countP IsActiveA c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveA c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), c.count b)
      = Multiset.countP IsActiveB c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveB c).symm]
  rfl

/-- The present active-A × active-B pairs (those with both states actually present
in `c`). -/
def presentActiveABPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeABPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-A × active-B pairs equals the
full-rectangle sum (absent pairs have `interactionCount = 0`), which by
`sum_interactionCount_activeAB` is `activeACount · activeBCount / totalPairs`. -/
theorem sum_interactionProb_presentActiveAB (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveABPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = (↑(activeACount c * activeBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  -- present-pair sum = full rectangle sum (drop absent pairs: interactionProb 0)
  have hpresent : (∑ p ∈ presentActiveABPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeABPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveABPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    -- p ∈ activeABPairs but not in present-filter ⇒ some count is 0
    rw [presentActiveABPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  -- full-rectangle interactionProb sum = (∑ interactionCount) / totalPairs
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeAB, ← div_eq_mul_inv]

/-- **Cancel-stage per-level drop probability.** On an all-phase-10 configuration
with at least one active-A agent (the majority-A regime), the transition kernel
maps into the `activeBCount`-drop set with probability `≥ activeBCount c /
(n·(n−1))`.  This is the per-level drop lower bound consumed by the
invariant-relative engine with `q m = 1 − m/(n(n−1))`. -/
theorem activeBCount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hA : 1 ≤ activeACount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeBCount (L := L) (K := K)) c) ≥
      (↑(activeBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  -- every present active-A × active-B pair lands in the drop target
  have hgood : ∀ pair ∈ presentActiveABPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeBCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveABPairs, activeABPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hA1⟩, ⟨_, hB2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeA_activeB_in_drop c hphase ha_mem hb_mem hA1 hB2
    simpa using this
  -- kernel mass ≥ interactionPMF mass of the good Finset
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeBCount (L := L) (K := K)) c)
    (↑(presentActiveABPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  -- the interactionPMF mass of the Finset = the interactionProb sum
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveABPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveABPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveAB] at hSmeasure
  change (NonuniformMajority L K).transitionKernel c _ ≥ _
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  -- activeBCount / totalPairs ≤ activeACount·activeBCount / totalPairs (activeACount ≥ 1)
  apply ENNReal.div_le_div_right
  have : activeBCount c ≤ activeACount c * activeBCount c := by
    calc activeBCount c = 1 * activeBCount c := (Nat.one_mul _).symm
      _ ≤ activeACount c * activeBCount c := Nat.mul_le_mul_right _ hA
  exact_mod_cast this

/-- **Cancel-stage rectangle drop probability.** The *full* active-A×active-B
rectangle mass: on an all-phase-10 configuration the kernel maps into the
`activeBCount`-drop set with probability `≥ activeACount·activeBCount /
(n·(n−1))`.  This is the un-truncated rate (the `activeBCount_drop_prob` above
specialises `activeACount ≥ 1`); the harmonic refinement specialises instead
`activeACount ≥ activeBCount` to get the `m²` rate. -/
theorem activeBCount_drop_prob_rect (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeBCount (L := L) (K := K)) c) ≥
      (↑(activeACount c * activeBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveABPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeBCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveABPairs, activeABPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hA1⟩, ⟨_, hB2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeA_activeB_in_drop c hphase ha_mem hb_mem hA1 hB2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeBCount (L := L) (K := K)) c)
    (↑(presentActiveABPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveABPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveABPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveAB] at hSmeasure
  change (NonuniformMajority L K).transitionKernel c _ ≥ _
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  exact hge

/-- **Cancel-stage quadratic per-level drop probability.** Under the majority
regime `activeBCount ≤ activeACount` (signed sum `≥ 0`), the kernel maps into the
`activeBCount`-drop set with probability `≥ (activeBCount c)² / (n·(n−1))`.  This
is the `m²`-rate the cancel stage really enjoys (`m` active-B against `≥ m`
active-A), giving the `∑ P/m² ≤ 2P = O(n²)` cancel cost. -/
theorem activeBCount_drop_prob_sq (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hAB : activeBCount c ≤ activeACount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeBCount (L := L) (K := K)) c) ≥
      (↑(activeBCount c ^ 2) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  refine le_trans ?_ (activeBCount_drop_prob_rect c hc hphase)
  apply ENNReal.div_le_div_right
  have : activeBCount c ^ 2 ≤ activeACount c * activeBCount c := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ hAB
  exact_mod_cast this

/-! ### Mirrored cancel stage (`activeACount`, majority-B case)

The B-majority branch is the exact A/B mirror of the preceding cancel stage:
an active-B meeting an active-A cancels both active sources to `T`, strictly
lowering `activeACount`. -/

/-- The `activeACount` of the post-cancel configuration is strictly below the base
`activeACount`, for an active-B / active-A ordered pair on an all-phase-10 config. -/
theorem activeACount_post_cancel_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb : IsActiveA b) :
    activeACount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeACount c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .A := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      Multiset.countP IsActiveA ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveA (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveA (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad
      have : a.output = .A := hbad.2
      rw [ha.2] at this; exact absurd this (by decide)
  have hlocal :=
    Phase10Transition_activeB_activeA_outputs_T
      (L := L) (K := K) a b ha.1 hb.1 ha.2 hb.2
  have hpair_after :
      Multiset.countP IsActiveA
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out, _h1full, _h2full⟩
    change Multiset.countP IsActiveA
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveA
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        have : (Phase10Transition L K a b).2.output = .A := hbad.2
        rw [h2out] at this; exact absurd this (by decide)
    · intro hbad
      have : (Phase10Transition L K a b).1.output = .A := hbad.2
      rw [h1out] at this; exact absurd this (by decide)
  have hres :
      Multiset.countP IsActiveA (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP IsActiveA c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveA
    rw [hsub, hpair_before]
  have hpos_old : 0 < Multiset.countP IsActiveA c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb
  unfold activeACount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- A single active-B / active-A ordered pair, scheduled on an all-phase-10
configuration, lands in the `activeACount`-drop target. -/
theorem scheduledStep_activeB_activeA_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb : IsActiveA b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (activeACount (L := L) (K := K)) c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .A := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact activeACount_post_cancel_lt c hphase ha_mem hb_mem ha hb

/-- The active-B × active-A rectangle of ordered pairs. -/
def activeBAPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveB a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => IsActiveA a))

/-- The total `interactionCount` over the active-B × active-A rectangle equals
`activeBCount c · activeACount c`. -/
theorem sum_interactionCount_activeBA (c : Config (AgentState L K)) :
    (∑ p ∈ activeBAPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeBCount c * activeACount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    have : a.output = .A := hb.2.2
    rw [ha.2.2] at this; exact absurd this (by decide)
  rw [activeBAPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), c.count a)
      = Multiset.countP IsActiveB c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveB c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a), c.count b)
      = Multiset.countP IsActiveA c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveA c).symm]
  rfl

/-- The present active-B × active-A pairs. -/
def presentActiveBAPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeBAPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-B × active-A pairs equals
`activeBCount · activeACount / totalPairs`. -/
theorem sum_interactionProb_presentActiveBA (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveBAPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = (↑(activeBCount c * activeACount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ p ∈ presentActiveBAPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeBAPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveBAPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    rw [presentActiveBAPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeBA, ← div_eq_mul_inv]

/-- **Mirrored cancel-stage per-level drop probability.** On an all-phase-10
configuration with at least one active-B agent, the transition kernel maps into
the `activeACount`-drop set with probability `≥ activeACount c / totalPairs`. -/
theorem activeACount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hB : 1 ≤ activeBCount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeACount (L := L) (K := K)) c) ≥
      (↑(activeACount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveBAPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeACount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveBAPairs, activeBAPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hB1⟩, ⟨_, hA2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeB_activeA_in_drop c hphase ha_mem hb_mem hB1 hA2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeACount (L := L) (K := K)) c)
    (↑(presentActiveBAPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveBAPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveBAPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveBA] at hSmeasure
  change (NonuniformMajority L K).transitionKernel c _ ≥ _
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  apply ENNReal.div_le_div_right
  have : activeACount c ≤ activeBCount c * activeACount c := by
    calc activeACount c = 1 * activeACount c := (Nat.one_mul _).symm
      _ ≤ activeBCount c * activeACount c := Nat.mul_le_mul_right _ hB
  exact_mod_cast this

/-- Mirrored rectangle drop probability for the cancel stage. -/
theorem activeACount_drop_prob_rect (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeACount (L := L) (K := K)) c) ≥
      (↑(activeBCount c * activeACount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveBAPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeACount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveBAPairs, activeBAPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hB1⟩, ⟨_, hA2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeB_activeA_in_drop c hphase ha_mem hb_mem hB1 hA2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeACount (L := L) (K := K)) c)
    (↑(presentActiveBAPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveBAPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveBAPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveBA] at hSmeasure
  change (NonuniformMajority L K).transitionKernel c _ ≥ _
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  exact hge

/-- Mirrored quadratic cancel-stage drop probability. -/
theorem activeACount_drop_prob_sq (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hBA : activeACount c ≤ activeBCount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeACount (L := L) (K := K)) c) ≥
      (↑(activeACount c ^ 2) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  refine le_trans ?_ (activeACount_drop_prob_rect c hc hphase)
  apply ENNReal.div_le_div_right
  have : activeACount c ^ 2 ≤ activeBCount c * activeACount c := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ hBA
  exact_mod_cast this

/-! ### Coupon stage (`wrongACount`, after `activeBCount = 0`)

The same machinery applies to the absorb-T / convert-passive coupon stages with
`Φ = wrongACount` (agents whose output is not `A`).  An active-A meeting any
non-active-B agent whose output is not `A` converts it to `A`, dropping
`wrongACount`.  In the post-cancel regime (`activeBCount = 0`) every wrong agent is
automatically non-active-B, so the useful class is active-A × {output ≠ A}. -/

/-- `wrongACount` of the post-conversion configuration is strictly below the base,
for an active-A agent meeting a non-active-B agent whose output is not `A`. -/
theorem wrongACount_post_convert_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb_wrong : b.output ≠ .A) (hb_not_activeB : ¬ IsActiveB b) :
    wrongACount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      wrongACount c := by
  have hne : a ≠ b := by
    intro h; subst h; exact hb_wrong ha.2
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
        ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
      (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
        (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb_wrong
    · intro hbad; exact hbad ha.2
  have hlocal :=
    Phase10Transition_activeA_nonActiveB_outputs_A
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeB
  have hpair_after :
      Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out⟩
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad; exact hbad h2out
    · intro hbad; exact hbad h1out
  have hres :
      Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
          (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP (fun x : AgentState L K => x.output ≠ .A) c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ
      (fun x : AgentState L K => x.output ≠ .A)
    rw [hsub, hpair_before]
  have hpos_old :
      0 < Multiset.countP (fun x : AgentState L K => x.output ≠ .A) c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb_wrong
  unfold wrongACount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- An active-A / non-active-B-wrong ordered pair lands in the `wrongACount`-drop
target. -/
theorem scheduledStep_activeA_wrongB_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb_wrong : b.output ≠ .A) (hb_not_activeB : ¬ IsActiveB b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (wrongACount (L := L) (K := K)) c := by
  have hne : a ≠ b := by intro h; subst h; exact hb_wrong ha.2
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact wrongACount_post_convert_lt c hphase ha_mem hb_mem ha hb_wrong hb_not_activeB

/-! ### Absorb-T stage drop machinery (`activeTCount`, active-A × active-T) -/

/-- An active-`T` is not an active-`B`. -/
private theorem not_activeB_of_activeT {b : AgentState L K} (hb : IsActiveT b) :
    ¬ IsActiveB b := by
  intro hbB
  have : b.output = .B := hbB.2
  rw [hb.2] at this; exact absurd this (by decide)

/-- `activeTCount` of the post-absorb configuration is strictly below the base,
for an active-A meeting an active-T (the active-T is converted to output A). -/
theorem activeTCount_post_absorb_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveT b) :
    activeTCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeTCount c := by
  have hb_not_activeB : ¬ IsActiveB b := not_activeB_of_activeT hb
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .T := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      Multiset.countP IsActiveT ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveT (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveT (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad; have : a.output = .T := hbad.2; rw [ha.2] at this; exact absurd this (by decide)
  have hlocal :=
    Phase10Transition_activeA_nonActiveB_outputs_A
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeB
  have hpair_after :
      Multiset.countP IsActiveT
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out⟩
    change Multiset.countP IsActiveT
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveT
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad; have : (Phase10Transition L K a b).2.output = .T := hbad.2
        rw [h2out] at this; exact absurd this (by decide)
    · intro hbad; have : (Phase10Transition L K a b).1.output = .T := hbad.2
      rw [h1out] at this; exact absurd this (by decide)
  have hres :
      Multiset.countP IsActiveT (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP IsActiveT c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveT
    rw [hsub, hpair_before]
  have hpos_old : 0 < Multiset.countP IsActiveT c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb
  unfold activeTCount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- An active-A / active-T ordered pair lands in the `activeTCount`-drop target. -/
theorem scheduledStep_activeA_activeT_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveT b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (activeTCount (L := L) (K := K)) c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .T := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact activeTCount_post_absorb_lt c hphase ha_mem hb_mem ha hb

/-- The "wrong, not active-B" responder class (output ≠ A and not an active-B). -/
def WrongNotActiveB (a : AgentState L K) : Prop :=
  a.output ≠ .A ∧ ¬ IsActiveB a

instance : DecidablePred (@WrongNotActiveB L K) := fun a => by
  unfold WrongNotActiveB; infer_instance

/-- The active-A × wrong-not-activeB rectangle of ordered pairs. -/
def activeAWrongPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveA a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => WrongNotActiveB a))

/-- Count of wrong-not-activeB agents. -/
def wrongNotBCount (c : Config (AgentState L K)) : ℕ :=
  c.countP WrongNotActiveB

/-- The total `interactionCount` over the active-A × wrong-not-activeB rectangle
equals `activeACount c · wrongNotBCount c`. -/
theorem sum_interactionCount_activeAWrong (c : Config (AgentState L K)) :
    (∑ p ∈ activeAWrongPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeACount c * wrongNotBCount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => WrongNotActiveB a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    exact hb.2.1 ha.2.2
  rw [activeAWrongPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a), c.count a)
      = Multiset.countP IsActiveA c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveA c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => WrongNotActiveB a), c.count b)
      = Multiset.countP WrongNotActiveB c from
    (HourCouplingAzuma.countP_eq_sum_count WrongNotActiveB c).symm]
  rfl

/-- When `activeBCount c = 0`, every wrong agent is non-active-B, so
`wrongNotBCount c = wrongACount c`. -/
theorem wrongNotBCount_eq_wrongACount_of_no_activeB
    (c : Config (AgentState L K)) (hB : activeBCount c = 0) :
    wrongNotBCount c = wrongACount c := by
  classical
  unfold wrongNotBCount wrongACount
  apply Multiset.countP_congr rfl
  intro a ha
  have hnotB : ¬ IsActiveB a := by
    have := Multiset.countP_eq_zero.1 (by simpa [activeBCount] using hB)
    exact this a ha
  simp only [WrongNotActiveB, hnotB, not_false_iff, and_true]

/-- The present active-A × wrong-not-activeB pairs. -/
def presentActiveAWrongPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeAWrongPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-A × wrong-not-activeB pairs
equals `activeACount · wrongNotBCount / totalPairs`. -/
theorem sum_interactionProb_presentActiveAWrong (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveAWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2)
      = (↑(activeACount c * wrongNotBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ p ∈ presentActiveAWrongPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeAWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveAWrongPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    rw [presentActiveAWrongPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeAWrong, ← div_eq_mul_inv]

/-- **Coupon-stage per-level drop probability.** On an all-phase-10 configuration
with `activeBCount = 0` (post-cancel majority-A regime) and at least one active-A,
the kernel maps into the `wrongACount`-drop set with probability `≥ wrongACount c /
(n·(n−1))`. -/
theorem wrongACount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hB : activeBCount c = 0)
    (hA : 1 ≤ activeACount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (wrongACount (L := L) (K := K)) c) ≥
      (↑(wrongACount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveAWrongPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (wrongACount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveAWrongPairs, activeAWrongPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hA1⟩, ⟨_, hW2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeA_wrongB_in_drop c hphase ha_mem hb_mem hA1 hW2.1 hW2.2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (wrongACount (L := L) (K := K)) c)
    (↑(presentActiveAWrongPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveAWrongPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveAWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveAWrong] at hSmeasure
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  apply ENNReal.div_le_div_right
  rw [wrongNotBCount_eq_wrongACount_of_no_activeB c hB]
  have : wrongACount c ≤ activeACount c * wrongACount c := by
    calc wrongACount c = 1 * wrongACount c := (Nat.one_mul _).symm
      _ ≤ activeACount c * wrongACount c := Nat.mul_le_mul_right _ hA
  exact_mod_cast this

/-! ### Mirrored coupon stage (`wrongBCount`, after `activeACount = 0`) -/

/-- `wrongBCount` of the post-conversion configuration is strictly below the base,
for an active-B agent meeting a non-active-A agent whose output is not `B`. -/
theorem wrongBCount_post_convert_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb_wrong : b.output ≠ .B) (hb_not_activeA : ¬ IsActiveA b) :
    wrongBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      wrongBCount c := by
  have hne : a ≠ b := by
    intro h; subst h; exact hb_wrong ha.2
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
        ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
      (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
        (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb_wrong
    · intro hbad; exact hbad ha.2
  have hlocal :=
    Phase10Transition_activeB_nonActiveA_outputs_B
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeA
  have hpair_after :
      Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out⟩
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad; exact hbad h2out
    · intro hbad; exact hbad h1out
  have hres :
      Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
          (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP (fun x : AgentState L K => x.output ≠ .B) c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ
      (fun x : AgentState L K => x.output ≠ .B)
    rw [hsub, hpair_before]
  have hpos_old :
      0 < Multiset.countP (fun x : AgentState L K => x.output ≠ .B) c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb_wrong
  unfold wrongBCount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- An active-B / non-active-A-wrong ordered pair lands in the `wrongBCount`-drop
target. -/
theorem scheduledStep_activeB_wrongA_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb_wrong : b.output ≠ .B) (hb_not_activeA : ¬ IsActiveA b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (wrongBCount (L := L) (K := K)) c := by
  have hne : a ≠ b := by intro h; subst h; exact hb_wrong ha.2
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact wrongBCount_post_convert_lt c hphase ha_mem hb_mem ha hb_wrong hb_not_activeA

/-- The "wrong, not active-A" responder class (output ≠ B and not an active-A). -/
def WrongNotActiveA (a : AgentState L K) : Prop :=
  a.output ≠ .B ∧ ¬ IsActiveA a

instance : DecidablePred (@WrongNotActiveA L K) := fun a => by
  unfold WrongNotActiveA; infer_instance

/-- The active-B × wrong-not-activeA rectangle of ordered pairs. -/
def activeBWrongPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveB a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => WrongNotActiveA a))

/-- Count of wrong-not-activeA agents. -/
def wrongNotACount (c : Config (AgentState L K)) : ℕ :=
  c.countP WrongNotActiveA

/-- The total `interactionCount` over the active-B × wrong-not-activeA rectangle
equals `activeBCount c · wrongNotACount c`. -/
theorem sum_interactionCount_activeBWrong (c : Config (AgentState L K)) :
    (∑ p ∈ activeBWrongPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeBCount c * wrongNotACount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => WrongNotActiveA a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    exact hb.2.1 ha.2.2
  rw [activeBWrongPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), c.count a)
      = Multiset.countP IsActiveB c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveB c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => WrongNotActiveA a), c.count b)
      = Multiset.countP WrongNotActiveA c from
    (HourCouplingAzuma.countP_eq_sum_count WrongNotActiveA c).symm]
  rfl

/-- When `activeACount c = 0`, every wrong-B agent is non-active-A, so
`wrongNotACount c = wrongBCount c`. -/
theorem wrongNotACount_eq_wrongBCount_of_no_activeA
    (c : Config (AgentState L K)) (hA : activeACount c = 0) :
    wrongNotACount c = wrongBCount c := by
  classical
  unfold wrongNotACount wrongBCount
  apply Multiset.countP_congr rfl
  intro a ha
  have hnotA : ¬ IsActiveA a := by
    have := Multiset.countP_eq_zero.1 (by simpa [activeACount] using hA)
    exact this a ha
  simp only [WrongNotActiveA, hnotA, not_false_iff, and_true]

/-- The present active-B × wrong-not-activeA pairs. -/
def presentActiveBWrongPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeBWrongPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-B × wrong-not-activeA pairs
equals `activeBCount · wrongNotACount / totalPairs`. -/
theorem sum_interactionProb_presentActiveBWrong (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveBWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2)
      = (↑(activeBCount c * wrongNotACount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ p ∈ presentActiveBWrongPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeBWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveBWrongPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    rw [presentActiveBWrongPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeBWrong, ← div_eq_mul_inv]

/-- **Mirrored coupon-stage per-level drop probability.** On an all-phase-10
configuration with `activeACount = 0` and at least one active-B, the kernel maps
into the `wrongBCount`-drop set with probability `≥ wrongBCount c / totalPairs`. -/
theorem wrongBCount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hA : activeACount c = 0)
    (hB : 1 ≤ activeBCount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (wrongBCount (L := L) (K := K)) c) ≥
      (↑(wrongBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveBWrongPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (wrongBCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveBWrongPairs, activeBWrongPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hB1⟩, ⟨_, hW2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeB_wrongA_in_drop c hphase ha_mem hb_mem hB1 hW2.1 hW2.2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (wrongBCount (L := L) (K := K)) c)
    (↑(presentActiveBWrongPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveBWrongPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveBWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveBWrong] at hSmeasure
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  apply ENNReal.div_le_div_right
  rw [wrongNotACount_eq_wrongBCount_of_no_activeA c hA]
  have : wrongBCount c ≤ activeBCount c * wrongBCount c := by
    calc wrongBCount c = 1 * wrongBCount c := (Nat.one_mul _).symm
      _ ≤ activeBCount c * wrongBCount c := Nat.mul_le_mul_right _ hB
  exact_mod_cast this

/-! ### Absorb-T stage aggregation + drop probability (`activeTCount`) -/

/-- The active-A × active-T rectangle of ordered pairs. -/
def activeATPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveA a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => IsActiveT a))

/-- The total `interactionCount` over the active-A × active-T rectangle equals
`activeACount c · activeTCount c`. -/
theorem sum_interactionCount_activeAT (c : Config (AgentState L K)) :
    (∑ p ∈ activeATPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeACount c * activeTCount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveT a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    have : a.output = .T := hb.2.2
    rw [ha.2.2] at this; exact absurd this (by decide)
  rw [activeATPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a), c.count a)
      = Multiset.countP IsActiveA c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveA c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveT a), c.count b)
      = Multiset.countP IsActiveT c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveT c).symm]
  rfl

/-- The present active-A × active-T pairs. -/
def presentActiveATPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeATPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-A × active-T pairs equals
`activeACount · activeTCount / totalPairs`. -/
theorem sum_interactionProb_presentActiveAT (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveATPairs (L := L) (K := K) c, c.interactionProb p.1 p.2)
      = (↑(activeACount c * activeTCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ p ∈ presentActiveATPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeATPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveATPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    rw [presentActiveATPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeAT, ← div_eq_mul_inv]

/-- **Absorb-T stage per-level drop probability.** On an all-phase-10 configuration
with at least one active-A, the kernel maps into the `activeTCount`-drop set with
probability `≥ activeTCount c / (n·(n−1))`. -/
theorem activeTCount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hA : 1 ≤ activeACount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeTCount (L := L) (K := K)) c) ≥
      (↑(activeTCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveATPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeTCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveATPairs, activeATPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hA1⟩, ⟨_, hT2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeA_activeT_in_drop c hphase ha_mem hb_mem hA1 hT2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeTCount (L := L) (K := K)) c)
    (↑(presentActiveATPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveATPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveATPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveAT] at hSmeasure
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  apply ENNReal.div_le_div_right
  have : activeTCount c ≤ activeACount c * activeTCount c := by
    calc activeTCount c = 1 * activeTCount c := (Nat.one_mul _).symm
      _ ≤ activeACount c * activeTCount c := Nat.mul_le_mul_right _ hA
  exact_mod_cast this

/-! ### Mirrored absorb-T stage aggregation (`activeBCount` driver) -/

/-- An active-`T` is not an active-`A`. -/
private theorem not_activeA_of_activeT {b : AgentState L K} (hb : IsActiveT b) :
    ¬ IsActiveA b := by
  intro hbA
  have : b.output = .A := hbA.2
  rw [hb.2] at this; exact absurd this (by decide)

/-- `activeTCount` of the post-absorb configuration is strictly below the base,
for an active-B meeting an active-T (the active-T is converted to output B). -/
theorem activeTCount_post_absorb_B_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb : IsActiveT b) :
    activeTCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeTCount c := by
  have hb_not_activeA : ¬ IsActiveA b := not_activeA_of_activeT hb
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .T := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      Multiset.countP IsActiveT ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveT (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveT (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad; have : a.output = .T := hbad.2; rw [ha.2] at this; exact absurd this (by decide)
  have hlocal :=
    Phase10Transition_activeB_nonActiveA_outputs_B
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeA
  have hpair_after :
      Multiset.countP IsActiveT
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out⟩
    change Multiset.countP IsActiveT
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveT
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad; have : (Phase10Transition L K a b).2.output = .T := hbad.2
        rw [h2out] at this; exact absurd this (by decide)
    · intro hbad; have : (Phase10Transition L K a b).1.output = .T := hbad.2
      rw [h1out] at this; exact absurd this (by decide)
  have hres :
      Multiset.countP IsActiveT (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP IsActiveT c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveT
    rw [hsub, hpair_before]
  have hpos_old : 0 < Multiset.countP IsActiveT c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb
  unfold activeTCount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- An active-B / active-T ordered pair lands in the `activeTCount`-drop target. -/
theorem scheduledStep_activeB_activeT_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb : IsActiveT b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (activeTCount (L := L) (K := K)) c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .T := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact activeTCount_post_absorb_B_lt c hphase ha_mem hb_mem ha hb

/-- The active-B × active-T rectangle of ordered pairs. -/
def activeBTPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveB a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => IsActiveT a))

/-- The total `interactionCount` over the active-B × active-T rectangle equals
`activeBCount c · activeTCount c`. -/
theorem sum_interactionCount_activeBT (c : Config (AgentState L K)) :
    (∑ p ∈ activeBTPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeBCount c * activeTCount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveT a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    have : a.output = .T := hb.2.2
    rw [ha.2.2] at this; exact absurd this (by decide)
  rw [activeBTPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), c.count a)
      = Multiset.countP IsActiveB c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveB c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveT a), c.count b)
      = Multiset.countP IsActiveT c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveT c).symm]
  rfl

/-- The present active-B × active-T pairs. -/
def presentActiveBTPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeBTPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-B × active-T pairs equals
`activeBCount · activeTCount / totalPairs`. -/
theorem sum_interactionProb_presentActiveBT (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveBTPairs (L := L) (K := K) c, c.interactionProb p.1 p.2)
      = (↑(activeBCount c * activeTCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ p ∈ presentActiveBTPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeBTPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveBTPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    rw [presentActiveBTPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeBT, ← div_eq_mul_inv]

/-- **Mirrored absorb-T stage per-level drop probability.** On an all-phase-10
configuration with at least one active-B, the kernel maps into the
`activeTCount`-drop set with probability `≥ activeTCount c / totalPairs`. -/
theorem activeTCount_drop_prob_B (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hB : 1 ≤ activeBCount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeTCount (L := L) (K := K)) c) ≥
      (↑(activeTCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveBTPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeTCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveBTPairs, activeBTPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hB1⟩, ⟨_, hT2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeB_activeT_in_drop c hphase ha_mem hb_mem hB1 hT2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeTCount (L := L) (K := K)) c)
    (↑(presentActiveBTPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveBTPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveBTPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveBT] at hSmeasure
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  apply ENNReal.div_le_div_right
  have : activeTCount c ≤ activeBCount c * activeTCount c := by
    calc activeTCount c = 1 * activeTCount c := (Nat.one_mul _).symm
      _ ≤ activeBCount c * activeTCount c := Nat.mul_le_mul_right _ hB
  exact_mod_cast this

/-! ## Per-pair potential monotonicity (Brick: `PotNonincrOn`)

For the three-stage invariant chain we need, on a both-phase-10 interacting pair,
that each stage potential never strictly increases.  We prove the per-pair
`countP`-bound directly by exhaustive case analysis on the two outputs and the two
`full` flags (the same brute-force pattern as the public `Phase10Transition_*`
output lemmas), then lift to the kernel via the support template
(`phaseBelowCount_step_le`-style: peel a pair, `countP` additivity, restore). -/

section PairMonotone

/-- `countP P {x, y} = (if P x then 1 else 0) + (if P y then 1 else 0)`, the
2-element evaluation we use throughout. -/
private theorem countP_pair {α : Type*} (P : α → Prop) [DecidablePred P] (x y : α) :
    Multiset.countP P ({x, y} : Multiset α)
      = (if P x then 1 else 0) + (if P y then 1 else 0) := by
  change Multiset.countP P (x ::ₘ ({y} : Multiset α)) = _
  rw [Multiset.countP_cons]
  have hy1 : Multiset.countP P ({y} : Multiset α) = if P y then 1 else 0 := by
    change Multiset.countP P (y ::ₘ (0 : Multiset α)) = _
    rw [Multiset.countP_cons]
    by_cases hy : P y <;> simp [hy]
  rw [hy1]
  by_cases hx : P x <;> simp [hx, Nat.add_comm]

/-- **Per-pair `activeBCount` non-increase** on a both-phase-10 pair: the cancel
reaction can only lower the number of active-`B` sources on the interacting pair;
the active→passive "spread" of Block 2 keeps the converted partner passive
(`full := false`), so it never creates a new active-`B`. -/
theorem Transition_activeBCount_le (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10) :
    Multiset.countP IsActiveB
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP IsActiveB ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition, IsActiveB]

/-- **Per-pair `activeACount` non-increase** on a both-phase-10 pair.  This is
the A/B mirror of `Transition_activeBCount_le`. -/
theorem Transition_activeACount_le (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10) :
    Multiset.countP IsActiveA
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP IsActiveA ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition, IsActiveA]

/-- **Per-pair `activeTCount` non-increase** on a both-phase-10 pair with **no
active-`B`** member.  Active-`T` is only created by the cancel reaction (which
needs an active-`A` against an active-`B`); with no active-`B` present in the pair,
cancel cannot fire, and the active→passive spread keeps the partner passive, so the
number of active-`T` sources cannot rise. -/
theorem Transition_activeTCount_le (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hnB_a : ¬ IsActiveB a) (hnB_b : ¬ IsActiveB b) :
    Multiset.countP IsActiveT
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP IsActiveT ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, IsActiveB, IsActiveT]

/-- **Per-pair `activeTCount` non-increase** on a both-phase-10 pair with **no
active-`A`** member.  B-majority mirror of `Transition_activeTCount_le`. -/
theorem Transition_activeTCount_le_noA (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hnA_a : ¬ IsActiveA a) (hnA_b : ¬ IsActiveA b) :
    Multiset.countP IsActiveT
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP IsActiveT ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, IsActiveA, IsActiveT]

/-- **Per-pair `wrongACount` non-increase** on a both-phase-10 pair with **no
active-`B`** and **no active-`T`** member.  Under that restriction every member is
either active-`A` or passive; an active-`A` only ever spreads `A` (never un-`A`s a
partner), and passives among themselves are inert, so the number of non-`A` outputs
cannot rise. -/
theorem Transition_wrongACount_le (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hnB_a : ¬ IsActiveB a) (hnB_b : ¬ IsActiveB b)
    (hnT_a : ¬ IsActiveT a) (hnT_b : ¬ IsActiveT b) :
    Multiset.countP (fun a => a.output ≠ Output.A)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => a.output ≠ Output.A)
          ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, IsActiveB, IsActiveT]

/-- **Per-pair `wrongBCount` non-increase** on a both-phase-10 pair with **no
active-`A`** and **no active-`T`** member.  B-majority mirror of
`Transition_wrongACount_le`. -/
theorem Transition_wrongBCount_le (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hnA_a : ¬ IsActiveA a) (hnA_b : ¬ IsActiveA b)
    (hnT_a : ¬ IsActiveT a) (hnT_b : ¬ IsActiveT b) :
    Multiset.countP (fun a => a.output ≠ Output.B)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => a.output ≠ Output.B)
          ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, IsActiveA, IsActiveT]

/-- **Per-pair `wrongTCount` non-increase** on a both-phase-10 pair with **no
active-`A`** and **no active-`B`** member.  Under that restriction every member is
either active-`T` or passive; an active-`T` only ever spreads `T` (never un-`T`s a
partner), and passives among themselves are inert, so the number of non-`T` outputs
cannot rise. -/
theorem Transition_wrongTCount_le (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hnA_a : ¬ IsActiveA a) (hnA_b : ¬ IsActiveA b)
    (hnB_a : ¬ IsActiveB a) (hnB_b : ¬ IsActiveB b) :
    Multiset.countP (fun a => a.output ≠ Output.T)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => a.output ≠ Output.T)
          ({a, b} : Multiset (AgentState L K)) := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  rw [countP_pair, countP_pair]
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp_all [Phase10Transition, IsActiveA, IsActiveB, IsActiveT]

end PairMonotone

/-! ## Kernel-level lifting: `InvClosed` and `PotNonincrOn`

We lift the per-pair `countP`-bounds to the real kernel via the support template
(peel a pair from `stepDistOrSelf`'s support, `countP` additivity, restore), with
the interacting pair members inheriting the all-phase-10 / typed restrictions from
the invariant on the whole configuration.

The three stage invariants:
* `Inv₁ := AllPhase10` (`= Phase10EpidemicPost`);
* `Inv₂ := AllPhase10 ∧ activeBCount = 0`;
* `Inv₃ := AllPhase10 ∧ activeBCount = 0 ∧ activeTCount = 0`. -/

section InvLift

open Protocol

/-- Stage-1 invariant: every agent is in Phase 10. -/
def AllPhase10 (c : Config (AgentState L K)) : Prop := ∀ x ∈ c, x.phase.val = 10

/-- Stage-2 invariant: all-phase-10 and no active-`B` source. -/
def Inv2 (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ activeBCount c = 0

/-- Stage-3 invariant: all-phase-10, no active-`B`, no active-`T` source. -/
def Inv3 (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ activeBCount c = 0 ∧ activeTCount c = 0

/-- B-majority stage-2 invariant: all-phase-10 and no active-`A` source. -/
def Inv2B (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ activeACount c = 0

/-- B-majority stage-3 invariant: all-phase-10, no active-`A`, no active-`T`. -/
def Inv3B (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ activeACount c = 0 ∧ activeTCount c = 0

/-- A configuration's `countP P` decomposes over a peeled applicable pair, using the
per-pair bound `hpair` to control the new pair's contribution. -/
theorem countP_scheduledStep_le
    (P : AgentState L K → Prop) [DecidablePred P]
    {c c' : Config (AgentState L K)}
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hpair : ∀ r₁ r₂ : AgentState L K, r₁ ∈ c → r₂ ∈ c →
      Multiset.countP P
          ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
            Multiset (AgentState L K))
        ≤ Multiset.countP P ({r₁, r₂} : Multiset (AgentState L K))) :
    Multiset.countP P c' ≤ Multiset.countP P c := by
  unfold Protocol.stepDistOrSelf at h
  split_ifs at h with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
    subst heq
    unfold Protocol.scheduledStep Protocol.stepOrSelf at *
    split_ifs at * with h_app
    · have h_sub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := by
        unfold Protocol.Applicable at h_app; exact h_app
      have hr₁ : r₁ ∈ c := Multiset.mem_of_le h_sub (by simp)
      have hr₂ : r₂ ∈ c := Multiset.mem_of_le h_sub (by simp)
      have h_restore : c - ({r₁, r₂} : Multiset (AgentState L K)) + {r₁, r₂} = c :=
        Multiset.sub_add_cancel h_sub
      calc Multiset.countP P (c - ({r₁, r₂} : Multiset (AgentState L K))
              + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
          = Multiset.countP P (c - ({r₁, r₂} : Multiset (AgentState L K)))
              + Multiset.countP P
                  {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
            rw [Multiset.countP_add]
        _ ≤ Multiset.countP P (c - ({r₁, r₂} : Multiset (AgentState L K)))
              + Multiset.countP P ({r₁, r₂} : Multiset (AgentState L K)) :=
            Nat.add_le_add_left (hpair r₁ r₂ hr₁ hr₂) _
        _ = Multiset.countP P (c - ({r₁, r₂} : Multiset (AgentState L K)) + {r₁, r₂}) := by
            rw [Multiset.countP_add]
        _ = Multiset.countP P c := by rw [h_restore]
    · rfl
  · simp [PMF.support_pure] at h; rw [h]

/-- Generic `PotNonincrOn` from a step-level `countP`-bound conditioned on the
invariant.  Reduces `K b {Φ b < Φ x} = 0` to the support-pointwise bound. -/
theorem potNonincrOn_of_countP_step
    (Inv : Config (AgentState L K) → Prop) (P : AgentState L K → Prop)
    [DecidablePred P]
    (hstep : ∀ c, Inv c → ∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      Multiset.countP P c' ≤ Multiset.countP P c) :
    PotNonincrOn (fun c => Inv c) (NonuniformMajority L K).transitionKernel
      (fun c => Multiset.countP P c) := by
  intro b hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | Multiset.countP P b < Multiset.countP P x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => ?_
  simp only [Set.mem_setOf_eq] at hbad
  exact absurd (hstep b hb c' hc') (Nat.not_le.mpr hbad)

/-! ### `InvClosed` for the three stages -/

/-- A support config of an all-phase-10 base is itself all-phase-10
(the `phaseBelowCount 10`-zero step-template). -/
private theorem allPhase10_step
    {c c' : Config (AgentState L K)} (hc : AllPhase10 (L := L) (K := K) c)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AllPhase10 (L := L) (K := K) c' := by
  have hpbc : phaseBelowCount 10 c = 0 :=
    (Phase10EpidemicPost_iff_phaseBelowCount_zero c).mp hc
  have hle := phaseBelowCount_step_le (L := L) (K := K) 10 c c' h
  rw [hpbc] at hle
  exact (Phase10EpidemicPost_iff_phaseBelowCount_zero c').mpr (Nat.le_zero.mp hle)

/-- A support config of a no-active-`B` all-phase-10 base also has no active-`B`. -/
private theorem activeBCount_step_zero
    {c c' : Config (AgentState L K)} (hphase : AllPhase10 (L := L) (K := K) c)
    (hB : activeBCount c = 0)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    activeBCount c' = 0 := by
  have hle : activeBCount c' ≤ activeBCount c :=
    countP_scheduledStep_le IsActiveB h
      (fun r₁ r₂ hr₁ hr₂ =>
        Transition_activeBCount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂))
  omega

/-- A support config of a no-active-`A` all-phase-10 base also has no active-`A`. -/
private theorem activeACount_step_zero
    {c c' : Config (AgentState L K)} (hphase : AllPhase10 (L := L) (K := K) c)
    (hA : activeACount c = 0)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    activeACount c' = 0 := by
  have hle : activeACount c' ≤ activeACount c :=
    countP_scheduledStep_le IsActiveA h
      (fun r₁ r₂ hr₁ hr₂ =>
        Transition_activeACount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂))
  omega

/-- A support config of an `Inv₃` base (no active-`B`, no active-`T`) has no
active-`T` (using the `activeTCount` per-pair bound, valid since no active-`B`). -/
private theorem activeTCount_step_zero
    {c c' : Config (AgentState L K)} (hphase : AllPhase10 (L := L) (K := K) c)
    (hB : activeBCount c = 0) (hT : activeTCount c = 0)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    activeTCount c' = 0 := by
  have hnoB : ∀ x ∈ c, ¬ IsActiveB x := fun x hx =>
    (Multiset.countP_eq_zero.1 hB) x hx
  have hle : activeTCount c' ≤ activeTCount c :=
    countP_scheduledStep_le IsActiveT h
      (fun r₁ r₂ hr₁ hr₂ =>
          Transition_activeTCount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)
            (hnoB r₁ hr₁) (hnoB r₂ hr₂))
  omega

/-- A support config of a no-active-`A`, no-active-`T` base has no active-`T`
(B-majority mirror). -/
private theorem activeTCount_step_zero_B
    {c c' : Config (AgentState L K)} (hphase : AllPhase10 (L := L) (K := K) c)
    (hA : activeACount c = 0) (hT : activeTCount c = 0)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    activeTCount c' = 0 := by
  have hnoA : ∀ x ∈ c, ¬ IsActiveA x := fun x hx =>
    (Multiset.countP_eq_zero.1 hA) x hx
  have hle : activeTCount c' ≤ activeTCount c :=
    countP_scheduledStep_le IsActiveT h
      (fun r₁ r₂ hr₁ hr₂ =>
        Transition_activeTCount_le_noA r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)
          (hnoA r₁ hr₁) (hnoA r₂ hr₂))
  omega

/-- **`InvClosed` for stage 1** (`AllPhase10`). -/
theorem invClosed_allPhase10 :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => AllPhase10 (L := L) (K := K) c) := by
  intro b hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ AllPhase10 (L := L) (K := K) x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact Set.disjoint_left.mpr fun c' hc' hbad =>
    hbad (allPhase10_step hb hc')

/-- **`InvClosed` for stage 2** (`Inv₂`). -/
theorem invClosed_inv2 :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Inv2 (L := L) (K := K) c) := by
  intro b hb
  obtain ⟨hphase, hB⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Inv2 (L := L) (K := K) x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  exact ⟨allPhase10_step hphase hc', activeBCount_step_zero hphase hB hc'⟩

/-- **`InvClosed` for stage 3** (`Inv₃`). -/
theorem invClosed_inv3 :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Inv3 (L := L) (K := K) c) := by
  intro b hb
  obtain ⟨hphase, hB, hT⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Inv3 (L := L) (K := K) x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  exact ⟨allPhase10_step hphase hc', activeBCount_step_zero hphase hB hc',
    activeTCount_step_zero hphase hB hT hc'⟩

/-- **`InvClosed` for mirrored stage 2** (`Inv2B`). -/
theorem invClosed_inv2B :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Inv2B (L := L) (K := K) c) := by
  intro b hb
  obtain ⟨hphase, hA⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Inv2B (L := L) (K := K) x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  exact ⟨allPhase10_step hphase hc', activeACount_step_zero hphase hA hc'⟩

/-- **`InvClosed` for mirrored stage 3** (`Inv3B`). -/
theorem invClosed_inv3B :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Inv3B (L := L) (K := K) c) := by
  intro b hb
  obtain ⟨hphase, hA, hT⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Inv3B (L := L) (K := K) x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  exact ⟨allPhase10_step hphase hc', activeACount_step_zero hphase hA hc',
    activeTCount_step_zero_B hphase hA hT hc'⟩

/-! ### `PotNonincrOn` for the three stages -/

/-- **Stage 1 `PotNonincrOn`**: `activeBCount` is non-increasing from all-phase-10
states. -/
theorem potNonincrOn_activeBCount :
    PotNonincrOn (fun c => AllPhase10 (L := L) (K := K) c)
      (NonuniformMajority L K).transitionKernel
      (fun c => activeBCount c) :=
  potNonincrOn_of_countP_step (fun c => AllPhase10 (L := L) (K := K) c) IsActiveB
    (fun c hphase c' hc' =>
      countP_scheduledStep_le IsActiveB hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_activeBCount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)))

/-- **Mirrored stage 1 `PotNonincrOn`**: `activeACount` is non-increasing from
all-phase-10 states. -/
theorem potNonincrOn_activeACount :
    PotNonincrOn (fun c => AllPhase10 (L := L) (K := K) c)
      (NonuniformMajority L K).transitionKernel
      (fun c => activeACount c) :=
  potNonincrOn_of_countP_step (fun c => AllPhase10 (L := L) (K := K) c) IsActiveA
    (fun c hphase c' hc' =>
      countP_scheduledStep_le IsActiveA hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_activeACount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)))

/-- **Stage 2 `PotNonincrOn`**: `activeTCount` is non-increasing from `Inv₂`
states (all-phase-10 with no active-`B`). -/
theorem potNonincrOn_activeTCount :
    PotNonincrOn (fun c => Inv2 (L := L) (K := K) c)
      (NonuniformMajority L K).transitionKernel
      (fun c => activeTCount c) :=
  potNonincrOn_of_countP_step (fun c => Inv2 (L := L) (K := K) c) IsActiveT
    (fun c hInv c' hc' => by
      obtain ⟨hphase, hB⟩ := hInv
      have hnoB : ∀ x ∈ c, ¬ IsActiveB x := fun x hx =>
        (Multiset.countP_eq_zero.1 hB) x hx
      exact countP_scheduledStep_le IsActiveT hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_activeTCount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)
            (hnoB r₁ hr₁) (hnoB r₂ hr₂)))

/-- **Mirrored stage 2 `PotNonincrOn`**: `activeTCount` is non-increasing from
`Inv2B` states (all-phase-10 with no active-`A`). -/
theorem potNonincrOn_activeTCount_B :
    PotNonincrOn (fun c => Inv2B (L := L) (K := K) c)
      (NonuniformMajority L K).transitionKernel
      (fun c => activeTCount c) :=
  potNonincrOn_of_countP_step (fun c => Inv2B (L := L) (K := K) c) IsActiveT
    (fun c hInv c' hc' => by
      obtain ⟨hphase, hA⟩ := hInv
      have hnoA : ∀ x ∈ c, ¬ IsActiveA x := fun x hx =>
        (Multiset.countP_eq_zero.1 hA) x hx
      exact countP_scheduledStep_le IsActiveT hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_activeTCount_le_noA r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)
            (hnoA r₁ hr₁) (hnoA r₂ hr₂)))

/-- **Stage 3 `PotNonincrOn`**: `wrongACount` is non-increasing from `Inv₃`
states (all-phase-10, no active-`B`, no active-`T`). -/
theorem potNonincrOn_wrongACount :
    PotNonincrOn (fun c => Inv3 (L := L) (K := K) c)
      (NonuniformMajority L K).transitionKernel
      (fun c => wrongACount c) :=
  potNonincrOn_of_countP_step (fun c => Inv3 (L := L) (K := K) c)
    (fun a => a.output ≠ Output.A)
    (fun c hInv c' hc' => by
      obtain ⟨hphase, hB, hT⟩ := hInv
      have hnoB : ∀ x ∈ c, ¬ IsActiveB x := fun x hx =>
        (Multiset.countP_eq_zero.1 hB) x hx
      have hnoT : ∀ x ∈ c, ¬ IsActiveT x := fun x hx =>
        (Multiset.countP_eq_zero.1 hT) x hx
      exact countP_scheduledStep_le (fun a => a.output ≠ Output.A) hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_wrongACount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)
            (hnoB r₁ hr₁) (hnoB r₂ hr₂) (hnoT r₁ hr₁) (hnoT r₂ hr₂)))

/-- **Mirrored stage 3 `PotNonincrOn`**: `wrongBCount` is non-increasing from
`Inv3B` states. -/
theorem potNonincrOn_wrongBCount :
    PotNonincrOn (fun c => Inv3B (L := L) (K := K) c)
      (NonuniformMajority L K).transitionKernel
      (fun c => wrongBCount c) :=
  potNonincrOn_of_countP_step (fun c => Inv3B (L := L) (K := K) c)
    (fun a => a.output ≠ Output.B)
    (fun c hInv c' hc' => by
      obtain ⟨hphase, hA, hT⟩ := hInv
      have hnoA : ∀ x ∈ c, ¬ IsActiveA x := fun x hx =>
        (Multiset.countP_eq_zero.1 hA) x hx
      have hnoT : ∀ x ∈ c, ¬ IsActiveT x := fun x hx =>
        (Multiset.countP_eq_zero.1 hT) x hx
      exact countP_scheduledStep_le (fun a => a.output ≠ Output.B) hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_wrongBCount_le r₁ r₂ (hphase r₁ hr₁) (hphase r₂ hr₂)
            (hnoA r₁ hr₁) (hnoA r₂ hr₂) (hnoT r₁ hr₁) (hnoT r₂ hr₂)))

end InvLift

/-! ## Per-level drop hypothesis `q m = 1 − m/totalPairs` (Brick: q-wiring)

The drop-probability lemmas give `K c (dropTarget Φ c) ≥ Φ(c)/totalPairs`.  When
`Φ c = m`, `dropTarget Φ c = potBelow Φ m`, so taking complements,
`K c (potBelow Φ m)ᶜ ≤ 1 − m/totalPairs`. -/

section QWiring

open Protocol

/-- The per-level drop ceiling `q m = 1 − m / totalPairs(n)`. -/
noncomputable def qLevel (n : ℕ) (m : ℕ) : ℝ≥0∞ :=
  1 - (m : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)

/-- The **quadratic** per-level not-dropped probability `1 − m²/(n(n−1))`, used
by the cancel stage where `m` active-B agents face `≥ m` active-A agents, so the
drop rate is the rectangle `m²/(n(n−1))`. -/
noncomputable def qLevelSq (n : ℕ) (m : ℕ) : ℝ≥0∞ :=
  1 - (m ^ 2 : ℕ) / ((n * (n - 1) : ℕ) : ℝ≥0∞)

/-- When `Φ c = m`, the `dropTarget` of `Φ` at `c` is exactly `potBelow Φ m`. -/
private theorem dropTarget_eq_potBelow (Φ : Config (AgentState L K) → ℕ)
    (c : Config (AgentState L K)) (m : ℕ) (hm : Φ c = m) :
    dropTarget Φ c = potBelow Φ m := by
  unfold dropTarget potBelow; rw [hm]

/-- **Complement arithmetic.** From a kernel lower bound on the drop target,
`K c (potBelow Φ m)ᶜ ≤ 1 − m/totalPairs`, when `Φ c = m`.  Uses
`K c univ = 1` (Markov) and `measure_compl`. -/
private theorem drop_compl_le
    (Φ : Config (AgentState L K) → ℕ) (c : Config (AgentState L K)) (m : ℕ)
    (hm : Φ c = m)
    (hge : (NonuniformMajority L K).transitionKernel c (dropTarget Φ c) ≥
      (↑(Φ c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)) :
    (NonuniformMajority L K).transitionKernel c (potBelow Φ m)ᶜ ≤
      1 - (m : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  have hdt : dropTarget Φ c = potBelow Φ m := dropTarget_eq_potBelow Φ c m hm
  rw [hdt, hm] at hge
  have hmeas : MeasurableSet (potBelow Φ m) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have htotal : (NonuniformMajority L K).transitionKernel c Set.univ = 1 :=
    measure_univ
  have hcompl : (NonuniformMajority L K).transitionKernel c (potBelow Φ m)ᶜ
      = 1 - (NonuniformMajority L K).transitionKernel c (potBelow Φ m) := by
    rw [← htotal, measure_compl hmeas (measure_ne_top _ _)]
  rw [hcompl]
  exact tsub_le_tsub_left hge 1

end QWiring

/-! ## Majority-case stage invariants (carry `card = n` and a positive signed sum)

The drop-probability lemmas require `2 ≤ card` and `1 ≤ activeACount`.  We thread
these as part of the invariant: in the majority-`A` case the active signed sum
`phase10ActiveSignedSum = activeACount − activeBCount` is a fixed positive integer
`g > 0`, conserved by the kernel; with `card = n` fixed too, `1 ≤ activeACount`
follows (`activeACount = activeBCount + g ≥ g ≥ 1`). -/

section MajStages

open Protocol

/-- Stage-1 majority invariant. -/
def S1 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ c.card = n ∧ 0 < phase10ActiveSignedSum c

/-- Stage-2 majority invariant (additionally no active-`B`). -/
def S2 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  S1 (L := L) (K := K) n c ∧ activeBCount c = 0

/-- Stage-3 majority invariant (additionally no active-`T`). -/
def S3 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  S2 (L := L) (K := K) n c ∧ activeTCount c = 0

/-- Stage-1 mirrored majority invariant (B wins): all phase 10, card `n`,
and negative active signed sum. -/
def S0 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ c.card = n ∧ phase10ActiveSignedSum c < 0

/-- Stage-2 mirrored majority invariant (additionally no active-`A`). -/
def S0_2 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  S0 (L := L) (K := K) n c ∧ activeACount c = 0

/-- Stage-3 mirrored majority invariant (additionally no active-`T`). -/
def S0_3 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  S0_2 (L := L) (K := K) n c ∧ activeTCount c = 0

/-- In a majority-`A` configuration there is at least one active-`A`. -/
theorem one_le_activeACount_of_signedSum_pos {c : Config (AgentState L K)}
    (hpos : 0 < phase10ActiveSignedSum c) : 1 ≤ activeACount c := by
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hpos
  omega

/-- In a majority-`B` configuration there is at least one active-`B`. -/
theorem one_le_activeBCount_of_signedSum_neg {c : Config (AgentState L K)}
    (hneg : phase10ActiveSignedSum c < 0) : 1 ≤ activeBCount c := by
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hneg
  omega

/-- `card` and `phase10ActiveSignedSum` are preserved on a support config of an
all-phase-10 base. -/
private theorem card_signedSum_step
    {n : ℕ} {c c' : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hcard : c.card = n)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    c'.card = n ∧ phase10ActiveSignedSum c' = phase10ActiveSignedSum c := by
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq _ c c' h]; exact hcard
  · unfold Protocol.stepDistOrSelf at h
    split_ifs at h with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at *
      split_ifs at * with h_app
      · exact phase10ActiveSignedSum_stepRel_eq c _ hphase ⟨r₁, r₂, h_app, rfl⟩
      · rfl
    · simp [PMF.support_pure] at h; rw [h]

/-- **`InvClosed` for stage 1** (majority). -/
theorem invClosed_S1 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => S1 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨hphase, hcard, hpos⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ S1 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hpos⟩

/-- **`InvClosed` for stage 2** (majority). -/
theorem invClosed_S2 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => S2 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨hphase, hcard, hpos⟩, hB⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ S2 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hpos⟩,
    activeBCount_step_zero hphase hB hc'⟩

/-- **`InvClosed` for stage 3** (majority). -/
theorem invClosed_S3 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => S3 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨⟨hphase, hcard, hpos⟩, hB⟩, hT⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ S3 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hpos⟩,
    activeBCount_step_zero hphase hB hc'⟩,
    activeTCount_step_zero hphase hB hT hc'⟩

/-- **`InvClosed` for mirrored stage 1** (B-majority). -/
theorem invClosed_S0 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => S0 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨hphase, hcard, hneg⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ S0 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hneg⟩

/-- **`InvClosed` for mirrored stage 2** (B-majority). -/
theorem invClosed_S0_2 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => S0_2 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨hphase, hcard, hneg⟩, hA⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ S0_2 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hneg⟩,
    activeACount_step_zero hphase hA hc'⟩

/-- **`InvClosed` for mirrored stage 3** (B-majority). -/
theorem invClosed_S0_3 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => S0_3 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨⟨hphase, hcard, hneg⟩, hA⟩, hT⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ S0_3 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hneg⟩,
    activeACount_step_zero hphase hA hc'⟩,
    activeTCount_step_zero_B hphase hA hT hc'⟩

/-! ## Per-stage expected-time bounds

Each stage instantiates `coupon_expectedHitting_le_uniform_on` with the stage
invariant, potential, the `InvClosed`/`PotNonincrOn` facts above, and the
per-level drop hypothesis `q := qLevel n` (via the drop-prob lemma).  The uniform
ceiling is `r := n·(n−1)` (`(1 − q m)⁻¹ = n(n−1)/m ≤ n(n−1)` for `1 ≤ m`). -/

section StageBounds

open Protocol

/-- `S2 → Inv2`. -/
theorem inv2_of_S2 {n : ℕ} {c : Config (AgentState L K)}
    (h : S2 (L := L) (K := K) n c) : Inv2 (L := L) (K := K) c :=
  ⟨h.1.1, h.2⟩

/-- `S3 → Inv3`. -/
theorem inv3_of_S3 {n : ℕ} {c : Config (AgentState L K)}
    (h : S3 (L := L) (K := K) n c) : Inv3 (L := L) (K := K) c :=
  ⟨h.1.1.1, h.1.2, h.2⟩

/-- `PotNonincrOn` weakening: a stronger invariant inherits non-increase. -/
private theorem potNonincrOn_weaken
    {Inv Inv' : Config (AgentState L K) → Prop} {Φ : Config (AgentState L K) → ℕ}
    (h : PotNonincrOn (fun c => Inv c) (NonuniformMajority L K).transitionKernel Φ)
    (himp : ∀ c, Inv' c → Inv c) :
    PotNonincrOn (fun c => Inv' c) (NonuniformMajority L K).transitionKernel Φ :=
  fun b hb => h b (himp b hb)

/-- The crude uniform ceiling `(1 − qLevel n m)⁻¹ ≤ n·(n−1)` for `1 ≤ m ≤ M`
(here `M ≤ n·(n−1)` so `m/(n(n−1)) ≤ 1`). -/
theorem qLevel_uniform_ceiling (n M : ℕ) (hMle : M ≤ n * (n - 1)) :
    ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - qLevel n m)⁻¹ ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  intro m hm1 hmM
  set TP : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) with hTPdef
  have hmTP : m ≤ n * (n - 1) := le_trans hmM hMle
  have hpos : 0 < n * (n - 1) := lt_of_lt_of_le hm1 hmTP
  have hTP0 : TP ≠ 0 := by
    rw [hTPdef]; simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hTPtop : TP ≠ ⊤ := by rw [hTPdef]; exact_mod_cast ENNReal.natCast_ne_top _
  have hmle1 : (m : ℝ≥0∞) / TP ≤ 1 := by
    rw [ENNReal.div_le_iff hTP0 hTPtop, one_mul, hTPdef]
    exact_mod_cast hmTP
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsub : 1 - qLevel n m = (m : ℝ≥0∞) / TP := by
    unfold qLevel; rw [hTPdef, ENNReal.sub_sub_cancel ENNReal.one_ne_top hmle1]
  rw [hsub, ENNReal.inv_div (Or.inl hTPtop) (Or.inr hm0)]
  -- TP/m ≤ TP since m ≥ 1
  calc TP / (m : ℝ≥0∞)
      ≤ TP / 1 := ENNReal.div_le_div_left (by exact_mod_cast hm1) TP
    _ = TP := by rw [div_one]

/-! ### Harmonic refinement of the `qLevel` coupon sum

The crude uniform ceiling `(1 − qLevel n m)⁻¹ ≤ n(n−1)` summed over `m ∈ [1,M]`
gives `M·n(n−1)` (`= O(n³)` for `M = O(n)`).  The paper-faithful bound replaces
the per-level constant by the *exact* per-level waiting time `(1 − qLevel n m)⁻¹ =
n(n−1)/m` and sums the harmonic series:

  * **linear-rate stages** (coupon: absorb-T, convert-passive, T-spread) keep
    `qLevel n m = 1 − m/P`, so `∑_{m=1}^{M} P/m = P·H_M ≤ P·(1 + log M)`,
    giving `O(n² log n)` interactions;
  * **quadratic-rate stages** (cancel: `m` active-B against `≥ m` active-A) use
    the refined `qLevelSq n m = 1 − m²/P`, so `∑_{m=1}^{M} P/m² ≤ 2P`, giving
    `O(n²)` interactions.

All bounds below are pure `ℝ≥0∞` arithmetic plus the Mathlib harmonic/`p`-series
facts; no protocol content. -/

/-- The **exact per-level waiting time** for the linear rate: when `1 ≤ m ≤ n(n−1)`,
`(1 − qLevel n m)⁻¹ = n(n−1)/m`. -/
theorem qLevel_inv_eq (n m : ℕ) (hm1 : 1 ≤ m) (hmTP : m ≤ n * (n - 1)) :
    (1 - qLevel n m)⁻¹ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (m : ℝ≥0∞) := by
  set TP : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) with hTPdef
  have hpos : 0 < n * (n - 1) := lt_of_lt_of_le hm1 hmTP
  have hTP0 : TP ≠ 0 := by rw [hTPdef]; simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hTPtop : TP ≠ ⊤ := by rw [hTPdef]; exact_mod_cast ENNReal.natCast_ne_top _
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hmle1 : (m : ℝ≥0∞) / TP ≤ 1 := by
    rw [ENNReal.div_le_iff hTP0 hTPtop, one_mul, hTPdef]; exact_mod_cast hmTP
  have hsub : 1 - qLevel n m = (m : ℝ≥0∞) / TP := by
    unfold qLevel; rw [hTPdef, ENNReal.sub_sub_cancel ENNReal.one_ne_top hmle1]
  rw [hsub, ENNReal.inv_div (Or.inl hTPtop) (Or.inr hm0)]

/-- **Telescope of `log m − log(m−1)` over `[2,M]`.** Standalone (clean
induction with no captured hypotheses). -/
theorem sum_log_diff_telescope (M : ℕ) (hM : 2 ≤ M) :
    ∑ m ∈ Finset.Icc 2 M, (Real.log (m : ℝ) - Real.log ((m : ℝ) - 1))
      = Real.log (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 2 2 = {2} from rfl, Finset.sum_singleton]
    norm_num
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1), ih]
    push_cast
    have hk1 : ((k : ℝ) + 1) - 1 = (k : ℝ) := by ring
    rw [hk1]; ring

/-- **Tail harmonic ≤ log, telescoped.** `∑_{m=2}^{M} 1/m ≤ log M`, via the
per-term bound `1/m ≤ log m − log(m−1)` (from `1 − x⁻¹ ≤ log x` at `x = m/(m−1)`)
and telescoping.  Self-contained (`Real.one_sub_inv_le_log_of_pos`), avoiding the
`NumberTheory.Harmonic` modules (whose oleans are stale in this build). -/
theorem sum_inv_Icc_two_le_log (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, (m : ℝ)⁻¹ ≤ Real.log M := by
  rcases Nat.lt_or_ge M 2 with hM | hM
  · interval_cases M
    · simp
    · simp
  · -- per term: (m:ℝ)⁻¹ ≤ log m - log (m-1) for m ≥ 2
    have hstep : ∀ m ∈ Finset.Icc 2 M,
        (m : ℝ)⁻¹ ≤ Real.log (m : ℝ) - Real.log ((m : ℝ) - 1) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm2 : 2 ≤ m := hm.1
      have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
        linarith
      have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
      have hx : (0 : ℝ) < (m : ℝ) / ((m : ℝ) - 1) := by positivity
      have hkey := Real.one_sub_inv_le_log_of_pos hx
      rw [Real.log_div (by linarith) (by linarith)] at hkey
      have hinv : ((m : ℝ) / ((m : ℝ) - 1))⁻¹ = ((m : ℝ) - 1) / (m : ℝ) := inv_div _ _
      rw [hinv] at hkey
      have hsimp : (1 : ℝ) - ((m : ℝ) - 1) / (m : ℝ) = (m : ℝ)⁻¹ := by
        field_simp; ring
      rw [hsimp] at hkey
      exact hkey
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [sum_log_diff_telescope M hM]

/-- **Harmonic (linear-rate) coupon sum, real form.** `∑_{m∈[1,M]} 1/m ≤ 1 + log M`. -/
theorem sum_inv_Icc_le_one_add_log (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ ≤ 1 + Real.log M := by
  rcases Nat.lt_or_ge M 1 with hM | hM
  · interval_cases M; simp
  · have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h1 : ((1 : ℕ) : ℝ)⁻¹ = 1 := by norm_num
    rw [h1]
    exact add_le_add le_rfl (sum_inv_Icc_two_le_log M)

/-- **Harmonic (linear-rate) coupon sum, `ℝ≥0∞` form.** For the linear `qLevel`,
`∑_{m=1}^{M} (1 − qLevel n m)⁻¹ = ∑ P/m = P·H_M ≤ P·(1 + log M)`.  Stated as a
bound by `(↑P) · ENNReal.ofReal (1 + log M)` for `2 ≤ n`, `1 ≤ M ≤ n(n−1)`. -/
theorem qLevel_coupon_sum_harmonic_le (n M : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M)
    (hMle : M ≤ n * (n - 1)) :
    ∑ m ∈ Finset.Icc 1 M, (1 - qLevel n m)⁻¹ ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) := by
  set TP : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) with hTPdef
  -- rewrite each term to TP/m = TP · (1/m), pull TP out
  have hofm : ∀ m : ℕ, 1 ≤ m → ENNReal.ofReal ((m : ℝ)⁻¹) = ((m : ℝ≥0∞))⁻¹ := by
    intro m hm0
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm0), ENNReal.ofReal_natCast]
  have hterm : ∀ m ∈ Finset.Icc 1 M, (1 - qLevel n m)⁻¹
      = TP * ENNReal.ofReal ((m : ℝ)⁻¹) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [qLevel_inv_eq n m hm.1 (le_trans hm.2 hMle), div_eq_mul_inv, hTPdef, hofm m hm.1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_left' ?_ TP
  -- ∑ ofReal (1/m) ≤ ofReal (∑ 1/m) ≤ ofReal (1 + log M)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact sum_inv_Icc_le_one_add_log M

/-- **`p`-series (quadratic-rate) coupon sum, real form.** `∑_{m=1}^{M} 1/m² ≤ 2`.
Proof by the telescoping bound `1/m² ≤ 1/(m−1) − 1/m` for `m ≥ 2`, plus the
`m = 1` term `= 1`. -/
theorem sum_inv_sq_Icc_le_two (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ((m : ℝ)^2)⁻¹ ≤ 2 := by
  rcases Nat.lt_or_ge M 1 with hM | hM
  · interval_cases M <;> simp
  · -- Icc 1 M = insert 1 (Ioc 1 M); sum = 1 + ∑_{Ioc 1 M} ≤ 1 + (1 - 1/M) ≤ 2
    have hsplit : Finset.Icc 1 M = insert 1 (Finset.Ioc 1 M) := by
      rw [Finset.Icc_eq_cons_Ioc hM, Finset.cons_eq_insert]
    rw [hsplit, Finset.sum_insert (by simp)]
    have htel : ∑ i ∈ Finset.Ioc 1 M, ((i : ℝ)^2)⁻¹ ≤ ((1 : ℕ) : ℝ)⁻¹ - (M : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by norm_num) hM
    rw [show ((1 : ℕ) : ℝ)⁻¹ = 1 by norm_num] at htel
    have hMnn : 0 ≤ (M : ℝ)⁻¹ := by positivity
    calc (((1 : ℕ) : ℝ)^2)⁻¹ + ∑ i ∈ Finset.Ioc 1 M, ((i : ℝ)^2)⁻¹
        ≤ 1 + (1 - (M : ℝ)⁻¹) := by
          rw [show (((1 : ℕ) : ℝ)^2)⁻¹ = 1 by norm_num]
          exact add_le_add le_rfl htel
      _ ≤ 2 := by linarith

/-- **Exact per-level waiting time, quadratic rate.** When `1 ≤ m` and `m² ≤
n(n−1)`, `(1 − qLevelSq n m)⁻¹ = n(n−1)/m²`. -/
theorem qLevelSq_inv_eq (n m : ℕ) (hm1 : 1 ≤ m) (hmTP : m ^ 2 ≤ n * (n - 1)) :
    (1 - qLevelSq n m)⁻¹ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((m ^ 2 : ℕ) : ℝ≥0∞) := by
  set TP : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) with hTPdef
  have hpos : 0 < n * (n - 1) := lt_of_lt_of_le (by positivity) hmTP
  have hTP0 : TP ≠ 0 := by rw [hTPdef]; simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hTPtop : TP ≠ ⊤ := by rw [hTPdef]; exact_mod_cast ENNReal.natCast_ne_top _
  have hm0 : ((m ^ 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; positivity
  have hmle1 : ((m ^ 2 : ℕ) : ℝ≥0∞) / TP ≤ 1 := by
    rw [ENNReal.div_le_iff hTP0 hTPtop, one_mul, hTPdef]; exact_mod_cast hmTP
  have hsub : 1 - qLevelSq n m = ((m ^ 2 : ℕ) : ℝ≥0∞) / TP := by
    unfold qLevelSq; rw [hTPdef, ENNReal.sub_sub_cancel ENNReal.one_ne_top hmle1]
  rw [hsub, ENNReal.inv_div (Or.inl hTPtop) (Or.inr hm0)]

/-- **`p`-series (quadratic-rate) coupon sum, `ℝ≥0∞` form.** For the refined
`qLevelSq n m = 1 − m²/P`, with `M² ≤ P = n(n−1)` (so every active level has
`m² ≤ P`), `∑_{m=1}^{M} (1 − qLevelSq n m)⁻¹ = ∑ P/m² ≤ 2P`. -/
theorem qLevelSq_coupon_sum_le (n M : ℕ) (hMsq : M ^ 2 ≤ n * (n - 1)) :
    ∑ m ∈ Finset.Icc 1 M, (1 - qLevelSq n m)⁻¹ ≤
      2 * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  set TP : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) with hTPdef
  have hofm : ∀ m : ℕ, 1 ≤ m →
      ENNReal.ofReal (((m : ℝ) ^ 2)⁻¹) = (((m ^ 2 : ℕ) : ℝ≥0∞))⁻¹ := by
    intro m hm0
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast]
    push_cast; ring_nf
  have hterm : ∀ m ∈ Finset.Icc 1 M, (1 - qLevelSq n m)⁻¹
      = TP * ENNReal.ofReal (((m : ℝ) ^ 2)⁻¹) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmsq : m ^ 2 ≤ n * (n - 1) :=
      le_trans (Nat.pow_le_pow_left hm.2 2) hMsq
    rw [qLevelSq_inv_eq n m hm.1 hmsq, div_eq_mul_inv, hTPdef, hofm m hm.1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [show (2 : ℝ≥0∞) * TP = TP * ENNReal.ofReal 2 by
    rw [mul_comm]; congr 1; simp [ENNReal.ofReal_ofNat]]
  refine mul_le_mul_left' ?_ TP
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact sum_inv_sq_Icc_le_two M

/-- The drop hypothesis for stage 1: under `S1 n`, the not-dropped mass at level
`m` is `≤ qLevel n m`. -/
theorem hdrop_S1 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), S1 (L := L) (K := K) n b →
      activeBCount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => activeBCount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hBm
  obtain ⟨hphase, hcard, hpos⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  have hA : 1 ≤ activeACount b := one_le_activeACount_of_signedSum_pos hpos
  have hge := activeBCount_drop_prob b hcard2 hphase hA
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => activeBCount c) b m hBm hge
  rw [hTPeq] at hcompl
  -- qLevel n m = 1 - m/(n(n-1)) matches the RHS of hcompl
  unfold qLevel
  exact hcompl

/-- **Stage 1 expected-time bound** (cancel: drive `activeBCount` to `0`).  From an
`S1 n` start `c` with `activeBCount c ≤ M` and `M ≤ n(n−1)`, the expected number of
interactions to reach `{activeBCount = 0}` is `≤ M · n(n−1)`. -/
theorem stage1_expectedHitting_le (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S1 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeBCount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeBCount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
  coupon_expectedHitting_le_uniform_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n)
    (fun c => activeBCount c)
    (potNonincrOn_weaken potNonincrOn_activeBCount (fun _ h => h.1))
    (qLevel n) (hdrop_S1 n hn) M c hM hc
    ((n * (n - 1) : ℕ) : ℝ≥0∞) (qLevel_uniform_ceiling n M hMle)

/-- The drop hypothesis for stage 2 (absorb-T): under `S2 n`. -/
theorem hdrop_S2 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), S2 (L := L) (K := K) n b →
      activeTCount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => activeTCount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hTm
  obtain ⟨⟨hphase, hcard, hpos⟩, hB⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  have hA : 1 ≤ activeACount b := one_le_activeACount_of_signedSum_pos hpos
  have hge := activeTCount_drop_prob b hcard2 hphase hA
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => activeTCount c) b m hTm hge
  rw [hTPeq] at hcompl
  unfold qLevel
  exact hcompl

/-- **Stage 2 expected-time bound** (absorb-T: drive `activeTCount` to `0` once no
active-B remains).  From an `S2 n` start `c` with `activeTCount c ≤ M`, `M ≤ n(n−1)`,
expected interactions to `{activeTCount = 0}` is `≤ M · n(n−1)`. -/
theorem stage2_expectedHitting_le (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S2 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeTCount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeTCount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
  coupon_expectedHitting_le_uniform_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S2 (L := L) (K := K) n c) (invClosed_S2 n)
    (fun c => activeTCount c)
    (potNonincrOn_weaken potNonincrOn_activeTCount (fun _ h => inv2_of_S2 h))
    (qLevel n) (hdrop_S2 n hn) M c hM hc
    ((n * (n - 1) : ℕ) : ℝ≥0∞) (qLevel_uniform_ceiling n M hMle)

/-- The drop hypothesis for stage 3 (convert-passive): under `S3 n`. -/
theorem hdrop_S3 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), S3 (L := L) (K := K) n b →
      wrongACount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => wrongACount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hWm
  obtain ⟨⟨⟨hphase, hcard, hpos⟩, hB⟩, hT⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  have hA : 1 ≤ activeACount b := one_le_activeACount_of_signedSum_pos hpos
  have hge := wrongACount_drop_prob b hcard2 hphase hB hA
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => wrongACount c) b m hWm hge
  rw [hTPeq] at hcompl
  unfold qLevel
  exact hcompl

/-- **Stage 3 expected-time bound** (convert-passive: drive `wrongACount` to `0`).
From an `S3 n` start `c` with `wrongACount c ≤ M`, `M ≤ n(n−1)`, expected
interactions to `{wrongACount = 0}` is `≤ M · n(n−1)`. -/
theorem stage3_expectedHitting_le (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S3 (L := L) (K := K) n c)
    (M : ℕ) (hM : wrongACount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
  coupon_expectedHitting_le_uniform_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S3 (L := L) (K := K) n c) (invClosed_S3 n)
    (fun c => wrongACount c)
    (potNonincrOn_weaken potNonincrOn_wrongACount (fun _ h => inv3_of_S3 h))
    (qLevel n) (hdrop_S3 n hn) M c hM hc
    ((n * (n - 1) : ℕ) : ℝ≥0∞) (qLevel_uniform_ceiling n M hMle)

/-! ### Refined (harmonic) stage bounds — `O(n² log n)` interactions per stage

Same engine, same per-level drop hypotheses, but the coupon sum is evaluated by the
harmonic bound `∑_{m=1}^{M} n(n−1)/m ≤ n(n−1)·(1+log M)` (`qLevel_coupon_sum_harmonic_le`)
rather than the crude uniform ceiling `M·n(n−1)`.  Each refined bound is
`≤ n(n−1)·ofReal(1+log M)`. -/

/-- **Refined stage 1 bound** (cancel, harmonic): `≤ n(n−1)·(1+log M)`. -/
theorem stage1_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S1 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeBCount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeBCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n)
      (fun c => activeBCount c)
      (potNonincrOn_weaken potNonincrOn_activeBCount (fun _ h => h.1))
      (qLevel n) (hdrop_S1 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-- **Refined stage 2 bound** (absorb-T, harmonic): `≤ n(n−1)·(1+log M)`. -/
theorem stage2_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S2 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeTCount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeTCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => S2 (L := L) (K := K) n c) (invClosed_S2 n)
      (fun c => activeTCount c)
      (potNonincrOn_weaken potNonincrOn_activeTCount (fun _ h => inv2_of_S2 h))
      (qLevel n) (hdrop_S2 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-- **Refined stage 3 bound** (convert-passive, harmonic): `≤ n(n−1)·(1+log M)`. -/
theorem stage3_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S3 (L := L) (K := K) n c)
    (M : ℕ) (hM : wrongACount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => S3 (L := L) (K := K) n c) (invClosed_S3 n)
      (fun c => wrongACount c)
      (potNonincrOn_weaken potNonincrOn_wrongACount (fun _ h => inv3_of_S3 h))
      (qLevel n) (hdrop_S3 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-! ### Mirrored B-majority stage bounds -/

/-- `S0_2 → Inv2B`. -/
theorem inv2B_of_S0_2 {n : ℕ} {c : Config (AgentState L K)}
    (h : S0_2 (L := L) (K := K) n c) : Inv2B (L := L) (K := K) c :=
  ⟨h.1.1, h.2⟩

/-- `S0_3 → Inv3B`. -/
theorem inv3B_of_S0_3 {n : ℕ} {c : Config (AgentState L K)}
    (h : S0_3 (L := L) (K := K) n c) : Inv3B (L := L) (K := K) c :=
  ⟨h.1.1.1, h.1.2, h.2⟩

/-- The drop hypothesis for mirrored stage 1: under `S0 n`. -/
theorem hdrop_S0 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), S0 (L := L) (K := K) n b →
      activeACount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => activeACount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hAm
  obtain ⟨hphase, hcard, hneg⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  have hB : 1 ≤ activeBCount b := one_le_activeBCount_of_signedSum_neg hneg
  have hge := activeACount_drop_prob b hcard2 hphase hB
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => activeACount c) b m hAm hge
  rw [hTPeq] at hcompl
  unfold qLevel
  exact hcompl

/-- Mirrored stage 1 expected-time bound, harmonic form. -/
theorem stage1B_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S0 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeACount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeACount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => S0 (L := L) (K := K) n c) (invClosed_S0 n)
      (fun c => activeACount c)
      (potNonincrOn_weaken potNonincrOn_activeACount (fun _ h => h.1))
      (qLevel n) (hdrop_S0 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-- The drop hypothesis for mirrored stage 2 (absorb-T): under `S0_2 n`. -/
theorem hdrop_S0_2 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), S0_2 (L := L) (K := K) n b →
      activeTCount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => activeTCount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hTm
  obtain ⟨⟨hphase, hcard, hneg⟩, hA⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  have hB : 1 ≤ activeBCount b := one_le_activeBCount_of_signedSum_neg hneg
  have hge := activeTCount_drop_prob_B b hcard2 hphase hB
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => activeTCount c) b m hTm hge
  rw [hTPeq] at hcompl
  unfold qLevel
  exact hcompl

/-- Mirrored stage 2 expected-time bound, harmonic form. -/
theorem stage2B_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S0_2 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeTCount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeTCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => S0_2 (L := L) (K := K) n c) (invClosed_S0_2 n)
      (fun c => activeTCount c)
      (potNonincrOn_weaken potNonincrOn_activeTCount_B (fun _ h => inv2B_of_S0_2 h))
      (qLevel n) (hdrop_S0_2 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-- The drop hypothesis for mirrored stage 3 (convert passive): under `S0_3 n`. -/
theorem hdrop_S0_3 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), S0_3 (L := L) (K := K) n b →
      wrongBCount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => wrongBCount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hWm
  obtain ⟨⟨⟨hphase, hcard, hneg⟩, hA⟩, hT⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  have hB : 1 ≤ activeBCount b := one_le_activeBCount_of_signedSum_neg hneg
  have hge := wrongBCount_drop_prob b hcard2 hphase hA hB
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => wrongBCount c) b m hWm hge
  rw [hTPeq] at hcompl
  unfold qLevel
  exact hcompl

/-- Mirrored stage 3 expected-time bound, harmonic form. -/
theorem stage3B_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S0_3 (L := L) (K := K) n c)
    (M : ℕ) (hM : wrongBCount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongBCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => S0_3 (L := L) (K := K) n c) (invClosed_S0_3 n)
      (fun c => wrongBCount c)
      (potNonincrOn_weaken potNonincrOn_wrongBCount (fun _ h => inv3B_of_S0_3 h))
      (qLevel n) (hdrop_S0_3 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

end StageBounds

/-! ## Capstone: Phase-10 backup expected stabilization (majority case)

The stabilized set is `StableDone = {wrongACount = 0}` (every agent outputs the
majority answer `A`).  We record the set-nesting `Done₃ ⊆ Done₂`, `Done₃ ⊆ Done₁`
(`wrongACount = 0 ⟹ activeBCount = activeTCount = 0`, since an active-`B`/`T` source
has output `B`/`T ≠ A`), and deliver the headline from an `S3` start (the final
coupon regime, where all three potentials are simultaneously non-increasing). -/

section Capstone

/-- `countP P ≤ countP Q` when `P` implies `Q` on every member. -/
private theorem countP_le_countP_of_imp {α : Type*}
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Multiset α) (h : ∀ a ∈ s, P a → Q a) :
    Multiset.countP P s ≤ Multiset.countP Q s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons]
      have ih' : Multiset.countP P s ≤ Multiset.countP Q s :=
        ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      by_cases hP : P a
      · have hQ : Q a := h a (Multiset.mem_cons_self a s) hP
        simp only [hP, hQ, if_true]; omega
      · by_cases hQ : Q a <;> simp only [hP, hQ, if_true, if_false] <;> omega

/-- Every active-`B` source is a "wrong" (output `≠ A`) agent, so
`activeBCount ≤ wrongACount`. -/
theorem activeBCount_le_wrongACount (c : Config (AgentState L K)) :
    activeBCount c ≤ wrongACount c := by
  unfold activeBCount wrongACount
  exact countP_le_countP_of_imp IsActiveB (fun a => a.output ≠ Output.A) c
    (fun a _ ha => by show a.output ≠ Output.A; rw [ha.2]; decide)

/-- Every active-`T` source is a "wrong" agent, so `activeTCount ≤ wrongACount`. -/
theorem activeTCount_le_wrongACount (c : Config (AgentState L K)) :
    activeTCount c ≤ wrongACount c := by
  unfold activeTCount wrongACount
  exact countP_le_countP_of_imp IsActiveT (fun a => a.output ≠ Output.A) c
    (fun a _ ha => by show a.output ≠ Output.A; rw [ha.2]; decide)

/-- `wrongACount = 0` forces `activeBCount = 0`. -/
theorem activeBCount_zero_of_wrongACount_zero {c : Config (AgentState L K)}
    (h : wrongACount c = 0) : activeBCount c = 0 :=
  Nat.le_zero.mp (le_trans (activeBCount_le_wrongACount c) (Nat.le_of_eq h))

/-- `wrongACount = 0` forces `activeTCount = 0`. -/
theorem activeTCount_zero_of_wrongACount_zero {c : Config (AgentState L K)}
    (h : wrongACount c = 0) : activeTCount c = 0 :=
  Nat.le_zero.mp (le_trans (activeTCount_le_wrongACount c) (Nat.le_of_eq h))

/-- **Set nesting** `{wrongACount = 0} ⊆ {activeBCount = 0}`. -/
theorem done3_subset_done1 :
    potBelow (fun c => wrongACount (L := L) (K := K) c) 1 ⊆
      potBelow (fun c => activeBCount (L := L) (K := K) c) 1 := by
  intro c hc
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hc ⊢
  exact activeBCount_zero_of_wrongACount_zero hc

/-- **Set nesting** `{wrongACount = 0} ⊆ {activeTCount = 0}`. -/
theorem done3_subset_done2 :
    potBelow (fun c => wrongACount (L := L) (K := K) c) 1 ⊆
      potBelow (fun c => activeTCount (L := L) (K := K) c) 1 := by
  intro c hc
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hc ⊢
  exact activeTCount_zero_of_wrongACount_zero hc

/-- **Phase-10 backup expected stabilization from the final coupon regime (`S3`).**
From an all-phase-10 majority-`A` start with no active-`B` and no active-`T`
(`S3 n`), card `= n ≥ 2`, and `wrongACount ≤ M ≤ n(n−1)`, the expected number of
interactions to reach the stabilized set `{wrongACount = 0}` (all outputs `A`) is
`≤ M · n(n−1) = O(n⁴)` crudely, `O(n² log n)` after the harmonic refinement.  This
is the convert-passive stage as the standalone headline. -/
theorem phase10_expected_stabilization_S3 (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S3 (L := L) (K := K) n c)
    (M : ℕ) (hM : wrongACount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
  stage3_expectedHitting_le n hn c hc M hM hMle

/-! ### Full three-stage chaining (S1 start)

The stabilization time from an `S1` start decomposes additively through the two
intermediate done-sets `Done₁ = {activeBCount = 0}` and (within it)
`Done₂' = Done₁ ∩ {activeTCount = 0}`.  `expectedHitting_le_through_mid` applied
through `Done₁` gives the machine-checked decomposition

  `E[hit Done₃] ≤ E[hit Done₁] + ∑ₜ P(Done₁ ∖ Done₃ at t)`,

with `E[hit Done₁]` discharged by `stage1_expectedHitting_le`.  The residual
cross-term `∑ₜ (K^t) c (Done₁ ∩ Done₃ᶜ)` is the occupation of
`{activeBCount = 0, wrongACount > 0}`; bounding it by the stage-2 + stage-3 coupon
sums is the one remaining obligation (see the closing campaign note: it needs a
`PotNonincrOn`-occupation bound for `activeTCount`/`wrongACount` transported from
the `S1` start, using that `{activeBCount = 0}` is **absorbing** under `S1` so the
run satisfies `S2`/`S3` from its first visit onward — a strong-Markov restart
extension of the `occLevel_le_on` engine). -/

/-- **Three-stage chaining decomposition (machine-checked).** From an `S1` start,
the expected hitting time of the stabilized set `Done₃ = {wrongACount = 0}` splits
as the stage-1 (cancel) time to `Done₁ = {activeBCount = 0}` plus the occupation of
the residual region `{activeBCount = 0, wrongACount > 0}`.  The stage-1 term is
fully bounded; the cross-term is the residual occupation. -/
theorem phase10_expected_stabilization_chain (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S1 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeBCount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
        + ∑' t : ℕ, (((NonuniformMajority L K).transitionKernel) ^ t) c
            (potBelow (fun c => activeBCount c) 1 ∩
              (potBelow (fun c => wrongACount c) 1)ᶜ) := by
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (done3_subset_done1) c) ?_
  exact add_le_add (stage1_expectedHitting_le n hn c hc M hM hMle) le_rfl

/-! ### Closing the chain: the two cross-terms

The remaining work is to bound, unconditionally from an `S1` start, the two
occupation cross-terms produced by chaining through `Done₁ = {activeBCount = 0}`
and `Done₂ = {activeTCount = 0}`.  Both are closed by the generic
`occupation_mid_le_on` (the strong-Markov restart): from an `Sᵢ`-start the band
mass concentrates on `Sᵢ`-states (`InvClosed`), where the next-stage hitting bound
applies.  The key uniform cap is `wrongACount/activeTCount ≤ card = n ≤ n(n−1)`. -/

/-- Any potential counting a subclass of agents is `≤ card = n` under `card = n`. -/
private theorem countP_le_n {n : ℕ} {c : Config (AgentState L K)}
    (P : AgentState L K → Prop) [DecidablePred P]
    (hcard : c.card = n) : Multiset.countP P c ≤ n := by
  rw [← hcard]; exact Multiset.countP_le_card P c

/-- `wrongACount ≤ n(n−1)` for a card-`n` config with `n ≥ 2`. -/
private theorem wrongACount_le_nn {n : ℕ} (hn : 2 ≤ n)
    {c : Config (AgentState L K)} (hcard : c.card = n) :
    wrongACount c ≤ n * (n - 1) := by
  have h1 : wrongACount c ≤ n := countP_le_n _ hcard
  have h2 : n ≤ n * (n - 1) := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  omega

/-- `activeTCount ≤ n(n−1)` for a card-`n` config with `n ≥ 2`. -/
private theorem activeTCount_le_nn {n : ℕ} (hn : 2 ≤ n)
    {c : Config (AgentState L K)} (hcard : c.card = n) :
    activeTCount c ≤ n * (n - 1) := by
  have h1 : activeTCount c ≤ n := countP_le_n _ hcard
  have h2 : n ≤ n * (n - 1) := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  omega

/-- **Stage 2→3 chained hitting bound.** From an `S2 n` start `y` the expected
hitting time of the stabilized set `Done₃ = {wrongACount = 0}` is `≤ 2·n(n−1)·n(n−1)`:
the absorb-T time to `Done₂ = {activeTCount = 0}` (stage 2) plus the occupation of
`Done₂ ∖ Done₃`, the latter closed by `occupation_mid_le_on` with `J = S2`,
`Mid = Done₂`, inner bound from stage 3 (every `S2 ∩ Done₂`-state is `S3`). -/
theorem stage23_expectedHitting_le (n : ℕ) (hn : 2 ≤ n)
    (y : Config (AgentState L K)) (hy : S2 (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y
        (potBelow (fun c => wrongACount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
        + ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  obtain ⟨⟨hphase, hcard, hpos⟩, hB⟩ := hy
  -- E[hit Done₃] ≤ E[hit Done₂] + ∑ₜ (K^t) y (Done₂ ∩ Done₃ᶜ).
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (done3_subset_done2) y) ?_
  refine add_le_add ?_ ?_
  · -- stage 2 with activeTCount y ≤ n(n−1).
    exact stage2_expectedHitting_le n hn y ⟨⟨hphase, hcard, hpos⟩, hB⟩
      (n * (n - 1)) (activeTCount_le_nn hn hcard) le_rfl
  · -- cross-term Done₂ ∩ Done₃ᶜ via occupation_mid_le_on, J = S2.
    refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => S2 (L := L) (K := K) n c) (invClosed_S2 n)
      (potBelow_measurable (fun c => activeTCount c) 1)
      (potBelow_measurable (fun c => wrongACount c) 1)
      _ ?_ y ⟨⟨hphase, hcard, hpos⟩, hB⟩
    -- inner: every S2-state z below activeTCount-level-1 is S3, with wrongACount ≤ n(n−1).
    intro z hzS2 hzMid
    obtain ⟨⟨hzphase, hzcard, hzpos⟩, hzB⟩ := hzS2
    have hzT : activeTCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    exact stage3_expectedHitting_le n hn z ⟨⟨⟨hzphase, hzcard, hzpos⟩, hzB⟩, hzT⟩
      (n * (n - 1)) (wrongACount_le_nn hn hzcard) le_rfl

/-- **Phase-10 backup expected stabilization (majority case, unconditional `S1`
start).** From any all-phase-10 majority-`A` configuration (`S1 n`, card `= n ≥ 2`)
the expected number of interactions to reach the stabilized set `{wrongACount = 0}`
(every agent outputs the majority answer `A`) is `≤ 3·n(n−1)·n(n−1) = O(n⁴)` crudely
(`O(n² log n)` after the orthogonal harmonic refinement).  The three coupon stages
(cancel `activeBCount`, absorb-T `activeTCount`, convert-passive `wrongACount`) are
chained additively through the two intermediate absorbing done-sets, each cross-term
closed by the strong-Markov restart `occupation_mid_le_on`. -/
theorem phase10_expected_stabilization (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S1 (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
        + (((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
            + ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)) := by
  obtain ⟨hphase, hcard, hpos⟩ := hc
  -- E[hit Done₃] ≤ E[hit Done₁] + ∑ₜ (K^t) c (Done₁ ∩ Done₃ᶜ).
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (done3_subset_done1) c) ?_
  refine add_le_add ?_ ?_
  · -- stage 1 with activeBCount c ≤ n(n−1).
    exact stage1_expectedHitting_le n hn c ⟨hphase, hcard, hpos⟩
      (n * (n - 1)) (countP_le_n _ hcard |>.trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))) le_rfl
  · -- cross-term Done₁ ∩ Done₃ᶜ via occupation_mid_le_on, J = S1.
    refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n)
      (potBelow_measurable (fun c => activeBCount c) 1)
      (potBelow_measurable (fun c => wrongACount c) 1)
      _ ?_ c ⟨hphase, hcard, hpos⟩
    -- inner: every S1-state z below activeBCount-level-1 is S2; apply stage23.
    intro z hzS1 hzMid
    have hzB : activeBCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    exact stage23_expectedHitting_le n hn z ⟨hzS1, hzB⟩

/-! ### Refined (harmonic) majority headline — `O(n² log n)` interactions

Same additive stage chaining as `phase10_expected_stabilization`, but each stage is
evaluated by its harmonic refinement (`stageᵢ_expectedHitting_le'`), so the total is
`≤ 3·n(n−1)·(1 + log(n(n−1)))` interactions.  Since `log(n(n−1)) ≤ log(n²) = 2 log n`,
this is `O(n²·log n)` interactions = `O(n·log n)` parallel time (the paper's Lemma
7.7 rate), versus the crude `O(n⁴)` of the un-primed version. -/

/-- Refined stages 2+3 from an `S2` start: `≤ 2·n(n−1)·(1 + log(n(n−1)))`. -/
theorem stage23_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (y : Config (AgentState L K)) (hy : S2 (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y
        (potBelow (fun c => wrongACount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
        + ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ)) := by
  obtain ⟨⟨hphase, hcard, hpos⟩, hB⟩ := hy
  have hP1 : 1 ≤ n * (n - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (done3_subset_done2) y) ?_
  refine add_le_add ?_ ?_
  · exact stage2_expectedHitting_le' n hn y ⟨⟨hphase, hcard, hpos⟩, hB⟩
      (n * (n - 1)) (activeTCount_le_nn hn hcard) hP1 le_rfl
  · refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => S2 (L := L) (K := K) n c) (invClosed_S2 n)
      (potBelow_measurable (fun c => activeTCount c) 1)
      (potBelow_measurable (fun c => wrongACount c) 1)
      _ ?_ y ⟨⟨hphase, hcard, hpos⟩, hB⟩
    intro z hzS2 hzMid
    obtain ⟨⟨hzphase, hzcard, hzpos⟩, hzB⟩ := hzS2
    have hzT : activeTCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    exact stage3_expectedHitting_le' n hn z ⟨⟨⟨hzphase, hzcard, hzpos⟩, hzB⟩, hzT⟩
      (n * (n - 1)) (wrongACount_le_nn hn hzcard) hP1 le_rfl

/-- **Refined Phase-10 backup expected stabilization (majority, `S1` start).**
`≤ 3·n(n−1)·(1 + log(n(n−1)))` interactions = `O(n² log n)`, the paper-faithful
Lemma 7.7 rate (vs the crude `O(n⁴)` of `phase10_expected_stabilization`). -/
theorem phase10_expected_stabilization' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S1 (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
        + (((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
            + ((n * (n - 1) : ℕ) : ℝ≥0∞)
                * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))) := by
  obtain ⟨hphase, hcard, hpos⟩ := hc
  have hP1 : 1 ≤ n * (n - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (done3_subset_done1) c) ?_
  refine add_le_add ?_ ?_
  · exact stage1_expectedHitting_le' n hn c ⟨hphase, hcard, hpos⟩
      (n * (n - 1)) (countP_le_n _ hcard |>.trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))) hP1 le_rfl
  · refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n)
      (potBelow_measurable (fun c => activeBCount c) 1)
      (potBelow_measurable (fun c => wrongACount c) 1)
      _ ?_ c ⟨hphase, hcard, hpos⟩
    intro z hzS1 hzMid
    have hzB : activeBCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    exact stage23_expectedHitting_le' n hn z ⟨hzS1, hzB⟩

/-- Per-stage term bound: `n(n−1)·(1 + log(n(n−1))) ≤ n²·(1 + 2·log n)`.  Uses
`n(n−1) ≤ n²` and `log(n(n−1)) ≤ log(n²) = 2 log n` (`n ≥ 1`). -/
theorem stage_term_le_nsq_log (n : ℕ) (hn : 2 ≤ n) :
    ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
      ≤ ((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n) := by
  have hPle : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤ ((n ^ 2 : ℕ) : ℝ≥0∞) := by
    apply Nat.cast_le.mpr; rw [pow_two]; exact Nat.mul_le_mul_left n (by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hPpos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) :=
      Nat.pos_of_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have hlogle : Real.log ((n * (n - 1) : ℕ) : ℝ) ≤ 2 * Real.log n := by
    have hmono : Real.log ((n * (n - 1) : ℕ) : ℝ) ≤ Real.log ((n ^ 2 : ℕ) : ℝ) := by
      refine Real.log_le_log hPpos ?_
      apply Nat.cast_le.mpr; rw [pow_two]; exact Nat.mul_le_mul_left n (by omega)
    refine le_trans hmono ?_
    rw [show ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 by push_cast; ring,
      Real.log_pow]
    push_cast; rw [mul_comm]
  refine mul_le_mul' hPle ?_
  apply ENNReal.ofReal_le_ofReal
  linarith [hlogle]

/-- **Collapsed `O(n² log n)` majority headline.** The refined bound, written as a
single clean `≤ 3·n²·(1 + 2·log n)` interaction count.  Dividing by `n` (the
file's parallel-time convention, see the header) gives `3·n·(1 + 2·log n) =
O(n·log n)` parallel time — the paper's Lemma 7.7 rate.  `C = 3`, shape
`n²·(1 + log n)`. -/
theorem phase10_expected_stabilization_O_nsq_log (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S1 (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongACount c) 1) ≤
      3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  refine le_trans (phase10_expected_stabilization' n hn c hc) ?_
  have hterm := stage_term_le_nsq_log n hn
  set A : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞)
    * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ)) with hA
  set B : ℝ≥0∞ := ((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n) with hB
  calc A + (A + A) ≤ B + (B + B) :=
        add_le_add hterm (add_le_add hterm hterm)
    _ = 3 * B := by ring

/-! ### Mirrored B-majority capstone -/

/-- Every active-`A` source is a "wrong" (output `≠ B`) agent, so
`activeACount ≤ wrongBCount`. -/
theorem activeACount_le_wrongBCount (c : Config (AgentState L K)) :
    activeACount c ≤ wrongBCount c := by
  unfold activeACount wrongBCount
  exact countP_le_countP_of_imp IsActiveA (fun a => a.output ≠ Output.B) c
    (fun a _ ha => by show a.output ≠ Output.B; rw [ha.2]; decide)

/-- Every active-`T` source is wrong for B, so `activeTCount ≤ wrongBCount`. -/
theorem activeTCount_le_wrongBCount (c : Config (AgentState L K)) :
    activeTCount c ≤ wrongBCount c := by
  unfold activeTCount wrongBCount
  exact countP_le_countP_of_imp IsActiveT (fun a => a.output ≠ Output.B) c
    (fun a _ ha => by show a.output ≠ Output.B; rw [ha.2]; decide)

/-- `wrongBCount = 0` forces `activeACount = 0`. -/
theorem activeACount_zero_of_wrongBCount_zero {c : Config (AgentState L K)}
    (h : wrongBCount c = 0) : activeACount c = 0 :=
  Nat.le_zero.mp (le_trans (activeACount_le_wrongBCount c) (Nat.le_of_eq h))

/-- `wrongBCount = 0` forces `activeTCount = 0`. -/
theorem activeTCount_zero_of_wrongBCount_zero {c : Config (AgentState L K)}
    (h : wrongBCount c = 0) : activeTCount c = 0 :=
  Nat.le_zero.mp (le_trans (activeTCount_le_wrongBCount c) (Nat.le_of_eq h))

/-- **Set nesting** `{wrongBCount = 0} ⊆ {activeACount = 0}`. -/
theorem doneB_subset_done1 :
    potBelow (fun c => wrongBCount (L := L) (K := K) c) 1 ⊆
      potBelow (fun c => activeACount (L := L) (K := K) c) 1 := by
  intro c hc
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hc ⊢
  exact activeACount_zero_of_wrongBCount_zero hc

/-- **Set nesting** `{wrongBCount = 0} ⊆ {activeTCount = 0}`. -/
theorem doneB_subset_done2 :
    potBelow (fun c => wrongBCount (L := L) (K := K) c) 1 ⊆
      potBelow (fun c => activeTCount (L := L) (K := K) c) 1 := by
  intro c hc
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hc ⊢
  exact activeTCount_zero_of_wrongBCount_zero hc

/-- `wrongBCount ≤ n(n−1)` for a card-`n` config with `n ≥ 2`. -/
private theorem wrongBCount_le_nn {n : ℕ} (hn : 2 ≤ n)
    {c : Config (AgentState L K)} (hcard : c.card = n) :
    wrongBCount c ≤ n * (n - 1) := by
  have h1 : wrongBCount c ≤ n := countP_le_n _ hcard
  have h2 : n ≤ n * (n - 1) := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  omega

/-- **Mirrored stage 2→3 chained hitting bound.** From an `S0_2 n` start the
expected hitting time of `{wrongBCount = 0}` is at most two harmonic stage terms. -/
theorem stage23B_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (y : Config (AgentState L K)) (hy : S0_2 (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y
        (potBelow (fun c => wrongBCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
        + ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ)) := by
  obtain ⟨⟨hphase, hcard, hneg⟩, hA⟩ := hy
  have hP1 : 1 ≤ n * (n - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (doneB_subset_done2) y) ?_
  refine add_le_add ?_ ?_
  · exact stage2B_expectedHitting_le' n hn y ⟨⟨hphase, hcard, hneg⟩, hA⟩
      (n * (n - 1)) (activeTCount_le_nn hn hcard) hP1 le_rfl
  · refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => S0_2 (L := L) (K := K) n c) (invClosed_S0_2 n)
      (potBelow_measurable (fun c => activeTCount c) 1)
      (potBelow_measurable (fun c => wrongBCount c) 1)
      _ ?_ y ⟨⟨hphase, hcard, hneg⟩, hA⟩
    intro z hzS0_2 hzMid
    obtain ⟨⟨hzphase, hzcard, hzneg⟩, hzA⟩ := hzS0_2
    have hzT : activeTCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    exact stage3B_expectedHitting_le' n hn z ⟨⟨⟨hzphase, hzcard, hzneg⟩, hzA⟩, hzT⟩
      (n * (n - 1)) (wrongBCount_le_nn hn hzcard) hP1 le_rfl

/-- **Refined Phase-10 backup expected stabilization (B-majority, `S0` start).** -/
theorem phase10_expected_stabilization_B' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S0 (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongBCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
        + (((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
            + ((n * (n - 1) : ℕ) : ℝ≥0∞)
                * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))) := by
  obtain ⟨hphase, hcard, hneg⟩ := hc
  have hP1 : 1 ≤ n * (n - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (doneB_subset_done1) c) ?_
  refine add_le_add ?_ ?_
  · exact stage1B_expectedHitting_le' n hn c ⟨hphase, hcard, hneg⟩
      (n * (n - 1)) (countP_le_n _ hcard |>.trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))) hP1 le_rfl
  · refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => S0 (L := L) (K := K) n c) (invClosed_S0 n)
      (potBelow_measurable (fun c => activeACount c) 1)
      (potBelow_measurable (fun c => wrongBCount c) 1)
      _ ?_ c ⟨hphase, hcard, hneg⟩
    intro z hzS0 hzMid
    have hzA : activeACount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    exact stage23B_expectedHitting_le' n hn z ⟨hzS0, hzA⟩

/-- **Collapsed `O(n² log n)` B-majority headline.** Same budget as the A-majority
branch, by the exact A/B mirror. -/
theorem phase10_expected_stabilization_B_O_nsq_log (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : S0 (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongBCount c) 1) ≤
      3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  refine le_trans (phase10_expected_stabilization_B' n hn c hc) ?_
  have hterm := stage_term_le_nsq_log n hn
  set A : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞)
    * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ)) with hA
  set B : ℝ≥0∞ := ((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n) with hB
  calc A + (A + A) ≤ B + (B + B) :=
        add_le_add hterm (add_le_add hterm hterm)
    _ = 3 * B := by ring

end Capstone

/-! ## Tie case (`backupSignal = 0`, i.e. `phase10ActiveSignedSum = 0`)

When the signed active sum is `0`, `activeACount = activeBCount` throughout, so the
majority invariant's `0 < phase10ActiveSignedSum` fails.  The stabilization is
two-stage:

* **Tie cancel stage** `Φ := activeBCount` on `Tie1 := AllPhase10 ∧ card = n ∧
  signedSum = 0`.  The cancel drop-prob `activeBCount_drop_prob` needs `1 ≤
  activeACount`; under `Tie1` with `activeBCount = m ≥ 1`, `activeACount = m ≥ 1`
  holds (signed sum `0`), so it applies VERBATIM.  After this stage
  `activeACount = activeBCount = 0` (signed sum `0`), so every remaining active
  agent is active-`T`.

* **T-spread stage** `Φ := wrongTCount` on `Tie2 := Tie1 ∧ activeBCount = 0`
  (whence also `activeACount = 0`).  An active-`T` converts any non-active-biased
  partner to output `T`; under `Tie2` every non-`T` agent is passive (not
  active-A/B), so it is a valid conversion target.  This is the genuinely new drop
  family `wrongTCount_drop_prob`.

The two stages chain through `Done = {activeBCount = 0}` exactly as in the majority
case, the cross-term closed by `occupation_mid_le_on` with `J = Tie1`. -/

section TieStages

open Protocol

/-- Tie-case stage-1 invariant (cancel): all phase-10, fixed card, signed sum `0`. -/
def Tie1 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllPhase10 (L := L) (K := K) c ∧ c.card = n ∧ phase10ActiveSignedSum c = 0

/-- Tie-case stage-2 invariant (T-spread): additionally no active-`B` (hence, with
signed sum `0`, no active-`A`). -/
def Tie2 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Tie1 (L := L) (K := K) n c ∧ activeBCount c = 0

/-- Under a tie (`signedSum = 0`), `activeACount = activeBCount`. -/
theorem activeACount_eq_activeBCount_of_tie {c : Config (AgentState L K)}
    (h : phase10ActiveSignedSum c = 0) : activeACount c = activeBCount c := by
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at h
  omega

/-- Under `Tie2`, `activeACount = 0`. -/
theorem activeACount_zero_of_Tie2 {n : ℕ} {c : Config (AgentState L K)}
    (h : Tie2 (L := L) (K := K) n c) : activeACount c = 0 := by
  obtain ⟨⟨_, _, hsum⟩, hB⟩ := h
  rw [activeACount_eq_activeBCount_of_tie hsum]; exact hB

/-- **`InvClosed` for the tie cancel stage** (`Tie1`). -/
theorem invClosed_Tie1 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Tie1 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨hphase, hcard, hsum⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Tie1 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hsum⟩

/-- **`InvClosed` for the tie T-spread stage** (`Tie2`). -/
theorem invClosed_Tie2 (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Tie2 (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨hphase, hcard, hsum⟩, hB⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Tie2 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hsum⟩,
    activeBCount_step_zero hphase hB hc'⟩

/-- The drop hypothesis for the tie cancel stage: under `Tie1`, the not-dropped
mass at level `m` is `≤ qLevel n m`.  Uses that `activeACount = activeBCount = m`
when `m ≥ 1` (so `1 ≤ activeACount`), so `activeBCount_drop_prob` applies. -/
theorem hdrop_Tie1 (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), Tie1 (L := L) (K := K) n b →
      activeBCount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => activeBCount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hBm
  obtain ⟨hphase, hcard, hsum⟩ := hb
  have hcard2 : 2 ≤ b.card := by omega
  -- For the drop-prob lemma we need 1 ≤ activeACount only when m ≥ 1; when m = 0
  -- the complement set is empty so the bound is vacuous.  Handle both via case split.
  by_cases hm0 : m = 0
  · -- m = 0: potBelow Φ 0 = ∅, complement = univ; but qLevel n 0 = 1, kernel mass ≤ 1.
    subst hm0
    have h1 : (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => activeBCount c) 0)ᶜ ≤ 1 := kernel_pow_le_one _ 1 b _ |>.trans_eq' (by rw [pow_one])
    have hq0 : qLevel n 0 = 1 := by
      unfold qLevel
      simp
    rw [hq0]; exact h1
  · have hAm : activeACount b = m := by
      rw [activeACount_eq_activeBCount_of_tie hsum, hBm]
    have hA : 1 ≤ activeACount b := by rw [hAm]; omega
    have hge := activeBCount_drop_prob b hcard2 hphase hA
    have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
      unfold Config.totalPairs; rw [hcard]
    have hcompl := drop_compl_le (fun c => activeBCount c) b m hBm hge
    rw [hTPeq] at hcompl
    unfold qLevel
    exact hcompl

/-- **Tie cancel-stage expected-time bound.** From a `Tie1 n` start `c` with
`activeBCount c ≤ M ≤ n(n−1)`, expected interactions to `{activeBCount = 0}` is
`≤ M · n(n−1)`. -/
theorem tie_stage1_expectedHitting_le (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie1 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeBCount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeBCount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
  coupon_expectedHitting_le_uniform_on
    (NonuniformMajority L K).transitionKernel
    (fun c => Tie1 (L := L) (K := K) n c) (invClosed_Tie1 n)
    (fun c => activeBCount c)
    (potNonincrOn_weaken potNonincrOn_activeBCount (fun _ h => h.1))
    (qLevel n) (hdrop_Tie1 n hn) M c hM hc
    ((n * (n - 1) : ℕ) : ℝ≥0∞) (qLevel_uniform_ceiling n M hMle)

/-! ### T-spread stage drop machinery (`wrongTCount`, active-T × wrong-not-biased)

This mirrors the `wrongACount` coupon-stage chain (`activeAWrongPairs` …
`wrongACount_drop_prob`), swapping the driver class active-A → active-T and the
responder class "wrong-not-activeB" → "wrong-not-biased" (output ≠ T and not active
A/B).  An active-T meeting a non-biased partner converts the partner's output to T
(`Phase10Transition_activeT_noActiveBiased_outputs_T`), strictly lowering
`wrongTCount`.  Under `Tie2` (no active-A/B) every wrong-T agent is non-biased, so
the responder count equals `wrongTCount`. -/

/-- The "wrong, not active-biased" responder class: output `≠ T` and not an active
A/B source.  Such an agent is converted to output `T` by an active-T partner. -/
def WrongNotBiased (a : AgentState L K) : Prop :=
  a.output ≠ Output.T ∧ ¬ (a.full = true ∧ (a.output = Output.A ∨ a.output = Output.B))

instance : DecidablePred (@WrongNotBiased L K) := fun a => by
  unfold WrongNotBiased; infer_instance

/-- Count of wrong-not-biased agents. -/
def wrongNotTBiasedCount (c : Config (AgentState L K)) : ℕ :=
  c.countP WrongNotBiased

/-- `wrongTCount` of the post-convert configuration is strictly below the base, for
an active-T meeting a wrong-not-biased partner (converted to output `T`).  Re-derived
in-file from `Phase10Transition_activeT_noActiveBiased_outputs_T`. -/
theorem wrongTCount_post_convert_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveT a) (hb : WrongNotBiased b) :
    wrongTCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      wrongTCount c := by
  obtain ⟨hb_wrong, hb_nb⟩ := hb
  have hne : a ≠ b := by
    intro h; subst h; exact hb_wrong ha.2
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
        ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
      (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
        (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb_wrong
    · simp only [not_not]; exact ha.2
  have hlocal :=
    Phase10Transition_activeT_noActiveBiased_outputs_T
      (L := L) (K := K) a b ha.1 ha.2 hb_nb
  have hpair_after :
      Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    obtain ⟨h1out, h2out⟩ := hlocal
    change Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · simp only [not_not]; exact h2out
    · simp only [not_not]; exact h1out
  have hres :
      Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T)
        (c - ({a, b} : Multiset (AgentState L K))) =
        wrongTCount c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ
      (fun x : AgentState L K => x.output ≠ Output.T)
    unfold wrongTCount
    rw [hsub, hpair_before]
  have hpos_old : 0 < wrongTCount c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb_wrong
  have hbridge : wrongTCount c
      = Multiset.countP (fun x : AgentState L K => x.output ≠ Output.T) c := rfl
  unfold wrongTCount
  rw [Multiset.countP_add, hpair_after, hres]
  rw [← hbridge] at *
  omega

/-- An active-T × wrong-not-biased ordered pair lands in the `wrongTCount`-drop
target. -/
theorem scheduledStep_activeT_wrong_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveT a) (hb : WrongNotBiased b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (wrongTCount (L := L) (K := K)) c := by
  have hne : a ≠ b := by intro h; subst h; exact hb.1 ha.2
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact wrongTCount_post_convert_lt c hphase ha_mem hb_mem ha hb

/-- The active-T × wrong-not-biased rectangle of ordered pairs. -/
def activeTWrongPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveT a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => WrongNotBiased a))

/-- The total `interactionCount` over the active-T × wrong-not-biased rectangle
equals `activeTCount c · wrongNotTBiasedCount c`. -/
theorem sum_interactionCount_activeTWrong (c : Config (AgentState L K)) :
    (∑ p ∈ activeTWrongPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeTCount c * wrongNotTBiasedCount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveT a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => WrongNotBiased a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    exact hb.2.1 ha.2.2
  rw [activeTWrongPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveT a), c.count a)
      = Multiset.countP IsActiveT c from
    (HourCouplingAzuma.countP_eq_sum_count IsActiveT c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => WrongNotBiased a), c.count b)
      = Multiset.countP WrongNotBiased c from
    (HourCouplingAzuma.countP_eq_sum_count WrongNotBiased c).symm]
  rfl

/-- When `activeACount c = 0` and `activeBCount c = 0`, every wrong-`T` agent is
non-biased, so `wrongNotTBiasedCount c = wrongTCount c`. -/
theorem wrongNotTBiasedCount_eq_wrongTCount_of_no_biased
    (c : Config (AgentState L K)) (hA : activeACount c = 0) (hB : activeBCount c = 0) :
    wrongNotTBiasedCount c = wrongTCount c := by
  classical
  unfold wrongNotTBiasedCount wrongTCount
  apply Multiset.countP_congr rfl
  intro a ha
  have hnotA : ¬ IsActiveA a :=
    (Multiset.countP_eq_zero.1 (by simpa [activeACount] using hA)) a ha
  have hnotB : ¬ IsActiveB a :=
    (Multiset.countP_eq_zero.1 (by simpa [activeBCount] using hB)) a ha
  have hnb : ¬ (a.full = true ∧ (a.output = Output.A ∨ a.output = Output.B)) := by
    rintro ⟨hfull, hout⟩
    rcases hout with hA' | hB'
    · exact hnotA ⟨hfull, hA'⟩
    · exact hnotB ⟨hfull, hB'⟩
  simp only [WrongNotBiased, hnb, not_false_iff, and_true]

/-- The present active-T × wrong-not-biased pairs. -/
def presentActiveTWrongPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeTWrongPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-T × wrong-not-biased pairs
equals `activeTCount · wrongNotTBiasedCount / totalPairs`. -/
theorem sum_interactionProb_presentActiveTWrong (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveTWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2)
      = (↑(activeTCount c * wrongNotTBiasedCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hpresent : (∑ p ∈ presentActiveTWrongPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeTWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    apply Finset.sum_subset (s₁ := presentActiveTWrongPairs (L := L) (K := K) c)
      (Finset.filter_subset _ _)
    intro p hp_in hpnot
    rw [presentActiveTWrongPairs, Finset.mem_filter, not_and, not_and_or, not_le, not_le,
      Nat.lt_one_iff, Nat.lt_one_iff] at hpnot
    have hcounts : c.count p.1 = 0 ∨ c.count p.2 = 0 := hpnot hp_in
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [hpp, h2, Nat.zero_mul]
      · rw [if_neg hpp]
        rcases hcounts with h1 | h2
        · rw [h1, Nat.zero_mul]
        · rw [h2, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeTWrong, ← div_eq_mul_inv]

/-- **T-spread stage per-level drop probability.** On an all-phase-10 configuration
with `activeACount = activeBCount = 0` (the post-cancel tie regime) and at least one
active-`T`, the kernel maps into the `wrongTCount`-drop set with probability
`≥ wrongTCount c / (n·(n−1))`. -/
theorem wrongTCount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hA : activeACount c = 0) (hB : activeBCount c = 0)
    (hT : 1 ≤ activeTCount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (wrongTCount (L := L) (K := K)) c) ≥
      (↑(wrongTCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  have hgood : ∀ pair ∈ presentActiveTWrongPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (wrongTCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveTWrongPairs, activeTWrongPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hT1⟩, ⟨_, hW2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeT_wrong_in_drop c hphase ha_mem hb_mem hT1 hW2
    simpa using this
  have hge := stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (wrongTCount (L := L) (K := K)) c)
    (↑(presentActiveTWrongPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveTWrongPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveTWrongPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveTWrong] at hSmeasure
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  apply ENNReal.div_le_div_right
  rw [wrongNotTBiasedCount_eq_wrongTCount_of_no_biased c hA hB]
  have : wrongTCount c ≤ activeTCount c * wrongTCount c := by
    calc wrongTCount c = 1 * wrongTCount c := (Nat.one_mul _).symm
      _ ≤ activeTCount c * wrongTCount c := Nat.mul_le_mul_right _ hT
  exact_mod_cast this

/-! ### T-spread stage: monotonicity, liveness invariant, drop, stage bound -/

/-- **`PotNonincrOn` for `wrongTCount` on `Tie2`.** Under `Tie2` every agent is
active-`T` or passive (no active-A/B), so the per-pair `wrongTCount` bound applies. -/
theorem potNonincrOn_wrongTCount (n : ℕ) :
    PotNonincrOn (fun c => Tie2 (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel
      (fun c => wrongTCount c) :=
  potNonincrOn_of_countP_step (fun c => Tie2 (L := L) (K := K) n c)
    (fun a => a.output ≠ Output.T)
    (fun c hInv c' hc' => by
      have hA : activeACount c = 0 := activeACount_zero_of_Tie2 hInv
      obtain ⟨⟨hphase, _, _⟩, hB⟩ := hInv
      have hphase' : ∀ x ∈ c, x.phase.val = 10 := hphase
      have hnoA : ∀ x ∈ c, ¬ IsActiveA x := fun x hx =>
        (Multiset.countP_eq_zero.1 (by simpa [activeACount] using hA)) x hx
      have hnoB : ∀ x ∈ c, ¬ IsActiveB x := fun x hx =>
        (Multiset.countP_eq_zero.1 (by simpa [activeBCount] using hB)) x hx
      exact countP_scheduledStep_le (fun a => a.output ≠ Output.T) hc'
        (fun r₁ r₂ hr₁ hr₂ =>
          Transition_wrongTCount_le r₁ r₂ (hphase' r₁ hr₁) (hphase' r₂ hr₂)
            (hnoA r₁ hr₁) (hnoA r₂ hr₂) (hnoB r₁ hr₁) (hnoB r₂ hr₂)))

/-- A support config of an all-phase-10 base inherits `hasActiveAgent`. -/
private theorem hasActiveAgent_step
    {c c' : Config (AgentState L K)} (hphase : AllPhase10 (L := L) (K := K) c)
    (hact : hasActiveAgent c)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    hasActiveAgent c' := by
  unfold Protocol.stepDistOrSelf at h
  split_ifs at h with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
    subst heq
    unfold Protocol.scheduledStep Protocol.stepOrSelf at *
    split_ifs at * with h_app
    · exact phase10_hasActiveAgent_preserved_by_step c _ hphase hact ⟨r₁, r₂, h_app, rfl⟩
    · simpa using hact
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at h; rw [h]; exact hact

/-- Tie-case T-spread liveness invariant: `Tie2` together with `hasActiveAgent`
(at least one active agent — which, under `Tie2`, is necessarily active-`T`). -/
def Tie2plus (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Tie2 (L := L) (K := K) n c ∧ hasActiveAgent c

/-- **`InvClosed` for the tie T-spread liveness stage** (`Tie2plus`). -/
theorem invClosed_Tie2plus (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Tie2plus (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨⟨hphase, hcard, hsum⟩, hB⟩, hact⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Tie2plus (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hsum⟩,
    activeBCount_step_zero hphase hB hc'⟩, hasActiveAgent_step hphase hact hc'⟩

/-- `Tie2plus → Tie2`. -/
theorem tie2_of_Tie2plus {n : ℕ} {c : Config (AgentState L K)}
    (h : Tie2plus (L := L) (K := K) n c) : Tie2 (L := L) (K := K) n c := h.1

/-- The drop hypothesis for the tie T-spread stage: under `Tie2plus`, the
not-dropped mass at level `m` is `≤ qLevel n m`.  Uses `1 ≤ activeTCount` from
`hasActiveAgent` + no-active-A/B. -/
theorem hdrop_Tie2plus (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K), Tie2plus (L := L) (K := K) n b →
      wrongTCount b = m →
      (NonuniformMajority L K).transitionKernel b
        (potBelow (fun c => wrongTCount c) m)ᶜ ≤ qLevel n m := by
  intro m b hb hWm
  obtain ⟨hTie2, hact⟩ := hb
  have hA : activeACount b = 0 := activeACount_zero_of_Tie2 hTie2
  obtain ⟨⟨hphase, hcard, _⟩, hB⟩ := hTie2
  have hcard2 : 2 ≤ b.card := by omega
  have hT : 1 ≤ activeTCount b := by
    obtain ⟨a, ha_mem, ha⟩ :=
      exists_activeT_of_hasActive_no_activeA_no_activeB b hact hA hB
    exact Multiset.countP_pos_of_mem (s := b) ha_mem ha
  have hge := wrongTCount_drop_prob b hcard2 hphase hA hB hT
  have hTPeq : (b.totalPairs : ℝ≥0∞) = ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs; rw [hcard]
  have hcompl := drop_compl_le (fun c => wrongTCount c) b m hWm hge
  rw [hTPeq] at hcompl
  unfold qLevel
  exact hcompl

/-- **Tie T-spread-stage expected-time bound.** From a `Tie2plus n` start `c` with
`wrongTCount c ≤ M ≤ n(n−1)`, expected interactions to `{wrongTCount = 0}` (all
outputs `T`) is `≤ M · n(n−1)`. -/
theorem tie_stage2_expectedHitting_le (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie2plus (L := L) (K := K) n c)
    (M : ℕ) (hM : wrongTCount c ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongTCount c) 1) ≤
      (M : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) :=
  coupon_expectedHitting_le_uniform_on
    (NonuniformMajority L K).transitionKernel
    (fun c => Tie2plus (L := L) (K := K) n c) (invClosed_Tie2plus n)
    (fun c => wrongTCount c)
    (potNonincrOn_weaken (potNonincrOn_wrongTCount n) (fun _ h => tie2_of_Tie2plus h))
    (qLevel n) (hdrop_Tie2plus n hn) M c hM hc
    ((n * (n - 1) : ℕ) : ℝ≥0∞) (qLevel_uniform_ceiling n M hMle)

/-! ### Tie-case combined headline (`Tie1` + liveness start) -/

/-- Every active-`B` source has output `B ≠ T`, so `activeBCount ≤ wrongTCount`. -/
theorem activeBCount_le_wrongTCount (c : Config (AgentState L K)) :
    activeBCount c ≤ wrongTCount c :=
  countP_le_countP_of_imp IsActiveB (fun a => a.output ≠ Output.T) c
    (fun a _ ha => by show a.output ≠ Output.T; rw [ha.2]; decide)

/-- `wrongTCount = 0` forces `activeBCount = 0`. -/
theorem activeBCount_zero_of_wrongTCount_zero {c : Config (AgentState L K)}
    (h : wrongTCount c = 0) : activeBCount c = 0 :=
  Nat.le_zero.mp (le_trans (activeBCount_le_wrongTCount c) (Nat.le_of_eq h))

/-- **Set nesting** `{wrongTCount = 0} ⊆ {activeBCount = 0}` (tie case). -/
theorem doneT_subset_done1 :
    potBelow (fun c => wrongTCount (L := L) (K := K) c) 1 ⊆
      potBelow (fun c => activeBCount (L := L) (K := K) c) 1 := by
  intro c hc
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hc ⊢
  exact activeBCount_zero_of_wrongTCount_zero hc

/-- Tie-case stage-1 liveness invariant: `Tie1` together with `hasActiveAgent`. -/
def Tie1plus (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Tie1 (L := L) (K := K) n c ∧ hasActiveAgent c

/-- **`InvClosed` for the tie cancel liveness stage** (`Tie1plus`). -/
theorem invClosed_Tie1plus (n : ℕ) :
    InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Tie1plus (L := L) (K := K) n c) := by
  intro b hb
  obtain ⟨⟨hphase, hcard, hsum⟩, hact⟩ := hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
    {x | ¬ Tie1plus (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  obtain ⟨hc'card, hc'sum⟩ := card_signedSum_step hphase hcard hc'
  exact ⟨⟨allPhase10_step hphase hc', hc'card, hc'sum ▸ hsum⟩,
    hasActiveAgent_step hphase hact hc'⟩

/-- **Phase-10 backup expected stabilization (TIE case, unconditional `Tie1` +
liveness start).** From any all-phase-10 tie configuration (`Tie1 n`, card `= n ≥
2`, signed sum `0`) with at least one active agent, the expected number of
interactions to reach `{wrongTCount = 0}` (every agent outputs the tie answer `T`)
is `≤ 2·n(n−1)·n(n−1)`.  The two coupon stages (cancel `activeBCount`, T-spread
`wrongTCount`) are chained through the absorbing `Done₁ = {activeBCount = 0}`, the
cross-term closed by `occupation_mid_le_on` with `J = Tie1plus`. -/
theorem phase10_expected_stabilization_tie (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie1plus (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongTCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
        + ((n * (n - 1) : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  obtain ⟨⟨hphase, hcard, hsum⟩, hact⟩ := hc
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (doneT_subset_done1) c) ?_
  refine add_le_add ?_ ?_
  · -- tie cancel stage with activeBCount c ≤ n(n−1).
    exact tie_stage1_expectedHitting_le n hn c ⟨hphase, hcard, hsum⟩
      (n * (n - 1)) (countP_le_n _ hcard |>.trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))) le_rfl
  · -- cross-term Done₁ ∩ Doneᵀᶜ via occupation_mid_le_on, J = Tie1plus.
    refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => Tie1plus (L := L) (K := K) n c) (invClosed_Tie1plus n)
      (potBelow_measurable (fun c => activeBCount c) 1)
      (potBelow_measurable (fun c => wrongTCount c) 1)
      _ ?_ c ⟨⟨hphase, hcard, hsum⟩, hact⟩
    -- inner: every Tie1plus-state z below activeBCount-level-1 is Tie2plus.
    intro z hzT1p hzMid
    obtain ⟨⟨hzphase, hzcard, hzsum⟩, hzact⟩ := hzT1p
    have hzB : activeBCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    have hWle : wrongTCount z ≤ n * (n - 1) :=
      (countP_le_n (fun a => a.output ≠ Output.T) hzcard).trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))
    exact tie_stage2_expectedHitting_le n hn z ⟨⟨⟨hzphase, hzcard, hzsum⟩, hzB⟩, hzact⟩
      (n * (n - 1)) hWle le_rfl

/-! ### Refined (harmonic) tie stage bounds + headline — `O(n² log n)` interactions -/

/-- **Refined tie cancel stage** (harmonic): `≤ n(n−1)·(1 + log M)`. -/
theorem tie_stage1_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie1 (L := L) (K := K) n c)
    (M : ℕ) (hM : activeBCount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => activeBCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => Tie1 (L := L) (K := K) n c) (invClosed_Tie1 n)
      (fun c => activeBCount c)
      (potNonincrOn_weaken potNonincrOn_activeBCount (fun _ h => h.1))
      (qLevel n) (hdrop_Tie1 n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-- **Refined tie T-spread stage** (harmonic): `≤ n(n−1)·(1 + log M)`. -/
theorem tie_stage2_expectedHitting_le' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie2plus (L := L) (K := K) n c)
    (M : ℕ) (hM : wrongTCount c ≤ M) (hM1 : 1 ≤ M) (hMle : M ≤ n * (n - 1)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongTCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log M) :=
  le_trans
    (coupon_expectedHitting_le_on
      (NonuniformMajority L K).transitionKernel
      (fun c => Tie2plus (L := L) (K := K) n c) (invClosed_Tie2plus n)
      (fun c => wrongTCount c)
      (potNonincrOn_weaken (potNonincrOn_wrongTCount n) (fun _ h => tie2_of_Tie2plus h))
      (qLevel n) (hdrop_Tie2plus n hn) M c hM hc)
    (qLevel_coupon_sum_harmonic_le n M hn hM1 hMle)

/-- **Refined Phase-10 backup expected stabilization (TIE case, `Tie1plus` start).**
`≤ 2·n(n−1)·(1 + log(n(n−1)))` interactions = `O(n² log n)` (paper Lemma 7.7 rate),
vs the crude `O(n⁴)` of `phase10_expected_stabilization_tie`. -/
theorem phase10_expected_stabilization_tie' (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie1plus (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongTCount c) 1) ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ))
        + ((n * (n - 1) : ℕ) : ℝ≥0∞)
            * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ)) := by
  obtain ⟨⟨hphase, hcard, hsum⟩, hact⟩ := hc
  have hP1 : 1 ≤ n * (n - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine le_trans
    (expectedHitting_le_through_mid (NonuniformMajority L K).transitionKernel
      (doneT_subset_done1) c) ?_
  refine add_le_add ?_ ?_
  · exact tie_stage1_expectedHitting_le' n hn c ⟨hphase, hcard, hsum⟩
      (n * (n - 1)) (countP_le_n _ hcard |>.trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))) hP1 le_rfl
  · refine occupation_mid_le_on (NonuniformMajority L K).transitionKernel
      (fun c => Tie1plus (L := L) (K := K) n c) (invClosed_Tie1plus n)
      (potBelow_measurable (fun c => activeBCount c) 1)
      (potBelow_measurable (fun c => wrongTCount c) 1)
      _ ?_ c ⟨⟨hphase, hcard, hsum⟩, hact⟩
    intro z hzT1p hzMid
    obtain ⟨⟨hzphase, hzcard, hzsum⟩, hzact⟩ := hzT1p
    have hzB : activeBCount z = 0 := by
      simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hzMid; exact hzMid
    have hWle : wrongTCount z ≤ n * (n - 1) :=
      (countP_le_n (fun a => a.output ≠ Output.T) hzcard).trans (by
        calc n = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega))
    exact tie_stage2_expectedHitting_le' n hn z ⟨⟨⟨hzphase, hzcard, hzsum⟩, hzB⟩, hzact⟩
      (n * (n - 1)) hWle hP1 le_rfl

/-- **Collapsed `O(n² log n)` tie headline.** `≤ 2·n²·(1 + 2·log n)` interactions;
divided by `n` (parallel convention), `2·n·(1 + 2·log n) = O(n·log n)` parallel.
`C = 2`, shape `n²·(1 + log n)`. -/
theorem phase10_expected_stabilization_tie_O_nsq_log (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : Tie1plus (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (potBelow (fun c => wrongTCount c) 1) ≤
      2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  refine le_trans (phase10_expected_stabilization_tie' n hn c hc) ?_
  have hterm := stage_term_le_nsq_log n hn
  set A : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞)
    * ENNReal.ofReal (1 + Real.log ((n * (n - 1) : ℕ) : ℝ)) with hA
  set B : ℝ≥0∞ := ((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n) with hB
  calc A + A ≤ B + B := add_le_add hterm hterm
    _ = 2 * B := by ring

/-- **Unconditional Phase-10 ready predicate.** Doty Lemma 7.7 proves the
A-majority case WLOG; the B-majority branch is the exact mirror `S0`. -/
def Phase10Ready (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  S1 (L := L) (K := K) n c ∨
    S0 (L := L) (K := K) n c ∨
      Tie1plus (L := L) (K := K) n c

end TieStages

end MajStages

end Phase10Drop

end ExactMajority

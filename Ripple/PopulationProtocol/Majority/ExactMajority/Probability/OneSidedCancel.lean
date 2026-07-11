/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic one-sided cancellation engine (Doty §6, Phases 7 & 8)

A reusable, protocol-agnostic engine for the **one-sided elimination** arguments
the blueprint assigns to Phases 7 and 8 (and reusable for Phase-5-style "everyone
gets hit" arguments).  The paper template is Doty et al. Lemma 4.7:

> A subpopulation `A` maintains its size above `a·n` (the **eliminators**), while a
> subpopulation `B` of targets is drained: every `A`-`B` interaction forces one
> agent in `B` to leave (a one-sided cancel reaction `a, b → a, 0`).  After
> `i` cancel reactions `|B| = b₁·n − i`; the time until `B` reaches `0` is whp
> `O(n log n)`.

We package this entirely in the existing kernel-power / `ℝ≥0∞` language.  We model
the target count by an abstract potential `Φ : Config → ℕ` (the size of `B`), and
the eliminator pool by a per-step **drop probability** lower bound carried by an
invariant `Inv` (the floor `|A| ≥ a·n`).  Two whp tails are delivered:

* **Form (b) — crude uniform.**  When `Φ ≥ 1`, a single interaction drains a target
  with probability `≥ 1 − q` (`q = 1 − eFloor/(n(n−1))`-shape).  A single geometric
  gives `(K^t) c {1 ≤ Φ} ≤ q^t`.  Horizon `t = Θ(n²)`; cheap fallback.  Packaged as
  `oneSidedCancel_crude_PhaseConvergenceW`.

* **Form (a) — level-decomposed (paper-faithful `O(n log n)`).**  Per target-level
  `m`, the drop rate is `eFloor·m/(n(n−1))`-shape, so the level-`m` window drains
  geometrically at its own (faster, level-dependent) rate.  Splitting the horizon
  `T = ∑_{m} t_m` into per-level windows and union-bounding gives
  `(K^T) c {1 ≤ Φ} ≤ ∑_{m=1}^{M₀} q_m ^ {t_m}`, the coupon-collector tail.  Packaged
  as `oneSidedCancel_levels_PhaseConvergenceW`.

Both reuse the invariant-relative level machinery from `Phase10ExpectedTime.lean`
(`PotNonincrOn`, `InvClosed`, `potDone`, `potBelow`, `level_occ_geometric_on`,
`pow_above_eq_zero_of_start_le_on`).  The *new* generic addition here is the
**fixed-horizon union-over-levels tail** (`levels_union_tail`): the level engine
there delivers `E[T]` (a `tsum`), whereas Phases 7/8 need a whp tail at a *fixed*
horizon `T`, which is the union over level windows.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

set_option linter.unusedSectionVars false

namespace OneSidedCancel

/-! ## Inlined generic level machinery

The invariant-relative level engine lives in `Phase10ExpectedTime.lean`, but that
file is under active development by a parallel agent (it currently does not build).
The handoff explicitly permits lifting the few self-contained generic defs we need
into this file under our own namespace with distinct (un-clashing) names.  These
are verbatim copies of the protocol-agnostic generic lemmas; they depend on nothing
protocol-specific. -/

section LevelMachinery

variable {α : Type*} [MeasurableSpace α]

/-- The "done" set of a `ℕ`-valued potential: where `Φ` has hit `0`. -/
def potDone (Φ : α → ℕ) : Set α := {x | Φ x = 0}

/-- The set of states strictly below level `m`. -/
def potBelow (Φ : α → ℕ) (m : ℕ) : Set α := {x | Φ x < m}

theorem potDone_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) :
    MeasurableSet (potDone Φ) :=
  DiscreteMeasurableSpace.forall_measurableSet _

theorem potBelow_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potBelow Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- `Inv` is closed under one kernel step: from an `Inv`-state the next-step mass on
`¬ Inv` is `0`. -/
def InvClosed (K : Kernel α α) (Inv : α → Prop) : Prop :=
  ∀ b : α, Inv b → K b {x | ¬ Inv x} = 0

/-- `Φ` is non-increasing along `K` **from every `Inv`-state**. -/
def PotNonincrOn (Inv : α → Prop) (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, Inv b → K b {x | Φ b < Φ x} = 0

/-- From an `Inv`-start the `(K^t)`-mass on `¬ Inv` stays `0`. -/
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
theorem potBelow_absorbing_on
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
`≤ m`. -/
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

/-- **One-step level-`m` occupation contraction** (invariant-relative). -/
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

end LevelMachinery

/-! ## Form (b) — the crude uniform whp tail

The simplest one-sided cancellation: while any target remains (`Φ ≥ 1`, i.e. the
state is in `(potDone Φ)ᶜ`), a single interaction fails to drain a target with
probability at most `q`.  Targets never increase (`PotNonincrOn`), so `{Φ = 0}` is
absorbing, and a single geometric over the not-done class gives `q^t`.

This is the `Φ`-potential specialization of `CounterTimeout.counterTimeout_tail_perStep`
with `Done := potDone Φ = {Φ = 0}`.  The eliminator floor enters only through `q`. -/

section Crude

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- `potDone Φ = {Φ = 0}` is absorbing under a target-count non-increasing on the
invariant: from a `{Φ = 0}`-state in `Inv`, one step cannot leave `{Φ = 0}`
(it cannot strictly raise `Φ`).  This is the `potDone` specialization of
`potBelow_absorbing_on` at `m = 1` (`{Φ < 1} = {Φ = 0}`). -/
theorem potDone_absorbing_on (K : Kernel α α) (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : PotNonincrOn Inv K Φ) :
    ∀ x ∈ potDone Φ, Inv x → K x (potDone Φ)ᶜ = 0 := by
  intro x hx hInv
  -- {Φ = 0} = {Φ < 1} = potBelow Φ 1, and its complement is {1 ≤ Φ}.
  have hxlt : x ∈ potBelow Φ 1 := by
    simp only [potBelow, Set.mem_setOf_eq]
    have : Φ x = 0 := hx
    omega
  have hcompl : (potDone Φ)ᶜ = (potBelow Φ 1)ᶜ := by
    ext y; simp only [potDone, potBelow, Set.mem_compl_iff, Set.mem_setOf_eq]; omega
  rw [hcompl]
  exact potBelow_absorbing_on K Inv Φ hmono 1 x hxlt hInv

/-- **One-step crude contraction.**  Under non-increasing `Φ` on `Inv` and a uniform
per-step drop bound on the not-done class, appending one step to horizon `t`
contracts the not-done mass by `q`:
`(K^(t+1)) c (potDone Φ)ᶜ ≤ q · (K^t) c (potDone Φ)ᶜ`, for an `Inv`-start `c`.

Mirrors `level_occ_contract_on` but at the absorbing target `{Φ = 0}`: a.e. the
chain is in `Inv` (by `InvClosed`); on `{Φ = 0}` the bad mass is `0` (absorbing),
on `{1 ≤ Φ}` the one-step bad mass is `≤ q` (`hstep`). -/
theorem crude_contract (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℝ≥0∞)
    (hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q)
    (c : α) (hInvc : Inv c) (t : ℕ) :
    (K ^ (t + 1)) c (potDone Φ)ᶜ ≤ q * (K ^ t) c (potDone Φ)ᶜ := by
  classical
  have hbad : MeasurableSet ((potDone Φ)ᶜ : Set α) := (potDone_measurable Φ).compl
  have hAbs : ∀ x ∈ potDone Φ, Inv x → K x (potDone Φ)ᶜ = 0 :=
    potDone_absorbing_on K Inv Φ hmono
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b (potDone Φ)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potDone Φ)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        -- a.e. b lives in Inv (InvClosed).
        have hnull_inv : (K ^ t) c {x | ¬ Inv x} = 0 :=
          pow_not_inv_eq_zero K Inv hClosed c hInvc t
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | Inv x}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have hcompl : ({x | Inv x}ᶜ : Set α) = {x | ¬ Inv x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          rw [hcompl]; exact hnull_inv
        · intro b hbInv
          simp only [Set.mem_setOf_eq] at hbInv
          by_cases hb0 : Φ b = 0
          · -- Φ b = 0: b ∈ potDone, Inv b, absorbing ⇒ K b bad = 0.
            have hbdone : b ∈ potDone Φ := hb0
            rw [hAbs b hbdone hbInv]; exact zero_le'
          · -- 1 ≤ Φ b: b ∈ (potDone Φ)ᶜ, so indicator = 1, and K b bad ≤ q.
            have hbmem : b ∈ ((potDone Φ)ᶜ : Set α) := by
              simp only [potDone, Set.mem_compl_iff, Set.mem_setOf_eq]; exact hb0
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hstep b hbInv (by omega)
    _ = q * (K ^ t) c (potDone Φ)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- **Form (b): crude whp tail.**  Under a target count `Φ` non-increasing on `Inv`
(`PotNonincrOn`) with `Inv` `K`-closed (`InvClosed`), and a uniform per-step drop
bound `hstep` — from every `Inv`-state with at least one target remaining, a single
interaction fails to drain a target with probability `≤ q` — the not-done mass
decays geometrically: starting from an `Inv`-state, after `t` interactions at least
one target remains with probability `≤ q^t`.

`(potDone Φ)ᶜ = {y | 1 ≤ Φ y}` is the "still has a target" event. -/
theorem crude_tail (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℝ≥0∞)
    (hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q)
    (c : α) (hInvc : Inv c) (t : ℕ) :
    (K ^ t) c (potDone Φ)ᶜ ≤ q ^ t := by
  induction t with
  | zero =>
      simp only [pow_zero]
      calc (K ^ 0) c (potDone Φ)ᶜ ≤ (K ^ 0) c Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ t ih =>
      calc (K ^ (t + 1)) c (potDone Φ)ᶜ
          ≤ q * (K ^ t) c (potDone Φ)ᶜ :=
            crude_contract K Inv hClosed Φ hmono q hstep c hInvc t
        _ ≤ q * q ^ t := by gcongr
        _ = q ^ (t + 1) := by rw [pow_succ]; ring

/-- **Form (b): crude whp tail, packaged as a `PhaseConvergenceW`.**

`Pre x = Inv x ∧ Φ x ≤ M₀` (the eliminator/target floor invariant plus a target
budget — `M₀` is unused in the crude bound but recorded for chaining), and
`Post x = Inv x ∧ Φ x = 0` (still in the invariant, no targets left).  The horizon
is `t` interactions with failure `ε ≥ q^t`.

The `¬Post` event `{¬(Inv ∧ Φ = 0)}` is covered by `{¬Inv} ∪ {1 ≤ Φ}`; from an
`Inv`-start the `{¬Inv}` mass is `0` (invariant closure), and the `{1 ≤ Φ}` mass is
`≤ q^t` (`crude_tail`). -/
noncomputable def crude_PhaseConvergenceW (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℝ≥0∞)
    (hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0)
    (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre x := Inv x ∧ Φ x ≤ M₀
  Post x := Inv x ∧ Φ x = 0
  t := t
  ε := ε
  convergence := by
    intro x₀ hPre₀
    obtain ⟨hInvx₀, _⟩ := hPre₀
    -- {¬Post} ⊆ {¬Inv} ∪ (potDone Φ)ᶜ.
    have hcover : {y : α | ¬ (Inv y ∧ Φ y = 0)} ⊆ {x | ¬ Inv x} ∪ (potDone Φ)ᶜ := by
      intro y hy
      simp only [Set.mem_setOf_eq, not_and] at hy
      by_cases hInvy : Inv y
      · exact Or.inr (by simp only [potDone, Set.mem_compl_iff, Set.mem_setOf_eq]; exact hy hInvy)
      · exact Or.inl hInvy
    calc (K ^ t) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
        ≤ (K ^ t) x₀ ({x | ¬ Inv x} ∪ (potDone Φ)ᶜ) := measure_mono hcover
      _ ≤ (K ^ t) x₀ {x | ¬ Inv x} + (K ^ t) x₀ (potDone Φ)ᶜ := measure_union_le _ _
      _ = 0 + (K ^ t) x₀ (potDone Φ)ᶜ := by
          rw [pow_not_inv_eq_zero K Inv hClosed x₀ hInvx₀ t]
      _ = (K ^ t) x₀ (potDone Φ)ᶜ := by rw [zero_add]
      _ ≤ q ^ t := crude_tail K Inv hClosed Φ hmono q hstep x₀ hInvx₀ t
      _ ≤ (ε : ℝ≥0∞) := hε

end Crude

/-! ## Form (a) — the level-decomposed paper-faithful whp tail

The crude tail uses a single uniform per-step drop probability, giving a `Θ(n²)`
horizon.  The paper's `O(n log n)` comes from the **level-dependent** drop rate:
when `Φ = m` targets remain, the per-interaction drain probability is
`eFloor·m / (n(n−1))`-shape — proportional to `m`.  So the level-`m` window
geometric tail uses `q_m = 1 − eFloor·m/(n(n−1))`, and the total horizon
`T = ∑_{m=1}^{M₀} t_m` is the coupon-collector sum.

We deliver the engine over an abstract level-dependent rate family `q : ℕ → ℝ≥0∞`
and a per-level window family `tWin : ℕ → ℕ`.  The whp tail at the fixed horizon
`T = ∑_{m=1}^{M₀} tWin m` is the union over level windows:

    (K^T) c {1 ≤ Φ} ≤ ∑_{m=1}^{M₀} (q m) ^ (tWin m).

The key new generic addition (absent from the E[T]-flavored level engine) is the
**fixed-horizon union-over-levels tail** `levels_union_tail`, proved by induction on
the number of levels via a Chapman-Kolmogorov split through the absorbing nested
sets `{Φ < m}`. -/

section Levels

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The level-`m` geometric tail, specialized for the union bound: for an `Inv`-start
at level `≤ m`, the mass still at-or-above level `m` after `t` steps is `≤ (q m)^t`.
This is `level_occ_geometric_on` packaged at the per-level rate `q m`. -/
theorem level_tail (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (m : ℕ) (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
    (K ^ t) c (potBelow Φ m)ᶜ ≤ (q m) ^ t :=
  level_occ_geometric_on K Inv hClosed Φ hmono m (q m) (hdrop m) c hc hInvc t

/-- **Chapman-Kolmogorov split through an absorbing level set.** For `1 ≤ m`, the mass
still above level `0` after `s + t` steps splits: either the first `s` steps fail to
drop below level `m` (mass `≤ (q m)^s`, since the start is at level `≤ m`), or they
do drop below `m`, landing at level `≤ m − 1` for the remaining `t` steps.  Formally:

    (K^(s+t)) c (potBelow Φ 1)ᶜ
      ≤ (K^s) c (potBelow Φ m)ᶜ
        + ∫_{potBelow Φ m} (K^t) b (potBelow Φ 1)ᶜ d((K^s) c).

The integral restricts to `{Φ < m}` = states at level `≤ m − 1`, the recursion base
for the next window. -/
theorem level_split_step (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℕ) (m : ℕ) (c : α) (s t : ℕ) :
    (K ^ (s + t)) c (potBelow Φ 1)ᶜ
      ≤ (K ^ s) c (potBelow Φ m)ᶜ
        + ∫⁻ b in (potBelow Φ m), (K ^ t) b (potBelow Φ 1)ᶜ ∂((K ^ s) c) := by
  have hbad1 : MeasurableSet ((potBelow Φ 1)ᶜ : Set α) := (potBelow_measurable Φ 1).compl
  have hbadm : MeasurableSet (potBelow Φ m : Set α) := potBelow_measurable Φ m
  -- (K^(s+t)) c B₁ᶜ = ∫ (K^t) b B₁ᶜ d((K^s) c), split the base measure over {Φ < m}.
  rw [Kernel.pow_add_apply_eq_lintegral K s t c hbad1]
  rw [← lintegral_add_compl _ hbadm]
  -- The {Φ < m} part is kept; the {Φ ≥ m} part is bounded by (K^s) c B_mᶜ.
  rw [add_comm]
  gcongr
  -- ∫_{(potBelow Φ m)ᶜ} (K^t) b B₁ᶜ d((K^s) c) ≤ (K^s) c (potBelow Φ m)ᶜ.
  calc ∫⁻ b in ((potBelow Φ m)ᶜ), (K ^ t) b (potBelow Φ 1)ᶜ ∂((K ^ s) c)
      ≤ ∫⁻ _ in ((potBelow Φ m)ᶜ), (1 : ℝ≥0∞) ∂((K ^ s) c) := by
        apply lintegral_mono
        intro b
        exact kernel_pow_le_one K t b _
    _ = (K ^ s) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- **Fixed-horizon union-over-levels tail (the new generic addition).**  Under a
target count `Φ` non-increasing on `Inv` (`PotNonincrOn`), `Inv` `K`-closed
(`InvClosed`), and a level-dependent per-step drop bound `hdrop` (when `Φ = m`, one
step drops below `m` with probability `≥ 1 − q m`), starting from an `Inv`-state at
level `≤ M₀`, after the total horizon `T = ∑_{m=1}^{M₀} tWin m` the mass still above
level `0` is bounded by the union over level windows:

    (K^(∑_{m=1}^{M₀} tWin m)) c (potBelow Φ 1)ᶜ ≤ ∑_{m=1}^{M₀} (q m) ^ (tWin m).

This is the coupon-collector whp tail.  For the Doty Phase 7/8 instantiation,
`q m = 1 − eFloor·m/(n(n−1))`-shape and `tWin m = Θ(n(n−1)/(eFloor·m) · log n)`, so
each term is `n^{-Θ(1)}` and `T = Θ(n log n / eFloor-fraction)`. -/
theorem levels_union_tail (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (tWin : ℕ → ℕ) :
    ∀ (M₀ : ℕ) (c : α), Φ c ≤ M₀ → Inv c →
      (K ^ (∑ m ∈ Finset.Icc 1 M₀, tWin m)) c (potBelow Φ 1)ᶜ
        ≤ ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by
  intro M₀
  induction M₀ with
  | zero =>
      intro c hc _hInvc
      -- Φ c ≤ 0 ⇒ Φ c = 0 ⇒ c ∈ potBelow Φ 1 ⇒ (K^0) c B₁ᶜ = 0.  Sum over ∅ = 0.
      have hc0 : Φ c = 0 := Nat.le_zero.mp hc
      have hmem : c ∈ potBelow Φ 1 := by
        simp only [potBelow, Set.mem_setOf_eq]; omega
      have heval : (K ^ (∑ m ∈ Finset.Icc 1 0, tWin m)) c (potBelow Φ 1)ᶜ = 0 := by
        simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1),
          Finset.sum_empty]
        rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
          Measure.dirac_apply' c ((potBelow_measurable Φ 1).compl)]
        have : c ∉ ((potBelow Φ 1)ᶜ : Set α) := by
          simp only [Set.mem_compl_iff]; exact fun h => h hmem
        simp [this]
      rw [heval]
      simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1), Finset.sum_empty,
        le_refl]
  | succ M₀ ih =>
      intro c hc hInvc
      set s := tWin (M₀ + 1) with hs
      set T' := ∑ m ∈ Finset.Icc 1 M₀, tWin m with hT'
      -- Horizon: ∑_{m=1}^{M₀+1} tWin m = s + T'.
      have hsum : ∑ m ∈ Finset.Icc 1 (M₀ + 1), tWin m = s + T' := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M₀ + 1), hs, hT', add_comm]
      have hsumRHS : ∑ m ∈ Finset.Icc 1 (M₀ + 1), (q m) ^ (tWin m)
          = (q (M₀ + 1)) ^ s + ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M₀ + 1), hs, add_comm]
      rw [hsum, hsumRHS]
      -- Chapman-Kolmogorov split through the absorbing level set {Φ < M₀+1}.
      refine le_trans (level_split_step K Φ (M₀ + 1) c s T') ?_
      apply add_le_add
      · -- top-level window: (K^s) c (potBelow Φ (M₀+1))ᶜ ≤ (q (M₀+1))^s.
        exact level_tail K Inv hClosed Φ hmono q hdrop (M₀ + 1) c hc hInvc s
      · -- residual: ∫_{potBelow Φ (M₀+1)} (K^T') b B₁ᶜ d((K^s) c) ≤ ∑_{m=1}^{M₀} (q m)^(tWin m).
        -- a.e. b in the base measure is in Inv; on {Φ < M₀+1} ∩ Inv, IH gives the bound.
        have hbase_inv : (K ^ s) c {x | ¬ Inv x} = 0 :=
          pow_not_inv_eq_zero K Inv hClosed c hInvc s
        have hbadm : MeasurableSet (potBelow Φ (M₀ + 1) : Set α) :=
          potBelow_measurable Φ (M₀ + 1)
        calc ∫⁻ b in (potBelow Φ (M₀ + 1)), (K ^ T') b (potBelow Φ 1)ᶜ ∂((K ^ s) c)
            ≤ ∫⁻ _ in (potBelow Φ (M₀ + 1)),
                (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) ∂((K ^ s) c) := by
              apply lintegral_mono_ae
              -- a.e. on the restricted measure: b ∈ Inv (null set {¬Inv} removed).
              rw [ae_restrict_iff' hbadm]
              -- Show: a.e. b, b ∈ potBelow (M₀+1) → (K^T') b B₁ᶜ ≤ RHS.
              have hnull : (K ^ s) c {x | ¬ Inv x} = 0 := hbase_inv
              rw [Filter.eventually_iff_exists_mem]
              refine ⟨{x | Inv x}, ?_, ?_⟩
              · rw [mem_ae_iff]
                have hcompl : ({x | Inv x}ᶜ : Set α) = {x | ¬ Inv x} := by
                  ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
                rw [hcompl]; exact hnull
              · intro b hbInv hbmem
                simp only [Set.mem_setOf_eq] at hbInv
                have hblev : Φ b ≤ M₀ := by
                  have : b ∈ potBelow Φ (M₀ + 1) := hbmem
                  simp only [potBelow, Set.mem_setOf_eq] at this; omega
                exact ih b hblev hbInv
          _ ≤ ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              calc (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) * ((K ^ s) c (potBelow Φ (M₀ + 1)))
                  ≤ (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) * 1 := by
                    gcongr; exact kernel_pow_le_one K s c _
                _ = ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by rw [mul_one]

/-- **Form (a): level-decomposed whp tail, packaged as a `PhaseConvergenceW`.**

Same `Pre`/`Post` shape as the crude packaging (`Pre = Inv ∧ Φ ≤ M₀`,
`Post = Inv ∧ Φ = 0`), but the horizon is the coupon-collector sum
`T = ∑_{m=1}^{M₀} tWin m` and the failure budget is the union-over-levels tail
`ε ≥ ∑_{m=1}^{M₀} (q m)^(tWin m)`.  This is the paper-faithful `O(n log n)` engine:
with the level-dependent rate `q m = 1 − eFloor·m/(n(n−1))`-shape, the horizon is
`Θ(n log n / eFloor-fraction)` and the failure is `O(1/n²)`.

`{¬Post} ⊆ {¬Inv} ∪ (potBelow Φ 1)ᶜ`; the `{¬Inv}` mass vanishes from an `Inv`-start,
and the `(potBelow Φ 1)ᶜ` mass is `≤ ∑ (q m)^(tWin m)` by `levels_union_tail`. -/
noncomputable def levels_PhaseConvergenceW (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre x := Inv x ∧ Φ x ≤ M₀
  Post x := Inv x ∧ Φ x = 0
  t := ∑ m ∈ Finset.Icc 1 M₀, tWin m
  ε := ε
  convergence := by
    intro x₀ hPre₀
    obtain ⟨hInvx₀, hΦx₀⟩ := hPre₀
    -- {¬Post} ⊆ {¬Inv} ∪ (potBelow Φ 1)ᶜ.
    have hcover : {y : α | ¬ (Inv y ∧ Φ y = 0)} ⊆ {x | ¬ Inv x} ∪ (potBelow Φ 1)ᶜ := by
      intro y hy
      simp only [Set.mem_setOf_eq, not_and] at hy
      by_cases hInvy : Inv y
      · refine Or.inr ?_
        simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
        have := hy hInvy; omega
      · exact Or.inl hInvy
    set T := ∑ m ∈ Finset.Icc 1 M₀, tWin m with hT
    calc (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
        ≤ (K ^ T) x₀ ({x | ¬ Inv x} ∪ (potBelow Φ 1)ᶜ) := measure_mono hcover
      _ ≤ (K ^ T) x₀ {x | ¬ Inv x} + (K ^ T) x₀ (potBelow Φ 1)ᶜ := measure_union_le _ _
      _ = 0 + (K ^ T) x₀ (potBelow Φ 1)ᶜ := by
          rw [pow_not_inv_eq_zero K Inv hClosed x₀ hInvx₀ T]
      _ = (K ^ T) x₀ (potBelow Φ 1)ᶜ := by rw [zero_add]
      _ ≤ ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by
          rw [hT]
          exact levels_union_tail K Inv hClosed Φ hmono q hdrop tWin M₀ x₀ hΦx₀ hInvx₀
      _ ≤ (ε : ℝ≥0∞) := hε

end Levels

end OneSidedCancel

end ExactMajority

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asynchronous Phase-0/1 entry via an aggregate depth moment

An exact Phase-1 window does not imply that every Clock is still at the
literal Phase-1 reset.  During the phase epidemic, a newly infected Clock is
reset by `phaseInit 1` and then immediately selected by `Phase1Transition`, so
it leaves that interaction one counter unit below reset.  Earlier infected
Clocks may be deeper still.

This file replaces the false pointwise-reset seam with a distributional
payload on the real protocol kernel.  At a chosen Phase-0/1 seam horizon `T`,
the payload consists of

* the mass outside the genuine positive-clock Phase-1 gate; and
* the aggregate exponential counter-depth moment on the good part.

The subsequent far-mass drain and clock survival run for `H` more interactions
on the same kernel.  Chapman--Kolmogorov transfers the two entry moments
directly, without selecting a synthetic synchronous endpoint and without
assuming agent identities.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1JointStopped

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1AsyncAggregateEntry

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

abbrev Cfg (L K : ℕ) := Config (AgentState L K)

private theorem isMarkovKernel_pow {α : Type*} [MeasurableSpace α]
    (κ : Kernel α α) [IsMarkovKernel κ] (t : ℕ) :
    IsMarkovKernel (κ ^ t) := by
  induction t with
  | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
  | succ t ih =>
      haveI := ih
      rw [pow_succ]
      exact inferInstanceAs (IsMarkovKernel ((κ ^ t) ∘ₖ κ))

/-! ## The Phase-1 stopped estimate from an arbitrary aggregate start mass -/

/-- First-exit clock tail from an arbitrary genuine start.  The old synchronized
reset hypothesis was used only to derive `counterDepthMass ≤ n`; the stopped
MGF argument itself needs exactly the aggregate bound stated here. -/
theorem stopped_good_exit_tail_of_mass_le
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c₀)
    (B : ℝ≥0∞)
    (hmass : ClockCounterDepthCover.counterDepthMass
        (L := L) (K := K) 1 R s c₀ ≤ B) :
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
        {c | ¬ Phase1ClockDepthStopped.Good
          (L := L) (K := K) n g mc c}
      ≤ ClockCounterDepthCover.counterDepthRate n s ^ H * B /
          ClockCounterDepthCover.counterDepthThreshold R s := by
  have htail := geometric_drift_tail
    (Phase1ClockDepthStopped.stopK (L := L) (K := K) n g mc)
    (Phase1ClockDepthStopped.stoppedDepthMass
      (L := L) (K := K) n g mc R s)
    (Phase1ClockDepthStopped.stoppedDepthMass_measurable n g mc R s)
    (ClockCounterDepthCover.counterDepthRate n s)
    (Phase1ClockDepthStopped.stoppedDepthMass_drift
      n g mc R hn s hs)
    H c₀ (ClockCounterDepthCover.counterDepthThreshold R s)
    (ClockCounterDepthCover.counterDepthThreshold_ne_zero R s)
    (ClockCounterDepthCover.counterDepthThreshold_ne_top R s)
  calc
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
        {c | ¬ Phase1ClockDepthStopped.Good
          (L := L) (K := K) n g mc c}
        ≤ (Phase1ClockDepthStopped.stopK
              (L := L) (K := K) n g mc ^ H) c₀
            {c | ClockCounterDepthCover.counterDepthThreshold R s ≤
              Phase1ClockDepthStopped.stoppedDepthMass
                (L := L) (K := K) n g mc R s c} := by
          apply measure_mono
          intro c hc
          simp only [Set.mem_setOf_eq] at hc ⊢
          simp [Phase1ClockDepthStopped.stoppedDepthMass, hc]
    _ ≤ ClockCounterDepthCover.counterDepthRate n s ^ H *
          Phase1ClockDepthStopped.stoppedDepthMass
            (L := L) (K := K) n g mc R s c₀ /
          ClockCounterDepthCover.counterDepthThreshold R s := htail
    _ ≤ ClockCounterDepthCover.counterDepthRate n s ^ H * B /
          ClockCounterDepthCover.counterDepthThreshold R s := by
        gcongr
        simpa [Phase1ClockDepthStopped.stoppedDepthMass, hgood₀] using hmass

/-- Joint stopped far/clock estimate with an arbitrary aggregate depth bound
at the genuine Phase-1 start. -/
theorem stopped_jointBad_tail_of_mass_le
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c₀)
    (B : ℝ≥0∞)
    (hmass : ClockCounterDepthCover.counterDepthMass
        (L := L) (K := K) 1 R s c₀ ≤ B) :
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
      {x | Phase1JointStopped.JointBad
        (L := L) (K := K) n g mc x}
      ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthRate n s ^ H * B /
          ClockCounterDepthCover.counterDepthThreshold R s := by
  let Bad : Set (Cfg L K) :=
    {x | ¬ Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc x}
  let Far : Set (Cfg L K) :=
    {x | 1 ≤ Phase1JointStopped.stoppedFarMass
      (L := L) (K := K) n g mc x}
  have hsubset :
      {x | Phase1JointStopped.JointBad
        (L := L) (K := K) n g mc x} ⊆ Bad ∪ Far := by
    intro x hx
    rcases hx with hbad | hfar
    · exact Or.inl hbad
    · by_cases hgood : Phase1ClockDepthStopped.Good
          (L := L) (K := K) n g mc x
      · right
        simp only [Far, Set.mem_setOf_eq,
          Phase1JointStopped.stoppedFarMass, hgood, if_true]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hfar
      · exact Or.inl hgood
  calc
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
      {x | Phase1JointStopped.JointBad
        (L := L) (K := K) n g mc x}
        ≤ (Phase1ClockDepthStopped.stopK
              (L := L) (K := K) n g mc ^ H) c₀ (Bad ∪ Far) :=
          measure_mono hsubset
    _ ≤ (Phase1ClockDepthStopped.stopK
            (L := L) (K := K) n g mc ^ H) c₀ Bad +
          (Phase1ClockDepthStopped.stopK
            (L := L) (K := K) n g mc ^ H) c₀ Far :=
        measure_union_le Bad Far
    _ ≤ (ClockCounterDepthCover.counterDepthRate n s ^ H * B /
            ClockCounterDepthCover.counterDepthThreshold R s) +
          ((1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
            Phase1JointStopped.stoppedFarMass
              (L := L) (K := K) n g mc c₀) :=
        add_le_add
          (stopped_good_exit_tail_of_mass_le
            n g mc H R hn s hs c₀ hgood₀ B hmass)
          (Phase1JointStopped.stopped_far_positive_tail
            n g mc H hn c₀)
    _ = (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthRate n s ^ H * B /
          ClockCounterDepthCover.counterDepthThreshold R s := by
      simp [Phase1JointStopped.stoppedFarMass, hgood₀, add_comm]

/-- Real-chain Phase-1 failure estimate from the actual aggregate depth mass
of a genuine start; no synchronized-reset premise occurs. -/
theorem real_phase1_failure_le_of_depthMass
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
      ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthRate n s ^ H *
            ClockCounterDepthCover.counterDepthMass
              (L := L) (K := K) 1 R s c₀ /
          ClockCounterDepthCover.counterDepthThreshold R s := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c | Phase1JointStopped.JointBad
            (L := L) (K := K) n g mc c} := by
            apply measure_mono
            intro c hpost
            by_cases hgood : Phase1ClockDepthStopped.Good
                (L := L) (K := K) n g mc c
            · exact Or.inr (fun hzero => hpost ⟨hgood.1, hzero⟩)
            · exact Or.inl hgood
    _ ≤ (Phase1ClockDepthStopped.stopK
          (L := L) (K := K) n g mc ^ H) c₀
        {c | Phase1JointStopped.JointBad
          (L := L) (K := K) n g mc c} :=
      Phase1JointStopped.real_jointBad_le_stopped n g mc H c₀
    _ ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthRate n s ^ H *
            ClockCounterDepthCover.counterDepthMass
              (L := L) (K := K) 1 R s c₀ /
          ClockCounterDepthCover.counterDepthThreshold R s :=
      stopped_jointBad_tail_of_mass_le n g mc H R hn s hs c₀ hgood₀
        _ le_rfl

/-! ## Distributional entry charge and Chapman--Kolmogorov bridge -/

/-- Genuine, exact-Phase-1, positive-clock entry set.  The asynchronous seam is
not asserted to land here pointwise; its complement is charged explicitly. -/
def entryGoodSet (n g mc : ℕ) : Set (Cfg L K) :=
  {c | Phase1ClockDepthStopped.Good (L := L) (K := K) n g mc c}

/-- Far-mass moment restricted to good asynchronous seam endpoints. -/
noncomputable def goodFarMass (n g mc : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  (entryGoodSet (L := L) (K := K) n g mc).indicator
    (fun x => (Phase1FarPhi.farPhiN x : ℝ≥0∞)) c

/-- Aggregate counter-depth moment restricted to good asynchronous endpoints. -/
noncomputable def goodDepthMass
    (n g mc R : ℕ) (s : ℝ) (c : Cfg L K) : ℝ≥0∞ :=
  (entryGoodSet (L := L) (K := K) n g mc).indicator
    (ClockCounterDepthCover.counterDepthMass
      (L := L) (K := K) 1 R s) c

/-- One unit of charge on an endpoint outside the genuine entry set. -/
noncomputable def badEntryBit (n g mc : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  (entryGoodSet (L := L) (K := K) n g mc)ᶜ.indicator
    (fun _ => (1 : ℝ≥0∞)) c

/-- Per-endpoint upper bound on Phase-1 failure after `H` further real
interactions.  This is the exact payload integrated at the asynchronous seam. -/
noncomputable def entryCharge
    (n g mc H R : ℕ) (s : ℝ) (c : Cfg L K) : ℝ≥0∞ :=
  badEntryBit (L := L) (K := K) n g mc c +
    (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
      goodFarMass (L := L) (K := K) n g mc c +
    (ClockCounterDepthCover.counterDepthRate n s ^ H /
        ClockCounterDepthCover.counterDepthThreshold R s) *
      goodDepthMass (L := L) (K := K) n g mc R s c

theorem goodFarMass_measurable (n g mc : ℕ) :
    Measurable (goodFarMass (L := L) (K := K) n g mc) :=
  Measurable.of_discrete

theorem goodDepthMass_measurable (n g mc R : ℕ) (s : ℝ) :
    Measurable (goodDepthMass (L := L) (K := K) n g mc R s) :=
  Measurable.of_discrete

theorem badEntryBit_measurable (n g mc : ℕ) :
    Measurable (badEntryBit (L := L) (K := K) n g mc) :=
  Measurable.of_discrete

theorem entryCharge_measurable (n g mc H R : ℕ) (s : ℝ) :
    Measurable (entryCharge (L := L) (K := K) n g mc H R s) :=
  Measurable.of_discrete

/-- The entry charge dominates the `H`-step work failure probability from
every endpoint, including endpoints where the genuine gate has already failed. -/
theorem phase1_failure_le_entryCharge
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c : Cfg L K) :
    ((NonuniformMajority L K).transitionKernel ^ H) c
        {x | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc x}
      ≤ entryCharge (L := L) (K := K) n g mc H R s c := by
  by_cases hgood : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c
  · have h := real_phase1_failure_le_of_depthMass
      n g mc H R hn s hs c hgood
    simpa [entryCharge, badEntryBit, goodFarMass, goodDepthMass,
      entryGoodSet, hgood, ENNReal.div_eq_inv_mul, mul_assoc, mul_comm,
      mul_left_comm] using h
  · letI := isMarkovKernel_pow
      (NonuniformMajority L K).transitionKernel H
    calc
      ((NonuniformMajority L K).transitionKernel ^ H) c
          {x | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc x}
          ≤ 1 := prob_le_one
      _ ≤ entryCharge (L := L) (K := K) n g mc H R s c := by
        simp [entryCharge, badEntryBit, goodFarMass, goodDepthMass,
          entryGoodSet, hgood]

/-- **Asynchronous joint bridge.**  Run `T` seam interactions and then `H`
Phase-1 interactions on the same real kernel.  The final failure probability
is bounded by the expected entry charge at time `T`; there is no pointwise
reset bridge and no synthetic restart. -/
theorem async_phase1_failure_le_entryCharge
    (n g mc T H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K) :
    ((NonuniformMajority L K).transitionKernel ^ (T + H)) c₀
        {x | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc x}
      ≤ ∫⁻ c, entryCharge (L := L) (K := K) n g mc H R s c
          ∂((NonuniformMajority L K).transitionKernel ^ T) c₀ := by
  rw [Kernel.pow_add_apply_eq_lintegral
    (NonuniformMajority L K).transitionKernel T H c₀
      (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact lintegral_mono
    (phase1_failure_le_entryCharge n g mc H R hn s hs)

/-! ## A decomposed aggregate-entry residual -/

/-- Minimal seam producer surface.  `badBudget` pays endpoints where phase
synchronization / structural faithfulness / positive counters failed.  The other two
fields are first moments on the good endpoint slice. -/
structure AggregateEntryPayload
    (n g mc T H R : ℕ) (s : ℝ) (c₀ : Cfg L K) where
  badBudget : ℝ≥0∞
  farMomentBudget : ℝ≥0∞
  depthMomentBudget : ℝ≥0∞
  bad_le :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        (entryGoodSet (L := L) (K := K) n g mc)ᶜ ≤ badBudget
  farMoment_le :
    (∫⁻ c, goodFarMass (L := L) (K := K) n g mc c
      ∂((NonuniformMajority L K).transitionKernel ^ T) c₀) ≤ farMomentBudget
  depthMoment_le :
    (∫⁻ c, goodDepthMass (L := L) (K := K) n g mc R s c
      ∂((NonuniformMajority L K).transitionKernel ^ T) c₀) ≤ depthMomentBudget

/-- The expected entry charge is exactly the sum of the three decomposed
payload terms. -/
theorem lintegral_entryCharge_eq
    (n g mc H R : ℕ) (s : ℝ) (μ : Measure (Cfg L K)) :
    (∫⁻ c, entryCharge (L := L) (K := K) n g mc H R s c ∂μ) =
      μ (entryGoodSet (L := L) (K := K) n g mc)ᶜ +
        (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (∫⁻ c, goodFarMass (L := L) (K := K) n g mc c ∂μ) +
        (ClockCounterDepthCover.counterDepthRate n s ^ H /
            ClockCounterDepthCover.counterDepthThreshold R s) *
          (∫⁻ c, goodDepthMass (L := L) (K := K) n g mc R s c ∂μ) := by
  unfold entryCharge
  rw [lintegral_add_left (by measurability),
    lintegral_add_left (badEntryBit_measurable n g mc),
    lintegral_const_mul _ (goodFarMass_measurable n g mc),
    lintegral_const_mul _ (goodDepthMass_measurable n g mc R s)]
  congr 2
  unfold badEntryBit
  rw [lintegral_indicator
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  simp

/-- The decomposed payload is sufficient for the full asynchronous joint
bound. -/
theorem async_phase1_failure_le_payload
    (n g mc T H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (payload : AggregateEntryPayload
      (L := L) (K := K) n g mc T H R s c₀) :
    ((NonuniformMajority L K).transitionKernel ^ (T + H)) c₀
        {x | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc x}
      ≤ payload.badBudget +
          (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
            payload.farMomentBudget +
          (ClockCounterDepthCover.counterDepthRate n s ^ H /
              ClockCounterDepthCover.counterDepthThreshold R s) *
            payload.depthMomentBudget := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ (T + H)) c₀
        {x | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc x}
        ≤ ∫⁻ c, entryCharge (L := L) (K := K) n g mc H R s c
            ∂((NonuniformMajority L K).transitionKernel ^ T) c₀ :=
          async_phase1_failure_le_entryCharge
            n g mc T H R hn s hs c₀
    _ = ((NonuniformMajority L K).transitionKernel ^ T) c₀
          (entryGoodSet (L := L) (K := K) n g mc)ᶜ +
        (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (∫⁻ c, goodFarMass (L := L) (K := K) n g mc c
            ∂((NonuniformMajority L K).transitionKernel ^ T) c₀) +
        (ClockCounterDepthCover.counterDepthRate n s ^ H /
            ClockCounterDepthCover.counterDepthThreshold R s) *
          (∫⁻ c, goodDepthMass (L := L) (K := K) n g mc R s c
            ∂((NonuniformMajority L K).transitionKernel ^ T) c₀) :=
      lintegral_entryCharge_eq n g mc H R s _
    _ ≤ payload.badBudget +
          (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
            payload.farMomentBudget +
          (ClockCounterDepthCover.counterDepthRate n s ^ H /
              ClockCounterDepthCover.counterDepthThreshold R s) *
            payload.depthMomentBudget := by
      gcongr
      · exact payload.bad_le
      · exact payload.farMoment_le
      · exact payload.depthMoment_le

/-- On every good entry endpoint the far observable is at most `2n`. -/
theorem goodFarMass_le_two_mul_n
    (n g mc : ℕ) (c : Cfg L K) :
    goodFarMass (L := L) (K := K) n g mc c ≤ ((2 * n : ℕ) : ℝ≥0∞) := by
  by_cases hgood : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c
  · have hc : c ∈ entryGoodSet (L := L) (K := K) n g mc := hgood
    rw [goodFarMass, Set.indicator_of_mem hc]
    exact_mod_cast Phase1FarPhiWork.farPhiN_le_two_mul_n c hgood.1
  · simp [goodFarMass, entryGoodSet, hgood]

/-- Consequently the good-entry far first moment is automatically at most
`2n` under every real-kernel prefix. -/
theorem goodFarMoment_le_two_mul_n
    (n g mc T : ℕ) (c₀ : Cfg L K) :
    (∫⁻ c, goodFarMass (L := L) (K := K) n g mc c
      ∂((NonuniformMajority L K).transitionKernel ^ T) c₀)
      ≤ ((2 * n : ℕ) : ℝ≥0∞) := by
  letI := isMarkovKernel_pow
    (NonuniformMajority L K).transitionKernel T
  haveI : IsProbabilityMeasure
      (((NonuniformMajority L K).transitionKernel ^ T) c₀) :=
    IsMarkovKernel.isProbabilityMeasure _
  calc
    (∫⁻ c, goodFarMass (L := L) (K := K) n g mc c
      ∂((NonuniformMajority L K).transitionKernel ^ T) c₀)
        ≤ ∫⁻ _c : Cfg L K, ((2 * n : ℕ) : ℝ≥0∞)
            ∂((NonuniformMajority L K).transitionKernel ^ T) c₀ :=
          lintegral_mono (goodFarMass_le_two_mul_n n g mc)
    _ = ((2 * n : ℕ) : ℝ≥0∞) := by simp

/-! ## Reset-50 calibration for an asynchronous aggregate entry moment -/

/-- The reset-50 clock calculation has exactly one `(L+1)`-block of aggregate
MGF slack beyond the old synchronized-start mass `n`.  The sharper rational
upper bound `exp 1 ≤ 68/25` is needed here; the coarser `11/4` bound only
certifies exponent 50 and hides this genuine seam allowance. -/
private theorem eight_mul_exp_twelve_le_four_thirds_pow_fortynine :
    (8 : ℝ) * Real.exp 12 ≤ (4 / 3 : ℝ) ^ 49 := by
  have he : Real.exp 1 ≤ (68 / 25 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hp : Real.exp 1 ^ 12 ≤ (68 / 25 : ℝ) ^ 12 :=
    pow_le_pow_left₀ (by positivity) he 12
  have hexp : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [show (12 : ℝ) = (12 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
  rw [hexp]
  calc
    (8 : ℝ) * Real.exp 1 ^ 12 ≤
        8 * (68 / 25 : ℝ) ^ 12 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (4 / 3 : ℝ) ^ 49 := by norm_num

/-- Real arithmetic core with effective reset `49(L+1)`.  Equivalently, this
is reset `50(L+1)` with an entry depth moment up to
`n·(4/3)^(L+1)`. -/
theorem phase1_clock_numerics_real_fortynine
    (n L H : ℕ) (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hH : H ≤ 18 * n * (L + 1)) :
    (1 + 2 / (3 * (n : ℝ))) ^ H * (n : ℝ) /
        (4 / 3 : ℝ) ^ (49 * (L + 1))
      ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set x : ℝ := 2 / (3 * (n : ℝ)) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hpowExp : (1 + x) ^ H ≤ Real.exp ((H : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by rw [add_comm]; exact Real.add_one_le_exp x) H
  have hHx : (H : ℝ) * x ≤ 12 * (L + 1 : ℕ) := by
    have hHR : (H : ℝ) ≤ 18 * (n : ℝ) * (L + 1 : ℕ) := by
      exact_mod_cast hH
    rw [hx]
    calc
      (H : ℝ) * (2 / (3 * (n : ℝ)))
          ≤ (18 * (n : ℝ) * (L + 1 : ℕ)) *
              (2 / (3 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hHR (by positivity)
      _ = 12 * (L + 1 : ℕ) := by field_simp; ring
  have hrate : (1 + x) ^ H ≤ Real.exp (12 * (L + 1 : ℕ)) :=
    hpowExp.trans (Real.exp_le_exp.mpr hHx)
  have hdenGrowth :
      Real.exp (12 * (L + 1 : ℕ)) * (8 : ℝ) ^ (L + 1) ≤
        (4 / 3 : ℝ) ^ (49 * (L + 1)) := by
    have hp := pow_le_pow_left₀ (by positivity)
      eight_mul_exp_twelve_le_four_thirds_pow_fortynine (L + 1)
    calc
      Real.exp (12 * (L + 1 : ℕ)) * (8 : ℝ) ^ (L + 1)
          = ((8 : ℝ) * Real.exp 12) ^ (L + 1) := by
            rw [mul_pow]
            rw [show (12 : ℝ) * (L + 1 : ℕ) =
                ((L + 1 : ℕ) : ℝ) * 12 by ring,
              Real.exp_nat_mul]
            ring
      _ ≤ ((4 / 3 : ℝ) ^ 49) ^ (L + 1) := hp
      _ = (4 / 3 : ℝ) ^ (49 * (L + 1)) := by rw [pow_mul]
  have hratio :
      (1 + x) ^ H * (n : ℝ) /
          (4 / 3 : ℝ) ^ (49 * (L + 1))
        ≤ (n : ℝ) / (8 : ℝ) ^ (L + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      (1 + x) ^ H * (n : ℝ) * (8 : ℝ) ^ (L + 1)
          ≤ Real.exp (12 * (L + 1 : ℕ)) * (n : ℝ) *
              (8 : ℝ) ^ (L + 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hrate (by positivity)) (by positivity)
      _ = (n : ℝ) *
            (Real.exp (12 * (L + 1 : ℕ)) * (8 : ℝ) ^ (L + 1)) := by
        ring
      _ ≤ (n : ℝ) * (4 / 3 : ℝ) ^ (49 * (L + 1)) :=
        mul_le_mul_of_nonneg_left hdenGrowth (by positivity)
  have hnLR : (n : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hnL
  have hnCube : (n : ℝ) ^ 3 ≤ ((2 : ℝ) ^ L) ^ 3 :=
    pow_le_pow_left₀ hnpos.le hnLR 3
  have hcubeBudget :
      2 * (n : ℝ) ^ 3 ≤ (8 : ℝ) ^ (L + 1) := by
    calc
      2 * (n : ℝ) ^ 3 ≤ 2 * ((2 : ℝ) ^ L) ^ 3 :=
        mul_le_mul_of_nonneg_left hnCube (by norm_num)
      _ = 2 * (2 : ℝ) ^ (3 * L) := by
        congr 1
        rw [← pow_mul]
        congr 1
        omega
      _ = 2 * (8 : ℝ) ^ L := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      _ ≤ 8 * (8 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (8 : ℝ) ^ (L + 1) := by rw [pow_succ']
  calc
    (1 + 2 / (3 * (n : ℝ))) ^ H * (n : ℝ) /
          (4 / 3 : ℝ) ^ (49 * (L + 1))
        = (1 + x) ^ H * (n : ℝ) /
            (4 / 3 : ℝ) ^ (49 * (L + 1)) := by rw [hx]
    _ ≤ (n : ℝ) / (8 : ℝ) ^ (L + 1) := hratio
    _ ≤ 1 / (2 * (n : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- The exact aggregate entry allowance left by reset 50 after an
`18n(L+1)` Phase-1 work horizon. -/
noncomputable def asyncDepthMomentCap (n L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n : ℝ) * (4 / 3 : ℝ) ^ (L + 1))

/-- Local copy of the rate normalization, kept in this file so the asynchronous
bridge does not depend on a synchronous-reset work theorem. -/
theorem counterDepthRate_log_four_thirds
    (n : ℕ) (hn : 1 ≤ n) :
    ClockCounterDepthCover.counterDepthRate n (Real.log (4 / 3 : ℝ)) =
      ENNReal.ofReal (1 + 2 / (3 * (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqpos : (0 : ℝ) < 4 / 3 := by norm_num
  have he0 : (0 : ℝ) ≤ Real.exp (Real.log (4 / 3 : ℝ)) - 1 := by
    rw [Real.exp_log hqpos]
    norm_num
  have hofac :
      ENNReal.ofReal
          (1 + 2 * (Real.exp (Real.log (4 / 3 : ℝ)) - 1) / (n : ℝ)) =
        1 + ENNReal.ofReal (Real.exp (Real.log (4 / 3 : ℝ)) - 1) *
          ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]
    congr 1
    rw [show 2 * (Real.exp (Real.log (4 / 3 : ℝ)) - 1) / (n : ℝ) =
        (Real.exp (Real.log (4 / 3 : ℝ)) - 1) * (2 / (n : ℝ)) by ring]
    rw [ENNReal.ofReal_mul he0]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
    norm_num
  unfold ClockCounterDepthCover.counterDepthRate
  rw [show (2 : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log (4 / 3 : ℝ)) - 1) /
          (n : ℝ≥0∞) =
        ENNReal.ofReal (Real.exp (Real.log (4 / 3 : ℝ)) - 1) *
          ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) by
        rw [mul_comm, mul_div_assoc]]
  rw [← hofac, Real.exp_log hqpos]
  congr 1
  field_simp
  ring

/-- The aggregate allowance really consumes at most the clock half-budget.
The seam horizon `T` is deliberately absent: its elapsed time is represented
by the actual entry moment, not added to the `18n(L+1)` work horizon. -/
theorem clockEntryCharge_le_half
    (n L H : ℕ) (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hH : H ≤ 18 * n * (L + 1))
    (B : ℝ≥0∞) (hB : B ≤ asyncDepthMomentCap n L) :
    (ClockCounterDepthCover.counterDepthRate n
          (Real.log (4 / 3 : ℝ)) ^ H /
        ClockCounterDepthCover.counterDepthThreshold
          (50 * (L + 1)) (Real.log (4 / 3 : ℝ))) * B
      ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
  have hqpos : (0 : ℝ) < 4 / 3 := by norm_num
  have hbase0 : (0 : ℝ) ≤ 1 + 2 / (3 * (n : ℝ)) := by positivity
  have hdenpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (50 * (L + 1)) := by
    positivity
  have hthreshold :
      ClockCounterDepthCover.counterDepthThreshold
          (50 * (L + 1)) (Real.log (4 / 3 : ℝ)) =
        ENNReal.ofReal ((4 / 3 : ℝ) ^ (50 * (L + 1))) := by
    unfold ClockCounterDepthCover.counterDepthThreshold
    rw [show Real.log (4 / 3 : ℝ) * ((50 * (L + 1) : ℕ) : ℝ) =
        ((50 * (L + 1) : ℕ) : ℝ) * Real.log (4 / 3 : ℝ) by ring,
      Real.exp_nat_mul, Real.exp_log hqpos]
  have hreal :
      ((1 + 2 / (3 * (n : ℝ))) ^ H /
          (4 / 3 : ℝ) ^ (50 * (L + 1))) *
          ((n : ℝ) * (4 / 3 : ℝ) ^ (L + 1))
        ≤ 1 / (2 * (n : ℝ) ^ 2) := by
    calc
      ((1 + 2 / (3 * (n : ℝ))) ^ H /
          (4 / 3 : ℝ) ^ (50 * (L + 1))) *
          ((n : ℝ) * (4 / 3 : ℝ) ^ (L + 1))
          = (1 + 2 / (3 * (n : ℝ))) ^ H * (n : ℝ) /
              (4 / 3 : ℝ) ^ (49 * (L + 1)) := by
            rw [show 50 * (L + 1) = 49 * (L + 1) + (L + 1) by omega,
              pow_add]
            field_simp
      _ ≤ 1 / (2 * (n : ℝ) ^ 2) :=
        phase1_clock_numerics_real_fortynine n L H hn hnL hH
  calc
    (ClockCounterDepthCover.counterDepthRate n
          (Real.log (4 / 3 : ℝ)) ^ H /
        ClockCounterDepthCover.counterDepthThreshold
          (50 * (L + 1)) (Real.log (4 / 3 : ℝ))) * B
        ≤ (ClockCounterDepthCover.counterDepthRate n
              (Real.log (4 / 3 : ℝ)) ^ H /
            ClockCounterDepthCover.counterDepthThreshold
              (50 * (L + 1)) (Real.log (4 / 3 : ℝ))) *
            asyncDepthMomentCap n L := by gcongr
    _ = ENNReal.ofReal
          (((1 + 2 / (3 * (n : ℝ))) ^ H /
              (4 / 3 : ℝ) ^ (50 * (L + 1))) *
            ((n : ℝ) * (4 / 3 : ℝ) ^ (L + 1))) := by
      rw [counterDepthRate_log_four_thirds n (by omega), hthreshold,
        asyncDepthMomentCap, ← ENNReal.ofReal_pow hbase0,
        ← ENNReal.ofReal_div_of_pos hdenpos,
        ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
      rw [DriftSurvival.coe_driftBudgetNN]
      exact ENNReal.ofReal_le_ofReal hreal

/-- The far-mass first moment `2n` consumes the other half-budget at the
canonical sharp-drift horizon. -/
theorem farEntryCharge_le_half
    (n g mc : ℕ) (hn : 2 ≤ n) (hmc : mc ≤ n)
    (hP : 0 < (mc - g + 3) / 4) :
    (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^
          Phase1FarPhiWork.horizon n g mc * ((2 * n : ℕ) : ℝ≥0∞)
      ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
  have hB0 : 0 < Phase1FarPhiWork.partnerB g mc :=
    Phase1FarPhiWork.partnerB_pos hP
  have hBle : Phase1FarPhiWork.partnerB g mc ≤
      (n : ℝ) * ((n : ℝ) - 1) :=
    Phase1FarPhiWork.partnerB_le_scheduler hn hmc
  rw [Phase1FarPhiWork.horizon,
    Phase1FarPhiWork.farBetaSharp_eq_ofReal_partnerB]
  exact DriftSurvival.drift_pow_le_budget_sub hn (by omega) (by omega)
    hB0 hBle

/-! ## Closed consumer and the one remaining seam producer -/

/-- The exact residual that the asynchronous Phase-0/1 seam must produce.
There is no pointwise counter reset:

* `bad_le` is the phase-epidemic / structural / premature-clock-exit mass;
* `depthMoment_le` is one aggregate MGF moment on the good endpoint slice.

The cap is calibrated above from reset 50 and is strictly larger than the
synchronous mass `n` by the factor `(4/3)^(L+1)`. -/
structure AsyncEntryHypotheses
    (n L g mc T : ℕ) (c₀ : Cfg L K) where
  badBudget : ℝ≥0∞
  bad_le :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        (entryGoodSet (L := L) (K := K) n g mc)ᶜ ≤ badBudget
  depthMoment_le :
    (∫⁻ c, goodDepthMass (L := L) (K := K) n g mc
        (50 * (L + 1)) (Real.log (4 / 3 : ℝ)) c
      ∂((NonuniformMajority L K).transitionKernel ^ T) c₀)
      ≤ asyncDepthMomentCap n L

/-- **Closed asynchronous Phase-1 consumer.**  Once the seam supplies the two
genuine residual fields above, the same real chain runs through the seam and
the sharp far drain.  The only additive seam cost is `badBudget`; far mass and
clock depth consume the two halves of `n⁻²`.

Crucially, `T` is not added to `18n(L+1)` in the clock calculation.  Its clock
exposure is already, and only, represented by `depthMoment_le`. -/
theorem phase1_async_joint_failure_le_bad_add_inv_sq
    (n L g mc T : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmc : mc ≤ n) (hP : 0 < (mc - g + 3) / 4)
    (hH : Phase1FarPhiWork.horizon n g mc ≤ 18 * n * (L + 1))
    (c₀ : Cfg L K)
    (residual : AsyncEntryHypotheses
      (K := K) n L g mc T c₀) :
    ((NonuniformMajority L K).transitionKernel ^
        (T + Phase1FarPhiWork.horizon n g mc)) c₀
      {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
      ≤ residual.badBudget + 1 / (n : ℝ≥0∞) ^ 2 := by
  let payload : AggregateEntryPayload
      (L := L) (K := K) n g mc T
        (Phase1FarPhiWork.horizon n g mc) (50 * (L + 1))
        (Real.log (4 / 3 : ℝ)) c₀ :=
    { badBudget := residual.badBudget
      farMomentBudget := ((2 * n : ℕ) : ℝ≥0∞)
      depthMomentBudget := asyncDepthMomentCap n L
      bad_le := residual.bad_le
      farMoment_le := goodFarMoment_le_two_mul_n n g mc T c₀
      depthMoment_le := residual.depthMoment_le }
  have hraw := async_phase1_failure_le_payload
    n g mc T (Phase1FarPhiWork.horizon n g mc) (50 * (L + 1))
    hn (Real.log (4 / 3 : ℝ))
    (Real.log_nonneg (by norm_num)) c₀ payload
  have hfar := farEntryCharge_le_half n g mc hn hmc hP
  have hclock := clockEntryCharge_le_half n L
    (Phase1FarPhiWork.horizon n g mc) hn hnL hH
    (asyncDepthMomentCap n L) le_rfl
  calc
    ((NonuniformMajority L K).transitionKernel ^
        (T + Phase1FarPhiWork.horizon n g mc)) c₀
      {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
        ≤ residual.badBudget +
          (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^
              Phase1FarPhiWork.horizon n g mc *
            ((2 * n : ℕ) : ℝ≥0∞) +
          (ClockCounterDepthCover.counterDepthRate n
                (Real.log (4 / 3 : ℝ)) ^
                Phase1FarPhiWork.horizon n g mc /
              ClockCounterDepthCover.counterDepthThreshold
                (50 * (L + 1)) (Real.log (4 / 3 : ℝ))) *
            asyncDepthMomentCap n L := hraw
    _ ≤ residual.badBudget +
          (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) +
          (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
      exact add_le_add (add_le_add le_rfl hfar) hclock
    _ = residual.badBudget + 1 / (n : ℝ≥0∞) ^ 2 := by
      rw [add_assoc, ← two_mul]
      exact congrArg (residual.badBudget + ·)
        (DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
          (D := 2) (n := n) (by omega) (by omega))

/-- Predicate form of the residual, convenient as a real work `Pre`. -/
def AsyncEntryPre
    (n L g mc T : ℕ) (εSeam : ℝ≥0) (c₀ : Cfg L K) : Prop :=
  ((NonuniformMajority L K).transitionKernel ^ T) c₀
      (entryGoodSet (L := L) (K := K) n g mc)ᶜ ≤ (εSeam : ℝ≥0∞) ∧
    (∫⁻ c, goodDepthMass (L := L) (K := K) n g mc
        (50 * (L + 1)) (Real.log (4 / 3 : ℝ)) c
      ∂((NonuniformMajority L K).transitionKernel ^ T) c₀)
      ≤ asyncDepthMomentCap n L

/-- Assembly-ready work object whose Pre is exactly the aggregate seam
producer obligation.  Its time is `T + horizon`; no claim identifies that sum
with `18n(L+1)`. -/
noncomputable def phase1AsyncJointWork
    (n L g mc T : ℕ) (εSeam : ℝ≥0)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmc : mc ≤ n) (hP : 0 < (mc - g + 3) / 4)
    (hH : Phase1FarPhiWork.horizon n g mc ≤ 18 * n * (L + 1)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := AsyncEntryPre (K := K) n L g mc T εSeam
  Post := Phase1FarPhiWork.Post (L := L) (K := K) n g mc
  t := T + Phase1FarPhiWork.horizon n g mc
  ε := εSeam + DriftSurvival.driftBudgetNN 2 n +
    DriftSurvival.driftBudgetNN 2 n
  convergence := by
    intro c₀ hpre
    let residual : AsyncEntryHypotheses
        (K := K) n L g mc T c₀ :=
      { badBudget := (εSeam : ℝ≥0∞)
        bad_le := hpre.1
        depthMoment_le := hpre.2 }
    have h := phase1_async_joint_failure_le_bad_add_inv_sq
      n L g mc T hn hnL hmc hP hH c₀ residual
    calc
      ((NonuniformMajority L K).transitionKernel ^
          (T + Phase1FarPhiWork.horizon n g mc)) c₀
        {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
          ≤ (εSeam : ℝ≥0∞) + 1 / (n : ℝ≥0∞) ^ 2 := h
      _ = ((εSeam + DriftSurvival.driftBudgetNN 2 n +
          DriftSurvival.driftBudgetNN 2 n : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_add, ENNReal.coe_add, add_assoc, ← two_mul]
        exact congrArg ((εSeam : ℝ≥0∞) + ·)
          (DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
            (D := 2) (n := n) (by omega) (by omega)).symm

theorem phase1AsyncJointWork_t_le
    (n L g mc T : ℕ) (εSeam : ℝ≥0)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmc : mc ≤ n) (hP : 0 < (mc - g + 3) / 4)
    (hH : Phase1FarPhiWork.horizon n g mc ≤ 18 * n * (L + 1)) :
    (phase1AsyncJointWork (K := K) n L g mc T εSeam
      hn hnL hmc hP hH).t ≤ T + 18 * n * (L + 1) := by
  exact Nat.add_le_add_left hH T

/-! Axiom audit for the kernel-level bridge. -/

#print axioms stopped_good_exit_tail_of_mass_le
#print axioms stopped_jointBad_tail_of_mass_le
#print axioms real_phase1_failure_le_of_depthMass
#print axioms phase1_failure_le_entryCharge
#print axioms async_phase1_failure_le_entryCharge
#print axioms AggregateEntryPayload
#print axioms lintegral_entryCharge_eq
#print axioms async_phase1_failure_le_payload
#print axioms goodFarMoment_le_two_mul_n
#print axioms phase1_clock_numerics_real_fortynine
#print axioms counterDepthRate_log_four_thirds
#print axioms clockEntryCharge_le_half
#print axioms farEntryCharge_le_half
#print axioms AsyncEntryHypotheses
#print axioms phase1_async_joint_failure_le_bad_add_inv_sq
#print axioms phase1AsyncJointWork
#print axioms phase1AsyncJointWork_t_le

end Phase1AsyncAggregateEntry
end Ripple.PopulationProtocol.ExactMajority

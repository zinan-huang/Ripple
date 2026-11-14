/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Joint stopped Phase-1 far-drain and clock-exit bound

The real Phase-1 failure event is transferred to the chain stopped on the
first failure of `Phase1GapFloorEntry ∧ ClockPos`.  On that one chain, the two bad
modes are split once at the final horizon:

* still-good positive far mass is paid by the sharp four-rectangle drift;
* first gate exit is paid by the aggregate counter-depth MGF.

Thus the clock term is a single hitting probability, not a sum over prefixes.
No global no-return property of `Goodᶜ` is assumed: the transfer is proved
directly for the final event, which contains every absorbed bad state.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1ClockDepthStopped
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiWork

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1JointStopped

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

/-- Far mass killed at the first failure of the genuine positive-clock gate. -/
noncomputable def stoppedFarMass
    (n g mc : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  if Phase1ClockDepthStopped.Good (L := L) (K := K) n g mc c then
    (Phase1FarPhi.farPhiN c : ℝ≥0∞)
  else 0

theorem stoppedFarMass_measurable (n g mc : ℕ) :
    Measurable (stoppedFarMass (L := L) (K := K) n g mc) :=
  Measurable.of_discrete

/-- The killed far observable is pointwise bounded by raw far mass. -/
theorem stoppedFarMass_le_raw (n g mc : ℕ) (c : Cfg L K) :
    stoppedFarMass (L := L) (K := K) n g mc c ≤
      (Phase1FarPhi.farPhiN c : ℝ≥0∞) := by
  unfold stoppedFarMass
  split <;> simp

/-- Sharp far-mass drift on the same first-bad stopped kernel used by the
clock MGF. -/
theorem stoppedFarMass_drift
    (n g mc : ℕ) (hn : 2 ≤ n) :
    ∀ c : Cfg L K,
      ∫⁻ c', stoppedFarMass (L := L) (K := K) n g mc c'
        ∂(Phase1ClockDepthStopped.stopK
          (L := L) (K := K) n g mc c)
      ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) *
          stoppedFarMass (L := L) (K := K) n g mc c := by
  intro c
  by_cases hgood : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c
  · rw [Phase1ClockDepthStopped.stopK_eq_real_of_good n g mc c hgood]
    calc
      (∫⁻ c', stoppedFarMass (L := L) (K := K) n g mc c'
          ∂((NonuniformMajority L K).transitionKernel c))
          ≤ ∫⁻ c', (Phase1FarPhi.farPhiN c' : ℝ≥0∞)
              ∂((NonuniformMajority L K).transitionKernel c) :=
            lintegral_mono (stoppedFarMass_le_raw n g mc)
      _ ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) *
            (Phase1FarPhi.farPhiN c : ℝ≥0∞) :=
          Phase1FarPhiSharp.farPhiN_multiplicative_drift_sharp
            hn c hgood.1
      _ = (1 - Phase1FarPhiSharp.farBetaSharp n g mc) *
            stoppedFarMass (L := L) (K := K) n g mc c := by
          simp [stoppedFarMass, hgood]
  · rw [Phase1ClockDepthStopped.stopK_eq_id_of_not_good n g mc c hgood,
      Kernel.id_apply,
      lintegral_dirac' c (stoppedFarMass_measurable n g mc)]
    simp [stoppedFarMass, hgood]

/-- Sharp far tail on the joint stopped chain. -/
theorem stopped_far_positive_tail
    (n g mc H : ℕ) (hn : 2 ≤ n) (c₀ : Cfg L K) :
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
      {c | 1 ≤ stoppedFarMass (L := L) (K := K) n g mc c}
      ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          stoppedFarMass (L := L) (K := K) n g mc c₀ := by
  simpa only [div_one] using
    geometric_drift_tail
      (Phase1ClockDepthStopped.stopK (L := L) (K := K) n g mc)
      (stoppedFarMass (L := L) (K := K) n g mc)
      (stoppedFarMass_measurable n g mc)
      (1 - Phase1FarPhiSharp.farBetaSharp n g mc)
      (stoppedFarMass_drift n g mc hn)
      H c₀ 1 one_ne_zero ENNReal.one_ne_top

/-- Final event containing both first gate exit and surviving positive far
mass. -/
def JointBad (n g mc : ℕ) (c : Cfg L K) : Prop :=
  ¬ Phase1ClockDepthStopped.Good (L := L) (K := K) n g mc c ∨
    Phase1FarPhi.farPhiN c ≠ 0

/-- A real endpoint in `JointBad` is dominated by the corresponding endpoint
of the first-bad stopped chain.  This remains true even if the real chain can
later return to `Good`: after the first exit the stopped endpoint is already in
the first disjunct. -/
theorem real_jointBad_le_stopped
    (n g mc H : ℕ) (c : Cfg L K) :
    ((NonuniformMajority L K).transitionKernel ^ H) c
        {x | JointBad (L := L) (K := K) n g mc x}
      ≤ (Phase1ClockDepthStopped.stopK
          (L := L) (K := K) n g mc ^ H) c
        {x | JointBad (L := L) (K := K) n g mc x} := by
  induction H generalizing c with
  | zero => rfl
  | succ H ih =>
      by_cases hgood : Phase1ClockDepthStopped.Good
          (L := L) (K := K) n g mc c
      · rw [show H + 1 = 1 + H by omega,
          Kernel.pow_add_apply_eq_lintegral
            (NonuniformMajority L K).transitionKernel 1 H c
              (DiscreteMeasurableSpace.forall_measurableSet _),
          Kernel.pow_add_apply_eq_lintegral
            (Phase1ClockDepthStopped.stopK
              (L := L) (K := K) n g mc) 1 H c
              (DiscreteMeasurableSpace.forall_measurableSet _),
          pow_one, pow_one,
          Phase1ClockDepthStopped.stopK_eq_real_of_good n g mc c hgood]
        exact lintegral_mono (fun y => ih y)
      · calc
          ((NonuniformMajority L K).transitionKernel ^ (H + 1)) c
              {x | JointBad (L := L) (K := K) n g mc x}
              ≤ 1 := by
                letI := isMarkovKernel_pow
                  (NonuniformMajority L K).transitionKernel (H + 1)
                exact prob_le_one
          _ = (Phase1ClockDepthStopped.stopK
                (L := L) (K := K) n g mc ^ (H + 1)) c
              {x | ¬ Phase1ClockDepthStopped.Good
                (L := L) (K := K) n g mc x} :=
            (Phase1ClockDepthStopped.stopK_pow_bad_eq_one
              n g mc (H + 1) c hgood).symm
          _ ≤ (Phase1ClockDepthStopped.stopK
                (L := L) (K := K) n g mc ^ (H + 1)) c
              {x | JointBad (L := L) (K := K) n g mc x} := by
            apply measure_mono
            intro x hx
            exact Or.inl hx

/-- The stopped joint event is paid once by the sharp far tail and once by the
first-exit clock tail. -/
theorem stopped_jointBad_tail
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
      {x | JointBad (L := L) (K := K) n g mc x}
      ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthTail n H R s := by
  let Bad : Set (Cfg L K) :=
    {x | ¬ Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc x}
  let Far : Set (Cfg L K) :=
    {x | 1 ≤ stoppedFarMass (L := L) (K := K) n g mc x}
  have hsubset :
      {x | JointBad (L := L) (K := K) n g mc x} ⊆ Bad ∪ Far := by
    intro x hx
    rcases hx with hbad | hfar
    · exact Or.inl hbad
    · by_cases hgood : Phase1ClockDepthStopped.Good
          (L := L) (K := K) n g mc x
      · right
        simp only [Far, Set.mem_setOf_eq, stoppedFarMass, hgood, if_true]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hfar
      · exact Or.inl hgood
  calc
    (Phase1ClockDepthStopped.stopK
        (L := L) (K := K) n g mc ^ H) c₀
      {x | JointBad (L := L) (K := K) n g mc x}
        ≤ (Phase1ClockDepthStopped.stopK
              (L := L) (K := K) n g mc ^ H) c₀ (Bad ∪ Far) :=
          measure_mono hsubset
    _ ≤ (Phase1ClockDepthStopped.stopK
            (L := L) (K := K) n g mc ^ H) c₀ Bad +
          (Phase1ClockDepthStopped.stopK
            (L := L) (K := K) n g mc ^ H) c₀ Far :=
        measure_union_le Bad Far
    _ ≤ ClockCounterDepthCover.counterDepthTail n H R s +
          ((1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
            stoppedFarMass (L := L) (K := K) n g mc c₀) :=
        add_le_add
          (Phase1ClockDepthStopped.stopped_good_exit_tail
            n g mc H R hn s hs c₀ hgood₀ hreset)
          (stopped_far_positive_tail n g mc H hn c₀)
    _ = (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthTail n H R s := by
      simp [stoppedFarMass, hgood₀, add_comm]

/-- Genuine real-chain Phase-1 failure bound with one sharp far term plus one
first-exit clock term. -/
theorem real_phase1_joint_failure_le
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
      ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthTail n H R s := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c | JointBad (L := L) (K := K) n g mc c} := by
            apply measure_mono
            intro c hpost
            by_cases hgood : Phase1ClockDepthStopped.Good
                (L := L) (K := K) n g mc c
            · exact Or.inr (fun hzero => hpost ⟨hgood.1, hzero⟩)
            · exact Or.inl hgood
    _ ≤ (Phase1ClockDepthStopped.stopK
          (L := L) (K := K) n g mc ^ H) c₀
        {c | JointBad (L := L) (K := K) n g mc c} :=
      real_jointBad_le_stopped n g mc H c₀
    _ ≤ (1 - Phase1FarPhiSharp.farBetaSharp n g mc) ^ H *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
        ClockCounterDepthCover.counterDepthTail n H R s :=
      stopped_jointBad_tail n g mc H R hn s hs c₀ hgood₀ hreset

#print axioms stoppedFarMass_measurable
#print axioms stoppedFarMass_le_raw
#print axioms stoppedFarMass_drift
#print axioms stopped_far_positive_tail
#print axioms real_jointBad_le_stopped
#print axioms stopped_jointBad_tail
#print axioms real_phase1_joint_failure_le

end Phase1JointStopped
end Ripple.PopulationProtocol.ExactMajority

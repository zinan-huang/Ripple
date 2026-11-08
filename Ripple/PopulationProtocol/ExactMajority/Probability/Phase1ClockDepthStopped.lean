/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 aggregate clock-depth drift on the honest stopped window

This file proves the identity-free counter-depth MGF drift needed by the
Phase-1 clock-prefix budget.  The drift is deliberately restricted to the
reachable honest gate `Phase1GapFloorEntry ∧ ClockPos`; it does not use the refuted
all-state drift interface, nor a species-count depletion cover.

The scheduler calculation is exact.  A selected Phase-1 clock with positive
counter decrements by one, so its truncated depth weight grows by at most
`exp s`.  Each ordered-pair marginal sees one `counterDepthMass / n`, giving
the aggregate rate `1 + 2 * (exp s - 1) / n`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ClockCounterDepthCover
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1ClockLeakZero
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.ExactMajority.Probability.CancelClockConcentration

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1ClockDepthStopped

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

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

abbrev State (L K : ℕ) := AgentState L K
abbrev Cfg (L K : ℕ) := Config (State L K)

/-- The exact Phase-1 gate on which the aggregate depth drift is valid. -/
def Good (n g mc : ℕ) (c : Cfg L K) : Prop :=
  Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c ∧
    Phase6LeakZero.ClockPos (L := L) (K := K) c

noncomputable instance (n g mc : ℕ) (c : Cfg L K) :
    Decidable (Good (L := L) (K := K) n g mc c) := by
  unfold Good
  infer_instance

/-! ## Count-sum / multiset-sum bridge -/

/-- The identity-free count presentation is exactly the corresponding
`Config.sumOf` observable. -/
theorem counterDepthMass_eq_sumOf (N R : ℕ) (s : ℝ)
    (c : Cfg L K) :
    ClockCounterDepthCover.counterDepthMass (L := L) (K := K) N R s c =
      Config.sumOf
        (ClockCounterDepthCover.counterDepthWeight
          (L := L) (K := K) N R s) c := by
  classical
  unfold ClockCounterDepthCover.counterDepthMass Config.sumOf
  rw [Finset.sum_multiset_map_count c
    (ClockCounterDepthCover.counterDepthWeight (L := L) (K := K) N R s)]
  rw [← Finset.sum_subset (Finset.subset_univ c.toFinset)
    (fun a _ ha => by
      rw [Multiset.mem_toFinset] at ha
      rw [Config.count, Multiset.count_eq_zero_of_notMem ha]
      simp)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Config.count, nsmul_eq_mul, mul_comm]

/-! ## Local counter and weight inequalities -/

/-- One unit of counter descent increases the truncated depth exponential by
at most `exp s`.  This includes the truncation boundary `counter = R + 1`. -/
theorem depthWeight_sub_one_le (R k : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hk : 0 < k) :
    ENNReal.ofReal
        (Real.exp (s * (((R - (k - 1)) : ℕ) : ℝ)))
      ≤ ENNReal.ofReal (Real.exp s) *
          ENNReal.ofReal
            (Real.exp (s * (((R - k) : ℕ) : ℝ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hnat : R - (k - 1) ≤ (R - k) + 1 := by omega
  have hcast :
      (((R - (k - 1)) : ℕ) : ℝ) ≤ (((R - k) : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat
  have hmul := mul_le_mul_of_nonneg_left hcast hs
  nlinarith

/-- A selected positive Phase-1 clock in the first coordinate has counter
exactly one smaller after the full dispatcher. -/
theorem transition_fst_clock_counter_eq_sub_one
    (r₁ r₂ : State L K)
    (h₁ : r₁.phase.val = 1) (h₂ : r₂.phase.val = 1)
    (hr₁ : r₁.role = Role.clock) (hc₁ : 0 < r₁.counter.val)
    (hc₂ : r₂.role = Role.clock → 0 < r₂.counter.val) :
    (Transition L K r₁ r₂).1.counter.val = r₁.counter.val - 1 := by
  have hp := Phase1ClockLeakZero.Phase1Transition_pair_phase_eq_of_counterPos
    (L := L) (K := K) r₁ r₂ h₁ h₂ (fun _ => hc₁) hc₂
  have ht := PhaseOnlyWindows.Transition_eq_Phase1Transition_of_phase1
    (L := L) (K := K) r₁ r₂ h₁ h₂ (by omega) (by omega)
  rw [ht, PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main]
  · simp [clockCounterStep, hr₁, stdCounterSubroutine,
      Nat.ne_of_gt hc₁]
  · intro hm
    rw [hr₁] at hm
    cases hm.1

/-- The symmetric counter identity for the second coordinate. -/
theorem transition_snd_clock_counter_eq_sub_one
    (r₁ r₂ : State L K)
    (h₁ : r₁.phase.val = 1) (h₂ : r₂.phase.val = 1)
    (hc₁ : r₁.role = Role.clock → 0 < r₁.counter.val)
    (hr₂ : r₂.role = Role.clock) (hc₂ : 0 < r₂.counter.val) :
    (Transition L K r₁ r₂).2.counter.val = r₂.counter.val - 1 := by
  have hp := Phase1ClockLeakZero.Phase1Transition_pair_phase_eq_of_counterPos
    (L := L) (K := K) r₁ r₂ h₁ h₂ hc₁ (fun _ => hc₂)
  have ht := PhaseOnlyWindows.Transition_eq_Phase1Transition_of_phase1
    (L := L) (K := K) r₁ r₂ h₁ h₂ (by omega) (by omega)
  rw [ht, PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main]
  · simp [clockCounterStep, hr₂, stdCounterSubroutine,
      Nat.ne_of_gt hc₂]
  · intro hm
    rw [hr₂] at hm
    cases hm.2

/-- First-coordinate depth weight grows by at most `exp s` on a positive
same-Phase-1 pair. -/
theorem transition_fst_depthWeight_le (R : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (r₁ r₂ : State L K)
    (h₁ : r₁.phase.val = 1) (h₂ : r₂.phase.val = 1)
    (hc₁ : r₁.role = Role.clock → 0 < r₁.counter.val)
    (hc₂ : r₂.role = Role.clock → 0 < r₂.counter.val) :
    ClockCounterDepthCover.counterDepthWeight (L := L) (K := K) 1 R s
        (Transition L K r₁ r₂).1
      ≤ ENNReal.ofReal (Real.exp s) *
          ClockCounterDepthCover.counterDepthWeight
            (L := L) (K := K) 1 R s r₁ := by
  have hp := Phase1ClockLeakZero.Transition_pair_phase1_eq_of_counterPos
    (L := L) (K := K) r₁ r₂ h₁ h₂ hc₁ hc₂
  have hr := PhaseOnlyWindows.Transition_role_phase1
    (L := L) (K := K) r₁ r₂ h₁ h₂
  by_cases hclock : r₁.role = Role.clock
  · have hpos := hc₁ hclock
    have hcounter := transition_fst_clock_counter_eq_sub_one
      (L := L) (K := K) r₁ r₂ h₁ h₂ hclock hpos hc₂
    simp only [ClockCounterDepthCover.counterDepthWeight, hp.1, h₁,
      hr.1, hclock, if_pos]
    rw [hcounter]
    exact depthWeight_sub_one_le R r₁.counter.val s hs hpos
  · simp [ClockCounterDepthCover.counterDepthWeight, hp.1, h₁,
      hr.1, hclock]

/-- Second-coordinate version of `transition_fst_depthWeight_le`. -/
theorem transition_snd_depthWeight_le (R : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (r₁ r₂ : State L K)
    (h₁ : r₁.phase.val = 1) (h₂ : r₂.phase.val = 1)
    (hc₁ : r₁.role = Role.clock → 0 < r₁.counter.val)
    (hc₂ : r₂.role = Role.clock → 0 < r₂.counter.val) :
    ClockCounterDepthCover.counterDepthWeight (L := L) (K := K) 1 R s
        (Transition L K r₁ r₂).2
      ≤ ENNReal.ofReal (Real.exp s) *
          ClockCounterDepthCover.counterDepthWeight
            (L := L) (K := K) 1 R s r₂ := by
  have hp := Phase1ClockLeakZero.Transition_pair_phase1_eq_of_counterPos
    (L := L) (K := K) r₁ r₂ h₁ h₂ hc₁ hc₂
  have hr := PhaseOnlyWindows.Transition_role_phase1
    (L := L) (K := K) r₁ r₂ h₁ h₂
  by_cases hclock : r₂.role = Role.clock
  · have hpos := hc₂ hclock
    have hcounter := transition_snd_clock_counter_eq_sub_one
      (L := L) (K := K) r₁ r₂ h₁ h₂ hc₁ hclock hpos
    simp only [ClockCounterDepthCover.counterDepthWeight, hp.2, h₂,
      hr.2, hclock, if_pos]
    rw [hcounter]
    exact depthWeight_sub_one_le R r₂.counter.val s hs hpos
  · simp [ClockCounterDepthCover.counterDepthWeight, hp.2, h₂,
      hr.2, hclock]

/-! ## Configuration localization and scheduler drift -/

private theorem sumOf_eq_base_add_pair (f : State L K → ℝ≥0∞)
    (c : Cfg L K) (r₁ r₂ : State L K)
    (hpair : ({r₁, r₂} : Config (State L K)) ≤ c) :
    Config.sumOf f c = Config.sumOf f (c - {r₁, r₂}) + (f r₁ + f r₂) := by
  unfold Config.sumOf
  rw [← Multiset.sub_add_cancel hpair, Multiset.map_add, Multiset.sum_add]
  simp

private theorem sumOf_stepOrSelf_eq_base_add_pair
    (f : State L K → ℝ≥0∞)
    (c : Cfg L K) (r₁ r₂ : State L K)
    (happ : Protocol.Applicable c r₁ r₂) :
    Config.sumOf f
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      = Config.sumOf f (c - {r₁, r₂}) +
          (f (Transition L K r₁ r₂).1 +
            f (Transition L K r₁ r₂).2) := by
  unfold Protocol.stepOrSelf
  rw [if_pos happ]
  unfold Config.sumOf
  rw [Multiset.map_add, Multiset.sum_add]
  have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
  rw [hδ]
  simp

private theorem mem_of_app_left {c : Cfg L K}
    {r₁ r₂ : State L K}
    (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le happ (by simp)

private theorem mem_of_app_right {c : Cfg L K}
    {r₁ r₂ : State L K}
    (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le happ (by simp)

/-- Localized pair inequality for the aggregate depth observable. -/
theorem counterDepthSum_stepOrSelf_le (n g mc R : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : Cfg L K)
    (hgood : Good (L := L) (K := K) n g mc c)
    (r₁ r₂ : State L K) :
    Config.sumOf
        (ClockCounterDepthCover.counterDepthWeight
          (L := L) (K := K) 1 R s)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ Config.sumOf
          (ClockCounterDepthCover.counterDepthWeight
            (L := L) (K := K) 1 R s) c
        + ENNReal.ofReal (Real.exp s - 1) *
            (ClockCounterDepthCover.counterDepthWeight
                (L := L) (K := K) 1 R s r₁ +
              ClockCounterDepthCover.counterDepthWeight
                (L := L) (K := K) 1 R s r₂) := by
  classical
  let w := ClockCounterDepthCover.counterDepthWeight
    (L := L) (K := K) 1 R s
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm₁ : r₁ ∈ c := mem_of_app_left happ
    have hm₂ : r₂ ∈ c := mem_of_app_right happ
    have hp₁ : r₁.phase.val = 1 := hgood.1.1.2 r₁ hm₁
    have hp₂ : r₂.phase.val = 1 := hgood.1.1.2 r₂ hm₂
    have hc₁ : r₁.role = Role.clock → 0 < r₁.counter.val := hgood.2 r₁ hm₁
    have hc₂ : r₂.role = Role.clock → 0 < r₂.counter.val := hgood.2 r₂ hm₂
    have hout :
        w (Transition L K r₁ r₂).1 + w (Transition L K r₁ r₂).2
          ≤ ENNReal.ofReal (Real.exp s) * (w r₁ + w r₂) := by
      rw [mul_add]
      exact add_le_add
        (transition_fst_depthWeight_le R s hs r₁ r₂ hp₁ hp₂ hc₁ hc₂)
        (transition_snd_depthWeight_le R s hs r₁ r₂ hp₁ hp₂ hc₁ hc₂)
    have hexp : ENNReal.ofReal (Real.exp s) =
        1 + ENNReal.ofReal (Real.exp s - 1) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by norm_num)
          (by linarith [Real.one_le_exp hs])]
      congr 1
      ring
    rw [sumOf_stepOrSelf_eq_base_add_pair w c r₁ r₂ happ,
      sumOf_eq_base_add_pair w c r₁ r₂ happ]
    calc
      Config.sumOf w (c - {r₁, r₂}) +
          (w (Transition L K r₁ r₂).1 + w (Transition L K r₁ r₂).2)
        ≤ Config.sumOf w (c - {r₁, r₂}) +
            ENNReal.ofReal (Real.exp s) * (w r₁ + w r₂) := by
          gcongr
      _ = Config.sumOf w (c - {r₁, r₂}) + (w r₁ + w r₂) +
            ENNReal.ofReal (Real.exp s - 1) * (w r₁ + w r₂) := by
          rw [hexp, add_mul, one_mul]
          ac_rfl
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable
      (P := NonuniformMajority L K) happ]
    exact le_add_right le_rfl

/-- Aggregate one-step MGF drift on the honest positive-clock gate.  This is
the local replacement for the refuted all-state drift hypothesis. -/
theorem counterDepthMass_drift_good
    (n g mc R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c : Cfg L K)
    (hgood : Good (L := L) (K := K) n g mc c) :
    ∫⁻ c', ClockCounterDepthCover.counterDepthMass
        (L := L) (K := K) 1 R s c'
      ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ClockCounterDepthCover.counterDepthRate n s *
          ClockCounterDepthCover.counterDepthMass
            (L := L) (K := K) 1 R s c := by
  classical
  let w := ClockCounterDepthCover.counterDepthWeight
    (L := L) (K := K) 1 R s
  let Φ := Config.sumOf w c
  have hcard : c.card = n := hgood.1.1.1
  have hc₂ : 2 ≤ c.card := by omega
  simp_rw [counterDepthMass_eq_sumOf]
  rw [Phase0Window.lintegral_transitionKernel_eq_sum
    (NonuniformMajority L K) c hc₂]
  have hpair : ∀ pair : State L K × State L K,
      Config.sumOf w
          (Protocol.stepOrSelf (NonuniformMajority L K) c pair.1 pair.2) *
          c.interactionProb pair.1 pair.2
        ≤ (Φ + ENNReal.ofReal (Real.exp s - 1) * (w pair.1 + w pair.2)) *
            c.interactionProb pair.1 pair.2 := by
    intro pair
    gcongr
    exact counterDepthSum_stepOrSelf_le n g mc R s hs c hgood pair.1 pair.2
  refine le_trans (Finset.sum_le_sum (fun pair _ => hpair pair)) ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hsumprob :
      (∑ pair : State L K × State L K,
        c.interactionProb pair.1 pair.2) = 1 := by
    have h := (c.interactionPMF hc₂).tsum_coe
    rw [tsum_eq_sum (s := Finset.univ)
      (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at h
    convert h using 1
  have hΦsum :
      (∑ pair : State L K × State L K,
        Φ * c.interactionProb pair.1 pair.2) = Φ := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  have hmid :
      (∑ pair : State L K × State L K,
        ENNReal.ofReal (Real.exp s - 1) * (w pair.1 + w pair.2) *
          c.interactionProb pair.1 pair.2)
        = ENNReal.ofReal (Real.exp s - 1) *
            (Φ / (n : ℝ≥0∞) + Φ / (n : ℝ≥0∞)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib,
      Phase0Window.sum_fst_interactionProb c hc₂ w,
      Phase0Window.sum_snd_interactionProb c hc₂ w,
      hcard]
  rw [hΦsum, hmid]
  change Φ + ENNReal.ofReal (Real.exp s - 1) *
      (Φ / (n : ℝ≥0∞) + Φ / (n : ℝ≥0∞)) ≤
    ClockCounterDepthCover.counterDepthRate n s * Φ
  unfold ClockCounterDepthCover.counterDepthRate
  rw [add_mul, one_mul]
  simp only [ENNReal.div_eq_inv_mul]
  ring_nf
  exact le_rfl

/-! ## First-bad stopped kernel -/

/-- Boolean-valued marker for first exit from `Good`. -/
noncomputable def goodBit (n g mc : ℕ) (c : Cfg L K) : ℕ :=
  if Good (L := L) (K := K) n g mc c then 0 else 1

/-- The real protocol kernel stopped on the first failure of
`Phase1GapFloorEntry ∧ ClockPos`. -/
noncomputable def stopK (n g mc : ℕ) : Kernel (Cfg L K) (Cfg L K) :=
  CancelClockConcentration.stoppedKernel
    (NonuniformMajority L K).transitionKernel
    (goodBit (L := L) (K := K) n g mc) 1

instance (n g mc : ℕ) : IsMarkovKernel (stopK (L := L) (K := K) n g mc) := by
  unfold stopK
  infer_instance

/-- On the gate, the stopped kernel is literally the real kernel. -/
theorem stopK_eq_real_of_good (n g mc : ℕ) (c : Cfg L K)
    (hgood : Good (L := L) (K := K) n g mc c) :
    stopK (L := L) (K := K) n g mc c =
      (NonuniformMajority L K).transitionKernel c := by
  unfold stopK CancelClockConcentration.stoppedKernel
  rw [Kernel.piecewise_apply]
  simp [CancelClockConcentration.activeSet, goodBit, hgood]

/-- After first gate failure, the stopped kernel self-loops. -/
theorem stopK_eq_id_of_not_good (n g mc : ℕ) (c : Cfg L K)
    (hgood : ¬ Good (L := L) (K := K) n g mc c) :
    stopK (L := L) (K := K) n g mc c = Kernel.id c := by
  unfold stopK CancelClockConcentration.stoppedKernel
  rw [Kernel.piecewise_apply]
  simp [CancelClockConcentration.activeSet, goodBit, hgood]

/-- At a structurally honest Phase-1 state, failure of `ClockPos` forces one
present clock to have counter zero, hence forces the aggregate threshold. -/
theorem threshold_le_mass_of_entry_not_clockPos
    (n g mc R : ℕ) (s : ℝ) (c : Cfg L K)
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c)
    (hpos : ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c) :
    ClockCounterDepthCover.counterDepthThreshold R s ≤
      ClockCounterDepthCover.counterDepthMass
        (L := L) (K := K) 1 R s c := by
  unfold Phase6LeakZero.ClockPos at hpos
  push Not at hpos
  obtain ⟨a, ha, hclock, hcounter⟩ := hpos
  have hzero : a.counter.val = 0 := by omega
  exact ClockCounterDepthCover.counterDepthMass_ge_of_mem_weight_ge_threshold
    (L := L) (K := K) 1 R s c a ha
    (by
      rw [ClockCounterDepthCover.counterDepthWeight_clock_zero
        (L := L) (K := K) 1 R s a (hentry.1.2 a ha) hclock hzero])

/-- Potential used by the first-bad stopped chain.  It is the genuine
identity-free mass while the gate is good and exactly the hitting threshold
after absorption. -/
noncomputable def stoppedDepthMass
    (n g mc R : ℕ) (s : ℝ) (c : Cfg L K) : ℝ≥0∞ :=
  if Good (L := L) (K := K) n g mc c then
    ClockCounterDepthCover.counterDepthMass (L := L) (K := K) 1 R s c
  else
    ClockCounterDepthCover.counterDepthThreshold R s

theorem stoppedDepthMass_measurable (n g mc R : ℕ) (s : ℝ) :
    Measurable (stoppedDepthMass (L := L) (K := K) n g mc R s) :=
  Measurable.of_discrete

/-- The MGF rate is at least one. -/
theorem one_le_counterDepthRate (n : ℕ) (s : ℝ) :
    (1 : ℝ≥0∞) ≤ ClockCounterDepthCover.counterDepthRate n s := by
  unfold ClockCounterDepthCover.counterDepthRate
  exact le_add_right le_rfl

/-- From a good state, the stopped potential is almost surely bounded by the
raw depth mass after one real step.  Structural `Phase1GapFloorEntry` failure has mass
zero; if only `ClockPos` fails, the raw mass already crosses the threshold. -/
theorem stoppedDepthMass_le_mass_ae
    (n g mc R : ℕ) (s : ℝ) (c : Cfg L K)
    (hgood : Good (L := L) (K := K) n g mc c) :
    (fun c' => stoppedDepthMass (L := L) (K := K) n g mc R s c')
      ≤ᵐ[(NonuniformMajority L K).transitionKernel c]
    (fun c' => ClockCounterDepthCover.counterDepthMass
      (L := L) (K := K) 1 R s c') := by
  have hzero :
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ Phase1PartnerFloor.Phase1GapFloorEntry
          (L := L) (K := K) n g mc c'} = 0 := by
    have h := Phase1ClockLeakZero.phase1GapFloorEntry_leak_zero_on_clockPos
      (L := L) (K := K) n g mc c hgood.1 hgood.2
    have heq :
        {c' | ¬ Phase1PartnerFloor.Phase1GapFloorEntry
          (L := L) (K := K) n g mc c'} =
          (Phase1FarPhiSurvival.phase1GapFloorEntryGate
            (L := L) (K := K) n g mc)ᶜ := by
      ext c'
      simp [Phase1FarPhiSurvival.phase1GapFloorEntryGate]
    rw [heq]
    exact h
  have haeEntry : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c' := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{c' | Phase1PartnerFloor.Phase1GapFloorEntry
      (L := L) (K := K) n g mc c'}, ?_, by simp⟩
    rw [mem_ae_iff]
    simpa only [Set.compl_setOf] using hzero
  filter_upwards [haeEntry] with c' hentry
  unfold stoppedDepthMass
  by_cases hgood' : Good (L := L) (K := K) n g mc c'
  · simp [hgood']
  · rw [if_neg hgood']
    exact threshold_le_mass_of_entry_not_clockPos n g mc R s c' hentry
      (fun hpos => hgood' ⟨hentry, hpos⟩)

/-- Global drift for the first-bad stopped chain.  The nontrivial branch uses
`counterDepthMass_drift_good`; absorbed states use `rate ≥ 1`. -/
theorem stoppedDepthMass_drift
    (n g mc R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) :
    ∀ c : Cfg L K,
      ∫⁻ c', stoppedDepthMass (L := L) (K := K) n g mc R s c'
        ∂(stopK (L := L) (K := K) n g mc c)
      ≤ ClockCounterDepthCover.counterDepthRate n s *
          stoppedDepthMass (L := L) (K := K) n g mc R s c := by
  intro c
  by_cases hgood : Good (L := L) (K := K) n g mc c
  · rw [stopK_eq_real_of_good n g mc c hgood]
    calc
      (∫⁻ c', stoppedDepthMass (L := L) (K := K) n g mc R s c'
          ∂((NonuniformMajority L K).transitionKernel c))
          ≤ ∫⁻ c', ClockCounterDepthCover.counterDepthMass
              (L := L) (K := K) 1 R s c'
              ∂((NonuniformMajority L K).transitionKernel c) :=
            lintegral_mono_ae
              (stoppedDepthMass_le_mass_ae n g mc R s c hgood)
      _ ≤ ClockCounterDepthCover.counterDepthRate n s *
            ClockCounterDepthCover.counterDepthMass
              (L := L) (K := K) 1 R s c :=
          counterDepthMass_drift_good n g mc R hn s hs c hgood
      _ = ClockCounterDepthCover.counterDepthRate n s *
            stoppedDepthMass (L := L) (K := K) n g mc R s c := by
          simp [stoppedDepthMass, hgood]
  · rw [stopK_eq_id_of_not_good n g mc c hgood, Kernel.id_apply,
      lintegral_dirac' c (stoppedDepthMass_measurable n g mc R s)]
    simp only [stoppedDepthMass, hgood, if_false]
    simpa only [one_mul] using
      (mul_le_mul_left (one_le_counterDepthRate n s)
        (ClockCounterDepthCover.counterDepthThreshold R s))

/-! ## Stopped hitting tail and real-prefix transfer -/

/-- A failed state remains in the bad set with probability one under every
power of the stopped kernel. -/
theorem stopK_pow_bad_eq_one
    (n g mc t : ℕ) (c : Cfg L K)
    (hbad : ¬ Good (L := L) (K := K) n g mc c) :
    (stopK (L := L) (K := K) n g mc ^ t) c
      {x | ¬ Good (L := L) (K := K) n g mc x} = 1 := by
  induction t with
  | zero =>
      rw [show stopK (L := L) (K := K) n g mc ^ 0 = Kernel.id from pow_zero _,
        Kernel.id_apply,
        Measure.dirac_apply' c (DiscreteMeasurableSpace.forall_measurableSet _)]
      simp [hbad]
  | succ t ih =>
      rw [show t + 1 = 1 + t by omega,
        Kernel.pow_add_apply_eq_lintegral
          (stopK (L := L) (K := K) n g mc) 1 t c
          (DiscreteMeasurableSpace.forall_measurableSet _),
        pow_one, stopK_eq_id_of_not_good n g mc c hbad,
        Kernel.id_apply,
        lintegral_dirac' c (Kernel.measurable_coe _
          (DiscreteMeasurableSpace.forall_measurableSet _))]
      exact ih

/-- At every fixed prefix, real-chain gate failure is dominated by first-exit
failure in the stopped chain.  The proof uses no no-return assumption. -/
theorem real_bad_le_stopped_bad
    (n g mc t : ℕ) (c : Cfg L K) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {x | ¬ Good (L := L) (K := K) n g mc x}
      ≤ (stopK (L := L) (K := K) n g mc ^ t) c
        {x | ¬ Good (L := L) (K := K) n g mc x} := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      by_cases hgood : Good (L := L) (K := K) n g mc c
      · rw [show t + 1 = 1 + t by omega,
          Kernel.pow_add_apply_eq_lintegral
            (NonuniformMajority L K).transitionKernel 1 t c
              (DiscreteMeasurableSpace.forall_measurableSet _),
          Kernel.pow_add_apply_eq_lintegral
            (stopK (L := L) (K := K) n g mc) 1 t c
              (DiscreteMeasurableSpace.forall_measurableSet _),
          pow_one, pow_one, stopK_eq_real_of_good n g mc c hgood]
        exact lintegral_mono (fun y => ih y)
      · calc
          ((NonuniformMajority L K).transitionKernel ^ (t + 1)) c
              {x | ¬ Good (L := L) (K := K) n g mc x}
              ≤ 1 := by
                letI := isMarkovKernel_pow
                  (NonuniformMajority L K).transitionKernel (t + 1)
                exact prob_le_one
          _ = (stopK (L := L) (K := K) n g mc ^ (t + 1)) c
              {x | ¬ Good (L := L) (K := K) n g mc x} :=
            (stopK_pow_bad_eq_one n g mc (t + 1) c hgood).symm

/-- First-exit tail from the honest positive-clock window, obtained from the
aggregate depth MGF on the stopped chain. -/
theorem stopped_good_exit_tail
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Good (L := L) (K := K) n g mc c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    (stopK (L := L) (K := K) n g mc ^ H) c₀
        {c | ¬ Good (L := L) (K := K) n g mc c}
      ≤ ClockCounterDepthCover.counterDepthTail n H R s := by
  have hwin : CounterSurvivalConc.WinN (L := L) (K := K) 1 n c₀ :=
    ⟨hgood₀.1.1.1, hgood₀.1.1.2, hgood₀.2⟩
  have hstart := ClockCounterDepthCover.counterDepthMass_start_le_n
    (L := L) (K := K) n 1 R s c₀ hwin hreset
  have htail := geometric_drift_tail
    (stopK (L := L) (K := K) n g mc)
    (stoppedDepthMass (L := L) (K := K) n g mc R s)
    (stoppedDepthMass_measurable n g mc R s)
    (ClockCounterDepthCover.counterDepthRate n s)
    (stoppedDepthMass_drift n g mc R hn s hs)
    H c₀ (ClockCounterDepthCover.counterDepthThreshold R s)
    (ClockCounterDepthCover.counterDepthThreshold_ne_zero R s)
    (ClockCounterDepthCover.counterDepthThreshold_ne_top R s)
  calc
    (stopK (L := L) (K := K) n g mc ^ H) c₀
        {c | ¬ Good (L := L) (K := K) n g mc c}
        ≤ (stopK (L := L) (K := K) n g mc ^ H) c₀
          {c | ClockCounterDepthCover.counterDepthThreshold R s ≤
            stoppedDepthMass (L := L) (K := K) n g mc R s c} := by
          apply measure_mono
          intro c hc
          simp only [Set.mem_setOf_eq] at hc
          simp [stoppedDepthMass, hc]
    _ ≤ ClockCounterDepthCover.counterDepthRate n s ^ H *
          stoppedDepthMass (L := L) (K := K) n g mc R s c₀ /
            ClockCounterDepthCover.counterDepthThreshold R s := htail
    _ ≤ ClockCounterDepthCover.counterDepthRate n s ^ H * (n : ℝ≥0∞) /
          ClockCounterDepthCover.counterDepthThreshold R s := by
          gcongr
          simpa [stoppedDepthMass, hgood₀] using hstart
    _ = ClockCounterDepthCover.counterDepthTail n H R s := rfl

/-- Every real prefix clock-failure mass is bounded by the corresponding
first-exit MGF tail. -/
theorem real_clockPos_bad_prefix_le
    (n g mc t R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Good (L := L) (K := K) n g mc c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ ClockCounterDepthCover.counterDepthTail n t R s := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬ Good (L := L) (K := K) n g mc c} := by
            apply measure_mono
            intro c hpos hgood
            exact hpos hgood.2
    _ ≤ (stopK (L := L) (K := K) n g mc ^ t) c₀
          {c | ¬ Good (L := L) (K := K) n g mc c} :=
        real_bad_le_stopped_bad n g mc t c₀
    _ ≤ ClockCounterDepthCover.counterDepthTail n t R s :=
        stopped_good_exit_tail n g mc t R hn s hs c₀ hgood₀ hreset

/-- The full real-prefix clock budget, with no species identities: sum the
aggregate first-exit MGF bound over the requested window. -/
theorem real_clockPos_bad_prefix_sum_le
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Good (L := L) (K := K) n g mc c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    ∑ t ∈ Finset.range H,
        ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ ∑ t ∈ Finset.range H,
          ClockCounterDepthCover.counterDepthTail n t R s := by
  exact Finset.sum_le_sum fun t _ =>
    real_clockPos_bad_prefix_le n g mc t R hn s hs c₀ hgood₀ hreset

/-- `counterDepthTail` is monotone in the time horizon because its MGF rate is
at least one. -/
theorem counterDepthTail_mono_time
    (n R : ℕ) (s : ℝ) {t H : ℕ} (ht : t ≤ H) :
    ClockCounterDepthCover.counterDepthTail n t R s ≤
      ClockCounterDepthCover.counterDepthTail n H R s := by
  unfold ClockCounterDepthCover.counterDepthTail
  gcongr
  exact one_le_counterDepthRate n s

/-- Uniform version of the prefix budget: every one of the `H` terms is
bounded by the horizon-`H` first-exit tail. -/
theorem real_clockPos_bad_prefix_sum_le_uniform
    (n g mc H R : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Cfg L K)
    (hgood₀ : Good (L := L) (K := K) n g mc c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    ∑ t ∈ Finset.range H,
        ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ (H : ℝ≥0∞) *
          ClockCounterDepthCover.counterDepthTail n H R s := by
  calc
    ∑ t ∈ Finset.range H,
        ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
        ≤ ∑ t ∈ Finset.range H,
            ClockCounterDepthCover.counterDepthTail n t R s :=
          real_clockPos_bad_prefix_sum_le
            n g mc H R hn s hs c₀ hgood₀ hreset
    _ ≤ ∑ _t ∈ Finset.range H,
          ClockCounterDepthCover.counterDepthTail n H R s := by
        exact Finset.sum_le_sum fun t ht =>
          counterDepthTail_mono_time n R s (Finset.mem_range.mp ht).le
    _ = (H : ℝ≥0∞) *
          ClockCounterDepthCover.counterDepthTail n H R s := by
        simp

#print axioms counterDepthMass_eq_sumOf
#print axioms depthWeight_sub_one_le
#print axioms transition_fst_clock_counter_eq_sub_one
#print axioms transition_snd_clock_counter_eq_sub_one
#print axioms transition_fst_depthWeight_le
#print axioms transition_snd_depthWeight_le
#print axioms counterDepthSum_stepOrSelf_le
#print axioms counterDepthMass_drift_good
#print axioms stopK_eq_real_of_good
#print axioms stopK_eq_id_of_not_good
#print axioms threshold_le_mass_of_entry_not_clockPos
#print axioms stoppedDepthMass_measurable
#print axioms one_le_counterDepthRate
#print axioms stoppedDepthMass_le_mass_ae
#print axioms stoppedDepthMass_drift
#print axioms stopK_pow_bad_eq_one
#print axioms real_bad_le_stopped_bad
#print axioms stopped_good_exit_tail
#print axioms real_clockPos_bad_prefix_le
#print axioms real_clockPos_bad_prefix_sum_le
#print axioms counterDepthTail_mono_time
#print axioms real_clockPos_bad_prefix_sum_le_uniform

end Phase1ClockDepthStopped
end Ripple.PopulationProtocol.ExactMajority

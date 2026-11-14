-- Ripple/PopulationProtocol/ExactMajority/Probability/LateFrozenPoolTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCounterTail
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingClassGates
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6RoleArrivals
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingFirstHit
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCalibration

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateFrozenPoolTail

open TimeTheorem PairLog LateF6Acceptance LateF6Hazards
open AveragingRecordedExpectation LateSamplingCounterTail LateSamplingClassGates

variable {L K : ℕ}

def FrozenCurrent (M A : ℕ) (C : Bias L → Prop)
    {m : ℕ} (f : Fin m → AgentState L K) : Prop :=
  (∀ i, Window (f i)) ∧ mainCount f = M ∧ A ≤ classCount C f

def frozenFirstFailure (init : Cfg L K) (s M A k : ℕ)
    (C : Bias L → Prop) (γ : ℝ) : Set (Ω L K) :=
  {ω | frozenCount (labelsAt init ω s) = 0 ∧
    frozenBadCount C (labelsAt init ω s) = 0 ∧
    ∃ T, s ≤ T ∧
      (∀ u, s ≤ u → u < T →
        FrozenCurrent M A C (labelsAt init ω u) ∧
          frozenCount (labelsAt init ω u) < k ∧
            frozenBadCount C (labelsAt init ω u) ≤ M - A) ∧
      frozenCount (labelsAt init ω T) = k ∧
      (((M - A : ℕ) : ℝ) / M + γ) * k ≤
        frozenBadCount C (labelsAt init ω T)}

theorem frozen_first_tail (init : Cfg L K) (hn : 2 ≤ init.card)
    (s M A k : ℕ) (hkM : k < M) (C : Bias L → Prop)
    (p : (i : Finset.Iic s) → Draw L K) (γ : ℝ) (hγ : 0 ≤ γ) :
    recordedFuture init s p (frozenFirstFailure init s M A k C γ) ≤
      ENNReal.ofReal (Real.exp (-2 * γ ^ 2 * k)) := by
  have hC : ∀ f : Fin init.card → AgentState L K, FrozenCurrent M A C f → ∀ d,
      frozenCount (stepLabels f d) = frozenCount f +
        bitNat (chosen (freezePair (fun _ => True)) f d) := by
    intro f hf d
    exact frozenCount_step f hf.1 d
  have hB : ∀ f : Fin init.card → AgentState L K, FrozenCurrent M A C f → ∀ d,
      frozenBadCount C (stepLabels f d) = frozenBadCount C f +
        bitNat (chosen (freezePair (fun b => ¬ C b)) f d) := by
    intro f hf d
    exact frozenBadCount_step C f hf.1 d
  have hkernel : ∀ f : Fin init.card → AgentState L K, FrozenCurrent M A C f → frozenCount f < k →
      frozenBadCount C f ≤ M - A →
      pairMass init (freezePair (fun b => ¬ C b)) f ≤
        ((((M - A : ℕ) : ℝ) - frozenBadCount C f) /
          ((M : ℝ) - frozenCount f)) *
            pairMass init (freezePair (fun _ => True)) f := by
    intro f hf _ _
    have h := freeze_bad_fraction C f hn hf.1 A hf.2.2
    rw [freeze_bad_ratio_eq C f hf.2.1 hf.2.2] at h
    exact h
  exact actual_urn_tail init hn s k (M - A) M hkM
    (FrozenCurrent M A C) frozenCount (frozenBadCount C)
    (freezePair (fun _ => True)) (freezePair (fun b => ¬ C b))
    (freezePair_class_implies (fun b => ¬ C b)) hC hB hkernel p γ hγ

theorem frozen_unit_steps (init : Cfg L K) (ω : Ω L K) (s T : ℕ)
    (C : Bias L → Prop)
    (hw : ∀ u, s ≤ u → u < T → ∀ i, Window (labelsAt init ω u i)) :
    LateSamplingFirstHit.UnitSteps
      (fun u => frozenCount (labelsAt init ω u))
      (fun u => frozenBadCount C (labelsAt init ω u)) s T := by
  intro u hsu huT
  let P := chosen (freezePair (fun _ => True))
    (labelsAt init ω u) (ω (u + 1))
  let Q := chosen (freezePair (fun b => ¬ C b))
    (labelsAt init ω u) (ω (u + 1))
  refine ⟨bitNat P, bitNat Q, ?_, ?_, ?_, ?_⟩
  · beta_reduce
    rw [labelsAt_succ]
    exact frozenCount_step _ (hw u hsu huT) _
  · beta_reduce
    rw [labelsAt_succ]
    exact frozenBadCount_step C _ (hw u hsu huT) _
  · rcases bitNat_zero_one P with h | h <;> omega
  · apply bitNat_mono
    rintro ⟨i, j, hsel, hclass⟩
    exact ⟨i, j, hsel, freezePair_class_implies _ _ _ _ hclass⟩

def frozenFailure (init : Cfg L K) (s M A k : ℕ)
    (C : Bias L → Prop) (γ : ℝ) : Set (Ω L K) :=
  {ω | frozenCount (labelsAt init ω s) = 0 ∧
    frozenBadCount C (labelsAt init ω s) = 0 ∧
    ∃ T, s ≤ T ∧
      (∀ u, s ≤ u → u ≤ T → FrozenCurrent M A C (labelsAt init ω u)) ∧
      frozenCount (labelsAt init ω T) = k ∧
      ¬ FrozenFloor C A M γ (labelsAt init ω T)}

theorem frozen_failure_subset_first (init : Cfg L K)
    (s M A k : ℕ) (hM : 0 < M) (hA : A ≤ M)
    (C : Bias L → Prop) (γ : ℝ) :
    frozenFailure init s M A k C γ ⊆ frozenFirstFailure init s M A k C γ := by
  rintro ω ⟨hzero, hbzero, T, hsT, hw, hK, hbad⟩
  have hu := frozen_unit_steps init ω s T C
    (fun u hsu huT => (hw u hsu huT.le).1)
  obtain ⟨t, hst, htT, hcount, hB, hbefore⟩ :=
    LateSamplingFirstHit.first_count_hit_with_bad hu hzero hsT hK
  have hbad' : (((M - A : ℕ) : ℝ) / M + γ) * k <
      frozenBadCount C (labelsAt init ω T) := by
    have hn := mt (frozen_floor_iff_bad C (labelsAt init ω T) hM hA γ).mpr hbad
    rw [hK] at hn
    exact lt_of_not_ge hn
  refine ⟨hzero, hbzero, t, hst, ?_, hcount, ?_⟩
  · intro u hsu hut
    have hcurrent := hw u hsu (hut.le.trans htT)
    refine ⟨hcurrent, hbefore u hsu hut, ?_⟩
    simpa only [hcurrent.2.1] using
      frozenBad_bound C (labelsAt init ω u) A hcurrent.2.2
  · rw [hB]
    exact hbad'.le

theorem frozen_tail (init : Cfg L K) (hn : 2 ≤ init.card)
    (s M A k : ℕ) (hkM : k < M) (hA : A ≤ M)
    (C : Bias L → Prop) (p : (i : Finset.Iic s) → Draw L K)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    recordedFuture init s p (frozenFailure init s M A k C γ) ≤
      ENNReal.ofReal (Real.exp (-2 * γ ^ 2 * k)) :=
  (measure_mono (frozen_failure_subset_first init s M A k (by omega) hA C γ)).trans
    (frozen_first_tail init hn s M A k hkM C p γ hγ)

theorem frozen_failure_at_all_empty (init : Cfg L K)
    (s M A : ℕ) (hM : 0 < M) (C : Bias L → Prop)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    frozenFailure init s M A M C γ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨_, _, T, hsT, hw, hK, hbad⟩
  have hcurrent := hw T hsT le_rfl
  exact hbad (frozen_floor_at_all C _ hM hcurrent.2.1 hK hcurrent.2.2 hγ)

theorem label_event_measurable (init : Cfg L K) (t : ℕ)
    (P : (Fin init.card → AgentState L K) → Prop) :
    MeasurableSet {ω | P (labelsAt init ω t)} :=
  (pairLogFiltration L K).le t _ (label_gate_measurable init t P)

theorem observed_window_measurable (init : Cfg L K) (s T : ℕ)
    (P : ℕ → (Fin init.card → AgentState L K) → Prop) :
    MeasurableSet {ω | ∀ u, s ≤ u → u ≤ T → P u (labelsAt init ω u)} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => label_event_measurable init u (P u)

theorem frozenFailure_measurable (init : Cfg L K) (s M A k : ℕ)
    (C : Bias L → Prop) (γ : ℝ) :
    MeasurableSet (frozenFailure init s M A k C γ) := by
  have hT (T : ℕ) : MeasurableSet {ω | s ≤ T ∧
      (∀ u, s ≤ u → u ≤ T → FrozenCurrent M A C (labelsAt init ω u)) ∧
      frozenCount (labelsAt init ω T) = k ∧
      ¬ FrozenFloor C A M γ (labelsAt init ω T)} := by
    have hst : MeasurableSet {ω : Ω L K | s ≤ T} := by
      by_cases h : s ≤ T <;> simp [h]
    exact hst.inter
      ((observed_window_measurable init s T (fun _ => FrozenCurrent M A C)).inter
        (label_event_measurable init T (fun f =>
          frozenCount f = k ∧ ¬ FrozenFloor C A M γ f)))
  have heq :
      frozenFailure init s M A k C γ =
        {ω | frozenCount (labelsAt init ω s) = 0} ∩
          ({ω | frozenBadCount C (labelsAt init ω s) = 0} ∩
            ⋃ T : ℕ, {ω | s ≤ T ∧
              (∀ u, s ≤ u → u ≤ T → FrozenCurrent M A C (labelsAt init ω u)) ∧
              frozenCount (labelsAt init ω T) = k ∧
              ¬ FrozenFloor C A M γ (labelsAt init ω T)}) := by
    ext ω
    simp only [frozenFailure, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
  rw [heq]
  exact (label_event_measurable init s (fun f => frozenCount f = 0)).inter
    ((label_event_measurable init s (fun f => frozenBadCount C f = 0)).inter
      (MeasurableSet.iUnion hT))

theorem frozen_test_tail (init : Cfg L K) (hn : 2 ≤ init.card)
    (n s M A k : ℕ) (hM : 0 < M) (hA : A ≤ M) (hkM : k ≤ M)
    (hk : Nat.ceil ((n : ℝ) / 1000000) ≤ k)
    (C : Bias L → Prop) (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
        (frozenFailure init s M A k C (1 / 40000)) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 800000000000000)) := by
  by_cases hkm : k = M
  · subst k
    rw [frozen_failure_at_all_empty init s M A hM C _ (by norm_num), measure_empty]
    exact zero_le
  · have hlt : k < M := by omega
    have ht := frozen_tail init hn s M A k hlt hA C p
      (1 / 40000) (by norm_num)
    have hcal := LateSamplingCalibration.frozen_hoeffding_exponent n
    have hk' : (Nat.ceil ((n : ℝ) / 1000000) : ℝ) ≤ k := by exact_mod_cast hk
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : -(2 : ℝ) * (1 / 40000) ^ 2 * k ≤
        -(n : ℝ) / 800000000000000 := by nlinarith
    exact ht.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))

end Ripple.PopulationProtocol.ExactMajority.LateFrozenPoolTail

end

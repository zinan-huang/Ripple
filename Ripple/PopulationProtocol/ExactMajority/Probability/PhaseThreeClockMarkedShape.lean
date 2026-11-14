-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMarkedShape.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalBarrierTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkSeedTail
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCoreCounts
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalRise

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedShape

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockSeedTails PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkEmbedding
  PhaseThreeClockNormalRise PhaseThreeClockNormalBarrierAlgebra
  PhaseThreeClockEarlyMarkSeedTail PhaseThreeClockSmallActivation
  PhaseThreeClockCore PhaseThreeClockCoreCounts

variable {L K m n : ℕ}

theorem normal_add_marked_eq_front (f : Fin m → AgentState L K)
    (A : Finset (Fin m)) (ell : ℕ) (hA : A ⊆ aboveSet f (ell + 1)) :
    normalCount f A ell + A.card = frontCount f (ell + 1) := by
  rw [normalCount_eq_sub f A ell hA]
  exact Nat.sub_add_cancel (Finset.card_le_card hA)

theorem marked_allowance_at_shape_cutoff (C X : ℕ)
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ))
    (hX : PhaseThreeModel.Numeric.shapeCutoff C ≤ X) :
    (C : ℝ) ^ (1 / 3 : ℝ) ≤
      (1 / 10 : ℝ) * (X : ℝ) ^ 2 / (C : ℝ) := by
  have hcal := (PhaseThreeModel.Numeric.cutoff_calibration hC hx (le_refl C)).2.2.2.2.2
  have hceil : (C : ℝ) ^ (17 / 25 : ℝ) ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX)
  have hsq := pow_le_pow_left₀
    (Real.rpow_nonneg hC.le (17 / 25 : ℝ)) hceil 2
  have hid :
      ((C : ℝ) ^ (17 / 25 : ℝ)) ^ 2 / C =
        (C : ℝ) ^ (9 / 25 : ℝ) := by
    calc
      ((C : ℝ) ^ (17 / 25 : ℝ)) ^ 2 / C =
          ((C : ℝ) ^ (17 / 25 : ℝ) * (C : ℝ) ^ (17 / 25 : ℝ)) / C := by ring
      _ = (C : ℝ) ^ ((9 / 25 : ℝ) + 1) / C := by
        rw [← Real.rpow_add hC]
        norm_num
      _ = ((C : ℝ) ^ (9 / 25 : ℝ) * C) / C := by
        rw [Real.rpow_add hC, Real.rpow_one]
      _ = _ := mul_div_cancel_right₀ _ hC.ne'
  have hquot := div_le_div_of_nonneg_right hsq hC.le
  rw [hid] at hquot
  calc
    (C : ℝ) ^ (1 / 3 : ℝ) ≤ (1 / 10 : ℝ) * (C : ℝ) ^ (9 / 25 : ℝ) := hcal
    _ ≤ (1 / 10 : ℝ) * ((X : ℝ) ^ 2 / C) :=
      mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = _ := by ring

theorem shape_of_normal_and_marks (C X Y A Z : ℕ)
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ))
    (hX : PhaseThreeModel.Numeric.shapeCutoff C ≤ X)
    (hsum : Y + A = Z)
    (hnormal : normalPotential C X Y ≤ 0)
    (hmarks : (A : ℝ) ≤ (C : ℝ) ^ (1 / 3 : ℝ)) :
    C * Z ≤ X ^ 2 := by
  have hsumR : (Y : ℝ) + A = Z := by exact_mod_cast hsum
  have hallow := hmarks.trans (marked_allowance_at_shape_cutoff C X hC hx hX)
  have hn : (Y : ℝ) ≤ (9 / 10 : ℝ) * (X : ℝ) ^ 2 / C := by
    dsimp only [normalPotential] at hnormal
    linarith
  have hZ : (Z : ℝ) ≤ (X : ℝ) ^ 2 / C := by
    simp only [mul_div_assoc] at hn hallow
    linarith
  have hmul := (le_div_iff₀ hC).mp hZ
  have hr : (C : ℝ) * Z ≤ (X : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hr

theorem normal_or_mark_failure_of_shape_failure (C X Y A Z : ℕ)
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ))
    (hX : PhaseThreeModel.Numeric.shapeCutoff C ≤ X)
    (hsum : Y + A = Z) (hbad : ¬ C * Z ≤ X ^ 2) :
    0 ≤ normalPotential C X Y ∨
      (C : ℝ) ^ (1 / 3 : ℝ) < A := by
  by_cases hnormal : 0 ≤ normalPotential C X Y
  · exact Or.inl hnormal
  · right
    by_contra hmarks
    exact hbad (shape_of_normal_and_marks C X Y A Z hC hx hX hsum
      (le_of_lt (lt_of_not_ge hnormal)) (le_of_not_gt hmarks))

theorem virtual_shape_of_normal_and_marks (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ell s v : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsv : s ≤ v) (hell : 1 ≤ ell)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω v i).phase.val ≤ 3)
    (hC : 0 < (C.card : ℝ)) (hx : 4194304 ≤ Real.log (C.card : ℝ))
    (hX : PhaseThreeModel.Numeric.shapeCutoff C.card ≤
      frontCount (virtualLabels init ω v) ell)
    (hnormal : normalPotential C.card
      (frontCount (virtualLabels init ω v) ell)
      (normalCount (virtualLabels init ω v)
        (markedAt init C ell (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v) ell) ≤ 0)
    (hmarks : ((markedAt init C ell
      (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v).card : ℝ) ≤
        (C.card : ℝ) ^ (1 / 3 : ℝ)) :
    C.card * frontCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) (ell + 1) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell ^ 2 := by
  rw [frontCountL_virtual_seed init ω s v (ell + 1) hseed hsv hcap,
    frontCountL_virtual_seed init ω s v ell hseed hsv hcap]
  exact shape_of_normal_and_marks C.card _ _ _ _ hC hx hX
    (normal_add_marked_eq_front _ _ ell
      (markedAt_subset_above_of_seedPrefix init ω C ell
        (PhaseThreeModel.Numeric.earlyCutoff C.card) s v hseed hsv hell hmask hcap))
    hnormal hmarks

theorem bulk_ratio_le_barrier (C X : ℕ) (hC : (1000 : ℝ) ≤ C)
    (hX : X ≤ StageEventSpec.bulkThreshold C) :
    (X : ℝ) / C ≤ 101 / 1000 := by
  have hpos : 0 < (C : ℝ) := by linarith
  have hceil : (StageEventSpec.bulkThreshold C : ℝ) <
      (C : ℝ) / 10 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hXR : (X : ℝ) ≤ StageEventSpec.bulkThreshold C := by exact_mod_cast hX
  apply (div_le_iff₀ hpos).mpr
  linarith

def markWindow (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s v : ℕ) (ω : InputLog n) : Prop :=
  (v : WithTop ℕ) ≤ smallActivationTime init s C.card ω ∨
    ∃ u : ℕ, smallActivationTime init s C.card ω = (u : WithTop ℕ) ∧ u ≤ v ∧
      PhaseThreeClockMarkedWindow.laterClockCount init C s ell u
        (PhaseThreeModel.Numeric.activationHalfHorizon init.card) (v - u) ω ≤
          (PhaseThreeModel.Numeric.fineTicks C.card : ℝ)

def normalShapeFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s : ℕ) : Set (InputLog n) :=
  {ω | ∃ v, s ≤ v ∧ (∀ i, (virtualLabels init ω v i).phase.val ≤ 3) ∧
    PhaseThreeModel.Numeric.earlyCutoff C.card ≤ frontCount (virtualLabels init ω v) ell ∧
    (frontCount (virtualLabels init ω v) ell : ℝ) / C.card ≤ 101 / 1000 ∧
    0 ≤ normalPotential C.card (frontCount (virtualLabels init ω v) ell)
      (normalCount (virtualLabels init ω v)
        (markedAt init C ell (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v) ell)}

def markedShapeFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s : ℕ) : Set (InputLog n) :=
  {ω | ∃ v, s ≤ v ∧ (∀ i, (virtualLabels init ω v i).phase.val ≤ 3) ∧
    PhaseThreeModel.Numeric.shapeCutoff C.card ≤ frontCount (virtualLabels init ω v) ell ∧
    frontCount (virtualLabels init ω v) ell ≤ StageEventSpec.bulkThreshold C.card ∧
    markWindow init C ell s v ω ∧
    ¬ C.card * frontCount (virtualLabels init ω v) (ell + 1) ≤
      frontCount (virtualLabels init ω v) ell ^ 2}

theorem markedShapeFailure_subset (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s : ℕ) (hell : 1 ≤ ell)
    (hC : 0 < (C.card : ℝ)) (hx : 4194304 ≤ Real.log (C.card : ℝ))
    (E : Set (InputLog n))
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    E ∩ markedShapeFailure init C ell s ⊆
      (E ∩ normalShapeFailure init C ell s) ∪
        (E ∩ fullMarkFailure init C ell s) := by
  have hlarge : (1000 : ℝ) ≤ C.card := by
    have he := Real.add_one_le_exp (Real.log (C.card : ℝ))
    rw [Real.exp_log hC] at he
    linarith
  have hcut := (PhaseThreeModel.Numeric.cutoff_calibration hC hx (le_refl C.card)).2.2.1
  rintro ω ⟨he, v, hsv, hcap, hshape, hbulk, hwindow, hbad⟩
  have hsum := normal_add_marked_eq_front (virtualLabels init ω v)
    (markedAt init C ell (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v) ell
    (markedAt_subset_above_of_seedPrefix init ω C ell
      (PhaseThreeModel.Numeric.earlyCutoff C.card) s v
      (hseed ω he).1 hsv hell (hseed ω he).2 hcap)
  rcases normal_or_mark_failure_of_shape_failure C.card _ _ _ _
    hC hx hshape hsum hbad with hn | hm
  · left
    exact ⟨he, v, hsv, hcap, hcut.trans hshape, bulk_ratio_le_barrier C.card _ hlarge hbulk, hn⟩
  · right
    exact ⟨he, v, hsv, hcap, hm, hwindow⟩

theorem marked_shape_prefix_tail_of_normal (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ell s : ℕ) (hell : 1 ≤ ell)
    (hC : 0 < (C.card : ℝ)) (hx : 4194304 ≤ Real.log (C.card : ℝ))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s))
    (hnormal : law init (E ∩ normalShapeFailure init C ell s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E) :
    law init (E ∩ markedShapeFailure init C ell s) ≤
      (2 * ENNReal.ofReal (1 / (C.card : ℝ) ^ 100)) * law init E := by
  calc
    _ ≤ law init ((E ∩ normalShapeFailure init C ell s) ∪
        (E ∩ fullMarkFailure init C ell s)) :=
      measure_mono (markedShapeFailure_subset init C ell s hell hC hx E hseed)
    _ ≤ law init (E ∩ normalShapeFailure init C ell s) +
        law init (E ∩ fullMarkFailure init C ell s) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E +
        ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E :=
      add_le_add hnormal (seed_full_mark_prefix_tail init hn C ell s hell E hE hseed)
    _ = _ := by ring

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedShape

end

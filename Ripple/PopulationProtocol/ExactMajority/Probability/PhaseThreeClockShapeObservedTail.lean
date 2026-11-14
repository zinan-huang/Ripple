-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockShapeObservedTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeBarrier
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalBarrierStarts
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedShape

/-!
# The actual normal barrier at its observed early cutoff

The cutoff is selected from the past.  Its disjoint fibres retain their original
probabilities.  The next unsafe update is skipped by ShapeFreeze; the later
normal-barrier stop includes its crossing endpoint.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeObservedTail

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockSeedTails PhaseThreeClockEarlyMarks
  PhaseThreeClockEarlyMarkInitialization PhaseThreeClockEarlyMarkSeedTail
  PhaseThreeClockEarlyMarkCalibration PhaseThreeClockSharpActivationSeed
  PhaseThreeClockNormalRise PhaseThreeClockPrefixTails PhaseThreeClockNormalBarrierAlgebra
  PhaseThreeClockNormalBarrierTails PhaseThreeClockNormalBarrierStarts
  PhaseThreeClockShapeFreeze PhaseThreeClockShapeBarrier PhaseThreeClockMarkedShape

variable {n : ℕ}

def normalShapeFailureAt (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s v : ℕ) : Set (InputLog n) :=
  {ω | s ≤ v ∧ (∀ i, (virtualLabels init ω v i).phase.val ≤ 3) ∧
    PhaseThreeModel.Numeric.earlyCutoff C.card ≤ frontCount (virtualLabels init ω v) ell ∧
    (frontCount (virtualLabels init ω v) ell : ℝ) / C.card ≤ 101 / 1000 ∧
    0 ≤ normalPotential C.card (frontCount (virtualLabels init ω v) ell)
      (normalCount (virtualLabels init ω v)
        (markedAt init C ell (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v) ell)}

theorem normalShapeFailureAt_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s v : ℕ) :
    MeasurableSet[pairLogFiltration _ _ v] (normalShapeFailureAt init C ell s v) := by
  have hr : MeasurableSet[pairLogFiltration _ _ v]
      {ω | PhaseThreeModel.Numeric.earlyCutoff C.card ≤
          frontCount (virtualLabels init ω v) ell ∧
        (frontCount (virtualLabels init ω v) ell : ℝ) / C.card ≤ 101 / 1000 ∧
        0 ≤ normalPotential C.card (frontCount (virtualLabels init ω v) ell)
          (normalCount (virtualLabels init ω v)
            (markedAt init C ell (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v) ell)} :=
    (show MeasurableSet {xy : ℕ × ℕ |
      PhaseThreeModel.Numeric.earlyCutoff C.card ≤ xy.1 ∧
        (xy.1 : ℝ) / C.card ≤ 101 / 1000 ∧
        0 ≤ normalPotential C.card xy.1 xy.2} from
      (Set.to_countable _).measurableSet).preimage
        (rawShapeCounts_measurable init C ell
          (PhaseThreeModel.Numeric.earlyCutoff C.card) s v)
  by_cases hsv : s ≤ v
  · convert (phaseCapAt_measurable init v).inter hr using 1
    ext ω
    simp only [normalShapeFailureAt, phaseCapAt, Set.mem_inter_iff,
      Set.mem_setOf_eq, hsv, true_and]
  · simp only [normalShapeFailureAt, hsv, false_and, Set.setOf_false, MeasurableSet.empty]

theorem normalShapeFailure_eq_iUnion (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s : ℕ) :
    normalShapeFailure init C ell s = ⋃ v, normalShapeFailureAt init C ell s v := by
  ext ω
  simp only [normalShapeFailure, normalShapeFailureAt, Set.mem_setOf_eq, Set.mem_iUnion]

theorem normalShapeFailure_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s : ℕ) :
    MeasurableSet (normalShapeFailure init C ell s) := by
  rw [normalShapeFailure_eq_iUnion]
  exact MeasurableSet.iUnion fun v =>
    ((pairLogFiltration _ _).le v) _ (normalShapeFailureAt_measurable init C ell s v)

theorem observedCutoff_shapeSafe (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell cutoff u : ℕ)
    (E : Set (InputLog n))
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s))
    (ω : InputLog n) (hω : ω ∈ observedCutoffPrefix init s ell cutoff E u) :
    shapeSafeAt init C s u ω :=
  ⟨⟨(hseed ω hω.1.1).1, (hseed ω hω.1.1).2.symm⟩, hω.2⟩

theorem observed_normal_shape_exponential_tail
    (init : InputCfg n) (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (hC : 0 < C.card) (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (observedCutoffPrefix init s ell
        (PhaseThreeModel.Numeric.earlyCutoff C.card) E u ∩ normalShapeFailure init C ell s) ≤
      ENNReal.ofReal (Real.exp (-(9 / 100 : ℝ) * (C.card : ℝ) ^ (1 / 50 : ℝ))) *
        law init (observedCutoffPrefix init s ell
          (PhaseThreeModel.Numeric.earlyCutoff C.card) E u) := by
  let cutoff := PhaseThreeModel.Numeric.earlyCutoff C.card
  let A := observedCutoffPrefix init s ell cutoff E u
  let d := actualNormalBarrierData init hc C hC ell cutoff s u hsu hell hlevel
  have hA : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u 0] A := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using
      observedCutoffPrefix_measurable init s ell cutoff u E hE
  have hfront : ∀ ω ∈ A, (C.card : ℝ) ^ (51 / 100 : ℝ) ≤ d.X 0 ω := by
    intro ω hω
    change (C.card : ℝ) ^ (51 / 100 : ℝ) ≤ frozenFront init C ell cutoff s u 0 ω
    rw [(frozen_initial_eq init C ell cutoff s u ω
      (observedCutoff_shapeSafe init C s ell cutoff u E hseed ω hω)).1]
    exact observedCutoffPrefix_front_lower init C s ell u E ω hω
  have hnormal : ∀ ω ∈ A, d.Y 0 ω ≤ 0 := by
    intro ω hω
    change frozenNormal init C ell cutoff s u 0 ω ≤ 0
    rw [(frozen_initial_eq init C ell cutoff s u ω
      (observedCutoff_shapeSafe init C s ell cutoff u E hseed ω hω)).2,
      observedCutoffPrefix_normal_zero init C s ell cutoff u hell hlevel E hseed ω hω]
    norm_num
  have hsub : A ∩ normalShapeFailure init C ell s ⊆ A ∩ normalBarrierCrossing d := by
    rintro ω ⟨ha, v, hsv, hcap, hcut, hratio, hF⟩
    have huv : u ≤ v := by
      by_contra hnot
      have hsmall := ha.1.2.2.2 v hsv (lt_of_not_ge hnot)
      exact not_lt_of_ge hcut hsmall
    have huvEq : u + (v - u) = v := Nat.add_sub_of_le huv
    have hsafe : shapeSafeAt init C s v ω :=
      ⟨⟨(hseed ω ha.1.1).1, (hseed ω ha.1.1).2.symm⟩, hcap⟩
    refine ⟨ha, raw_crossing_mem_normalBarrierCrossing
      init hc C hC ell cutoff s u hsu hell hlevel (v - u) ω ?_ ?_ ?_⟩
    · simpa only [huvEq] using hsafe
    · simpa only [huvEq] using hratio
    · simpa only [huvEq] using hF
  exact (measure_mono hsub).trans (normal_barrier_cutoff_prefix_tail d A hA hfront hnormal)

theorem normal_error_calibration (C : ℕ)
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ)) :
    Real.exp (-(9 / 100 : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ)) ≤
      1 / (C : ℝ) ^ 100 :=
  ((PhaseThreeModel.Numeric.exponential_error_calibration hC hx).2.1).trans_eq
    (negative_hundred_rpow_eq C)

theorem observed_normal_shape_prefix_tail
    (init : InputCfg n) (hc : 2 ≤ init.card) (C : Finset (Fin init.card))
    (hC : 0 < C.card) (hx : 536870912 ≤ Real.log (C.card : ℝ))
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (observedCutoffPrefix init s ell
        (PhaseThreeModel.Numeric.earlyCutoff C.card) E u ∩ normalShapeFailure init C ell s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) *
        law init (observedCutoffPrefix init s ell
          (PhaseThreeModel.Numeric.earlyCutoff C.card) E u) := by
  apply (observed_normal_shape_exponential_tail
    init hc C hC ell s u hsu hell hlevel E hE hseed).trans
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal
    (normal_error_calibration C.card (by exact_mod_cast hC) hx)) _

theorem seed_normal_shape_prefix_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ normalShapeFailure init C ell s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  classical
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr he
  have hsη := hseed η hη
  have hcount : clockCount (labelsAt init η s) = C.card := by
    change (clockSet (labelsAt init η s)).card = C.card
    rw [← hsη.2]
  obtain ⟨hm, hlo, hCn⟩ :=
    seed_clock_calibration_inputs init hn η s C.card hsη.1 hcount
  obtain ⟨hC, hx, -⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hm hlo hCn
  have hlarge : (2 : ℝ) ≤ C.card := by
    have hexp := Real.add_one_le_exp (Real.log (C.card : ℝ))
    rw [Real.exp_log hC] at hexp
    linarith
  have hc : 2 ≤ init.card := (by exact_mod_cast hlarge : 2 ≤ C.card).trans hCn
  have hCnat : 0 < C.card := by exact_mod_cast hC
  let cutoff := PhaseThreeModel.Numeric.earlyCutoff C.card
  let A : ℕ → Set (InputLog n) := fun u => observedCutoffPrefix init s ell cutoff E u
  have hlocal (u : ℕ) :
      law init (A u ∩ normalShapeFailure init C ell s) ≤
        ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) := by
    by_cases hsu : s ≤ u
    · exact observed_normal_shape_prefix_tail
        init hc C hCnat hx ell s u hsu hell hlevel E hE hseed
    · have hempty : A u = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        exact hsu hω.1.2.1
      simp only [hempty, Set.empty_inter, measure_empty, mul_zero, le_refl]
  have hcover : E ∩ normalShapeFailure init C ell s ⊆
      ⋃ u, A u ∩ normalShapeFailure init C ell s := by
    rintro ω ⟨heω, hb⟩
    rcases hb with ⟨v, hsv, hcap, hcut, hratio, hF⟩
    obtain ⟨u, huv, hu⟩ := exists_earlyCutoffFibre init s ell cutoff v ω hsv hcut
    have hcapu : ω ∈ phaseCapAt init u := fun i =>
      (PhaseThreeClockActivationLaw.virtualLabels_phase_mono init ω i huv).trans (hcap i)
    exact Set.mem_iUnion.mpr
      ⟨u, ⟨⟨heω, hu⟩, hcapu⟩, v, hsv, hcap, hcut, hratio, hF⟩
  calc
    law init (E ∩ normalShapeFailure init C ell s) ≤
        law init (⋃ u, A u ∩ normalShapeFailure init C ell s) := measure_mono hcover
    _ ≤ ∑' u, law init (A u ∩ normalShapeFailure init C ell s) := measure_iUnion_le _
    _ ≤ ∑' u, ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init (A u) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * ∑' u, law init (A u) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left'
      (observedCutoffPrefix_tsum_le init s ell cutoff E hE) _

theorem seed_marked_shape_prefix_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ markedShapeFailure init C ell s) ≤
      (2 * ENNReal.ofReal (1 / (C.card : ℝ) ^ 100)) * law init E := by
  classical
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr he
  have hsη := hseed η hη
  have hcount : clockCount (labelsAt init η s) = C.card := by
    change (clockSet (labelsAt init η s)).card = C.card
    rw [← hsη.2]
  obtain ⟨hm, hlo, hCn⟩ :=
    seed_clock_calibration_inputs init hn η s C.card hsη.1 hcount
  obtain ⟨hC, hx, -⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hm hlo hCn
  exact marked_shape_prefix_tail_of_normal init hn C ell s hell hC hx E hE hseed
    (seed_normal_shape_prefix_tail init hn C ell s hell hlevel E hE hseed)

theorem seed_normal_shape_entry_fibre_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      StageEventSpec.SeedProfile n init (trace init ω s) ∧
      C = clockSet (labelsAt init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
      ω ∈ normalShapeFailure init C ell s} ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  let E := seedClockMaskPrefix init s C
  have hE : MeasurableSet[pairLogFiltration _ _ s] E :=
    (seedPrefix_measurable init s).inter (seed_clockMask_measurable init s C)
  have hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s) :=
    fun _ h => h
  have hsub :
      {ω : InputLog n | seedTime init 3 ω = (s : WithTop ℕ) ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        C = clockSet (labelsAt init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
        ω ∈ normalShapeFailure init C ell s} ⊆ E ∩ normalShapeFailure init C ell s := by
    rintro ω ⟨hs, hp, hm, -, hb⟩
    exact ⟨⟨⟨hs, hp⟩, hm⟩, hb⟩
  exact (measure_mono hsub).trans
    ((seed_normal_shape_prefix_tail init hn C ell s hell hlevel E hE hseed).trans
      (mul_le_mul_left' (measure_mono (fun _ h => h.1.1 :
        E ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)})) _))

theorem seed_marked_shape_entry_fibre_tail
    (init : InputCfg n) (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (ell s : ℕ) (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      StageEventSpec.SeedProfile n init (trace init ω s) ∧
      C = clockSet (labelsAt init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
      ω ∈ markedShapeFailure init C ell s} ≤
      (2 * ENNReal.ofReal (1 / (C.card : ℝ) ^ 100)) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  let E := seedClockMaskPrefix init s C
  have hE : MeasurableSet[pairLogFiltration _ _ s] E :=
    (seedPrefix_measurable init s).inter (seed_clockMask_measurable init s C)
  have hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s) :=
    fun _ h => h
  have hsub :
      {ω : InputLog n | seedTime init 3 ω = (s : WithTop ℕ) ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        C = clockSet (labelsAt init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ StageEventSpec.AsyncEntry init ω s T) ∧
        ω ∈ markedShapeFailure init C ell s} ⊆ E ∩ markedShapeFailure init C ell s := by
    rintro ω ⟨hs, hp, hm, -, hb⟩
    exact ⟨⟨⟨hs, hp⟩, hm⟩, hb⟩
  exact (measure_mono hsub).trans
    ((seed_marked_shape_prefix_tail init hn C ell s hell hlevel E hE hseed).trans
      (mul_le_mul_left' (measure_mono (fun _ h => h.1.1 :
        E ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)})) _))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeObservedTail

end

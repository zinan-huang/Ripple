-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHalfChain.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHalfPassage

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHalfChain

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
open PhaseThreeClockProbabilityFloors PhaseThreeClockFirstPositive
open PhaseThreeClockNextFrontBirth PhaseThreeClockHalfPassage

variable {L : ℕ}

theorem half_chain_prefix_tail (init : Cfg L 256) (hm : 2 ≤ init.card)
    (C s Q : ℕ) (hC : 10 ≤ C) (hCm : C ≤ init.card)
    (hdensity : 6 * init.card ≤ 25 * C) (hQ : Q ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω s ∧
      clockCount (virtualLabels init ω s) = C) :
    law init (E ∩ {ω | frontCount
      (virtualLabels init ω (s + 25 * init.card * Q)) Q < halfCount C}) ≤
      (Q : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) * law init E := by
  revert hQ
  induction Q with
  | zero =>
      intro hQ
      have hempty : E ∩ {ω | frontCount
          (virtualLabels init ω (s + 25 * init.card * 0)) 0 < halfCount C} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨he, hb⟩
        simp only [Set.mem_setOf_eq, Nat.mul_zero, Nat.add_zero, frontCount_zero,
          (hstart ω he).2] at hb
        exact (not_lt_of_ge (halfCount_bounds C).2.2) hb
      rw [hempty, measure_empty]
      simp
  | succ Q ih =>
      intro hQ
      let t := s + 25 * init.card * Q
      let A : Set (Ω L 256) :=
        E ∩ {ω | halfCount C ≤ frontCount (virtualLabels init ω t) Q}
      have hst : s ≤ t := by dsimp only [t]; omega
      have htime : t + 25 * init.card = s + 25 * init.card * (Q + 1) := by
        dsimp only [t]
        rw [Nat.mul_succ]
        omega
      have hA : MeasurableSet[pairLogFiltration L 256 t] A := by
        refine (((pairLogFiltration L 256).mono hst) E hE).inter ?_
        exact (measurable_virtualLabels init t)
          (Set.to_countable {f : Fin init.card → AgentState L 256 |
            halfCount C ≤ frontCount f Q}).measurableSet
      have hstartA : ∀ ω ∈ A, HomogeneousStart init ω t ∧
          clockCount (virtualLabels init ω t) = C ∧
          halfCount C ≤ frontCount (virtualLabels init ω t) ((Q + 1) - 1) := by
        rintro ω ⟨he, hp⟩
        have hu := (hstart ω he).1
        refine ⟨homogeneousStart_of_time init ω s hu t hst, ?_, ?_⟩
        · exact (congrArg Finset.card
            (clockSet_fixed_from_homogeneous init ω s hu t hst)).trans
              (hstart ω he).2
        · simpa only [Nat.add_sub_cancel] using hp
      have hs := half_passage_prefix_tail init hm C (Q + 1) t hC hCm hdensity
        (by omega) hQ A hA hstartA
      rw [htime] at hs
      have hcover :
          E ∩ {ω | frontCount
            (virtualLabels init ω (s + 25 * init.card * (Q + 1))) (Q + 1) < halfCount C} ⊆
          (E ∩ {ω | frontCount (virtualLabels init ω t) Q < halfCount C}) ∪
          (A ∩ {ω | frontCount
            (virtualLabels init ω (s + 25 * init.card * (Q + 1))) (Q + 1) < halfCount C}) := by
        rintro ω ⟨he, hb⟩
        by_cases hp : halfCount C ≤ frontCount (virtualLabels init ω t) Q
        · exact Or.inr ⟨⟨he, hp⟩, hb⟩
        · exact Or.inl ⟨he, Nat.lt_of_not_ge hp⟩
      have hmass : law init A ≤ law init E := measure_mono Set.inter_subset_left
      calc
        _ ≤ law init ((E ∩ {ω | frontCount (virtualLabels init ω t) Q < halfCount C}) ∪
            (A ∩ {ω | frontCount
              (virtualLabels init ω (s + 25 * init.card * (Q + 1))) (Q + 1) < halfCount C})) :=
          measure_mono hcover
        _ ≤ law init (E ∩ {ω | frontCount (virtualLabels init ω t) Q < halfCount C}) +
            law init (A ∩ {ω | frontCount
              (virtualLabels init ω (s + 25 * init.card * (Q + 1))) (Q + 1) < halfCount C}) :=
          measure_union_le _ _
        _ ≤ (Q : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) * law init E +
            ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) * law init E :=
          add_le_add (ih (by omega)) (hs.trans (mul_le_mul_left' hmass _))
        _ = _ := by push_cast; ring

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHalfChain

end

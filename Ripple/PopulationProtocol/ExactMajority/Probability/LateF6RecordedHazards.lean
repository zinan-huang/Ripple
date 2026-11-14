-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6RecordedHazards.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6HazardBounds
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedExpectation

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
namespace Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
open TimeTheorem PairLog PairLogAuxiliary AveragingRecordedExpectation
variable {L K : ℕ}

theorem pairIndicator_recorded_condExp (init : Cfg L K) (hn : 2 ≤ init.card)
    (s t : ℕ) (hst : s ≤ t) (p : (i : Finset.Iic s) → Draw L K)
    (G : ((i : Finset.Iic t) → Draw L K) → Prop)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop) :
    (recordedFuture init s p)[pairIndicator init t G A | pairLogFiltration L K t]
      =ᵐ[recordedFuture init s p] pairHazard init t G A := by
  classical
  let F : ((i : Finset.Iic t) → Draw L K) → Draw L K → ℝ := fun q d =>
    bit (G q ∧ ∃ i j, selectLabels (prefixLabels init t q) d = some (i, j) ∧
      A (prefixLabels init t q) i j)
  have hinput : pairIndicator init t G A = recordedNext t F := rfl
  have hbound : ∀ q d, |F q d| ≤ 1 := by
    intro q d
    dsimp [F, bit]
    split_ifs <;> norm_num
  have hint (q : (i : Finset.Iic t) → Draw L K) :
      (∫ d, F q d ∂pairKernel init t q) =
        mask (G q) (pairFraction (prefixLabels init t q) A) := by
    change (∫ d, F q d ∂(drawLaw (prefixCfg init t q)).toMeasure) = _
    rw [← prefixLabels_config init t q]
    by_cases hG : G q
    · have hF : F q = (fun d => bit (∃ i j,
          selectLabels (prefixLabels init t q) d = some (i, j) ∧
            A (prefixLabels init t q) i j)) := by
        funext d
        simp only [F, hG, true_and]
      rw [hF]
      simpa only [mask, if_pos hG] using
        kernel_pairIndicator_integral (prefixLabels init t q) hn A
    · simp [F, hG, bit, mask]
  rw [hinput]
  filter_upwards [recordedNext_condExp init s t hst p F 1 hbound] with ω hω
  exact hω.trans (hint (frestrictLe t ω))

end Ripple.PopulationProtocol.ExactMajority.LateF6Hazards
end

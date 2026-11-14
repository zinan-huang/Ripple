import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase0Window

/-!
# Growth exits under a deterministic invariant

This is a generic recorded-law adapter. It does not assert a concrete protocol
height drift. Extending a potential by infinity outside the invariant makes the
global drift statement available without pretending that the invariant's
complement is absorbing.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.TraceDrain

open TimeTheorem PairLog PairLogAuxiliary

variable {L K : ℕ}

def extendTop (J : Cfg L K → Prop) (φ : Cfg L K → ℝ≥0∞) (c : Cfg L K) : ℝ≥0∞ := by
  classical
  exact if J c then φ c else ⊤

/-- The first target hit is frozen by growth_exit_tail_from. In an application
with an absorbing backup predicate B and killed potential, use H = Height ∧ ¬B:
a later backup cannot erase a height already observed before backup. -/
theorem growth_exit_tail_from_on (init : Cfg L K)
    (J H : Cfg L K → Prop) (φ : Cfg L K → ℝ≥0∞)
    (κ : ℝ≥0∞) (hκ : 1 ≤ κ)
    (hcard : ∀ c, J c → 2 ≤ c.card)
    (hnext : ∀ c, J c → ¬ H c → ∀ p : AgentState L K × AgentState L K,
      J (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hdrift : ∀ c, J c → ¬ H c →
      ∫⁻ c', φ c' ∂(NonuniformMajority L K).transitionKernel c ≤ κ * φ c)
    (thr : ℝ≥0∞) (hthr : ∀ c, J c → H c → thr ≤ φ c)
    (s T : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K)) (Ψ : ℝ≥0∞)
    (hA : ∀ p ∈ A, J (prefixCfg init s p) ∧ φ (prefixCfg init s p) ≤ Ψ) :
    thr * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∃ u, s ≤ u ∧ u ≤ s + T ∧ H (trace init ω u)} ≤
      κ ^ T * Ψ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  classical
  have hext : ∀ c, ¬ H c →
      ∫⁻ c', extendTop J φ c' ∂(NonuniformMajority L K).transitionKernel c ≤
        κ * extendTop J φ c := by
    intro c hcH
    by_cases hcJ : J c
    · have hint :
          (∫⁻ c', extendTop J φ c' ∂(NonuniformMajority L K).transitionKernel c) =
          ∫⁻ c', φ c' ∂(NonuniformMajority L K).transitionKernel c := by
        rw [Phase0Window.lintegral_transitionKernel_eq_sum
          (NonuniformMajority L K) c (hcard c hcJ),
          Phase0Window.lintegral_transitionKernel_eq_sum
          (NonuniformMajority L K) c (hcard c hcJ)]
        apply Finset.sum_congr rfl
        intro p _
        simp only [extendTop, if_pos (hnext c hcJ hcH p)]
      rw [hint]
      simpa only [extendTop, if_pos hcJ] using hdrift c hcJ hcH
    · have htop : κ * (⊤ : ℝ≥0∞) = ⊤ := by
        apply top_unique
        calc (⊤ : ℝ≥0∞) = 1 * ⊤ := by simp
          _ ≤ κ * ⊤ := mul_le_mul_right' hκ _
      simp only [extendTop, if_neg hcJ, htop, le_top]
  have hthreshold : ∀ c, ¬ (¬ H c) → thr ≤ extendTop J φ c := by
    intro c hc
    by_cases hcJ : J c
    · simpa only [extendTop, if_pos hcJ] using hthr c hcJ (not_not.mp hc)
    · simp only [extendTop, if_neg hcJ, le_top]
  have hstart : ∀ p ∈ A, extendTop J φ (prefixCfg init s p) ≤ Ψ := by
    intro p hp
    simpa only [extendTop, if_pos (hA p hp).1] using (hA p hp).2
  have h := growth_exit_tail_from init (extendTop J φ) (fun c => ¬ H c)
    κ hκ hext thr hthreshold s T A Ψ hstart
  simpa only [not_not] using h

end Ripple.PopulationProtocol.ExactMajority.TraceDrain

end

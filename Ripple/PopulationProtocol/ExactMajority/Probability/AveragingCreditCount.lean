-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCreditCount.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebt

/-!
# The count decomposition for 0.9616 M protected credit

The decomposition is pointwise on mixed configurations: inactive agents are
already charged in Y. No completion-of-activation assumption is needed.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCreditCount

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit AveragingCreditTransitions AveragingTerminalReadout
open AveragingDebtAlgebra AveragingTerminalDebt

variable {L K : ℕ}

def mainUnit (s : AgentState L K) : ℚ := if s.role = .main then 1 else 0

def exceptionWeight (k : ℕ) (s : AgentState L K) : ℕ :=
  if s.role = .main ∧ ¬ s.phase.val < 3 then
    match s.bias with
    | .zero => if k < s.hour.val then 1 else 0
    | .dyadic _ i => if k < i.val then 1 else 0
  else 0

def exceptionCount (k : ℕ) (c : Cfg L K) : ℕ :=
  (c.map (exceptionWeight k)).sum

def shallowMajorityWeight (σ : Sign) (ell : ℕ) (s : AgentState L K) : ℕ :=
  if s.role = .main ∧ ¬ s.phase.val < 3 then
    match s.bias with
    | .zero => 0
    | .dyadic tau i => if tau = σ ∧ i.val < ell then 1 else 0
  else 0

def shallowMajorityCount (σ : Sign) (ell : ℕ) (c : Cfg L K) : ℕ :=
  (c.map (shallowMajorityWeight σ ell)).sum

theorem minorityPart_nonneg (σ : Sign) (x : ℚ) : 0 ≤ minorityPart σ x := by
  cases σ <;> exact le_max_right _ _

theorem minorityPart_dyadic (σ tau : Sign) (i : Fin (L + 1)) :
    minorityPart σ (Bias.toRat (.dyadic tau i)) =
      if tau = σ then 0 else weightQ i := by
  have hw := weightQ_nonneg i
  cases σ <;> cases tau <;>
    simp [minorityPart, Bias.toRat, weightQ, neg_div,
      max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]

theorem activeDebt_dyadic (σ : Sign) (k h : ℕ) (s : AgentState L K)
    (hp : 3 ≤ s.phase.val) (hm : s.role = .main)
    (tau : Sign) (i : Fin (L + 1)) (hb : s.bias = .dyadic tau i) :
    agentDebt (positiveCoefficient σ k) (negativeCoefficient σ k) h s =
      if tau = σ then 0 else 2 * scaledWeight k i.val := by
  rw [agentDebt_eq_active _ _ h s hm hp]
  simp only [activeDebt, hb]
  rw [massBlend_coefficients, minorityPart_dyadic]
  by_cases ht : tau = σ
  · simp [ht]
  · simp [ht, scaledWeight, weightQ, pow_succ] <;> ring

theorem activeDebt_zero (σ : Sign) (k h : ℕ) (s : AgentState L K)
    (hp : 3 ≤ s.phase.val) (hm : s.role = .main) (hb : s.bias = .zero) :
    agentDebt (positiveCoefficient σ k) (negativeCoefficient σ k) h s =
      if s.hour.val < h then (1 : ℚ) else 0 := by
  rw [agentDebt_eq_active _ _ h s hm hp]
  simp [activeDebt, hb, Bias.toRat, massBlend]

theorem mixedCredit_dyadic (σ : Sign) (ell k : ℕ) (s : AgentState L K)
    (hp : 3 ≤ s.phase.val) (hm : s.role = .main)
    (tau : Sign) (i : Fin (L + 1)) (hb : s.bias = .dyadic tau i) :
    mixedAgentCredit σ ell k s =
      if tau = σ then protectedWeight ell k i.val else -scaledWeight k i.val := by
  rw [mixedAgentCredit_eq_agentCredit σ ell k s hp]
  simp [agentCredit, hm, biasCredit, signedCredit, hb]

theorem scaledWeight_ge_one_of_le (k j : ℕ) (hj : j ≤ k) :
    (1 : ℚ) ≤ scaledWeight k j := by
  unfold scaledWeight
  apply (one_le_div (by positivity : (0 : ℚ) < (2 : ℚ) ^ j)).2
  exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hj

theorem agent_credit_deficit_le (σ : Sign) (ell k : ℕ) (s : AgentState L K) :
    mainUnit s - mixedAgentCredit σ ell k s ≤
      agentDebt (positiveCoefficient σ k) (negativeCoefficient σ k) (k + 1) s +
        (exceptionWeight k s : ℚ) + (shallowMajorityWeight σ ell s : ℚ) := by
  by_cases hp : s.phase.val < 3
  · rw [agentDebt_eq_pending _ _ (k + 1) s hp, massBlend_coefficients]
    have hn := mul_nonneg (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ k)
      (minorityPart_nonneg σ (PhaseTwoSparse.smallValue s.smallBias))
    simp only [mixedAgentCredit, if_pos hp, exceptionWeight, shallowMajorityWeight,
      hp, not_true_eq_false, and_false, if_false, Nat.cast_zero, add_zero, ↓reduceIte]
    unfold mainUnit
    rw [pow_succ]
    linarith
  · have hpa : 3 ≤ s.phase.val := by omega
    by_cases hm : s.role = .main
    · rw [show mainUnit s = 1 by simp [mainUnit, hm]]
      cases hb : s.bias with
      | zero =>
          rw [activeDebt_zero σ k (k + 1) s hpa hm hb]
          have hc : mixedAgentCredit σ ell k s = 0 := by
            simp [mixedAgentCredit, hp, agentCredit, hm, biasCredit, hb]
          rw [hc]
          by_cases hh : s.hour.val ≤ k
          · have hlo : s.hour.val < k + 1 := by omega
            have hhi : ¬ k < s.hour.val := by omega
            simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hlo, hhi]
          · have hlo : ¬ s.hour.val < k + 1 := by omega
            have hhi : k < s.hour.val := by omega
            simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hlo, hhi]
      | dyadic tau i =>
          rw [activeDebt_dyadic σ k (k + 1) s hpa hm tau i hb,
            mixedCredit_dyadic σ ell k s hpa hm tau i hb]
          by_cases hs : tau = σ
          · rw [if_pos hs, if_pos hs]
            by_cases hlow : i.val < ell
            · rw [protectedWeight_eq_zero_of_lt ell k i.val hlow]
              by_cases hdeep : k < i.val <;>
                simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hs, hlow, hdeep]
            · by_cases hdeep : k < i.val
              · have hnonneg := protectedWeight_nonneg ell k i.val
                simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hdeep,
                  hs, hlow] <;> linarith
              · have hw := protectedWeight_eq_one_of_mem_band ell k i.val
                  (by omega) (by omega)
                rw [hw]
                simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hs, hlow, hdeep]
          · rw [if_neg hs, if_neg hs]
            by_cases hdeep : k < i.val
            · have hnonneg := scaledWeight_nonneg k i.val
              simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hdeep,
                hs] <;> linarith
            · have hone := scaledWeight_ge_one_of_le k i.val (by omega)
              simp [exceptionWeight, shallowMajorityWeight, hm, hp, hb, hdeep,
                hs] <;> linarith
    · have hc : mixedAgentCredit σ ell k s = 0 := by
        simp [mixedAgentCredit, hp, agentCredit, hm]
      have hn := coefficients_nonneg σ k
      simpa [mainUnit, hm, hc, exceptionWeight, shallowMajorityWeight] using
        agentDebt_nonneg (positiveCoefficient σ k) (negativeCoefficient σ k)
          (k + 1) s hn.1 hn.2

theorem mainCount_cons_cast (s : AgentState L K) (c : Cfg L K) :
    (RoleSplitConcentration.mainCount (s ::ₘ c) : ℚ) =
      mainUnit s + (RoleSplitConcentration.mainCount c : ℚ) := by
  by_cases hm : s.role = .main <;>
    simp [RoleSplitConcentration.mainCount, Multiset.countP_cons, mainUnit, hm, add_comm]

theorem credit_count_decomposition (σ : Sign) (ell k : ℕ) (c : Cfg L K) :
    (RoleSplitConcentration.mainCount c : ℚ) - mixedTotalCredit σ ell k c ≤
      debtY σ k c + (exceptionCount k c : ℚ) + (shallowMajorityCount σ ell c : ℚ) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [RoleSplitConcentration.mainCount, mixedTotalCredit, debtY, totalDebt,
        Config.sumOf, exceptionCount, shallowMajorityCount]
  | cons s c ih =>
      have hs := agent_credit_deficit_le σ ell k s
      rw [mainCount_cons_cast]
      simp only [mixedTotalCredit, debtY, totalDebt, Config.sumOf, exceptionCount,
        shallowMajorityCount, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] at ih ⊢
      linarith

theorem shallowMajorityWeight_le_phi (σ : Sign) (ell : ℕ) (s : AgentState L K) :
    (shallowMajorityWeight σ ell s : ℚ) ≤ augmentedAgentPhi ell s := by
  have hnonneg := augmentedAgentPhi_nonneg ell s
  by_cases hm : s.role = .main
  · by_cases hp : s.phase.val < 3
    · simpa [shallowMajorityWeight, hm, hp] using hnonneg
    · cases hb : s.bias with
      | zero =>
          simpa [shallowMajorityWeight, hm, hp, hb] using hnonneg
      | dyadic tau i =>
          by_cases hi : tau = σ ∧ i.val < ell
          · have hone : (1 : ℚ) ≤ (4 : ℚ) ^ (ell - 1 - i.val) := by
              simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 4)
                (Nat.zero_le (ell - 1 - i.val)))
            simpa [shallowMajorityWeight, hm, hp, hb, hi, augmentedAgentPhi,
              agentPhiAboveQ, phiBiasWeightQ, hi.2] using hone
          · simpa [shallowMajorityWeight, hm, hp, hb, hi] using hnonneg
  · simpa [shallowMajorityWeight, hm] using hnonneg

theorem shallowMajorityCount_le_phi (σ : Sign) (ell : ℕ) (c : Cfg L K) :
    (shallowMajorityCount σ ell c : ℚ) ≤ augmentedPhi ell c := by
  induction c using Multiset.induction_on with
  | empty => simp [shallowMajorityCount, augmentedPhi]
  | cons s c ih =>
      have hs := shallowMajorityWeight_le_phi σ ell s
      simp only [shallowMajorityCount, augmentedPhi, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add] at ih ⊢
      exact add_le_add hs ih

/-- 1 - .035 - .0024 - .001 = .9616. The input credit is still the mixed
credit, so immigration after this checkpoint remains part of the certificate. -/
theorem initial_mixed_credit_of_terminal_bounds
    (σ : Sign) (ell M : ℕ) (c : Cfg L K)
    (hM : RoleSplitConcentration.mainCount c = M)
    (hY : debtY σ (ell + 2) c ≤ (7 / 200 : ℚ) * M)
    (hexception : (exceptionCount (ell + 2) c : ℚ) ≤ (3 / 1250 : ℚ) * M)
    (hphi : augmentedPhi ell c ≤ (1 / 1000 : ℚ) * M) :
    (601 / 625 : ℚ) * M ≤ mixedTotalCredit σ ell (ell + 2) c := by
  have hd := credit_count_decomposition σ ell (ell + 2) c
  have hs := shallowMajorityCount_le_phi σ ell c
  rw [hM] at hd
  linarith

end Ripple.PopulationProtocol.ExactMajority.AveragingCreditCount

end

import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditTransitions
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoSparse

/-!
# Local pending-credit algebra

Pending minority mass is charged before Init-3. Safe Init-3 then preserves
credit exactly when the protected band starts above zero. The actual
Main-Main integer-averaging branch cannot decrease this credit.

This file does not prove the full mixed-phase dispatcher invariant or the
terminal X/Y service estimates.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingPendingCredit

open TimeTheorem AveragingMixedAlgebra AveragingCreditTransitions
open PhaseTwoSparse

variable {L K : ℕ}

def minorityPart : Sign → ℚ → ℚ
  | .pos, x => max (-x) 0
  | .neg, x => max x 0

def mixedAgentCredit (σ : Sign) (ell k : ℕ) (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then
    -((2 : ℚ) ^ k) * minorityPart σ (smallValue a.smallBias)
  else agentCredit σ ell k a

def mixedTotalCredit (σ : Sign) (ell k : ℕ) (c : Cfg L K) : ℚ :=
  Config.sumOf (mixedAgentCredit σ ell k) c

theorem minorityPart_pos_identity (x : ℚ) :
    2 * minorityPart .pos x = |x| - x := by
  by_cases hx : 0 ≤ x
  · rw [minorityPart, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [minorityPart, max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx']
    ring

theorem minorityPart_neg_identity (x : ℚ) :
    2 * minorityPart .neg x = |x| + x := by
  by_cases hx : 0 ≤ x
  · rw [minorityPart, max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [minorityPart, max_eq_right hx', abs_of_nonpos hx']
    ring

theorem minorityPart_pair_le (σ : Sign) (x y u v : ℚ)
    (hsum : u + v = x + y) (habs : |u| + |v| ≤ |x| + |y|) :
    minorityPart σ u + minorityPart σ v ≤
      minorityPart σ x + minorityPart σ y := by
  cases σ
  · linarith [minorityPart_pos_identity x, minorityPart_pos_identity y,
      minorityPart_pos_identity u, minorityPart_pos_identity v]
  · linarith [minorityPart_neg_identity x, minorityPart_neg_identity y,
      minorityPart_neg_identity u, minorityPart_neg_identity v]

theorem avgFin7_smallValue_sum (x y : Fin 7) :
    smallValue (avgFin7 x y).1 + smallValue (avgFin7 x y).2 =
      smallValue x + smallValue y := by
  have hnat : (avgFin7 x y).1.val + (avgFin7 x y).2.val = x.val + y.val := by
    simp only [avgFin7]
    omega
  have hq : ((avgFin7 x y).1.val : ℚ) + ((avgFin7 x y).2.val : ℚ) =
      (x.val : ℚ) + (y.val : ℚ) := by
    exact_mod_cast hnat
  simp only [smallValue]
  linarith

theorem avgFin7_minorityPart_le (σ : Sign) (x y : Fin 7) :
    minorityPart σ (smallValue (avgFin7 x y).1) +
        minorityPart σ (smallValue (avgFin7 x y).2) ≤
      minorityPart σ (smallValue x) + minorityPart σ (smallValue y) :=
  minorityPart_pair_le σ _ _ _ _ (avgFin7_smallValue_sum x y)
    (averaging_absolute_mass x y)

theorem mixedAgentCredit_eq_agentCredit (σ : Sign) (ell k : ℕ)
    (a : AgentState L K) (ha : 3 ≤ a.phase.val) :
    mixedAgentCredit σ ell k a = agentCredit σ ell k a := by
  simp only [mixedAgentCredit, if_neg (by omega : ¬ a.phase.val < 3)]

theorem mixedTotalCredit_eq_totalCredit (σ : Sign) (ell k : ℕ)
    (c : Cfg L K) (hphase : ∀ a ∈ c, 3 ≤ a.phase.val) :
    mixedTotalCredit σ ell k c = totalCredit σ ell k c := by
  revert hphase
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp [mixedTotalCredit, totalCredit, Config.sumOf]
  | cons a c ih =>
      intro hphase
      have ha := mixedAgentCredit_eq_agentCredit σ ell k a
        (hphase a (Multiset.mem_cons_self a c))
      have hc := ih (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
      unfold mixedTotalCredit totalCredit at hc ⊢
      simp only [Config.sumOf, Multiset.map_cons, Multiset.sum_cons] at hc ⊢
      rw [ha, hc]

/-- Pending signed-side debt is nonincreasing under the literal implemented
integer averaging, so its negation is nondecreasing credit. -/
theorem Phase1Transition_pending_main_credit_pair_mono
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hsp : s.phase.val < 3) (htp : t.phase.val < 3) :
    mixedAgentCredit σ ell k s + mixedAgentCredit σ ell k t ≤
      mixedAgentCredit σ ell k (Phase1Transition L K s t).1 +
        mixedAgentCredit σ ell k (Phase1Transition L K s t).2 := by
  have hdebt := avgFin7_minorityPart_le σ s.smallBias t.smallBias
  have hscaled := mul_le_mul_of_nonneg_left hdebt
    (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ k)
  simp only [mul_add] at hscaled
  simp [Phase1Transition, clockCounterStep, hsm, htm, mixedAgentCredit, hsp, htp]
  linarith

/-- A safe pending nonzero starts at index zero, below the protected band.
Its minority debt has already been paid before initialization. -/
theorem initializeAtPhaseThree_mixed_credit_eq
    (σ : Sign) (ell k : ℕ) (hell : 0 < ell) (a : AgentState L K)
    (hpending : a.phase.val < 3)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    mixedAgentCredit σ ell k (initializeAtPhaseThree a) =
      mixedAgentCredit σ ell k a := by
  have hinit : ¬ (initializeAtPhaseThree a).phase.val < 3 := by
    rw [initializeAtPhaseThree_phase]
    omega
  simp only [mixedAgentCredit, if_neg hinit, if_pos hpending]
  by_cases hm : a.role = .main
  · have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
      omega
    rcases hc with hb | hb | hb <;> cases σ <;>
      norm_num [agentCredit, initializeAtPhaseThree, phaseInit, hm, hb,
        biasCredit, signedCredit, protectedWeight, scaledWeight, smallValue,
        minorityPart, hell] <;> (try ring) <;> (try linarith) <;> (try simp) <;> (try decide)
  · have hr : (initializeAtPhaseThree a).role ≠ .main := by
      simpa only [initializeAtPhaseThree_role] using hm
    have hz : smallValue a.smallBias = 0 := by
      norm_num [smallValue, hcarrier hm]
    rw [agentCredit, if_neg hr, hz]
    cases σ <;> norm_num [minorityPart]

end Ripple.PopulationProtocol.ExactMajority.AveragingPendingCredit

end

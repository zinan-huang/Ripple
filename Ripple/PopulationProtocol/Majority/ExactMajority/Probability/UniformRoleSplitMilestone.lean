import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot035Expose
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

structure UniformRoleSplitMilestone
    (η : ℝ) (n : ℕ) where
  mp : MilestonePhase (NonuniformMajority L K)
  tRole : ℕ
  post_sound :
    ∀ c, mp.Post c → RoleSplitGood (L := L) (K := K) η n c
  pre_unhit :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
        ∀ i : Fin mp.k, ¬ mp.milestone i c₀
  potential :
    Real.log (n : ℝ) ≤ mp.pMin * mp.meanTime
  potential_nonneg :
    0 ≤ mp.pMin * mp.meanTime
  horizon :
    5 * mp.meanTime ≤ (tRole : ℝ)

theorem roleSplitTail_le_inv_sq_uniform
    {η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (U : UniformRoleSplitMilestone (L := L) (K := K) η n)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    roleSplitTail (L := L) (K := K) η n U.tRole c₀ ≤
      ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
  roleSplitTail_le_inv_sq
    (L := L) (K := K)
    hn U.mp U.post_sound (U.pre_unhit c₀ hinit)
    U.potential U.potential_nonneg U.tRole U.horizon

theorem phase0_roleSplit_whp_inv_sq_uniform
    {η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (U : UniformRoleSplitMilestone (L := L) (K := K) η n)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ U.tRole) c₀
      {c | ¬ RoleSplitGood (L := L) (K := K) η n c}
      ≤ ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
  phase0_roleSplit_whp
    (L := L) (K := K)
    hinit U.tRole _ (roleSplitTail_le_inv_sq_uniform
      (L := L) (K := K) hn U hinit)

-- NOTE: the slot-0 atom `Slot0RoleSplitTail.htail` bounds the LARGER bad event
-- `¬(allPhaseEq 0 n c ∧ RoleSplitGood η n c)` (the phase-0 window AND the role split), whereas
-- `phase0_roleSplit_whp_inv_sq_uniform` bounds only `¬ RoleSplitGood`.  Wiring the slot-0 atom therefore
-- needs the deterministic phase-0 window persistence `(κ^tRole) c₀ {¬ allPhaseEq 0 n} = 0` + a union bound
-- (Phase-0 transitions keep every agent at phase 0).  That window-persistence lemma is the remaining hook.

#print axioms roleSplitTail_le_inv_sq_uniform
#print axioms phase0_roleSplit_whp_inv_sq_uniform

end RoleSplitConcentration
end ExactMajority

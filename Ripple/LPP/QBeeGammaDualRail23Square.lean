/-
  The concrete rational cubic-transfer tensor and symmetric squaring stage for
  the CRN-safe 23→33 gamma QBee certificate.
-/

import Ripple.LPP.QBeeGammaDualRail23Stages
import Ripple.LPP.SymmetricSquaring

namespace Ripple.LPP.QBee.Generated.GammaDualRail23

open Ripple

/-- Rational transfer tensor of `balancedCubicForm`. Production terms transfer
the balancing species `0` to `i+1`; degradation terms transfer `i+1` back to
`0`. The other two indices are the remaining cubic context factors. -/
noncomputable def balancedTransfers : CubicTransfers 35 :=
  CubicTransfers.ofBalancingDilation stage2AQ stage2BQ
    stage2AQ_nonneg stage2BQ_nonneg

theorem balancedTransfers_toField :
    balancedTransfers.toField = balancedField := by
  simpa [balancedTransfers, balancedField] using
    CubicTransfers.ofBalancingDilation_toField stage2AQ stage2BQ
      stage2AQ_nonneg stage2BQ_nonneg stage2InnerField_form

theorem balancedTransfers_contextAvoidsSource :
    balancedTransfers.ContextAvoidsSource := by
  intro source target ctx1 ctx2 hrate
  induction source using Fin.cases with
  | zero =>
      induction target using Fin.cases with
      | zero => simp [balancedTransfers, CubicTransfers.ofBalancingDilation] at hrate
      | succ j =>
          induction ctx1 using Fin.cases with
          | zero => simp [balancedTransfers, CubicTransfers.ofBalancingDilation] at hrate
          | succ a =>
              induction ctx2 using Fin.cases with
              | zero => simp [balancedTransfers, CubicTransfers.ofBalancingDilation] at hrate
              | succ b =>
                  exact ⟨Ne.symm (Fin.succ_ne_zero a),
                    Ne.symm (Fin.succ_ne_zero b)⟩
  | succ i =>
      induction target using Fin.cases with
      | succ j => simp [balancedTransfers, CubicTransfers.ofBalancingDilation] at hrate
      | zero =>
          induction ctx1 using Fin.cases with
          | zero => simp [balancedTransfers, CubicTransfers.ofBalancingDilation] at hrate
          | succ a =>
              induction ctx2 using Fin.cases with
              | succ b =>
                  simp [balancedTransfers, CubicTransfers.ofBalancingDilation] at hrate
              | zero =>
                  have hB : stage2BQ i a ≠ 0 := by
                    simpa [balancedTransfers, CubicTransfers.ofBalancingDilation] using hrate
                  constructor
                  · intro hia
                    have h : i = a := Fin.succ_injective 34 hia
                    subst a
                    exact hB (stage2BQ_self_zero i)
                  · simp

set_option maxRecDepth 100000 in
/-- The optimized certificate has 35 cubic coordinates, hence 630 upper-pair
coordinates. The journal's older one-extra-auxiliary certificate gives 666. -/
theorem symmetricSquare_dimension : upperPairDim 35 = 630 := by decide

noncomputable def squaredReactions :
    WeightedReactions (upperPairDim 35) (CubicTransfers.liftCount 35) :=
  balancedTransfers.symmetricLift

noncomputable def squaredSynPP : SynPPBalance (upperPairDim 35) :=
  balancedTransfers.symmetricSynPP

noncomputable def squaredRateSpec : Kurtz.RateSpec (upperPairDim 35) :=
  balancedTransfers.symmetricRateSpec

theorem squaredRateSpec_drift_continuous_component
    (i : Fin (upperPairDim 35)) :
    Continuous (fun x ↦ squaredRateSpec.drift x i) :=
  balancedTransfers.symmetricRateSpec_drift_continuous_component i

/-- A balanced 35-coordinate ODE derivative lifts to the generated
upper-triangular quadratic reaction field. -/
theorem squared_solution_lift {x : ℝ → Fin 35 → ℝ} {t : ℝ}
    (hx : HasDerivAt x (balancedField (x t)) t) :
    HasDerivAt
      (fun s ↦ halfProduct (x s))
      (squaredReactions.toField (halfProduct (x t))) t := by
  have hx' : HasDerivAt x (balancedTransfers.toField (x t)) t := by
    rw [balancedTransfers_toField]
    exact hx
  simpa [squaredReactions] using
    balancedTransfers.symmetricLift_halfProduct_hasDerivAt hx'

/-- Any balanced trajectory becomes a mean-field solution of the concrete
630-state `RateSpec`; the normalization time change is generic. -/
noncomputable def squaredMeanFieldSolution
    (x : ℝ → Fin 35 → ℝ)
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (balancedField (x t)) t) :
    Kurtz.MeanFieldSolution (upperPairDim 35) squaredRateSpec :=
  balancedTransfers.symmetricMeanFieldSolution x (by
    intro t ht
    rw [balancedTransfers_toField]
    exact hx t ht)

theorem squaredRateSpec_kurtzStructural (N : ℕ) (hN : 0 < N) :
    let tr := squaredSynPP.toPLPPTransitions
    (CTMC.DensityDepCTMC.mk N hN tr.toRateSpec).DriftZeroAtAbsorbingOnSimplex ∧
      (CTMC.DensityDepCTMC.mk N hN tr.toRateSpec).ConservativeJumps := by
  exact balancedTransfers.symmetricRateSpec_kurtzStructural
    balancedTransfers_contextAvoidsSource N hN

/-- The symmetric compiler is boundary-compatible on every population
simplex: active reactions consume two distinct input states, while repeated
inputs are identity padding. -/
theorem squaredRateSpec_boundaryCompatibleOnSimplex (N : ℕ) (hN : 0 < N) :
    (CTMC.DensityDepCTMC.mk N hN squaredRateSpec).BoundaryCompatibleOnSimplex := by
  let R := balancedTransfers.symmetricLift
  have hactive : R.ActiveInputsDistinct :=
    balancedTransfers.symmetricLift_activeInputsDistinct
      balancedTransfers_contextAvoidsSource
  have hsyn : R.toSynPPBalance.DiagonalIdentity :=
    R.toSynPPBalance_diagonalIdentity_of_active hactive
  have hdiag : R.toSynPPBalance.toPLPPTransitions.DiagonalIdentity :=
    R.toSynPPBalance.toPLPPTransitions_diagonalIdentity hsyn
  simpa [squaredRateSpec, squaredSynPP, squaredReactions, R] using
    R.toSynPPBalance.toPLPPTransitions.toDensityDepCTMC_boundaryCompatibleOnSimplex
      hdiag N hN

/-- Concrete 630-state entry into the repository's generic frozen Kurtz
engine. Its remaining arguments are exactly the engine's analytic solution
and generic finite-horizon QV hypotheses. -/
def squared_kurtz_finite_horizon_v3 :=
  balancedTransfers.symmetricLift_kurtz_finite_horizon_v3
    balancedTransfers_contextAvoidsSource

#print axioms balancedTransfers_contextAvoidsSource
#print axioms balancedTransfers_toField
#print axioms squared_solution_lift
#print axioms squaredMeanFieldSolution
#print axioms squaredRateSpec_kurtzStructural
#print axioms squaredRateSpec_boundaryCompatibleOnSimplex
#print axioms squared_kurtz_finite_horizon_v3

end Ripple.LPP.QBee.Generated.GammaDualRail23

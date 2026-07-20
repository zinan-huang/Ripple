/-
  Reachable-state uniform bounds for mass-action CRNs.

  `massActionPMF_complement_le_raceBound` gives the local PMF complement
  in terms of the propensity ratio, used downstream by the zero-propensity
  route in `ReachablePropensityDominance.lean`.

  The `CTMObstruction` section records a structural fact about the
  `statePairTransferNetwork`: at every encoded read state, two distinct
  computation reactions are enabled with propensity one.  This confirms
  that the naive quasi-determinism route is impossible for this network;
  the correct route goes via zero-propensity (control P-invariant).
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.UniformRaceBound
import Ripple.sCRNUniversality.Stochastic.MassActionBridge
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseBimolecularRefinement

namespace Ripple.sCRNUniversality.Stochastic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u v w

namespace MassAction

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- The mass-action PMF complement is bounded by the usual propensity-race
    complement.  This is the reachable-uniform analogue of the private helper
    used in `MassAction.RaceLaw`. -/
theorem massActionPMF_complement_le_raceBound
    (hPos : N.hasPositiveRates) (z : State S) (i : N.I) :
    (massActionPMF N hPos z).toMeasure {some i}ᶜ ≤
      ENNReal.ofReal
        (1 - ((N.rxn i).propensity z : Rat) /
          (N.totalPropensity z : Rat)) := by
  rw [measure_compl
    (show MeasurableSet ({some i} : Set (Option N.I)) from trivial)
    (measure_ne_top _ _)]
  rw [measure_univ]
  rw [PMF.toMeasure_apply_singleton _ _
    (show MeasurableSet ({some i} : Set (Option N.I)) from trivial)]
  change 1 - massActionWeight N hPos z (some i) ≤ _
  unfold massActionWeight
  classical
  by_cases hT : N.Terminal z
  · simp only [hT, dite_true, tsub_zero]
    have hprop0 : (N.rxn i).propensity z = 0 :=
      Reaction.propensity_eq_zero_of_not_enabled (hT i)
    rw [hprop0]
    simp
  · simp only [hT, dite_false]
    set q := jumpProbAt N z i
    have hq_ennreal : (q : ENNReal) = ((q : NNReal) : ENNReal) := rfl
    have hq_ofReal : (q : ENNReal) =
        ENNReal.ofReal
          (((((N.rxn i).propensity z : Rat) /
            (N.totalPropensity z : Rat)) : Rat) : Real) := by
      rw [hq_ennreal, ← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [hq_ofReal]
    have hcast_eq :
        (((((N.rxn i).propensity z : Rat) /
          (N.totalPropensity z : Rat)) : Rat) : Real) =
          (((N.rxn i).propensity z : Rat) : Real) /
            (((N.totalPropensity z : Rat) : Real)) := by
      push_cast
      ring
    rw [hcast_eq, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]

end MassAction

/-! ### Obstruction for the current state-pair refinement -/

namespace CTMObstruction

open CTM

/-- The concrete state-pair refinement is not quasi-deterministic.  At every
    encoded read state it contains distinct enabled read-component reactions
    with the same source control state and different target control states. -/
theorem statePairTransferNetwork_has_two_enabled_at_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (q : Q) (m : Nat) :
    ∃ i j :
        (BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).I,
      i ≠ j ∧
        (BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).EnabledAt
            (FourPhaseEncoding.enc
              ({ state := MicroState.readPhase q, tape := m } : MicroCfg Q s)) i ∧
        (BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).EnabledAt
            (FourPhaseEncoding.enc
              ({ state := MicroState.readPhase q, tape := m } : MicroCfg Q s)) j := by
  let source : MicroState Q := MicroState.readPhase q
  let target₁ : MicroState Q := MicroState.readPhase q
  let target₂ : MicroState Q := MicroState.afterRead source false false q
  let readIdx₁ : (FourPhaseEncoding.controlSwapStatePairNetwork (Q := Q)).I :=
    ⟨(source, target₁), Network.OneRxnIdx.step⟩
  let readIdx₂ : (FourPhaseEncoding.controlSwapStatePairNetwork (Q := Q)).I :=
    ⟨(source, target₂), Network.OneRxnIdx.step⟩
  let i :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I := Sum.inl (Sum.inl readIdx₁)
  let j :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I := Sum.inl (Sum.inl readIdx₂)
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro hij
    dsimp [i, j] at hij
    have hIdx : readIdx₁ = readIdx₂ := by
      exact Sum.inl.inj (Sum.inl.inj hij)
    have hPair : (source, target₁) = (source, target₂) :=
      congrArg Sigma.fst hIdx
    have hTarget : target₁ = target₂ := congrArg Prod.snd hPair
    have hPhase := congrArg MicroState.phase hTarget
    dsimp [target₁, target₂, source, MicroState.readPhase,
      MicroState.afterRead] at hPhase
    cases hPhase
  · change (FourPhaseEncoding.controlSwapReaction source target₁).enabled
      (FourPhaseEncoding.enc
        ({ state := MicroState.readPhase q, tape := m } : MicroCfg Q s))
    simpa [source] using
      (FourPhaseEncoding.controlSwapReaction_firesTo
        (s := s) source target₁ m).enabled
  · change (FourPhaseEncoding.controlSwapReaction source target₂).enabled
      (FourPhaseEncoding.enc
        ({ state := MicroState.readPhase q, tape := m } : MicroCfg Q s))
    simpa [source] using
      (FourPhaseEncoding.controlSwapReaction_firesTo
        (s := s) source target₂ m).enabled

end CTMObstruction

end Ripple.sCRNUniversality.Stochastic

#print axioms Ripple.sCRNUniversality.Stochastic.MassAction.massActionPMF_complement_le_raceBound
#print axioms Ripple.sCRNUniversality.Stochastic.CTMObstruction.statePairTransferNetwork_has_two_enabled_at_read

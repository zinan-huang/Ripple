/-
  Reachable-state uniform bounds for sigma-composed mass-action CRNs.

  The main theorem below packages the valid part of the intended SCWB
  instantiation: component-wise quasi-determinism and an absolute propensity
  bound imply the reachable-state hypothesis of
  `rawLaw_multistep_uniform_bound_reachable`, provided the scheduled reaction
  stays enabled and has propensity at least one on every relevant prefix.

  The final theorem records the obstruction to applying this package to the
  current `statePairTransferNetwork`: already at an encoded read state, two
  distinct computation reactions are enabled.  Thus that network cannot
  supply the required quasi-determinism hypothesis.
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.UniformRaceBound
import Ripple.sCRNUniversality.Stochastic.MassActionBridge
import Ripple.sCRNUniversality.Stochastic.PropensityDominance
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

section SigmaBound

open MassAction

variable {S : Type u} [Fintype S] [DecidableEq S]
variable {A : Type v} [Fintype A]

/-- Instantiate the reachable multi-step raw-law bound for a sigma-composed
    network.  `hQuasi` eliminates the non-scheduled reactions inside the
    scheduled component; `hOtherBound` bounds every other component.  The
    lower bound on the intended propensity turns the resulting absolute
    propensity bound into the ratio bound required by the mass-action PMF. -/
theorem rawLaw_multistep_uniform_bound_reachable_of_sigma_quasi_and_bound
    (Ns : A → Network S)
    [DecidableEq A] [∀ a, DecidableEq (Ns a).I]
    [DecidableEq (Network.sigma Ns).I]
    (z0 : State S) (n : Nat)
    (component : Fin n → A)
    (reaction : ∀ k : Fin n, (Ns (component k)).I)
    (η : NNRat)
    (hPos : ∀ a, (Ns a).hasPositiveRates)
    (hEnabled : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState (Network.sigma Ns) z0 k.val) →
        (Ns (component k)).EnabledAt z (reaction k))
    (hIntendedOne : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState (Network.sigma Ns) z0 k.val) →
        1 ≤ ((Ns (component k)).rxn (reaction k)).propensity z)
    (hQuasi : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState (Network.sigma Ns) z0 k.val) →
        ∀ j : (Ns (component k)).I, j ≠ reaction k →
          ¬ (Ns (component k)).EnabledAt z j)
    (hOtherBound : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState (Network.sigma Ns) z0 k.val) →
        ∀ a : A, a ≠ component k → (Ns a).totalPropensity z ≤ η) :
    (rawLaw (Network.sigma Ns)
        ((Network.sigma_hasPositiveRates_iff Ns).2 hPos) z0)
      (⋃ k : Fin n,
        {omega | omega (k.val + 1) ≠ some ⟨component k, reaction k⟩}) ≤
      n * ENNReal.ofReal (((Fintype.card A - 1) * η : NNRat) : Rat) := by
  classical
  let hPosSigma : (Network.sigma Ns).hasPositiveRates :=
    (Network.sigma_hasPositiveRates_iff Ns).2 hPos
  let bound : NNRat := (Fintype.card A - 1) * η
  apply rawLaw_multistep_uniform_bound_reachable
    (Network.sigma Ns) hPosSigma z0 n
    (fun k => ⟨component k, reaction k⟩)
    (ENNReal.ofReal (bound : Rat))
  intro k z hz
  let intended : (Network.sigma Ns).I := ⟨component k, reaction k⟩
  have hEnabledSigma : (Network.sigma Ns).EnabledAt z intended := by
    exact hEnabled k z hz
  have hNonTerm : ¬ (Network.sigma Ns).Terminal z := by
    intro hTerminal
    exact hTerminal intended hEnabledSigma
  have hAbs := sigma_propensity_dominance_of_quasi_and_bound
    Ns (component k) (reaction k) z η
    (hQuasi k z hz) (fun a i => hPos a i) (hOtherBound k z hz)
  have hAbs' :
      (Finset.univ.erase intended).sum
          (fun j => ((Network.sigma Ns).rxn j).propensity z) ≤ bound := by
    unfold sigmaErasePropensitySum at hAbs
    dsimp [bound]
    convert hAbs using 1
    congr 1
    congr 1
    funext a b
    exact Subsingleton.elim _ _
  have hTotalOne : 1 ≤ (Network.sigma Ns).totalPropensity z := by
    calc
      1 ≤ ((Ns (component k)).rxn (reaction k)).propensity z :=
        hIntendedOne k z hz
      _ = ((Network.sigma Ns).rxn intended).propensity z := by
        rfl
      _ ≤ (Network.sigma Ns).totalPropensity z :=
        propensity_le_totalPropensity (Network.sigma Ns) intended
  have hRatio :
      (Finset.univ.erase intended).sum
          (fun j => ((Network.sigma Ns).rxn j).propensity z) ≤
        bound * (Network.sigma Ns).totalPropensity z := by
    calc
      (Finset.univ.erase intended).sum
          (fun j => ((Network.sigma Ns).rxn j).propensity z)
          ≤ bound := hAbs'
      _ = bound * 1 := (mul_one bound).symm
      _ ≤ bound * (Network.sigma Ns).totalPropensity z :=
        mul_le_mul_right hTotalOne bound
  exact le_trans
    (MassAction.massActionPMF_complement_le_raceBound
      (Network.sigma Ns) hPosSigma z intended)
    (raceBound_le_of_propensity_dominance hPosSigma hNonTerm bound hRatio)

end SigmaBound

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
#print axioms Ripple.sCRNUniversality.Stochastic.rawLaw_multistep_uniform_bound_reachable_of_sigma_quasi_and_bound
#print axioms Ripple.sCRNUniversality.Stochastic.CTMObstruction.statePairTransferNetwork_has_two_enabled_at_read

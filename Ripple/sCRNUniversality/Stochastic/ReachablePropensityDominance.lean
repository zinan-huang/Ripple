import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingSafety
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseQuasiDeterminism
import Ripple.sCRNUniversality.Stochastic.ReachableUniformBound

/-!
# Reachable propensity dominance

This file separates two facts which the proposed zero-propensity argument
conflates.

* For mass-action reactions with positive rates, an enabled reaction has
  strictly positive propensity.  A zero propensity must therefore be proved
  from a missing reactant (equivalently, from failure of `enabled`).
* The aggregate four-phase read reaction has such a missing-reactant guard,
  but the current state-pair transfer refinement starts with an unguarded
  control swap.  At an encoded read state, two distinct control swaps in that
  concrete network both have propensity exactly one.

The final section records the reusable zero-propensity route.  Its single CRN
invariant hypothesis says that every off-schedule, non-clock reaction has a
missing reactant at every relevant reachable state.  Once that hypothesis and
the clock propensity ratio are supplied, the local `hUniform` and multi-step
`rawLaw` bounds follow without quasi-determinism.
-/

namespace Ripple.sCRNUniversality.Stochastic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u v

/-! ## What the current four-phase encoding actually makes exclusive -/

namespace EncodingFacts

open CTM

/-- `enc` contains exactly one control species.  This is the actual species
exclusivity invariant available in the current encoding; tape contents are
represented instead by the two counts `tape` and `tapeBar`. -/
theorem enc_control_species_exclusive
    {Q : Type u} [DecidableEq Q] {s : Nat}
    (cfg : MicroCfg Q s) (st₁ st₂ : MicroState Q) (hne : st₁ ≠ st₂)
    (z : State (FourPhaseEncoding.Species Q))
    (hz : z = FourPhaseEncoding.enc cfg) :
    z (FourPhaseSpecies.ctrlOf st₁) > 0 →
      z (FourPhaseSpecies.ctrlOf st₂) = 0 := by
  subst z
  intro hpos
  have hst₁ : st₁ = cfg.state :=
    FourPhaseEncoding.enc_ctrlOf_eq_of_pos cfg st₁ hpos
  have hst₂ : st₂ ≠ cfg.state := by
    intro heq
    exact hne (hst₁.trans heq.symm)
  cases st₂ with
  | mk q phase readSymbol pendingWrite pendingState =>
      apply FourPhaseEncoding.enc_ctrl_eq_zero_of_ne_ctrlOf
      intro hctrl
      apply hst₂
      exact FourPhaseSpecies.ctrlOf_injective hctrl

/-- The real read-symbol invariant is a stoichiometric threshold: the probe
for the wrong bit has fewer molecules than the read reaction requires.  Its
count need not be zero. -/
theorem enc_wrong_readProbe_lt_need
    {Q : Type u} [DecidableEq Q] {s : Nat}
    (cfg : MicroCfg Q s) (r : Bool)
    (hwrong : r ≠ Encoding.readMSB? s cfg.tape) :
    FourPhaseEncoding.enc cfg (FourPhaseEncoding.readProbe r) <
      FourPhaseEncoding.readProbeNeed s r := by
  cases hr : r with
  | false =>
      have hMSB : Encoding.readMSB? s cfg.tape = true := by
        cases hm : Encoding.readMSB? s cfg.tape with
        | false => exact False.elim (hwrong (hr.trans hm.symm))
        | true => rfl
      have hTapeLe : 2 * 3 ^ s ≤ cfg.tape :=
        Encoding.readMSB?_eq_true.mp hMSB
      have hPowPos : 0 < 3 ^ s := Nat.pow_pos (by omega)
      change FourPhaseEncoding.enc cfg FourPhaseSpecies.tapeBar < 3 ^ s
      rw [FourPhaseEncoding.enc_tapeBar]
      unfold FourPhaseEncoding.maxTape
      omega
  | true =>
      have hMSB : Encoding.readMSB? s cfg.tape = false := by
        cases hm : Encoding.readMSB? s cfg.tape with
        | false => rfl
        | true => exact False.elim (hwrong (hr.trans hm.symm))
      have hTapeLt : cfg.tape < 2 * 3 ^ s :=
        Encoding.readMSB?_eq_false.mp hMSB
      change FourPhaseEncoding.enc cfg FourPhaseSpecies.tape < 2 * 3 ^ s
      simpa using hTapeLt

/-- Consequently, a wrong *aggregate* read reaction has zero propensity at an
encoded state.  This statement does not apply to the concrete control-swap
reaction used by the state-pair refinement below. -/
theorem wrong_read_reaction_propensity_zero_at_enc
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (cfg : MicroCfg Q s) (q : Q) (r w : Bool) (qNext : Q)
    (hwrong : r ≠ Encoding.readMSB? s cfg.tape) :
    (CTM.ReadGadget.reaction (s := s) q r w qNext).propensity
        (FourPhaseEncoding.enc cfg) = 0 := by
  apply Reaction.propensity_eq_zero_of_not_enabled
  intro hEnabled
  have hNeed :
      FourPhaseEncoding.readProbeNeed s r ≤
        FourPhaseEncoding.enc cfg (FourPhaseEncoding.readProbe r) := by
    have := hEnabled (FourPhaseEncoding.readProbe r)
    cases r <;>
      simpa [CTM.ReadGadget.reaction, CTM.ReadGadget.input,
        FourPhaseEncoding.readProbe, FourPhaseEncoding.readProbeNeed,
        State.add] using this
  exact (Nat.not_lt_of_ge hNeed)
    (enc_wrong_readProbe_lt_need cfg r hwrong)

end EncodingFacts

/-! ## Missing-reactant form of the reachable invariant -/

namespace ZeroPropensityRoute

open CTM MassAction

/-- A reaction with any under-supplied reactant has zero propensity. -/
theorem propensity_eq_zero_of_missing_reactant
    {S : Type u} [Fintype S]
    (N : Network.{u, v} S) {z : State S} {j : N.I}
    (hMissing : ∃ species : S, z species < (N.rxn j).l species) :
    (N.rxn j).propensity z = 0 := by
  apply Reaction.propensity_eq_zero_of_not_enabled
  intro hEnabled
  rcases hMissing with ⟨species, hlt⟩
  exact (Nat.not_lt_of_ge (hEnabled species)) hlt

/-- States reachable from a four-phase encoded initial configuration. -/
def reachableFromEnc
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (N : Network.{u, v} (FourPhaseEncoding.Species Q))
    (cfg₀ : MicroCfg Q s) : Set (State (FourPhaseEncoding.Species Q)) :=
  {z | N.ReachableFrom (FourPhaseEncoding.enc cfg₀) z}

/-- The precise fallback invariant needed to prove that a wrong computation
reaction has zero propensity.  `hMissing` is the only encoding/network-specific
gap: it requires an under-supplied reactant for every wrong computation
reaction at every reachable state. -/
theorem wrong_computation_propensity_zero_at_reachable
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (N : Network.{u, v} (FourPhaseEncoding.Species Q))
    (cfg₀ : MicroCfg Q s)
    (isComputationReaction : N.I → Prop)
    (scheduledReactionAt : State (FourPhaseEncoding.Species Q) → N.I)
    (hMissing : ∀ z ∈ reachableFromEnc N cfg₀, ∀ j : N.I,
      isComputationReaction j → j ≠ scheduledReactionAt z →
        ∃ species, z species < (N.rxn j).l species)
    (z : State (FourPhaseEncoding.Species Q))
    (hz : z ∈ reachableFromEnc N cfg₀)
    (i j : N.I)
    (_hi : isComputationReaction i)
    (hj : isComputationReaction j)
    (hscheduled : i = scheduledReactionAt z)
    (hwrong : j ≠ i) :
    (N.rxn j).propensity z = 0 := by
  apply propensity_eq_zero_of_missing_reactant N
  apply hMissing z hz j hj
  intro hjscheduled
  exact hwrong (hjscheduled.trans hscheduled.symm)

end ZeroPropensityRoute

/-! ## The obstruction is stronger than syntactic non-uniqueness -/

namespace ConcreteObstruction

open CTM

/-- Every concrete state-pair control swap has propensity one at its encoded
source, independently of the target control state. -/
theorem controlSwapReaction_propensity_one
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (st st' : MicroState Q) (m : Nat) :
    (FourPhaseEncoding.controlSwapReaction st st').propensity
      (FourPhaseEncoding.enc
        ({ state := st, tape := m } : MicroCfg Q s)) = 1 := by
  unfold Reaction.propensity
  rw [FourPhaseEncoding.controlSwapReaction]
  simp only [FourPhaseEncoding.aggregateReaction_k, one_mul]
  apply Finset.prod_eq_one
  intro species _hspecies
  cases species <;>
    simp [FourPhaseEncoding.aggregateReaction,
      FourPhaseEncoding.aggregateInput, FourPhaseEncoding.enc,
      FourPhaseEncoding.control, FourPhaseEncoding.tape,
      FourPhaseEncoding.tapeBar, State.add, FourPhaseSpecies.ctrlOf]

/-- At every encoded read state, two distinct concrete computation reactions
have propensity exactly one. -/
theorem statePairTransferNetwork_has_two_propensity_one_at_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (q : Q) (m : Nat) :
    ∃ i j :
        (BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).I,
      i ≠ j ∧
        ((BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).rxn i).propensity
            (FourPhaseEncoding.enc
              ({ state := MicroState.readPhase q, tape := m } :
                MicroCfg Q s)) = 1 ∧
        ((BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).rxn j).propensity
            (FourPhaseEncoding.enc
              ({ state := MicroState.readPhase q, tape := m } :
                MicroCfg Q s)) = 1 := by
  let source : MicroState Q := MicroState.readPhase q
  let target₁ : MicroState Q := MicroState.readPhase q
  let target₂ : MicroState Q :=
    MicroState.afterRead source false false q
  let readIdx₁ :
      (FourPhaseEncoding.controlSwapStatePairNetwork (Q := Q)).I :=
    ⟨(source, target₁), Network.OneRxnIdx.step⟩
  let readIdx₂ :
      (FourPhaseEncoding.controlSwapStatePairNetwork (Q := Q)).I :=
    ⟨(source, target₂), Network.OneRxnIdx.step⟩
  let i :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I :=
    Sum.inl (Sum.inl readIdx₁)
  let j :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I :=
    Sum.inl (Sum.inl readIdx₂)
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro hij
    dsimp [i, j] at hij
    have hIdx : readIdx₁ = readIdx₂ :=
      Sum.inl.inj (Sum.inl.inj hij)
    have hPair : (source, target₁) = (source, target₂) :=
      congrArg Sigma.fst hIdx
    have hTarget : target₁ = target₂ := congrArg Prod.snd hPair
    have hPhase := congrArg MicroState.phase hTarget
    dsimp [target₁, target₂, source, MicroState.readPhase,
      MicroState.afterRead] at hPhase
    cases hPhase
  · change (FourPhaseEncoding.controlSwapReaction source target₁).propensity
      (FourPhaseEncoding.enc
        ({ state := MicroState.readPhase q, tape := m } :
          MicroCfg Q s)) = 1
    simpa [source] using
      (controlSwapReaction_propensity_one (s := s) source target₁ m)
  · change (FourPhaseEncoding.controlSwapReaction source target₂).propensity
      (FourPhaseEncoding.enc
        ({ state := MicroState.readPhase q, tape := m } :
          MicroCfg Q s)) = 1
    simpa [source] using
      (controlSwapReaction_propensity_one (s := s) source target₂ m)

/-- No choice of a scheduled concrete reaction can make every other concrete
computation propensity zero at an encoded read state. -/
theorem statePairTransferNetwork_exists_wrong_propensity_one_at_read
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (q : Q) (m : Nat)
    (intended :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I) :
    ∃ wrong,
      wrong ≠ intended ∧
        ((BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).rxn wrong).propensity
            (FourPhaseEncoding.enc
              ({ state := MicroState.readPhase q, tape := m } :
                MicroCfg Q s)) = 1 := by
  rcases statePairTransferNetwork_has_two_propensity_one_at_read M q m with
    ⟨i, j, hij, hi, hj⟩
  by_cases h : i = intended
  · exact ⟨j, by
      intro hjEq
      exact hij (h.trans hjEq.symm), hj⟩
  · exact ⟨i, h, hi⟩

end ConcreteObstruction

/-! ## Conditional zero-propensity route to `hUniform` and `rawLaw` -/

namespace ZeroPropensityRoute

open MassAction

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- If every off-schedule, non-clock reaction has zero propensity and the
clock propensity is ratio-bounded, then the scheduled PMF complement is
bounded by the same ratio. -/
theorem reachable_hUniform_via_zero_propensity
    (hPos : N.hasPositiveRates)
    (isClock : N.I → Prop) [DecidablePred isClock]
    (z : State S) (intended : N.I)
    (hEnabled : N.EnabledAt z intended)
    (ε : NNRat)
    (hZero : ∀ j : N.I, j ≠ intended → ¬ isClock j →
      (N.rxn j).propensity z = 0)
    (hClock :
      (Finset.univ.filter isClock).sum
          (fun j => (N.rxn j).propensity z) ≤
        ε * N.totalPropensity z) :
    (massActionPMF N hPos z).toMeasure {some intended}ᶜ ≤
      ENNReal.ofReal (ε : Rat) := by
  have hRest :
      (Finset.univ.erase intended).sum
          (fun j => (N.rxn j).propensity z) ≤
        (Finset.univ.filter isClock).sum
          (fun j => (N.rxn j).propensity z) := by
    apply Finset.sum_le_sum_of_ne_zero
    intro j hj hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hjClock
    exact hne (hZero j (Finset.ne_of_mem_erase hj) hjClock)
  have hNonTerm : ¬ N.Terminal z := by
    intro hTerminal
    exact hTerminal intended hEnabled
  exact le_trans
    (MassAction.massActionPMF_complement_le_raceBound
      N hPos z intended)
    (raceBound_le_of_propensity_dominance hPos hNonTerm ε
      (le_trans hRest hClock))

/-- Reachable multi-step raw-law bound obtained from the local
zero-propensity route. -/
theorem scwb_rawLaw_uniform_bound
    (hPos : N.hasPositiveRates) (z₀ : State S)
    (n : Nat) (schedule : Fin n → N.I)
    (isClock : N.I → Prop) [DecidablePred isClock]
    (ε : NNRat)
    (hEnabled : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState N z₀ k.val) →
      N.EnabledAt z (schedule k))
    (hZero : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState N z₀ k.val) →
      ∀ j : N.I, j ≠ schedule k → ¬ isClock j →
        (N.rxn j).propensity z = 0)
    (hClock : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState N z₀ k.val) →
      (Finset.univ.filter isClock).sum
          (fun j => (N.rxn j).propensity z) ≤
        ε * N.totalPropensity z) :
    (rawLaw N hPos z₀)
      (⋃ k : Fin n,
        {omega | omega (k.val + 1) ≠ some (schedule k)}) ≤
      n * ENNReal.ofReal (ε : Rat) := by
  apply rawLaw_multistep_uniform_bound_reachable
    N hPos z₀ n schedule (ENNReal.ofReal (ε : Rat))
  intro k z hz
  exact reachable_hUniform_via_zero_propensity
    N hPos isClock z (schedule k) (hEnabled k z hz) ε
    (hZero k z hz) (hClock k z hz)

end ZeroPropensityRoute

end Ripple.sCRNUniversality.Stochastic

namespace Ripple.sCRNUniversality.Stochastic.EncodingFacts

#print axioms enc_control_species_exclusive
#print axioms enc_wrong_readProbe_lt_need
#print axioms wrong_read_reaction_propensity_zero_at_enc

end Ripple.sCRNUniversality.Stochastic.EncodingFacts

namespace Ripple.sCRNUniversality.Stochastic.ConcreteObstruction

#print axioms controlSwapReaction_propensity_one
#print axioms statePairTransferNetwork_has_two_propensity_one_at_read
#print axioms statePairTransferNetwork_exists_wrong_propensity_one_at_read

end Ripple.sCRNUniversality.Stochastic.ConcreteObstruction

namespace Ripple.sCRNUniversality.Stochastic.ZeroPropensityRoute

#print axioms propensity_eq_zero_of_missing_reactant
#print axioms wrong_computation_propensity_zero_at_reachable
#print axioms reachable_hUniform_via_zero_propensity
#print axioms scwb_rawLaw_uniform_bound

end Ripple.sCRNUniversality.Stochastic.ZeroPropensityRoute

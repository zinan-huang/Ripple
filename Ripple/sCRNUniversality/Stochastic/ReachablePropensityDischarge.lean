import Ripple.sCRNUniversality.Stochastic.ReachablePropensityDominance
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseBimolecularRefinement
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingTransferSafety
import Ripple.sCRNUniversality.Core.Invariants

/-!
# Concrete reachable propensity discharge

The state-pair transfer network has one control molecule in every reaction
input and output.  This file packages that observation as a linear invariant
and uses it to discharge zero-propensity obligations for reactions whose
source control differs from the enabled scheduled reaction.
-/

namespace Ripple.sCRNUniversality.Stochastic

open CTM
open scoped BigOperators ENNReal

universe u v

/-! ## The control P-invariant -/

/-- Weight one on control species and zero on both tape species. -/
def controlWeight (Q : Type u) : FourPhaseEncoding.Species Q → Int
  | FourPhaseSpecies.ctrl _ _ _ _ _ => 1
  | FourPhaseSpecies.tape => 0
  | FourPhaseSpecies.tapeBar => 0

/-- Stoichiometric balance implies preservation of the corresponding linear
form.  `Core.Invariants` defines both notions; this is the algebraic bridge. -/
theorem Reaction.PreservesLin.of_balances
    {S : Type u} [Fintype S] {rho : Reaction S} {w : S → Int}
    (hBalance : rho.Balances w) :
    rho.PreservesLin w := by
  intro z z' hFire
  rw [show z' = rho.fire z from hFire.eq_fire]
  unfold Reaction.Balances Complex.lin at hBalance
  unfold State.lin
  calc
    (∑ species, w species * ((rho.fire z species : Nat) : Int)) =
        ∑ species,
          (w species * (z species : Int) -
            w species * (rho.l species : Int) +
            w species * (rho.r species : Int)) := by
      apply Finset.sum_congr rfl
      intro species _
      rw [rho.fire_apply, Nat.cast_add,
        Nat.cast_sub (hFire.enabled species)]
      simp only [mul_add, mul_sub]
    _ = (∑ species, w species * (z species : Int)) -
          (∑ species, w species * (rho.l species : Int)) +
          (∑ species, w species * (rho.r species : Int)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ species, w species * (z species : Int) := by
      rw [hBalance]
      exact sub_add_cancel _ _

/-- Network-level form of `Reaction.PreservesLin.of_balances`. -/
theorem Network.PreservesLin.of_balances
    {S : Type u} [Fintype S] {N : Network.{u, v} S} {w : S → Int}
    (hBalance : N.Balances w) :
    N.PreservesLin w := by
  intro i
  exact Reaction.PreservesLin.of_balances (hBalance i)

private theorem complex_lin_add
    {S : Type u} [Fintype S] (w : S → Int) (x y : Complex S) :
    Complex.lin w (State.add x y) =
      Complex.lin w x + Complex.lin w y := by
  simp only [Complex.lin, State.add, Nat.cast_add, mul_add,
    Finset.sum_add_distrib]

private theorem complex_lin_single
    {S : Type u} [Fintype S] [DecidableEq S]
    (w : S → Int) (species : S) (n : Nat) :
    Complex.lin w (State.single species n) = w species * (n : Int) := by
  simp [Complex.lin, State.single]

private theorem state_lin_add
    {S : Type u} [Fintype S] (w : S → Int) (x y : State S) :
    State.lin w (State.add x y) = State.lin w x + State.lin w y := by
  simp only [State.lin, State.add, Nat.cast_add, mul_add,
    Finset.sum_add_distrib]

private theorem state_lin_single
    {S : Type u} [Fintype S] [DecidableEq S]
    (w : S → Int) (species : S) (n : Nat) :
    State.lin w (State.single species n) = w species * (n : Int) := by
  simp [State.lin, State.single]

theorem aggregateReaction_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (st st' : MicroState Q)
    (tapeIn tapeBarIn tapeOut tapeBarOut : Nat) :
    (FourPhaseEncoding.aggregateReaction st st'
      tapeIn tapeBarIn tapeOut tapeBarOut).Balances
        (controlWeight Q) := by
  unfold Reaction.Balances
  simp [FourPhaseEncoding.aggregateReaction,
    FourPhaseEncoding.aggregateInput,
    FourPhaseEncoding.aggregateOutput,
    complex_lin_add, complex_lin_single, controlWeight,
    FourPhaseSpecies.ctrlOf]

private theorem oneRxn_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (rho : Reaction (FourPhaseEncoding.Species Q))
    (h : rho.Balances (controlWeight Q)) :
    (Network.oneRxnNetwork rho).Balances (controlWeight Q) := by
  intro i
  cases i
  exact h

private theorem controlSwapNetwork_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (st st' : MicroState Q) :
    (FourPhaseEncoding.controlSwapNetwork st st').Balances
      (controlWeight Q) := by
  apply oneRxn_balances_controlWeight
  simpa [FourPhaseEncoding.controlSwapReaction] using
    aggregateReaction_balances_controlWeight
      st st' 0 0 0 0

private theorem tapeTransferWithControlNetwork_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (st st' : MicroState Q) :
    (FourPhaseEncoding.tapeTransferWithControlNetwork st st').Balances
      (controlWeight Q) := by
  rw [FourPhaseEncoding.tapeTransferWithControlNetwork,
    Network.parallel_balances_iff,
    FourPhaseEncoding.tapeTransferUnitNetwork,
    Network.parallel_balances_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply oneRxn_balances_controlWeight
    simpa [FourPhaseEncoding.transferTapeToTapeBarReaction] using
      aggregateReaction_balances_controlWeight st st 1 0 0 1
  · apply oneRxn_balances_controlWeight
    simpa [FourPhaseEncoding.transferTapeBarToTapeReaction] using
      aggregateReaction_balances_controlWeight st st 0 1 1 0
  · exact controlSwapNetwork_balances_controlWeight st st'

private theorem statePairNetwork_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (Npair : MicroState Q → MicroState Q →
      Network (FourPhaseEncoding.Species Q))
    (hPair : ∀ st st', (Npair st st').Balances (controlWeight Q)) :
    (FourPhaseEncoding.statePairNetwork Npair).Balances
      (controlWeight Q) := by
  rintro ⟨⟨st, st'⟩, i⟩
  exact hPair st st' i

private theorem controlSwapStatePairNetwork_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q] :
    (FourPhaseEncoding.controlSwapStatePairNetwork (Q := Q)).Balances
      (controlWeight Q) := by
  apply statePairNetwork_balances_controlWeight
  exact controlSwapNetwork_balances_controlWeight

private theorem tapeTransferWithControlStatePairNetwork_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q] :
    (FourPhaseEncoding.tapeTransferWithControlStatePairNetwork
      (Q := Q)).Balances (controlWeight Q) := by
  apply statePairNetwork_balances_controlWeight
  exact tapeTransferWithControlNetwork_balances_controlWeight

/-- Every reaction of the concrete state-pair network balances total control
weight. -/
theorem statePairTransferNetwork_balances_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).Balances (controlWeight Q) := by
  change
    ((FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
      (s := s) M).network).Balances (controlWeight Q)
  dsimp [
    FourPhaseConcrete.FootprintedConcreteFourPhaseExpansionFamily.network,
    FourPhaseEncoding.statePairTransferFootprintedConcreteFourPhaseExpansionFamily
  ]
  rw [Network.parallel_balances_iff,
    Network.parallel_balances_iff,
    Network.parallel_balances_iff]
  exact ⟨
    ⟨controlSwapStatePairNetwork_balances_controlWeight,
      tapeTransferWithControlStatePairNetwork_balances_controlWeight⟩,
    ⟨tapeTransferWithControlStatePairNetwork_balances_controlWeight,
      tapeTransferWithControlStatePairNetwork_balances_controlWeight⟩
  ⟩

/-- The concrete network preserves total control weight. -/
theorem statePairTransferNetwork_preserves_controlWeight
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :
    (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).PreservesLin (controlWeight Q) :=
  Network.PreservesLin.of_balances
    (statePairTransferNetwork_balances_controlWeight (s := s) M)

/-- The encoded initial state has exactly one unit of control weight. -/
theorem enc_controlWeight_sum
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (cfg : MicroCfg Q s) :
    State.lin (controlWeight Q) (FourPhaseEncoding.enc cfg) = 1 := by
  simp [FourPhaseEncoding.enc, FourPhaseEncoding.control,
    FourPhaseEncoding.tape, FourPhaseEncoding.tapeBar,
    state_lin_add, state_lin_single, controlWeight,
    FourPhaseSpecies.ctrlOf]

/-- Total control weight is one at every state reachable from an encoding. -/
theorem reachable_controlWeight_sum
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z) :
    State.lin (controlWeight Q) z = 1 := by
  calc
    State.lin (controlWeight Q) z =
        State.lin (controlWeight Q) (FourPhaseEncoding.enc cfg₀) :=
      Network.Reaches.lin_eq_of_preservesLin
        (statePairTransferNetwork_preserves_controlWeight (s := s) M)
        hReach
    _ = 1 := enc_controlWeight_sum cfg₀

/-! ## Exactly one active control species -/

/-- The natural-number contribution of one species to total control count. -/
def controlCount (Q : Type u)
    (z : State (FourPhaseEncoding.Species Q))
    (species : FourPhaseEncoding.Species Q) : Nat :=
  match species with
  | FourPhaseSpecies.ctrl _ _ _ _ _ => z species
  | FourPhaseSpecies.tape => 0
  | FourPhaseSpecies.tapeBar => 0

/-- Total number of control molecules, expressed in `Nat`. -/
def controlTotal (Q : Type u) [Fintype Q]
    (z : State (FourPhaseEncoding.Species Q)) : Nat :=
  Finset.univ.sum (controlCount Q z)

@[simp]
theorem controlCount_ctrlOf
    {Q : Type u} (z : State (FourPhaseEncoding.Species Q))
    (st : MicroState Q) :
    controlCount Q z (FourPhaseSpecies.ctrlOf st) =
      z (FourPhaseSpecies.ctrlOf st) := by
  cases st
  rfl

theorem controlTotal_cast
    {Q : Type u} [Fintype Q]
    (z : State (FourPhaseEncoding.Species Q)) :
    (controlTotal Q z : Int) = State.lin (controlWeight Q) z := by
  unfold controlTotal State.lin
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro species _
  cases species <;> simp [controlCount, controlWeight]

theorem reachable_controlTotal_eq_one
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z) :
    controlTotal Q z = 1 := by
  have hInt : (controlTotal Q z : Int) = 1 := by
    rw [controlTotal_cast]
    exact reachable_controlWeight_sum M cfg₀ hReach
  exact_mod_cast hInt

/-- At a reachable state there is exactly one control state with positive
count. -/
theorem reachable_unique_active_control
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z) :
    ∃! st : MicroState Q, 0 < z (FourPhaseSpecies.ctrlOf st) := by
  have hTotal : controlTotal Q z = 1 :=
    reachable_controlTotal_eq_one M cfg₀ hReach
  have hExists : ∃ st : MicroState Q,
      0 < z (FourPhaseSpecies.ctrlOf st) := by
    by_contra hNone
    push Not at hNone
    have hZero : ∀ species : FourPhaseEncoding.Species Q,
        controlCount Q z species = 0 := by
      intro species
      cases species with
      | ctrl q phase readSymbol pendingWrite pendingState =>
          apply Nat.eq_zero_of_not_pos
          intro hPos
          exact (Nat.not_lt_of_ge
            (hNone ({
              q := q
              phase := phase
              readSymbol := readSymbol
              pendingWrite := pendingWrite
              pendingState := pendingState
            } : MicroState Q))) hPos
      | tape => rfl
      | tapeBar => rfl
    have : controlTotal Q z = 0 := by
      apply Finset.sum_eq_zero
      intro species _
      exact hZero species
    omega
  rcases hExists with ⟨active, hActive⟩
  refine ⟨active, hActive, ?_⟩
  intro other hOther
  by_contra hne
  have hCtrlNe :
      FourPhaseSpecies.ctrlOf active ≠ FourPhaseSpecies.ctrlOf other := by
    intro hEq
    exact hne (FourPhaseSpecies.ctrlOf_injective hEq).symm
  have hSubset :
      ({FourPhaseSpecies.ctrlOf active,
        FourPhaseSpecies.ctrlOf other} :
          Finset (FourPhaseEncoding.Species Q)) ⊆ Finset.univ := by
    simp
  have hTwoLe :
      controlCount Q z (FourPhaseSpecies.ctrlOf active) +
          controlCount Q z (FourPhaseSpecies.ctrlOf other) ≤
        controlTotal Q z := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := controlCount Q z) hSubset
      (by
        intro species _ _
        exact Nat.zero_le _)
    simpa [controlTotal, hCtrlNe] using h
  simp only [controlCount_ctrlOf] at hTwoLe
  omega

/-- Every control species other than a known active one has count zero. -/
theorem reachable_wrong_control_zero
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z)
    {active st : MicroState Q}
    (hActive : 0 < z (FourPhaseSpecies.ctrlOf active))
    (hne : st ≠ active) :
    z (FourPhaseSpecies.ctrlOf st) = 0 := by
  rcases reachable_unique_active_control M cfg₀ hReach with
    ⟨unique, hUniquePos, hUnique⟩
  have hActiveEq : active = unique := hUnique active hActive
  by_contra hPos
  have hStPos : 0 < z (FourPhaseSpecies.ctrlOf st) :=
    Nat.pos_of_ne_zero hPos
  have hStEq : st = unique := hUnique st hStPos
  exact hne (hStEq.trans hActiveEq.symm)

/-! ## Source controls and missing reactants -/

/-- Source microstate carried by a concrete state-pair reaction index. -/
def sourceState
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I) : MicroState Q :=
  match j with
  | Sum.inl (Sum.inl ⟨pair, _⟩) => pair.1
  | Sum.inl (Sum.inr ⟨pair, _⟩) => pair.1
  | Sum.inr (Sum.inl ⟨pair, _⟩) => pair.1
  | Sum.inr (Sum.inr ⟨pair, _⟩) => pair.1

/-- Every concrete reaction is guarded by its source control species. -/
theorem statePairTransferNetwork_guardedBy_sourceState
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I) :
    ((BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).rxn j).GuardedBy
        (FourPhaseSpecies.ctrlOf (sourceState M j)) := by
  rcases j with (((⟨⟨st, st'⟩, i⟩ | ⟨⟨st, st'⟩, i⟩) |
      (⟨⟨st, st'⟩, i⟩ | ⟨⟨st, st'⟩, i⟩)))
  · cases i
    exact FourPhaseEncoding.controlSwapReaction_guardedBy_ctrlOf st st'
  all_goals
    rcases i with ((i | i) | i)
    · cases i
      exact
        FourPhaseEncoding.transferTapeToTapeBarReaction_guardedBy_ctrlOf
          st st' 1
    · cases i
      exact
        FourPhaseEncoding.transferTapeBarToTapeReaction_guardedBy_ctrlOf
          st st' 1
    · cases i
      exact FourPhaseEncoding.controlSwapReaction_guardedBy_ctrlOf st st'

/-- A wrong-source reaction is missing its source control reactant. -/
theorem wrong_source_missing_reactant
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z)
    {active : MicroState Q}
    (hActive : 0 < z (FourPhaseSpecies.ctrlOf active))
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I)
    (hSource : sourceState M j ≠ active) :
    ∃ species : FourPhaseEncoding.Species Q,
      z species <
        ((BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).rxn j).l species := by
  refine ⟨FourPhaseSpecies.ctrlOf (sourceState M j), ?_⟩
  have hZero : z (FourPhaseSpecies.ctrlOf (sourceState M j)) = 0 :=
    reachable_wrong_control_zero M cfg₀ hReach hActive hSource
  have hGuard := statePairTransferNetwork_guardedBy_sourceState M j
  rw [hZero]
  exact lt_of_lt_of_le Nat.zero_lt_one hGuard

/-- Wrong-source reactions have zero propensity at every reachable state. -/
theorem wrong_source_propensity_zero_at_reachable
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z)
    {active : MicroState Q}
    (hActive : 0 < z (FourPhaseSpecies.ctrlOf active))
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I)
    (hSource : sourceState M j ≠ active) :
    ((BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).rxn j).propensity z = 0 := by
  apply ZeroPropensityRoute.propensity_eq_zero_of_missing_reactant
    (BimolecularFourPhaseRefinement.statePairTransferNetwork (s := s) M)
  exact wrong_source_missing_reactant M cfg₀ hReach hActive j hSource

/-- If an intended reaction is enabled, every reaction with a different
source control has zero propensity. -/
theorem statePairTransfer_hZero_at_reachable
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z)
    (intended : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I)
    (hEnabled :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).EnabledAt z intended)
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I)
    (hSource : sourceState M j ≠ sourceState M intended) :
    ((BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).rxn j).propensity z = 0 := by
  have hActive :
      0 < z (FourPhaseSpecies.ctrlOf (sourceState M intended)) := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (statePairTransferNetwork_guardedBy_sourceState M intended)
        (hEnabled (FourPhaseSpecies.ctrlOf (sourceState M intended))))
  exact wrong_source_propensity_zero_at_reachable
    M cfg₀ hReach hActive j hSource

/-- Reactions sharing the intended source control, except for the intended
reaction itself. -/
def sameSourceClock
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q)
    (intended j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I) : Prop :=
  j ≠ intended ∧ sourceState M j = sourceState M intended

theorem statePairTransfer_hZero_nonClock_at_reachable
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    {z : State (FourPhaseEncoding.Species Q)}
    (hReach :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).Reaches (FourPhaseEncoding.enc cfg₀) z)
    (intended : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I)
    (hEnabled :
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).EnabledAt z intended)
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I)
    (hne : j ≠ intended) (hNotClock : ¬ sameSourceClock M intended j) :
    ((BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).rxn j).propensity z = 0 := by
  apply statePairTransfer_hZero_at_reachable M cfg₀ hReach intended
    hEnabled j
  intro hSame
  exact hNotClock ⟨hne, hSame⟩

/-! ## Prefix states are reachable -/

open MassAction

theorem stateStep_reaches
    {S : Type u} [Fintype S] [DecidableEq S]
    (N : Network.{u, v} S) [DecidableEq N.I]
    (z : State S) (o : Option N.I) :
    N.Reaches z (stateStep N z o) := by
  classical
  unfold stateStep
  split
  · exact Network.reaches_refl N z
  · apply Network.reaches_of_stepAt
    exact ⟨fireOptionSanitized_enabled N z o _, rfl⟩

theorem prefixToState_reaches
    {S : Type u} [Fintype S] [DecidableEq S]
    (N : Network.{u, v} S) [DecidableEq N.I]
    (z₀ : State S) (n : Nat)
    (p : (i : Finset.Iic n) → Option N.I) :
    N.Reaches z₀ (prefixToState N z₀ n p) := by
  classical
  induction n with
  | zero =>
      simpa [prefixToState] using Network.reaches_refl N z₀
  | succ n ih =>
      rw [prefixToState]
      apply Network.reaches_trans (ih _)
      exact stateStep_reaches N _ _

/-! ## A global clock predicate for a finite schedule -/

/-- A reaction is a clock reaction for a schedule when it is a same-source
competitor of at least one scheduled reaction.  This schedule-wide predicate
has the fixed type required by `scwb_rawLaw_uniform_bound`. -/
def scheduleSourceClock
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s n : Nat}
    (M : Binary Q)
    (schedule : Fin n →
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I)
    (j : (BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).I) : Prop :=
  ∃ k : Fin n, sameSourceClock M (schedule k) j

open Classical in
/-- The schedule-wide clock propensity is bounded by total propensity. -/
theorem statePairTransfer_clock_propensity_bound
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s n : Nat}
    (M : Binary Q)
    (schedule : Fin n →
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I)
    (z : State (FourPhaseEncoding.Species Q)) :
    (Finset.univ.filter (scheduleSourceClock M schedule)).sum
        (fun j =>
          ((BimolecularFourPhaseRefinement.statePairTransferNetwork
            (s := s) M).rxn j).propensity z) ≤
      (1 : NNRat) *
        (BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).totalPropensity z := by
  calc
    (Finset.univ.filter (scheduleSourceClock M schedule)).sum
        (fun j =>
          ((BimolecularFourPhaseRefinement.statePairTransferNetwork
            (s := s) M).rxn j).propensity z) ≤
        Finset.univ.sum
          (fun j =>
            ((BimolecularFourPhaseRefinement.statePairTransferNetwork
              (s := s) M).rxn j).propensity z) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro j _ _
        exact bot_le
    _ = (1 : NNRat) *
        (BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).totalPropensity z := by
      simp [Network.totalPropensity]

open MassAction

/-- The unconditional schedule-wide clock ratio.  A smaller ratio would need
both a tape-mass/propensity estimate and a step-indexed clock predicate; the
generic theorem accepts only one fixed predicate for the whole schedule. -/
def statePairTransferEpsilonBound : NNRat := 1

open Classical in
/-- Unconditional stochastic bound for the state-pair transfer network.
With ε = 1 the PMF complement at every reachable state is trivially ≤ 1
(probability measure), so no enabledness, zero-propensity, or clock
hypotheses are needed. -/
theorem scwb_rawLaw_concrete_bound
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) (cfg₀ : MicroCfg Q s)
    (n : Nat)
    (schedule : Fin n →
      (BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I) :
    (rawLaw
      (BimolecularFourPhaseRefinement.statePairTransferNetwork (s := s) M)
      (BimolecularFourPhaseRefinement.statePairTransferNetwork_hasPositiveRates
        (s := s) M)
      (FourPhaseEncoding.enc cfg₀))
      (⋃ k : Fin n,
        {ω | ω (k.val + 1) ≠ some (schedule k)}) ≤
      n * ENNReal.ofReal (statePairTransferEpsilonBound : Rat) := by
  classical
  apply MassAction.rawLaw_multistep_uniform_bound_reachable
  intro k z _hz
  exact MeasureTheory.prob_le_one.trans
    (by simp [statePairTransferEpsilonBound, ENNReal.ofReal_one])

end Ripple.sCRNUniversality.Stochastic

#print axioms Ripple.sCRNUniversality.Stochastic.scwb_rawLaw_concrete_bound
-- Expected: [propext, Classical.choice, Quot.sound]

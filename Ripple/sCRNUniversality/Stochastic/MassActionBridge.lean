/-
  Bridge from MassActionRaceLaw to ClockBoundedLaw.

  LIMITATION: The `hBound` hypothesis in `ClockBoundedLaw.ofMassAction` and
  the `hDominance` hypothesis in `stochastic_error_le_of_propensity_dominance`
  include `∀ omega, (L.path omega).state t = z` (deterministic state at time t).
  This is satisfiable only for deterministic CRNs (one enabled reaction per
  state). For combined comp+clock CRNs, use `rawLaw_multistep_uniform_bound`
  from `MassAction/UniformRaceBound.lean` instead.
-/
import Ripple.sCRNUniversality.Stochastic.CRNtoQMatrix
import Ripple.sCRNUniversality.Stochastic.ClockErrorModel

namespace Ripple.sCRNUniversality.Stochastic

universe u v w

variable {S : Type u} [Fintype S] [DecidableEq S]

section OfMassAction

variable {N : Network.{u, v} S} [DecidableEq N.I] {Omega : Type w}

/-- Construct a ClockBoundedLaw from a MassActionRaceLaw and a uniform
    bound on the propensity complement. The bound says: at every time step,
    for every enabled intended reaction at any deterministic state, the
    ENNReal race-bound value 1 − prop(intended)/total is at most ε.

    This is the central bridge: MassActionRaceLaw → ClockBoundedLaw. -/
noncomputable def ClockBoundedLaw.ofMassAction
    (L : MassActionRaceLaw N Omega)
    (hPos : N.hasPositiveRates)
    (microstepsPerStep : Nat)
    (ε : ENNReal)
    (hBound : ∀ (t : Nat) (intended : N.I) (z : State S),
        (∀ omega, (L.path omega).state t = z) →
        N.EnabledAt z intended →
        ENNReal.ofReal
          (1 - ((N.rxn intended).propensity z : Rat) /
               (N.totalPropensity z : Rat)) ≤ ε) :
    ClockBoundedLaw N Omega where
  prob := L.prob
  probAxioms := L.probAxioms
  path := L.path
  microstepsPerStep := microstepsPerStep
  perMicrostepError := ε
  microstepBound := fun step micro intended z hstate hEnabled =>
    le_trans (L.raceBound _ intended z hstate hEnabled hPos)
      (hBound _ intended z hstate hEnabled)

/-- The stochastic simulation error bound: given mass-action kinetics with
    per-microstep error at most ε ≤ δ/(4n), the n-step failure probability
    is at most δ.

    This is the SCWB paper's Theorem 3.2 (stochastic part), conditional
    on the existence of a MassActionRaceLaw. -/
theorem stochastic_error_le_of_massAction
    (L : MassActionRaceLaw N Omega)
    (hPos : N.hasPositiveRates)
    (nSteps : Nat) (δ ε : ENNReal)
    (hε : ε ≤ δ / (4 * nSteps : Nat))
    (hBound : ∀ (t : Nat) (intended : N.I) (z : State S),
        (∀ omega, (L.path omega).state t = z) →
        N.EnabledAt z intended →
        ENNReal.ofReal
          (1 - ((N.rxn intended).propensity z : Rat) /
               (N.totalPropensity z : Rat)) ≤ ε) :
    (ClockBoundedLaw.ofMassAction L hPos 4 ε hBound).nStepFailureBound nSteps ≤ δ :=
  ClockBoundedLaw.error_le_target _ rfl nSteps δ hε

/-- Propensity dominance implies the race-bound value is small.
    If the non-intended propensity sum is at most ε · totalPropensity,
    then the ENNReal race-bound value is at most ofReal(ε). -/
theorem raceBound_le_of_propensity_dominance
    (hPos : N.hasPositiveRates)
    {z : State S} {intended : N.I}
    (hNonTerm : ¬ N.Terminal z)
    (ε : NNRat)
    (hDom : (Finset.univ.erase intended).sum
        (fun j => (N.rxn j).propensity z) ≤
          ε * N.totalPropensity z) :
    ENNReal.ofReal
      (1 - ((N.rxn intended).propensity z : Rat) /
           (N.totalPropensity z : Rat)) ≤
      ENNReal.ofReal (ε : Rat) := by
  apply ENNReal.ofReal_le_ofReal
  suffices hRat : (1 : Rat) -
      ((N.rxn intended).propensity z : Rat) /
        (N.totalPropensity z : Rat) ≤ (ε : Rat) by
    exact_mod_cast hRat
  rw [raceBound_value_eq_complement (N := N)]
  rw [complement_jumpProbAt_coe hPos hNonTerm]
  have hTP_pos : (0 : Rat) < (N.totalPropensity z : Rat) :=
    by exact_mod_cast totalPropensity_pos_of_nonTerminal N hPos hNonTerm
  rw [div_le_iff₀ hTP_pos]
  have : ((Finset.univ.erase intended).sum
      (fun j => (N.rxn j).propensity z) : Rat) ≤
      (ε : Rat) * (N.totalPropensity z : Rat) := by
    exact_mod_cast hDom
  linarith

/-- Full stochastic error bound via propensity dominance.
    If at every microstep the non-intended propensity fraction is at most ε,
    and ε ≤ δ/(4n), then the n-step simulation error is at most δ. -/
theorem stochastic_error_le_of_propensity_dominance
    (L : MassActionRaceLaw N Omega)
    (hPos : N.hasPositiveRates)
    (nSteps : Nat) (δ : ENNReal) (ε : NNRat)
    (hε : ENNReal.ofReal (ε : Rat) ≤ δ / (4 * nSteps : Nat))
    (hDominance : ∀ (t : Nat) (intended : N.I) (z : State S),
        (∀ omega, (L.path omega).state t = z) →
        N.EnabledAt z intended →
        ¬ N.Terminal z →
        (Finset.univ.erase intended).sum
          (fun j => (N.rxn j).propensity z) ≤
            ε * N.totalPropensity z) :
    ∃ (CB : ClockBoundedLaw N Omega),
      CB.microstepsPerStep = 4 ∧
      CB.nStepFailureBound nSteps ≤ δ := by
  have hBound : ∀ (t : Nat) (intended : N.I) (z : State S),
      (∀ omega, (L.path omega).state t = z) →
      N.EnabledAt z intended →
      ENNReal.ofReal
        (1 - ((N.rxn intended).propensity z : Rat) /
             (N.totalPropensity z : Rat)) ≤
        ENNReal.ofReal (ε : Rat) := by
    intro t intended z hstate hEnabled
    by_cases hTerm : N.Terminal z
    · exact absurd hEnabled (hTerm intended)
    · exact raceBound_le_of_propensity_dominance hPos hTerm ε
        (hDominance t intended z hstate hEnabled hTerm)
  exact ⟨ClockBoundedLaw.ofMassAction L hPos 4 _ hBound,
    rfl, ClockBoundedLaw.error_le_target _ rfl nSteps δ hε⟩

end OfMassAction

end Ripple.sCRNUniversality.Stochastic

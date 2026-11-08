/-
  Propensity dominance bounds the race-bound value 1 - propensity/total.
  (The deterministic-state bridge from the race-law interface to a
  per-microstep clock error law was removed as a superseded route; the
  stochastic bounds use `rawLaw_multistep_uniform_bound` from
  `MassAction/UniformRaceBound.lean`.)
-/
import Ripple.sCRNUniversality.Stochastic.CRNtoQMatrix

namespace Ripple.sCRNUniversality.Stochastic

universe u v w

variable {S : Type u} [Fintype S] [DecidableEq S]

section OfMassAction

variable {N : Network.{u, v} S} [DecidableEq N.I] {Omega : Type w}

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

end OfMassAction

end Ripple.sCRNUniversality.Stochastic

/-
  LIMITATION: `multiStepRaceFailureBound` requires `hstates : ∀ k omega,
  (L.path omega).state (startTime + k) = states k` — deterministic state
  at all time steps. Unsatisfiable for t ≥ 1 in non-deterministic CRNs.
  For combined comp+clock CRNs, use `rawLaw_multistep_uniform_bound` from
  `MassAction/UniformRaceBound.lean` instead.
-/
import Ripple.sCRNUniversality.Stochastic.PropensityRace

namespace Ripple.sCRNUniversality

namespace Stochastic

universe u v w

variable {S : Type u} [Fintype S]
variable {N : Network.{u, v} S} {Omega : Type w}

noncomputable def multiStepRaceFailureBound
    (L : MassActionRaceLaw N Omega)
    (steps : List N.I) (startTime : Nat)
    (states : Fin steps.length → State S)
    (hstates : forall (k : Fin steps.length),
      forall omega, (L.path omega).state (startTime + k.val) = states k)
    (henabled : forall (k : Fin steps.length),
      N.EnabledAt (states k) (steps.get k))
    (hPos : N.hasPositiveRates) :
    Probability.EventBound L.prob where
  event := Probability.finUnion (Finset.univ : Finset (Fin steps.length))
    (fun k => notFiredEvent L.path (startTime + k.val) (steps.get k))
  bound := (Finset.univ : Finset (Fin steps.length)).sum
    (fun k => (L.oneStepRaceEventBound
      (startTime + k.val) (steps.get k) (states k)
      (hstates k) (henabled k) hPos).bound)
  prob_le := by
    exact le_trans
      (L.probAxioms.finUnion_le_sum
        (I := Fin steps.length)
        (Finset.univ : Finset (Fin steps.length))
        (fun k => notFiredEvent L.path (startTime + k.val) (steps.get k)))
      (Finset.sum_le_sum (fun k _ =>
        (L.oneStepRaceEventBound
          (startTime + k.val) (steps.get k) (states k)
          (hstates k) (henabled k) hPos).prob_le))

end Stochastic

end Ripple.sCRNUniversality

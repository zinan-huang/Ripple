import Ripple.sCRNUniversality.Stochastic.Propensity
import Ripple.sCRNUniversality.Stochastic.JumpPathLaw

namespace Ripple.sCRNUniversality

namespace Stochastic

universe u v w

def notFiredEvent {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
    (path : Omega → N.Path) (t : Nat) (i : N.I) : Probability.Event Omega :=
  fun omega => (path omega).fired t ≠ some i

structure MassActionRaceLaw {S : Type u} [Fintype S]
    (N : Network.{u, v} S) (Omega : Type w)
    extends JumpPathLaw N Omega where
  raceBound :
    forall (t : Nat) (i : N.I) (z : State S)
      (hstate : forall omega, (path omega).state t = z)
      (hEnabled : N.EnabledAt z i) (hPos : N.hasPositiveRates),
    prob.Pr (notFiredEvent path t i) ≤
      ENNReal.ofReal
        (1 - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat))

namespace MassActionRaceLaw

variable {S : Type u} [Fintype S]
variable {N : Network.{u, v} S} {Omega : Type w}

def toInitialLaw
    (L : MassActionRaceLaw N Omega)
    (z0 : State S) (hinitial : forall omega, (L.path omega).state 0 = z0) :
    InitialJumpPathLaw N z0 Omega where
  law := L.toJumpPathLaw
  initial := hinitial

noncomputable def oneStepRaceEventBound
    (L : MassActionRaceLaw N Omega) (t : Nat) (i : N.I)
    (z : State S) (hstate : forall omega, (L.path omega).state t = z)
    (hEnabled : N.EnabledAt z i) (hPos : N.hasPositiveRates) :
    Probability.EventBound L.prob where
  event := notFiredEvent L.path t i
  bound := ENNReal.ofReal
    (1 - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat))
  prob_le := L.raceBound t i z hstate hEnabled hPos

end MassActionRaceLaw

end Stochastic

end Ripple.sCRNUniversality

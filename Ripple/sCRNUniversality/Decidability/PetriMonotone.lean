/-
  Petri net monotonicity for backward coverability.

  Key theorem: if m fires transition i reaching m', and m ≤ w (i.e., Covers w m),
  then w can also fire i, reaching some w' with m' ≤ w' (i.e., Covers w' m').

  This is already proved in Petri.lean as `PetriNet.StepAt.lift_covers` and at
  the Reaction level as `Reaction.FiresTo.lift_covers`. This module re-exports
  and extends those results with additional monotonicity lemmas needed by the
  backward coverability algorithm.
-/
import Ripple.sCRNUniversality.Core.Petri

namespace Ripple.sCRNUniversality.Decidability

open Ripple.sCRNUniversality

variable {S : Type*}

-- ══════════════════════════════════════════════════════════════════
-- Core monotonicity: single step
-- ══════════════════════════════════════════════════════════════════

/-- If m fires reaction i reaching m', and w covers m, then w fires i
    reaching some w' that covers m'. -/
theorem petri_step_monotone {P : PetriNet S} {i : P.I} {m m' w : State S}
    (hStep : P.StepAt i m m') (hle : Covers w m) :
    ∃ w', P.StepAt i w w' ∧ Covers w' m' :=
  PetriNet.StepAt.lift_covers hStep hle

/-- Equivalent formulation using the Network type. -/
theorem network_step_monotone {N : Network S} {i : N.I} {m m' w : State S}
    (hStep : N.StepAt i m m') (hle : Covers w m) :
    ∃ w', N.StepAt i w w' ∧ Covers w' m' :=
  Network.StepAt.lift_covers hStep hle

-- ══════════════════════════════════════════════════════════════════
-- Monotonicity for execution traces
-- ══════════════════════════════════════════════════════════════════

/-- If an execution from m reaches m', and w covers m, then the same
    sequence of transitions fires from w reaching some w' covering m'. -/
theorem petri_exec_monotone {P : PetriNet S} {m m' w : State S}
    {is : List P.I}
    (hExec : P.Exec m m' is) (hle : Covers w m) :
    ∃ w', P.Exec w w' is ∧ Covers w' m' :=
  PetriNet.Exec.lift_covers hExec hle

theorem network_exec_monotone {N : Network S} {m m' w : State S}
    {is : List N.I}
    (hExec : N.Exec m m' is) (hle : Covers w m) :
    ∃ w', N.Exec w w' is ∧ Covers w' m' :=
  Network.Exec.lift_covers hExec hle

-- ══════════════════════════════════════════════════════════════════
-- Monotonicity for reachability
-- ══════════════════════════════════════════════════════════════════

/-- If m reaches m', and w covers m, then w reaches some w' covering m'. -/
theorem petri_reaches_monotone {P : PetriNet S} {m m' w : State S}
    (hReach : P.Reaches m m') (hle : Covers w m) :
    ∃ w', P.Reaches w w' ∧ Covers w' m' :=
  PetriNet.Reaches.lift_covers hReach hle

theorem network_reaches_monotone {N : Network S} {m m' w : State S}
    (hReach : N.Reaches m m') (hle : Covers w m) :
    ∃ w', N.Reaches w w' ∧ Covers w' m' :=
  Network.Reaches.lift_covers hReach hle

-- ══════════════════════════════════════════════════════════════════
-- Monotonicity for coverability
-- ══════════════════════════════════════════════════════════════════

/-- If target is coverable from m, and w covers m, then target is
    coverable from w. -/
theorem petri_coverable_monotone {P : PetriNet S} {m target w : State S}
    (hCov : P.CoverableFrom m target) (hle : Covers w m) :
    P.CoverableFrom w target :=
  PetriNet.coverable_lift_initial hle hCov

theorem network_coverable_monotone {N : Network S} {m target w : State S}
    (hCov : N.CoverableFrom m target) (hle : Covers w m) :
    N.CoverableFrom w target :=
  Network.coverable_lift_initial hle hCov

-- ══════════════════════════════════════════════════════════════════
-- Upward closure of coverable set
-- ══════════════════════════════════════════════════════════════════

/-- The set of states from which a target is coverable is upward-closed. -/
theorem petri_coverableFrom_upwardClosed (P : PetriNet S) (target : State S) :
    ∀ m w, P.CoverableFrom m target → Covers w m → P.CoverableFrom w target :=
  fun _ _ hCov hle => petri_coverable_monotone hCov hle

theorem network_coverableFrom_upwardClosed (N : Network S) (target : State S) :
    ∀ m w, N.CoverableFrom m target → Covers w m → N.CoverableFrom w target :=
  fun _ _ hCov hle => network_coverable_monotone hCov hle

-- ══════════════════════════════════════════════════════════════════
-- Enabled monotonicity (explicit, for convenience)
-- ══════════════════════════════════════════════════════════════════

/-- If a transition is enabled at m, and w covers m, then it is enabled at w. -/
theorem petri_enabled_monotone {P : PetriNet S} {i : P.I} {m w : State S}
    (hEnabled : P.enabled i m) (hle : Covers w m) :
    P.enabled i w :=
  PetriNet.enabled_of_covers hEnabled hle

theorem network_enabled_monotone {N : Network S} {i : N.I} {m w : State S}
    (hEnabled : (N.rxn i).enabled m) (hle : Covers w m) :
    (N.rxn i).enabled w :=
  Reaction.enabled_of_covers hEnabled hle

-- ══════════════════════════════════════════════════════════════════
-- Fire monotonicity (the output is also monotone in the input)
-- ══════════════════════════════════════════════════════════════════

/-- Firing the same transition from a larger state produces a larger result. -/
theorem petri_fire_monotone {P : PetriNet S} {i : P.I} {m w : State S}
    (hle : Covers w m) :
    Covers (P.fire i w) (P.fire i m) :=
  PetriNet.fire_covers_fire_of_covers hle

theorem reaction_fire_monotone {rho : Reaction S} {m w : State S}
    (hle : Covers w m) :
    Covers (rho.fire w) (rho.fire m) :=
  Reaction.fire_covers_fire_of_covers hle

end Ripple.sCRNUniversality.Decidability

import Ripple.sCRNUniversality.Core.Finite
import Ripple.sCRNUniversality.Core.Schedule
import Ripple.sCRNUniversality.Computation.CRNRefinement

namespace Ripple.sCRNUniversality

universe u v w x

structure BimolecularNetworkRefinement
    {S : Type u} [Fintype S]
    {T : Type v} [Fintype T]
    (Nagg : Network.{u, w} S)
    (Ncon : Network.{v, x} T) where
  enc : State S -> State T
  GoodStepAt : Nagg.I -> State S -> State S -> Prop
  goodStepAt_stepAt :
    forall {i : Nagg.I} {z z' : State S},
      GoodStepAt i z z' -> Nagg.StepAt i z z'
  concrete_allAtMostBimolecularInput : Ncon.allAtMostBimolecularInput
  concrete_hasPositiveRates : Ncon.hasPositiveRates
  stepAt_exec :
    forall {i : Nagg.I} {z z' : State S},
      GoodStepAt i z z' ->
        exists js : List Ncon.I,
          Ncon.Exec (enc z) (enc z') js

/--
Alias emphasizing the two important limitations of
`BimolecularNetworkRefinement`: the concrete network is only required to be
at most bimolecular on inputs, and transport is forward-only for
`GoodStepAt` / `GoodExec`.
-/
abbrev AtMostBimolecularForwardRefinement
    {S : Type u} [Fintype S]
    {T : Type v} [Fintype T]
    (Nagg : Network.{u, w} S)
    (Ncon : Network.{v, x} T) :=
  BimolecularNetworkRefinement Nagg Ncon

namespace BimolecularNetworkRefinement

variable {S : Type u} [Fintype S]
variable {T : Type v} [Fintype T]
variable {Nagg : Network.{u, w} S}
variable {Ncon : Network.{v, x} T}

def GoodExec (R : BimolecularNetworkRefinement Nagg Ncon) :
    State S -> State S -> List Nagg.I -> Prop :=
  ExecOf R.GoodStepAt

def GoodReaches (R : BimolecularNetworkRefinement Nagg Ncon)
    (z z' : State S) : Prop :=
  exists is : List Nagg.I, R.GoodExec z z' is

theorem goodReaches_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    R.GoodReaches z z' :=
  ⟨is, hExec⟩

def GoodCoverableFrom (R : BimolecularNetworkRefinement Nagg Ncon)
    (z0 target : State S) : Prop :=
  exists z, R.GoodReaches z0 z /\ Covers z target

theorem aggregate_exec_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Nagg.Exec z z' is := by
  induction hExec with
  | nil z =>
      exact ExecOf.nil z
  | cons hStep _tail ih =>
      exact ExecOf.cons (R.goodStepAt_stepAt hStep) ih

theorem aggregate_reaches_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Nagg.Reaches z z' := by
  rcases hReach with ⟨is, hExec⟩
  exact ⟨is, R.aggregate_exec_of_goodExec hExec⟩

theorem goodCoverableFrom_of_goodReaches_covers
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 z target : State S}
    (hReach : R.GoodReaches z0 z)
    (hCovers : Covers z target) :
    R.GoodCoverableFrom z0 target :=
  ⟨z, hReach, hCovers⟩

theorem aggregate_coverableFrom_of_goodReaches_covers
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' target : State S}
    (hReach : R.GoodReaches z z')
    (hCovers : Covers z' target) :
    Nagg.CoverableFrom z target :=
  Network.coverable_of_reaches_of_covers
    (R.aggregate_reaches_of_goodReaches hReach)
    hCovers

theorem aggregate_coverableFrom_of_goodCoverableFrom
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S}
    (hCoverable : R.GoodCoverableFrom z0 target) :
    Nagg.CoverableFrom z0 target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact Network.coverable_of_reaches_of_covers
    (R.aggregate_reaches_of_goodReaches hReach)
    hCovers

theorem aggregate_speciesCoverableFrom_of_goodCoverableFrom_to_coord
    [DecidableEq S]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {species : S} {amount : Nat}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> amount <= z species) :
    Nagg.SpeciesCoverableFrom z0 species amount := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact Network.speciesCoverableFrom_of_reaches_coord
    (R.aggregate_reaches_of_goodReaches hReach)
    (hTarget hCovers)

theorem aggregate_speciesCoverableFrom_one_of_goodCoverableFrom_to_pos
    [DecidableEq S]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {species : S}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> 0 < z species) :
    Nagg.SpeciesCoverableFrom z0 species := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact Network.speciesCoverableFrom_one_of_reaches_pos
    (R.aggregate_reaches_of_goodReaches hReach)
    (hTarget hCovers)

def aggregateIntendedSchedule_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Nagg.IntendedSchedule z z' :=
  Network.IntendedSchedule.of_exec
    (R.aggregate_exec_of_goodExec hExec)

@[simp]
theorem aggregateIntendedSchedule_of_goodExec_schedule
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    (R.aggregateIntendedSchedule_of_goodExec hExec).schedule = is := by
  rfl

noncomputable def aggregateIntendedSchedule_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Nagg.IntendedSchedule z z' :=
  R.aggregateIntendedSchedule_of_goodExec
    (Classical.choose_spec hReach)

@[simp]
theorem aggregateIntendedSchedule_of_goodReaches_schedule
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    (R.aggregateIntendedSchedule_of_goodReaches hReach).schedule =
      Classical.choose hReach := by
  rfl

theorem exec_of_aggregateIntendedSchedule_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Nagg.Exec z z'
      (R.aggregateIntendedSchedule_of_goodExec hExec).schedule :=
  (R.aggregateIntendedSchedule_of_goodExec hExec).exec

theorem goodExec_of_aggregateIntendedSchedule_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    R.GoodExec z z'
      (R.aggregateIntendedSchedule_of_goodExec hExec).schedule := by
  simpa using hExec

theorem aggregateIntendedSchedule_reaches_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Nagg.Reaches z z' :=
  (R.aggregateIntendedSchedule_of_goodExec hExec).reaches

theorem exec_of_aggregateIntendedSchedule_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Nagg.Exec z z'
      (R.aggregateIntendedSchedule_of_goodReaches hReach).schedule :=
  (R.aggregateIntendedSchedule_of_goodReaches hReach).exec

theorem goodExec_of_aggregateIntendedSchedule_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    R.GoodExec z z'
      (R.aggregateIntendedSchedule_of_goodReaches hReach).schedule := by
  simpa using Classical.choose_spec hReach

theorem aggregateIntendedSchedule_reaches_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Nagg.Reaches z z' :=
  (R.aggregateIntendedSchedule_of_goodReaches hReach).reaches

theorem state_after_goodExec_of_aggregateIntendedWinsRaceAt
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    {path : Nagg.Path} {Bad : Nagg.BadIndexSet} {t : Nat}
    (hExec : R.GoodExec z z' is)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.aggregateIntendedSchedule_of_goodExec hExec)) :
    path.state
        (t +
          (R.aggregateIntendedSchedule_of_goodExec hExec).firingCount) =
      z' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.aggregateIntendedSchedule_of_goodExec hExec)
      hwin

theorem state_after_goodReaches_of_aggregateIntendedWinsRaceAt
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    {path : Nagg.Path} {Bad : Nagg.BadIndexSet} {t : Nat}
    (hReach : R.GoodReaches z z')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.aggregateIntendedSchedule_of_goodReaches hReach)) :
    path.state
        (t +
          (R.aggregateIntendedSchedule_of_goodReaches hReach).firingCount) =
      z' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.aggregateIntendedSchedule_of_goodReaches hReach)
      hwin

theorem exec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    exists js : List Ncon.I,
      Ncon.Exec (R.enc z) (R.enc z') js := by
  induction hExec with
  | nil z =>
      exact ⟨[], ExecOf.nil (R.enc z)⟩
  | cons hStep _tail ih =>
      rcases R.stepAt_exec hStep with ⟨js1, hExec1⟩
      rcases ih with ⟨js2, hExec2⟩
      exact ⟨js1 ++ js2, ExecOf.append hExec1 hExec2⟩

noncomputable def concreteIntendedSchedule_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Ncon.IntendedSchedule (R.enc z) (R.enc z') where
  schedule := Classical.choose (R.exec hExec)
  exec := Classical.choose_spec (R.exec hExec)

theorem exec_of_concreteIntendedSchedule_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Ncon.Exec (R.enc z) (R.enc z')
      (R.concreteIntendedSchedule_of_goodExec hExec).schedule :=
  (R.concreteIntendedSchedule_of_goodExec hExec).exec

theorem concreteIntendedSchedule_reaches_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Ncon.Reaches (R.enc z) (R.enc z') :=
  (R.concreteIntendedSchedule_of_goodExec hExec).reaches

noncomputable def concreteIntendedSchedule_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Ncon.IntendedSchedule (R.enc z) (R.enc z') :=
  R.concreteIntendedSchedule_of_goodExec
    (Classical.choose_spec hReach)

theorem exec_of_concreteIntendedSchedule_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Ncon.Exec (R.enc z) (R.enc z')
      (R.concreteIntendedSchedule_of_goodReaches hReach).schedule :=
  (R.concreteIntendedSchedule_of_goodReaches hReach).exec

theorem concreteIntendedSchedule_reaches_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Ncon.Reaches (R.enc z) (R.enc z') :=
  (R.concreteIntendedSchedule_of_goodReaches hReach).reaches

theorem state_after_goodExec_of_concreteIntendedWinsRaceAt
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    {path : Ncon.Path} {Bad : Ncon.BadIndexSet} {t : Nat}
    (hExec : R.GoodExec z z' is)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.concreteIntendedSchedule_of_goodExec hExec)) :
    path.state
        (t +
          (R.concreteIntendedSchedule_of_goodExec hExec).firingCount) =
      R.enc z' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.concreteIntendedSchedule_of_goodExec hExec)
      hwin

theorem state_after_goodReaches_of_concreteIntendedWinsRaceAt
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    {path : Ncon.Path} {Bad : Ncon.BadIndexSet} {t : Nat}
    (hReach : R.GoodReaches z z')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.concreteIntendedSchedule_of_goodReaches hReach)) :
    path.state
        (t +
          (R.concreteIntendedSchedule_of_goodReaches hReach).firingCount) =
      R.enc z' := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.concreteIntendedSchedule_of_goodReaches hReach)
      hwin

theorem reaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Ncon.Reaches (R.enc z) (R.enc z') := by
  rcases hReach with ⟨is, hExec⟩
  rcases R.exec hExec with ⟨js, hExec'⟩
  exact ⟨js, hExec'⟩

theorem coverableFrom_of_goodReaches_covers
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {target : State T}
    (hReach : R.GoodReaches z z')
    (hCovers : Covers (R.enc z') target) :
    Ncon.CoverableFrom (R.enc z) target :=
  Network.coverable_of_reaches_of_covers
    (R.reaches hReach)
    hCovers

theorem coverableFrom_of_goodReaches_of_le
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {target : State T}
    (hReach : R.GoodReaches z z')
    (hTarget : forall t, target t <= R.enc z' t) :
    Ncon.CoverableFrom (R.enc z) target :=
  R.coverableFrom_of_goodReaches_covers hReach hTarget

theorem speciesCoverableFrom_of_goodReaches_coord
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {species : T} {amount : Nat}
    (hReach : R.GoodReaches z z')
    (hamount : amount <= R.enc z' species) :
    Ncon.SpeciesCoverableFrom (R.enc z) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (R.reaches hReach)
    hamount

theorem speciesCoverableFrom_one_of_goodReaches_pos
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {species : T}
    (hReach : R.GoodReaches z z')
    (hpos : 0 < R.enc z' species) :
    Ncon.SpeciesCoverableFrom (R.enc z) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (R.reaches hReach)
    hpos

theorem coverableFrom_of_goodCoverableFrom_to_target
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {targetT : State T}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> Covers (R.enc z) targetT) :
    Ncon.CoverableFrom (R.enc z0) targetT := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact ⟨R.enc z, R.reaches hReach, hTarget hCovers⟩

theorem exists_concreteIntendedSchedule_of_goodCoverableFrom_to_target
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {targetT : State T}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> Covers (R.enc z) targetT) :
    exists z : State S,
      Nonempty (Ncon.IntendedSchedule (R.enc z0) (R.enc z)) /\
        Covers (R.enc z) targetT := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact ⟨z, ⟨R.concreteIntendedSchedule_of_goodReaches hReach⟩,
    hTarget hCovers⟩

theorem speciesCoverableFrom_of_goodCoverableFrom_to_coord
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {species : T} {amount : Nat}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> amount <= R.enc z species) :
    Ncon.SpeciesCoverableFrom (R.enc z0) species amount := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact R.speciesCoverableFrom_of_goodReaches_coord
    hReach
    (hTarget hCovers)

theorem speciesCoverableFrom_one_of_goodCoverableFrom_to_pos
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {species : T}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> 0 < R.enc z species) :
    Ncon.SpeciesCoverableFrom (R.enc z0) species := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact R.speciesCoverableFrom_one_of_goodReaches_pos
    hReach
    (hTarget hCovers)

/--
Forward transport of a good aggregate execution to a concrete execution.

This is a wrapper for `exec`; it does not assert that every aggregate execution
is good.
-/
theorem forward_exec_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    exists js : List Ncon.I,
      Ncon.Exec (R.enc z) (R.enc z') js :=
  R.exec hExec

/--
Forward transport of a good aggregate reachability witness.

This is a wrapper for `reaches`; it does not assert stochastic reachability or
fairness.
-/
theorem forward_reaches_of_goodReaches
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S}
    (hReach : R.GoodReaches z z') :
    Ncon.Reaches (R.enc z) (R.enc z') :=
  R.reaches hReach

/--
The good aggregate execution is also an ordinary aggregate execution.
Useful when separating intended aggregate schedules from raw reachability.
-/
theorem aggregate_forward_exec_of_goodExec
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {is : List Nagg.I}
    (hExec : R.GoodExec z z' is) :
    Nagg.Exec z z' is :=
  R.aggregate_exec_of_goodExec hExec

/--
Forward coverability transport from a good aggregate coverability witness.

This wrapper name keeps the `GoodCoverableFrom` hypothesis visible.
-/
theorem forward_coverableFrom_of_goodCoverableFrom_to_target
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {targetT : State T}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> Covers (R.enc z) targetT) :
    Ncon.CoverableFrom (R.enc z0) targetT :=
  R.coverableFrom_of_goodCoverableFrom_to_target hCoverable hTarget

theorem forward_speciesCoverableFrom_of_goodCoverableFrom_to_coord
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {species : T} {amount : Nat}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> amount <= R.enc z species) :
    Ncon.SpeciesCoverableFrom (R.enc z0) species amount :=
  R.speciesCoverableFrom_of_goodCoverableFrom_to_coord
    hCoverable
    hTarget

theorem forward_speciesCoverableFrom_one_of_goodCoverableFrom_to_pos
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S} {species : T}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hTarget :
      forall {z : State S}, Covers z target -> 0 < R.enc z species) :
    Ncon.SpeciesCoverableFrom (R.enc z0) species :=
  R.speciesCoverableFrom_one_of_goodCoverableFrom_to_pos
    hCoverable
    hTarget

/--
Forward coverability transport from a good aggregate reachability witness and a
concrete target-cover proof.
-/
theorem forward_coverableFrom_of_goodReaches_covers
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {target : State T}
    (hReach : R.GoodReaches z z')
    (hCovers : Covers (R.enc z') target) :
    Ncon.CoverableFrom (R.enc z) target :=
  R.coverableFrom_of_goodReaches_covers hReach hCovers

theorem forward_coverableFrom_of_goodReaches_of_le
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {target : State T}
    (hReach : R.GoodReaches z z')
    (hTarget : forall t, target t <= R.enc z' t) :
    Ncon.CoverableFrom (R.enc z) target :=
  R.coverableFrom_of_goodReaches_of_le hReach hTarget

theorem forward_speciesCoverableFrom_of_goodReaches_coord
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {species : T} {amount : Nat}
    (hReach : R.GoodReaches z z')
    (hamount : amount <= R.enc z' species) :
    Ncon.SpeciesCoverableFrom (R.enc z) species amount :=
  R.speciesCoverableFrom_of_goodReaches_coord hReach hamount

theorem forward_speciesCoverableFrom_one_of_goodReaches_pos
    [DecidableEq T]
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z z' : State S} {species : T}
    (hReach : R.GoodReaches z z')
    (hpos : 0 < R.enc z' species) :
    Ncon.SpeciesCoverableFrom (R.enc z) species :=
  R.speciesCoverableFrom_one_of_goodReaches_pos hReach hpos

theorem coverableFrom_encoded_target_of_goodCoverableFrom
    (R : BimolecularNetworkRefinement Nagg Ncon)
    {z0 target : State S}
    (hCoverable : R.GoodCoverableFrom z0 target)
    (hEncCovers :
      forall {z target : State S},
        Covers z target -> Covers (R.enc z) (R.enc target)) :
    Ncon.CoverableFrom (R.enc z0) (R.enc target) :=
  R.coverableFrom_of_goodCoverableFrom_to_target
    hCoverable
    (fun h => hEncCovers h)

def ofRawNetwork
    (enc : State S -> State T)
    (hBimol : Ncon.allAtMostBimolecularInput)
    (hRates : Ncon.hasPositiveRates)
    (hStep :
      forall {i : Nagg.I} {z z' : State S},
        Nagg.StepAt i z z' ->
          exists js : List Ncon.I,
            Ncon.Exec (enc z) (enc z') js) :
    BimolecularNetworkRefinement Nagg Ncon where
  enc := enc
  GoodStepAt := fun i z z' => Nagg.StepAt i z z'
  goodStepAt_stepAt := by
    intro _i _z _z' hStep
    exact hStep
  concrete_allAtMostBimolecularInput := hBimol
  concrete_hasPositiveRates := hRates
  stepAt_exec := by
    intro _i _z _z' hGood
    exact hStep hGood

def ofRawNetwork_of_allBimolecularInput
    (enc : State S -> State T)
    (hBimol : Ncon.allBimolecularInput)
    (hRates : Ncon.hasPositiveRates)
    (hStep :
      forall {i : Nagg.I} {z z' : State S},
        Nagg.StepAt i z z' ->
          exists js : List Ncon.I,
            Ncon.Exec (enc z) (enc z') js) :
    BimolecularNetworkRefinement Nagg Ncon :=
  ofRawNetwork enc
    (Network.allAtMostBimolecularInput_of_allBimolecularInput hBimol)
    hRates
    hStep

end BimolecularNetworkRefinement

structure UniformRateBimolecularNetworkRefinement
    {S : Type u} [Fintype S]
    {T : Type v} [Fintype T]
    (Nagg : Network.{u, w} S)
    (Ncon : Network.{v, x} T)
    extends BimolecularNetworkRefinement Nagg Ncon where
  concrete_allUnitRate : Ncon.allUnitRate
  concrete_equalRates : Ncon.equalRates

/--
Alias emphasizing that the additional rate fields are static unit/equal-rate
predicates, not stochastic race or timing claims.
-/
abbrev AtMostBimolecularUnitRateForwardRefinement
    {S : Type u} [Fintype S]
    {T : Type v} [Fintype T]
    (Nagg : Network.{u, w} S)
    (Ncon : Network.{v, x} T) :=
  UniformRateBimolecularNetworkRefinement Nagg Ncon

structure FullBimolecularNetworkRefinement
    {S : Type u} [Fintype S]
    {T : Type v} [Fintype T]
    (Nagg : Network.{u, w} S)
    (Ncon : Network.{v, x} T)
    extends BimolecularNetworkRefinement Nagg Ncon where
  concrete_allAtMostBimolecularFull :
    Ncon.allAtMostBimolecularFull

namespace FullBimolecularNetworkRefinement

variable {S : Type u} [Fintype S]
variable {T : Type v} [Fintype T]
variable {Nagg : Network.{u, w} S}
variable {Ncon : Network.{v, x} T}

theorem concrete_allAtMostBimolecularInput'
    (R : FullBimolecularNetworkRefinement Nagg Ncon) :
    Ncon.allAtMostBimolecularInput :=
  Network.allAtMostBimolecularInput_of_full
    R.concrete_allAtMostBimolecularFull

theorem concrete_allAtMostBimolecularOutput
    (R : FullBimolecularNetworkRefinement Nagg Ncon) :
    Ncon.allAtMostBimolecularOutput :=
  Network.allAtMostBimolecularOutput_of_full
    R.concrete_allAtMostBimolecularFull

end FullBimolecularNetworkRefinement

end Ripple.sCRNUniversality

import Ripple.sCRNUniversality.Computation.CRNRefinement
import Ripple.sCRNUniversality.Core.Schedule

namespace Ripple.sCRNUniversality

universe u v w x

namespace NetworkRefinement

variable {S : Type u} {T : Type v}
variable {Nhi : Network.{u, w} S}
variable {Nlo : Network.{v, x} T}

/--
Package the low-level deterministic schedule chosen by a network refinement
for a supplied high-level execution.

This is a forward execution witness only; it does not state scheduler safety
or stochastic reachability.
-/
noncomputable def concreteIntendedSchedule_of_exec
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    Nlo.IntendedSchedule (R.enc a) (R.enc b) where
  schedule := Classical.choose (R.exec hExec)
  exec := Classical.choose_spec (R.exec hExec)

theorem exec_of_concreteIntendedSchedule_of_exec
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    Nlo.Exec (R.enc a) (R.enc b)
      (R.concreteIntendedSchedule_of_exec hExec).schedule :=
  (R.concreteIntendedSchedule_of_exec hExec).exec

theorem concreteIntendedSchedule_reaches_of_exec
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    Nlo.Reaches (R.enc a) (R.enc b) :=
  (R.concreteIntendedSchedule_of_exec hExec).reaches

theorem concrete_coverableFrom_of_exec_covers
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I} {target : State T}
    (hExec : Nhi.Exec a b is)
    (hCovers : Covers (R.enc b) target) :
    Nlo.CoverableFrom (R.enc a) target :=
  Network.coverable_of_reaches_of_covers
    (R.concreteIntendedSchedule_of_exec hExec).reaches
    hCovers

theorem concrete_coverableFrom_of_exec_of_le
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I} {target : State T}
    (hExec : Nhi.Exec a b is)
    (hTarget : forall t, target t <= R.enc b t) :
    Nlo.CoverableFrom (R.enc a) target :=
  R.concrete_coverableFrom_of_exec_covers hExec hTarget

theorem concrete_speciesCoverableFrom_of_exec_coord
    [DecidableEq T]
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    {species : T} {amount : Nat}
    (hExec : Nhi.Exec a b is)
    (hamount : amount <= R.enc b species) :
    Nlo.SpeciesCoverableFrom (R.enc a) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (R.concreteIntendedSchedule_of_exec hExec).reaches
    hamount

theorem concrete_speciesCoverableFrom_one_of_exec_pos
    [DecidableEq T]
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I} {species : T}
    (hExec : Nhi.Exec a b is)
    (hpos : 0 < R.enc b species) :
    Nlo.SpeciesCoverableFrom (R.enc a) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (R.concreteIntendedSchedule_of_exec hExec).reaches
    hpos

theorem state_after_exec_of_concreteIntendedWinsRaceAt
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    {path : Nlo.Path} {Bad : Nlo.BadIndexSet} {t : Nat}
    (hExec : Nhi.Exec a b is)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.concreteIntendedSchedule_of_exec hExec)) :
    path.state
        (t + (R.concreteIntendedSchedule_of_exec hExec).firingCount) =
      R.enc b := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.concreteIntendedSchedule_of_exec hExec)
      hwin

noncomputable def concreteIntendedSchedule_of_reaches
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nlo.IntendedSchedule (R.enc a) (R.enc b) :=
  R.concreteIntendedSchedule_of_exec (Classical.choose_spec hReach)

theorem exec_of_concreteIntendedSchedule_of_reaches
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nlo.Exec (R.enc a) (R.enc b)
      (R.concreteIntendedSchedule_of_reaches hReach).schedule :=
  (R.concreteIntendedSchedule_of_reaches hReach).exec

theorem concreteIntendedSchedule_reaches_of_reaches
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nlo.Reaches (R.enc a) (R.enc b) :=
  (R.concreteIntendedSchedule_of_reaches hReach).reaches

theorem state_after_reaches_of_concreteIntendedWinsRaceAt
    (R : NetworkRefinement Nhi Nlo)
    {a b : State S}
    {path : Nlo.Path} {Bad : Nlo.BadIndexSet} {t : Nat}
    (hReach : Nhi.Reaches a b)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.concreteIntendedSchedule_of_reaches hReach)) :
    path.state
        (t + (R.concreteIntendedSchedule_of_reaches hReach).firingCount) =
      R.enc b := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.concreteIntendedSchedule_of_reaches hReach)
      hwin

end NetworkRefinement

namespace BoundedNetworkRefinement

variable {S : Type u} {T : Type v}
variable {Nhi : Network.{u, w} S}
variable {Nlo : Network.{v, x} T}

/--
Package the bounded low-level deterministic schedule chosen by a bounded
network refinement for a supplied high-level execution.
-/
noncomputable def boundedConcreteIntendedSchedule_of_exec
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    Nlo.BoundedIntendedSchedule
      (R.step_len_bound * is.length) (R.enc a) (R.enc b) where
  schedule := Classical.choose (R.exec_bounded hExec)
  exec := (Classical.choose_spec (R.exec_bounded hExec)).1
  length_bound := (Classical.choose_spec (R.exec_bounded hExec)).2

theorem exec_of_boundedConcreteIntendedSchedule_of_exec
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    Nlo.Exec (R.enc a) (R.enc b)
      (R.boundedConcreteIntendedSchedule_of_exec hExec).schedule :=
  (R.boundedConcreteIntendedSchedule_of_exec hExec).exec

theorem boundedConcreteIntendedSchedule_firingCount_le_of_exec
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    (R.boundedConcreteIntendedSchedule_of_exec hExec).firingCount <=
      R.step_len_bound * is.length :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (R.boundedConcreteIntendedSchedule_of_exec hExec)

theorem boundedConcreteIntended_reaches_of_exec
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    Nlo.Reaches (R.enc a) (R.enc b) :=
  (R.boundedConcreteIntendedSchedule_of_exec hExec).reaches

theorem boundedConcrete_coverableFrom_of_exec_covers
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I} {target : State T}
    (hExec : Nhi.Exec a b is)
    (hCovers : Covers (R.enc b) target) :
    Nlo.CoverableFrom (R.enc a) target :=
  Network.coverable_of_reaches_of_covers
    (R.boundedConcreteIntendedSchedule_of_exec hExec).reaches
    hCovers

theorem boundedConcrete_coverableFrom_of_exec_of_le
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I} {target : State T}
    (hExec : Nhi.Exec a b is)
    (hTarget : forall t, target t <= R.enc b t) :
    Nlo.CoverableFrom (R.enc a) target :=
  R.boundedConcrete_coverableFrom_of_exec_covers hExec hTarget

theorem boundedConcrete_speciesCoverableFrom_of_exec_coord
    [DecidableEq T]
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    {species : T} {amount : Nat}
    (hExec : Nhi.Exec a b is)
    (hamount : amount <= R.enc b species) :
    Nlo.SpeciesCoverableFrom (R.enc a) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (R.boundedConcreteIntendedSchedule_of_exec hExec).reaches
    hamount

theorem boundedConcrete_speciesCoverableFrom_one_of_exec_pos
    [DecidableEq T]
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I} {species : T}
    (hExec : Nhi.Exec a b is)
    (hpos : 0 < R.enc b species) :
    Nlo.SpeciesCoverableFrom (R.enc a) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (R.boundedConcreteIntendedSchedule_of_exec hExec).reaches
    hpos

theorem state_after_exec_of_boundedConcreteIntendedWinsRaceAt
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S} {is : List Nhi.I}
    {path : Nlo.Path} {Bad : Nlo.BadIndexSet} {t : Nat}
    (hExec : Nhi.Exec a b is)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.boundedConcreteIntendedSchedule_of_exec hExec).toIntendedSchedule) :
    path.state
        (t +
          (R.boundedConcreteIntendedSchedule_of_exec hExec).firingCount) =
      R.enc b :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (R.boundedConcreteIntendedSchedule_of_exec hExec)
    hwin

noncomputable def boundedConcreteIntendedSchedule_of_reaches
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nlo.BoundedIntendedSchedule
      (R.step_len_bound * (Classical.choose hReach).length)
      (R.enc a) (R.enc b) :=
  R.boundedConcreteIntendedSchedule_of_exec (Classical.choose_spec hReach)

theorem exec_of_boundedConcreteIntendedSchedule_of_reaches
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nlo.Exec (R.enc a) (R.enc b)
      (R.boundedConcreteIntendedSchedule_of_reaches hReach).schedule :=
  (R.boundedConcreteIntendedSchedule_of_reaches hReach).exec

theorem boundedConcreteIntendedSchedule_firingCount_le_of_reaches
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    (R.boundedConcreteIntendedSchedule_of_reaches hReach).firingCount <=
      R.step_len_bound * (Classical.choose hReach).length :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (R.boundedConcreteIntendedSchedule_of_reaches hReach)

theorem boundedConcreteIntended_reaches_of_reaches
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nlo.Reaches (R.enc a) (R.enc b) :=
  (R.boundedConcreteIntendedSchedule_of_reaches hReach).reaches

theorem state_after_reaches_of_boundedConcreteIntendedWinsRaceAt
    (R : BoundedNetworkRefinement Nhi Nlo)
    {a b : State S}
    {path : Nlo.Path} {Bad : Nlo.BadIndexSet} {t : Nat}
    (hReach : Nhi.Reaches a b)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.boundedConcreteIntendedSchedule_of_reaches hReach).toIntendedSchedule) :
    path.state
        (t +
          (R.boundedConcreteIntendedSchedule_of_reaches hReach).firingCount) =
      R.enc b :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (R.boundedConcreteIntendedSchedule_of_reaches hReach)
    hwin

end BoundedNetworkRefinement

end Ripple.sCRNUniversality

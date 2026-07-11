import Ripple.sCRNUniversality.Core.Schedule
import Ripple.sCRNUniversality.Probability.Contracts

namespace Ripple.sCRNUniversality

namespace Stochastic

universe u v w

structure JumpPathLaw {S : Type u}
    (N : Network.{u, v} S) (Omega : Type w) where
  prob : Probability.ProbSpec Omega
  probAxioms : Probability.ProbAxioms.{w, 0} prob
  path : Omega -> N.Path

structure InitialJumpPathLaw {S : Type u}
    (N : Network.{u, v} S) (z0 : State S)
    (Omega : Type w) where
  law : JumpPathLaw N Omega
  initial : forall omega, (law.path omega).state 0 = z0

namespace JumpPathLaw

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}

def pathEvent (L : JumpPathLaw N Omega)
    (E : N.Path -> Prop) : Probability.Event Omega :=
  {omega | E (L.path omega)}

theorem pathEvent_mono
    (L : JumpPathLaw N Omega) {E F : N.Path -> Prop}
    (h : forall path, E path -> F path) :
    L.pathEvent E ⊆ L.pathEvent F := by
  intro omega homega
  exact h (L.path omega) homega

def stateAt (L : JumpPathLaw N Omega)
    (t : Nat) (z : State S) : Probability.Event Omega :=
  {omega | (L.path omega).state t = z}

def firedAt (L : JumpPathLaw N Omega)
    (t : Nat) (i : N.I) : Probability.Event Omega :=
  {omega | (L.path omega).fired t = some i}

def terminalAt (L : JumpPathLaw N Omega)
    (t : Nat) : Probability.Event Omega :=
  {omega | N.Terminal ((L.path omega).state t)}

def firesListAt (L : JumpPathLaw N Omega)
    (t : Nat) (is : List N.I) : Probability.Event Omega :=
  {omega | (L.path omega).FiresListAt t is}

theorem firesListAt_append_subset_left
    (L : JumpPathLaw N Omega) (t : Nat) (is js : List N.I) :
    L.firesListAt t (is ++ js) ⊆ L.firesListAt t is := by
  intro omega h
  exact Network.Path.firesListAt_append_left
    (path := L.path omega) h

theorem firesListAt_append_subset_right
    (L : JumpPathLaw N Omega) (t : Nat) (is js : List N.I) :
    L.firesListAt t (is ++ js) ⊆
      L.firesListAt (t + is.length) js := by
  intro omega h
  exact Network.Path.firesListAt_append_right
    (path := L.path omega) h

def intendedFiresAt
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) :
    Probability.Event Omega :=
  {omega |
    (L.path omega).state t = z0 /\
      (L.path omega).FiresListAt t I.schedule}

def intendedDoneAt
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) :
    Probability.Event Omega :=
  {omega |
    (L.path omega).state (t + I.schedule.length) = z1}

theorem intendedFiresAt_subset_firesListAt
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) :
    L.intendedFiresAt I t ⊆ L.firesListAt t I.schedule := by
  intro omega h
  exact h.2

theorem intendedFiresAt_subset_doneAt
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) :
    L.intendedFiresAt I t ⊆ L.intendedDoneAt I t := by
  intro omega h
  exact Network.Path.state_after_intended_of_firesListAt
    (L.path omega) I h.1 h.2

theorem firesListAt_subset_intendedDoneAt_of_start
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (hstart : forall omega, (L.path omega).state t = z0) :
    L.firesListAt t I.schedule ⊆ L.intendedDoneAt I t := by
  intro omega hfires
  exact Network.Path.state_after_intended_of_firesListAt
    (L.path omega) I (hstart omega) hfires

end JumpPathLaw

structure RacePredicate {S : Type u}
    (N : Network.{u, v} S) where
  winsAt : N.Path -> Nat -> N.I -> Prop
  wins_fired :
    forall {path : N.Path} {t : Nat} {i : N.I},
      winsAt path t i -> path.fired t = some i

namespace RacePredicate

variable {S : Type u} {N : Network.{u, v} S}

def WinsListAt (R : RacePredicate N) (path : N.Path) :
    Nat -> List N.I -> Prop
  | _t, [] => True
  | t, i :: is =>
      R.winsAt path t i /\ R.WinsListAt path (t + 1) is

theorem firesListAt_of_winsListAt
    (R : RacePredicate N) (path : N.Path) :
    forall {t : Nat} {is : List N.I},
      R.WinsListAt path t is -> path.FiresListAt t is
  | _t, [], _h => trivial
  | t, i :: is, h => by
      exact ⟨R.wins_fired h.1,
        firesListAt_of_winsListAt R path
          (t := t + 1) (is := is) h.2⟩

end RacePredicate

namespace JumpPathLaw

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}

def raceWinsListAt
    (L : JumpPathLaw N Omega) (R : RacePredicate N)
    (t : Nat) (is : List N.I) : Probability.Event Omega :=
  {omega | R.WinsListAt (L.path omega) t is}

theorem raceWinsListAt_subset_firesListAt
    (L : JumpPathLaw N Omega) (R : RacePredicate N)
    (t : Nat) (is : List N.I) :
    L.raceWinsListAt R t is ⊆ L.firesListAt t is := by
  intro omega h
  exact R.firesListAt_of_winsListAt (L.path omega) h

theorem raceWinsListAt_subset_intendedFiresAt
    (L : JumpPathLaw N Omega) (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (hstart : forall omega, (L.path omega).state t = z0) :
    L.raceWinsListAt R t I.schedule ⊆ L.intendedFiresAt I t := by
  intro omega hWins
  exact ⟨hstart omega,
    R.firesListAt_of_winsListAt (L.path omega) hWins⟩

theorem raceWinsListAt_subset_intendedDoneAt_of_start
    (L : JumpPathLaw N Omega) (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (hstart : forall omega, (L.path omega).state t = z0) :
    L.raceWinsListAt R t I.schedule ⊆ L.intendedDoneAt I t :=
  Set.Subset.trans
    (raceWinsListAt_subset_intendedFiresAt L R I t hstart)
    (intendedFiresAt_subset_doneAt L I t)

theorem intendedWinsRaceAt_subset_intendedFiresAt
    (L : JumpPathLaw N Omega) (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) :
    L.pathEvent (fun path => path.IntendedWinsRaceAt Bad t I) ⊆
      L.intendedFiresAt I t := by
  intro omega hwin
  exact hwin.1

theorem intendedWinsRaceAt_subset_intendedDoneAt
    (L : JumpPathLaw N Omega) (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) :
    L.pathEvent (fun path => path.IntendedWinsRaceAt Bad t I) ⊆
      L.intendedDoneAt I t := by
  intro omega hwin
  exact (L.path omega).state_after_intendedWinsRaceAt Bad I hwin

end JumpPathLaw

structure IntendedRaceBound
    {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
    (L : JumpPathLaw N Omega) (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat) where
  failure : Probability.EventBound L.prob
  not_wins_subset_failure :
    Probability.ErrorEvent
      (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
        failure.event

namespace IntendedRaceBound

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
variable {L : JumpPathLaw N Omega} {R : RacePredicate N}
variable {z0 z1 : State S}
variable {I : N.IntendedSchedule z0 z1} {t : Nat}

def toCompletionContract
    (B : IntendedRaceBound L R I t)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.CompletionContract L.prob where
  done := fun omega => omega ∈ L.intendedDoneAt I t
  bound := B.failure.bound
  prob_le := by
    have hsubset :
        Probability.ErrorEvent
          (fun omega => omega ∈ L.intendedDoneAt I t) ⊆
          B.failure.event := by
      intro omega hnotDone
      apply B.not_wins_subset_failure
      intro hWins
      have hFires :
          (L.path omega).FiresListAt t I.schedule :=
        R.firesListAt_of_winsListAt (L.path omega) hWins
      have hDone :
          (L.path omega).state (t + I.schedule.length) = z1 :=
        Network.Path.state_after_intended_of_firesListAt
          (L.path omega) I (hstart omega) hFires
      exact hnotDone hDone
    exact le_trans (L.probAxioms.monotone hsubset) B.failure.prob_le

def toSuccessContract
    (B : IntendedRaceBound L R I t)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (B.toCompletionContract hstart)

def toCorrectnessContract
    (B : IntendedRaceBound L R I t)
    (hstart : forall omega, (L.path omega).state t = z0)
    (done correct : N.Path -> Prop)
    (hcorrect :
      forall path,
        path.state (t + I.schedule.length) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  Probability.CorrectnessContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    B.failure
    (by
      intro omega hwrong
      apply B.not_wins_subset_failure
      intro hWins
      have hFires :
          (L.path omega).FiresListAt t I.schedule :=
        R.firesListAt_of_winsListAt (L.path omega) hWins
      have hDone :
          (L.path omega).state (t + I.schedule.length) = z1 :=
        Network.Path.state_after_intended_of_firesListAt
          (L.path omega) I (hstart omega) hFires
      exact hwrong.2
        (hcorrect (L.path omega) hDone hwrong.1))

end IntendedRaceBound

namespace InitialJumpPathLaw

variable {S : Type u} {N : Network.{u, v} S}
variable {Omega : Type w} {z0 z1 : State S}

def intendedRaceCompletionAtZero
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (B : IntendedRaceBound X.law R I 0) :
    Probability.CompletionContract X.law.prob :=
  B.toCompletionContract (by
    intro omega
    exact X.initial omega)

def intendedRaceSuccessAtZero
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (B : IntendedRaceBound X.law R I 0) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.intendedRaceCompletionAtZero R I B)

def intendedRaceCorrectnessAtZero
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (B : IntendedRaceBound X.law R I 0)
    (done correct : N.Path -> Prop)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  B.toCorrectnessContract X.initial done correct
    (by
      intro path hendpoint hdone
      exact hcorrect path
        (by
          simpa [Network.IntendedSchedule.firingCount] using hendpoint)
        hdone)

end InitialJumpPathLaw

end Stochastic

end Ripple.sCRNUniversality

import Ripple.sCRNUniversality.Stochastic.JumpPathLaw
import Ripple.sCRNUniversality.Core.Fairness

namespace Ripple.sCRNUniversality

namespace Stochastic

universe u v w

structure PathEventBound
    {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
    (L : JumpPathLaw N Omega) (bad : N.Path -> Prop) where
  bound : Probability.EventBound L.prob
  pathEvent_subset_bound :
    L.pathEvent bad ⊆ bound.event

structure PathFailureBound
    {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
    (L : JumpPathLaw N Omega) (success : N.Path -> Prop) where
  failure : Probability.EventBound L.prob
  error_subset_failure :
    Probability.ErrorEvent (fun omega => success (L.path omega)) ⊆
      failure.event

namespace PathEventBound

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
variable {L : JumpPathLaw N Omega} {bad success : N.Path -> Prop}

def ofEventBound
    (B : Probability.EventBound L.prob)
    (hsubset : L.pathEvent bad ⊆ B.event) :
    PathEventBound L bad where
  bound := B
  pathEvent_subset_bound := hsubset

def toEventBound
    (B : PathEventBound L bad) :
    Probability.EventBound L.prob where
  event := L.pathEvent bad
  bound := B.bound.bound
  prob_le := le_trans
    (L.probAxioms.monotone B.pathEvent_subset_bound)
    B.bound.prob_le

def mono
    (B : PathEventBound L bad)
    {bad' : N.Path -> Prop}
    (hbad : forall path, bad' path -> bad path) :
    PathEventBound L bad' where
  bound := B.bound
  pathEvent_subset_bound := by
    intro omega hbad'
    exact B.pathEvent_subset_bound
      (hbad (L.path omega) hbad')

def toEventBound_of_implication
    (B : PathEventBound L bad)
    {bad' : N.Path -> Prop}
    (hbad : forall path, bad' path -> bad path) :
    Probability.EventBound L.prob :=
  (B.mono hbad).toEventBound

def of_subset
    (B : PathEventBound L bad)
    {bad' : N.Path -> Prop}
    (hsubset : L.pathEvent bad' ⊆ L.pathEvent bad) :
    PathEventBound L bad' where
  bound := B.bound
  pathEvent_subset_bound := by
    intro omega hbad'
    exact B.pathEvent_subset_bound (hsubset hbad')

def weaken_bound
    (B : PathEventBound L bad) {bound' : ENNReal}
    (hbound : B.bound.bound <= bound') :
    PathEventBound L bad where
  bound := Probability.EventBound.weaken_bound B.bound hbound
  pathEvent_subset_bound := by
    simpa [Probability.EventBound.weaken_bound] using
      B.pathEvent_subset_bound

def toFailureBound
    (B : PathEventBound L bad)
    (hbad : forall path, Not (success path) -> bad path) :
    PathFailureBound L success where
  failure := B.bound
  error_subset_failure := by
    intro omega hnot
    exact B.pathEvent_subset_bound (hbad (L.path omega) hnot)

def toSuccessContract
    (B : PathEventBound L bad)
    (success : N.Path -> Prop)
    (hbad : forall path, Not (success path) -> bad path) :
    Probability.SuccessContract L.prob :=
  Probability.SuccessContract.ofEventBound
    L.probAxioms
    (fun omega => success (L.path omega))
    B.bound
    (by
      intro omega hnot
      exact B.pathEvent_subset_bound (hbad (L.path omega) hnot))

def toCompletionContract
    (B : PathEventBound L bad)
    (done : N.Path -> Prop)
    (hbad : forall path, Not (done path) -> bad path) :
    Probability.CompletionContract L.prob :=
  Probability.CompletionContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    B.bound
    (by
      intro omega hnot
      exact B.pathEvent_subset_bound (hbad (L.path omega) hnot))

def toCorrectnessContract
    (B : PathEventBound L bad)
    (done correct : N.Path -> Prop)
    (hbad :
      forall path, done path -> Not (correct path) -> bad path) :
    Probability.CorrectnessContract L.prob :=
  Probability.CorrectnessContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    B.bound
    (by
      intro omega hwrong
      exact B.pathEvent_subset_bound
        (hbad (L.path omega) hwrong.1 hwrong.2))

def toDeadlineContract
    (B : PathEventBound L bad)
    (finishTime : N.Path -> Nat) (deadline : Nat)
    (hbad : forall path, deadline < finishTime path -> bad path) :
    Probability.DeadlineContract L.prob :=
  Probability.DeadlineContract.ofEventBound
    L.probAxioms
    (fun omega => finishTime (L.path omega))
    deadline
    B.bound
    (by
      intro omega hlate
      exact B.pathEvent_subset_bound (hbad (L.path omega) hlate))

def toModuleContract
    {liveBad corrBad : N.Path -> Prop}
    (B_live : PathEventBound L liveBad)
    (B_corr : PathEventBound L corrBad)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (hlive_bound : B_live.bound.bound <= liveBound)
    (hcorr_bound : B_corr.bound.bound <= corrBound)
    (hlive :
      forall path, Not (done path) -> liveBad path)
    (hcorr :
      forall path, done path -> Not (correct path) -> corrBad path) :
    Probability.ModuleContract L.prob :=
  Probability.ModuleContract.ofEventBounds
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    liveBound
    corrBound
    B_live.bound
    B_corr.bound
    hlive_bound
    hcorr_bound
    (by
      intro omega hnotDone
      exact B_live.pathEvent_subset_bound
        (hlive (L.path omega) hnotDone))
    (by
      intro omega hwrong
      exact B_corr.pathEvent_subset_bound
        (hcorr (L.path omega) hwrong.1 hwrong.2))

def toModuleContract_selfBounds
    {liveBad corrBad : N.Path -> Prop}
    (B_live : PathEventBound L liveBad)
    (B_corr : PathEventBound L corrBad)
    (done correct : N.Path -> Prop)
    (hlive :
      forall path, Not (done path) -> liveBad path)
    (hcorr :
      forall path, done path -> Not (correct path) -> corrBad path) :
    Probability.ModuleContract L.prob :=
  PathEventBound.toModuleContract
    B_live
    B_corr
    done
    correct
    B_live.bound.bound
    B_corr.bound.bound
    le_rfl
    le_rfl
    hlive
    hcorr

end PathEventBound

namespace PathFailureBound

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
variable {L : JumpPathLaw N Omega} {success : N.Path -> Prop}

def ofEventBound
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => success (L.path omega)) ⊆
        B.event) :
    PathFailureBound L success where
  failure := B
  error_subset_failure := hsubset

def toEventBound
    (B : PathFailureBound L success) :
    Probability.EventBound L.prob where
  event := Probability.ErrorEvent (fun omega => success (L.path omega))
  bound := B.failure.bound
  prob_le := le_trans
    (L.probAxioms.monotone B.error_subset_failure)
    B.failure.prob_le

def toPathEventBound
    (B : PathFailureBound L success)
    (bad : N.Path -> Prop)
    (hbad : forall path, bad path -> Not (success path)) :
    PathEventBound L bad where
  bound := B.failure
  pathEvent_subset_bound := by
    intro omega hbad'
    exact B.error_subset_failure
      (hbad (L.path omega) hbad')

def toPathEventBound_notSuccess
    (B : PathFailureBound L success) :
    PathEventBound L (fun path => Not (success path)) :=
  B.toPathEventBound
    (fun path => Not (success path))
    (fun _path hnot => hnot)

def consequence
    (B : PathFailureBound L success)
    (success' : N.Path -> Prop)
    (hsuccess : forall path, success path -> success' path) :
    PathFailureBound L success' where
  failure := B.failure
  error_subset_failure := by
    intro omega hnot
    exact B.error_subset_failure (by
      intro hsuccess_old
      exact hnot (hsuccess (L.path omega) hsuccess_old))

def toEventBound_of_implication
    (B : PathFailureBound L success)
    (success' : N.Path -> Prop)
    (hsuccess : forall path, success path -> success' path) :
    Probability.EventBound L.prob :=
  (B.consequence success' hsuccess).toEventBound

def of_subset
    (B : PathFailureBound L success)
    (success' : N.Path -> Prop)
    (hsubset :
      Probability.ErrorEvent (fun omega => success' (L.path omega)) ⊆
        Probability.ErrorEvent (fun omega => success (L.path omega))) :
    PathFailureBound L success' where
  failure := B.failure
  error_subset_failure := by
    intro omega hnot
    exact B.error_subset_failure (hsubset hnot)

def weaken_bound
    (B : PathFailureBound L success) {bound' : ENNReal}
    (hbound : B.failure.bound <= bound') :
    PathFailureBound L success where
  failure := Probability.EventBound.weaken_bound B.failure hbound
  error_subset_failure := by
    simpa [Probability.EventBound.weaken_bound] using
      B.error_subset_failure

def toSuccessContract
    (B : PathFailureBound L success) :
    Probability.SuccessContract L.prob :=
  Probability.SuccessContract.ofEventBound
    L.probAxioms
    (fun omega => success (L.path omega))
    B.failure
    B.error_subset_failure

def toSuccessContract_of_implication
    (B : PathFailureBound L success)
    (success' : N.Path -> Prop)
    (hsuccess : forall path, success path -> success' path) :
    Probability.SuccessContract L.prob :=
  (B.consequence success' hsuccess).toSuccessContract

def toCompletionContract
    (B : PathFailureBound L success) :
    Probability.CompletionContract L.prob :=
  Probability.CompletionContract.ofEventBound
    L.probAxioms
    (fun omega => success (L.path omega))
    B.failure
    B.error_subset_failure

def toCompletionContract_of_implication
    (B : PathFailureBound L success)
    (done : N.Path -> Prop)
    (hsuccess : forall path, success path -> done path) :
    Probability.CompletionContract L.prob :=
  (B.consequence done hsuccess).toCompletionContract

def toCorrectnessContract
    (B : PathFailureBound L success)
    (done correct : N.Path -> Prop)
    (hsuccess :
      forall path, success path -> done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  B.toSuccessContract.toCorrectnessContract_of_implication
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    (by
      intro omega hsuccess_path hdone
      exact hsuccess (L.path omega) hsuccess_path hdone)

def toDeadlineContract
    (B : PathFailureBound L success)
    (finishTime : N.Path -> Nat) (deadline : Nat)
    (hsuccess :
      forall path, success path -> finishTime path <= deadline) :
    Probability.DeadlineContract L.prob :=
  Probability.DeadlineContract.ofEventBound
    L.probAxioms
    (fun omega => finishTime (L.path omega))
    deadline
    B.failure
    (by
      intro omega hlate
      exact B.error_subset_failure (by
        intro hsuccess_path
        exact not_lt_of_ge
          (hsuccess (L.path omega) hsuccess_path)
          hlate))

def toModuleContract
    {done corrBad : N.Path -> Prop}
    (B_live : PathFailureBound L done)
    (B_corr : PathEventBound L corrBad)
    (correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (hlive_bound : B_live.failure.bound <= liveBound)
    (hcorr_bound : B_corr.bound.bound <= corrBound)
    (hcorr :
      forall path, done path -> Not (correct path) -> corrBad path) :
    Probability.ModuleContract L.prob :=
  Probability.ModuleContract.ofEventBounds
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    liveBound
    corrBound
    B_live.failure
    B_corr.bound
    hlive_bound
    hcorr_bound
    B_live.error_subset_failure
    (by
      intro omega hwrong
      exact B_corr.pathEvent_subset_bound
        (hcorr (L.path omega) hwrong.1 hwrong.2))

def toModuleContract_selfBounds
    {done corrBad : N.Path -> Prop}
    (B_live : PathFailureBound L done)
    (B_corr : PathEventBound L corrBad)
    (correct : N.Path -> Prop)
    (hcorr :
      forall path, done path -> Not (correct path) -> corrBad path) :
    Probability.ModuleContract L.prob :=
  PathFailureBound.toModuleContract
    B_live
    B_corr
    correct
    B_live.failure.bound
    B_corr.bound.bound
    le_rfl
    le_rfl
    hcorr

def toModuleContract_ofFailureBounds
    {liveSuccess corrSuccess : N.Path -> Prop}
    (B_live : PathFailureBound L liveSuccess)
    (B_corr : PathFailureBound L corrSuccess)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (hlive_bound : B_live.failure.bound <= liveBound)
    (hcorr_bound : B_corr.failure.bound <= corrBound)
    (hlive : forall path, liveSuccess path -> done path)
    (hcorr :
      forall path, corrSuccess path -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  Probability.ModuleContract.ofEventBounds
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    liveBound
    corrBound
    B_live.failure
    B_corr.failure
    hlive_bound
    hcorr_bound
    (by
      intro omega hnotDone
      exact B_live.error_subset_failure (by
        intro hsuccess
        exact hnotDone (hlive (L.path omega) hsuccess)))
    (by
      intro omega hwrong
      exact B_corr.error_subset_failure (by
        intro hsuccess
        exact hwrong.2
          (hcorr (L.path omega) hsuccess hwrong.1)))

def toModuleContract_selfBounds_ofFailureBounds
    {liveSuccess corrSuccess : N.Path -> Prop}
    (B_live : PathFailureBound L liveSuccess)
    (B_corr : PathFailureBound L corrSuccess)
    (done correct : N.Path -> Prop)
    (hlive : forall path, liveSuccess path -> done path)
    (hcorr :
      forall path, corrSuccess path -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  PathFailureBound.toModuleContract_ofFailureBounds
    B_live
    B_corr
    done
    correct
    B_live.failure.bound
    B_corr.failure.bound
    le_rfl
    le_rfl
    hlive
    hcorr

end PathFailureBound

namespace IntendedRaceBound

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}
variable {L : JumpPathLaw N Omega} {R : RacePredicate N}
variable {z0 z1 : State S}
variable {I : N.IntendedSchedule z0 z1} {t : Nat}

/--
Forget an intended-race-specific bound into the generic path failure-bound
adapter. This only reuses the externally supplied event bound and subset proof.
-/
def toPathFailureBound
    (B : IntendedRaceBound L R I t) :
    PathFailureBound L
      (fun path => R.WinsListAt path t I.schedule) where
  failure := B.failure
  error_subset_failure := by
    simpa using B.not_wins_subset_failure

def toDeadlineContract
    (B : IntendedRaceBound L R I t) :
    Probability.DeadlineContract L.prob :=
  B.toPathFailureBound.toDeadlineContract
    (fun _path => t + I.firingCount)
    (t + I.firingCount)
    (by
      intro _path _hWins
      exact le_rfl)

def toPathEventBound
    (B : IntendedRaceBound L R I t) :
    PathEventBound L
      (fun path => Not (R.WinsListAt path t I.schedule)) where
  bound := B.failure
  pathEvent_subset_bound := by
    simpa [JumpPathLaw.pathEvent, Probability.ErrorEvent] using
      B.not_wins_subset_failure

end IntendedRaceBound

namespace JumpPathLaw

variable {S : Type u} {N : Network.{u, v} S} {Omega : Type w}

def pathSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (success : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => success (L.path omega)) ⊆
        B.event) :
    Probability.SuccessContract L.prob :=
  Probability.SuccessContract.ofEventBound
    L.probAxioms
    (fun omega => success (L.path omega))
    B
    hsubset

def pathCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (done : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => done (L.path omega)) ⊆
        B.event) :
    Probability.CompletionContract L.prob :=
  Probability.CompletionContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    B
    hsubset

def pathCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      {omega | done (L.path omega) /\ Not (correct (L.path omega))} ⊆
        B.event) :
    Probability.CorrectnessContract L.prob :=
  Probability.CorrectnessContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    B
    hsubset

def pathDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (finishTime : N.Path -> Nat)
    (deadline : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      {omega | deadline < finishTime (L.path omega)} ⊆ B.event) :
    Probability.DeadlineContract L.prob :=
  Probability.DeadlineContract.ofEventBound
    L.probAxioms
    (fun omega => finishTime (L.path omega))
    deadline
    B
    hsubset

def pathModuleContract_ofEventBounds
    (L : JumpPathLaw N Omega)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_sub :
      {omega | Not (done (L.path omega))} ⊆ B_live.event)
    (hcorr_sub :
      {omega | done (L.path omega) /\ Not (correct (L.path omega))} ⊆
        B_corr.event) :
    Probability.ModuleContract L.prob :=
  Probability.ModuleContract.ofEventBounds
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    hlive_sub
    hcorr_sub

def pathModuleContract_ofEventBounds_selfBounds
    (L : JumpPathLaw N Omega)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_sub :
      {omega | Not (done (L.path omega))} ⊆ B_live.event)
    (hcorr_sub :
      {omega | done (L.path omega) /\ Not (correct (L.path omega))} ⊆
        B_corr.event) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofEventBounds
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_sub
    hcorr_sub

def pathModuleContract_ofWitnessEventBounds
    (L : JumpPathLaw N Omega)
    (liveWitness corrWitness done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => liveWitness (L.path omega)) ⊆ B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => corrWitness (L.path omega)) ⊆ B_corr.event)
    (hlive : forall path, liveWitness path -> done path)
    (hcorr :
      forall path, corrWitness path -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofEventBounds
    done
    correct
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    (by
      intro omega hnotDone
      apply hlive_subset
      intro hw
      exact hnotDone (hlive (L.path omega) hw))
    (by
      intro omega hwrong
      apply hcorr_subset
      intro hw
      exact hwrong.2
        (hcorr (L.path omega) hw hwrong.1))

def pathModuleContract_ofWitnessEventBounds_selfBounds
    (L : JumpPathLaw N Omega)
    (liveWitness corrWitness done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => liveWitness (L.path omega)) ⊆ B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => corrWitness (L.path omega)) ⊆ B_corr.event)
    (hlive : forall path, liveWitness path -> done path)
    (hcorr :
      forall path, corrWitness path -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofWitnessEventBounds
    liveWitness
    corrWitness
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_subset
    hcorr_subset
    hlive
    hcorr

def pathSuccessContract_ofWitnessEventBound
    (L : JumpPathLaw N Omega)
    (witness success : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => witness (L.path omega)) ⊆
        B.event)
    (hwitness : forall path, witness path -> success path) :
    Probability.SuccessContract L.prob :=
  Probability.SuccessContract.ofEventBoundWitness
    L.probAxioms
    (fun omega => witness (L.path omega))
    (fun omega => success (L.path omega))
    B
    hsubset
    (by
      intro omega h
      exact hwitness (L.path omega) h)

def pathCompletionContract_ofWitnessEventBound
    (L : JumpPathLaw N Omega)
    (witness done : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => witness (L.path omega)) ⊆
        B.event)
    (hwitness : forall path, witness path -> done path) :
    Probability.CompletionContract L.prob :=
  Probability.CompletionContract.consequence
    L.probAxioms
    (L.pathCompletionContract_ofEventBound witness B hsubset)
    (fun omega => done (L.path omega))
    (by
      intro omega h
      exact hwitness (L.path omega) h)

def pathCorrectnessContract_ofWitnessEventBound
    (L : JumpPathLaw N Omega)
    (witness done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => witness (L.path omega)) ⊆
        B.event)
    (hwitness :
      forall path, witness path -> done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  Probability.CorrectnessContract.ofEventBoundWitness
    L.probAxioms
    (fun omega => witness (L.path omega))
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    B
    hsubset
    (by
      intro omega hw hd
      exact hwitness (L.path omega) hw hd)

def pathDeadlineContract_ofWitnessEventBound
    (L : JumpPathLaw N Omega)
    (witness : N.Path -> Prop)
    (finishTime : N.Path -> Nat) (deadline : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent (fun omega => witness (L.path omega)) ⊆
        B.event)
    (hwitness :
      forall path, witness path -> finishTime path <= deadline) :
    Probability.DeadlineContract L.prob :=
  Probability.DeadlineContract.ofEventBoundWitness
    L.probAxioms
    (fun omega => witness (L.path omega))
    (fun omega => finishTime (L.path omega))
    deadline
    B
    hsubset
    (by
      intro omega h
      exact hwitness (L.path omega) h)

def firesListAtSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (t : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t is) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofEventBound
    (fun path => path.FiresListAt t is)
    B
    hsubset

def firesListAtPrefixSuccessContract_of_appendEventBound
    (L : JumpPathLaw N Omega)
    (t : Nat) (is js : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t (is ++ js)) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.FiresListAt t (is ++ js))
    (fun path => path.FiresListAt t is)
    B
    hsubset
    (by
      intro path hfires
      exact Network.Path.firesListAt_append_left hfires)

def firesListAtSuffixSuccessContract_of_appendEventBound
    (L : JumpPathLaw N Omega)
    (t : Nat) (is js : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t (is ++ js)) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.FiresListAt t (is ++ js))
    (fun path => path.FiresListAt (t + is.length) js)
    B
    hsubset
    (by
      intro path hfires
      exact Network.Path.firesListAt_append_right hfires)

def eventuallyFiresSuccessContract_of_firedAtEventBound
    (L : JumpPathLaw N Omega)
    (i : N.I) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).fired t = some i) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.fired t = some i)
    (fun path => path.EventuallyFires i t)
    B
    hsubset
    (by
      intro path hfired
      exact Network.Path.eventuallyFires_of_fired hfired)

def eventuallyFiresSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (i : N.I) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).EventuallyFires i t0) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofEventBound
    (fun path => path.EventuallyFires i t0)
    B
    hsubset

def eventuallyFiresListSuccessContract_of_firesListAtEventBound
    (L : JumpPathLaw N Omega)
    (t : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t is) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.FiresListAt t is)
    (fun path => path.EventuallyFiresList t is)
    B
    hsubset
    (by
      intro path hfires
      exact Network.Path.eventuallyFiresList_of_firesListAt hfires)

def eventuallyFiresListSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (t : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).EventuallyFiresList t is) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofEventBound
    (fun path => path.EventuallyFiresList t is)
    B
    hsubset

/--
If an external producer bounds failure of weak fairness at `i` from `t0`, and
the path-level enabledness side condition is available, then eventual firing is
a pure consequence. This does not prove fairness for any stochastic model.
-/
def eventuallyFiresSuccessContract_ofWeaklyFairAtEventBound
    (L : JumpPathLaw N Omega)
    (i : N.I) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).WeaklyFairAt i t0) ⊆
          B.event)
    (henabled :
      forall path : N.Path, path.AlwaysEnabledFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.WeaklyFairAt i t0)
    (fun path => path.EventuallyFires i t0)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFires_of_weaklyFairAt
        hfair
        (henabled path))

def eventuallyFiresSuccessContract_ofWeaklyFairEventBound
    (L : JumpPathLaw N Omega)
    (i : N.I) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).WeaklyFair) ⊆
          B.event)
    (henabled :
      forall path : N.Path, path.AlwaysEnabledFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.WeaklyFair)
    (fun path => path.EventuallyFires i t0)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFires_of_weaklyFair
        hfair
        (henabled path))

def eventuallyFiresListSuccessContract_ofWeaklyFairEventBound
    (L : JumpPathLaw N Omega)
    (t0 : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).WeaklyFair) ⊆
          B.event)
    (henabled :
      forall path : N.Path,
        forall i, i ∈ is -> path.AlwaysEnabledFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.WeaklyFair)
    (fun path => path.EventuallyFiresList t0 is)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFiresList_of_weaklyFair
        hfair
        (henabled path))

/--
Weak fairness plus persistent enabledness of every intended index gives eventual
firing of the intended list. This is not a contiguous-schedule or endpoint
contract.
-/
def eventuallyFiresIntendedScheduleSuccessContract_ofWeaklyFairEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).WeaklyFair) ⊆
          B.event)
    (henabled :
      forall path : N.Path,
        forall i, i ∈ I.schedule -> path.AlwaysEnabledFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.WeaklyFair)
    (fun path => path.EventuallyFiresList t0 I.schedule)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFiresIntendedSchedule_of_weaklyFair
        I
        hfair
        (henabled path))

def eventuallyFiresSuccessContract_ofStronglyFairAtEventBound
    (L : JumpPathLaw N Omega)
    (i : N.I) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).StronglyFairAt i t0) ⊆
          B.event)
    (henabled :
      forall path : N.Path, path.EnabledInfinitelyOftenFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.StronglyFairAt i t0)
    (fun path => path.EventuallyFires i t0)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFires_of_firesInfinitelyOftenFrom
        (Network.Path.firesInfinitelyOftenFrom_of_stronglyFairAt
          hfair
          (henabled path)))

def eventuallyFiresSuccessContract_ofStronglyFairEventBound
    (L : JumpPathLaw N Omega)
    (i : N.I) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).StronglyFair) ⊆
          B.event)
    (henabled :
      forall path : N.Path, path.EnabledInfinitelyOftenFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.StronglyFair)
    (fun path => path.EventuallyFires i t0)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFires_of_firesInfinitelyOftenFrom
        (Network.Path.firesInfinitelyOftenFrom_of_stronglyFair
          hfair
          (henabled path)))

def eventuallyFiresListSuccessContract_ofStronglyFairEventBound
    (L : JumpPathLaw N Omega)
    (t0 : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).StronglyFair) ⊆
          B.event)
    (henabled :
      forall path : N.Path,
        forall i, i ∈ is -> path.EnabledInfinitelyOftenFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.StronglyFair)
    (fun path => path.EventuallyFiresList t0 is)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFiresList_of_stronglyFair
        hfair
        (henabled path))

def eventuallyFiresIntendedScheduleSuccessContract_ofStronglyFairEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t0 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).StronglyFair) ⊆
          B.event)
    (henabled :
      forall path : N.Path,
        forall i, i ∈ I.schedule -> path.EnabledInfinitelyOftenFrom i t0) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.StronglyFair)
    (fun path => path.EventuallyFiresList t0 I.schedule)
    B
    hsubset
    (by
      intro path hfair
      exact Network.Path.eventuallyFiresIntendedSchedule_of_stronglyFair
        I
        hfair
        (henabled path))

def noBadFiresBeforeSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet) (t0 t1 : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).NoBadFiresBefore Bad t0 t1) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofEventBound
    (fun path => path.NoBadFiresBefore Bad t0 t1)
    B
    hsubset

def noBadFiresBeforeSuccessContract_of_intendedWinsRaceAtEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).IntendedWinsRaceAt Bad t I) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.IntendedWinsRaceAt Bad t I)
    (fun path => path.NoBadFiresBefore Bad t (t + I.schedule.length))
    B
    hsubset
    (by
      intro path hwin
      exact Network.Path.noBadFiresBefore_of_intendedWinsRaceAt hwin)

def raceWinsListSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N) (t : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t is) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofEventBound
    (fun path => R.WinsListAt path t is)
    B
    hsubset

def raceWinsListCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N) (t : Nat) (is : List N.I)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t is) ⊆
          B.event)
    (hcorrect :
      forall path,
        R.WinsListAt path t is -> done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.pathCorrectnessContract_ofWitnessEventBound
    (fun path => R.WinsListAt path t is)
    done
    correct
    B
    hsubset
    hcorrect

def raceWinsListDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N) (t : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t is) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => R.WinsListAt path t is)
    (fun _path => t + is.length)
    (t + is.length)
    B
    hsubset
    (by
      intro _path _hWins
      exact le_rfl)

def firesListSuccessContract_ofRaceWinsEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N) (t : Nat) (is : List N.I)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t is) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => R.WinsListAt path t is)
    (fun path => path.FiresListAt t is)
    B
    hsubset
    (by
      intro path hWins
      exact R.firesListAt_of_winsListAt path hWins)

def firesListCorrectnessContract_ofRaceWinsEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N) (t : Nat) (is : List N.I)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t is) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.FiresListAt t is -> done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.pathCorrectnessContract_ofWitnessEventBound
    (fun path => R.WinsListAt path t is)
    done
    correct
    B
    hsubset
    (by
      intro path hWins hdone
      exact hcorrect path (R.firesListAt_of_winsListAt path hWins) hdone)

def intendedDoneAtCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I t) ⊆
          B.event) :
    Probability.CompletionContract L.prob :=
  L.pathCompletionContract_ofEventBound
    (fun path => path.state (t + I.schedule.length) = z1)
    B
    hsubset

def intendedDoneAtSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I t) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.intendedDoneAtCompletionContract_ofEventBound I t B hsubset)

def intendedDoneAtCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I t) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state (t + I.schedule.length) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.pathCorrectnessContract_ofWitnessEventBound
    (fun path => path.state (t + I.schedule.length) = z1)
    done
    correct
    B
    hsubset
    hcorrect

def intendedDoneAtDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I t) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.state (t + I.firingCount) = z1)
    (fun _path => t + I.firingCount)
    (t + I.firingCount)
    B
    (by
      intro omega hnotEndpoint
      apply hsubset
      intro hdone
      exact hnotEndpoint (by
        simpa [JumpPathLaw.intendedDoneAt,
          Network.IntendedSchedule.firingCount] using hdone))
    (by
      intro _path _hendpoint
      exact le_rfl)

def intendedFiresCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresIntendedContiguouslyAt t I) ⊆
          B.event) :
    Probability.CompletionContract L.prob :=
  L.pathCompletionContract_ofWitnessEventBound
    (fun path => path.FiresIntendedContiguouslyAt t I)
    (fun path => path.state (t + I.schedule.length) = z1)
    B
    hsubset
    (by
      intro path hfire
      exact path.state_after_intended_of_firesListAt I hfire.1 hfire.2)

def intendedFiresSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresIntendedContiguouslyAt t I) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.intendedFiresCompletionContract_ofEventBound I t B hsubset)

def intendedFiresCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresIntendedContiguouslyAt t I) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state (t + I.schedule.length) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.pathCorrectnessContract_ofWitnessEventBound
    (fun path => path.FiresIntendedContiguouslyAt t I)
    done
    correct
    B
    hsubset
    (by
      intro path hfire hdone
      exact hcorrect path
        (path.state_after_intended_of_firesListAt I hfire.1 hfire.2)
        hdone)

def intendedFiresDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresIntendedContiguouslyAt t I) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.FiresIntendedContiguouslyAt t I)
    (fun _path => t + I.firingCount)
    (t + I.firingCount)
    B
    hsubset
    (by
      intro _path _hfire
      exact le_rfl)

def intendedWinsRaceAtSuccessContract_of_intendedFiresEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresIntendedContiguouslyAt t I) ⊆
          B.event)
    (hnotBad : forall i, i ∈ I.schedule -> Not (Bad i)) :
    Probability.SuccessContract L.prob :=
  L.pathSuccessContract_ofWitnessEventBound
    (fun path => path.FiresIntendedContiguouslyAt t I)
    (fun path => path.IntendedWinsRaceAt Bad t I)
    B
    hsubset
    (by
      intro path hfire
      exact
        Network.Path.intendedWinsRaceAt_of_firesIntendedContiguouslyAt_forall_not_bad
          hfire hnotBad)

def intendedFiresCompletionContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.CompletionContract L.prob :=
  Probability.CompletionContract.ofEventBound
    L.probAxioms
    (fun omega => (L.path omega).state (t + I.schedule.length) = z1)
    B
    (by
      intro omega hnotDone
      apply hsubset
      intro hfires
      exact hnotDone
        ((L.path omega).state_after_intended_of_firesListAt
          I (hstart omega) hfires))

def intendedFiresSuccessContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.intendedFiresCompletionContract_ofFiresListAtEventBound
      I t B hsubset hstart)

def intendedFiresCorrectnessContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hcorrect :
      forall path,
        path.state (t + I.schedule.length) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  Probability.CorrectnessContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    B
    (by
      intro omega hwrong
      apply hsubset
      intro hfires
      have hendpoint :
          (L.path omega).state (t + I.schedule.length) = z1 :=
        (L.path omega).state_after_intended_of_firesListAt
          I (hstart omega) hfires
      exact hwrong.2
        (hcorrect (L.path omega) hendpoint hwrong.1))

def intendedFiresDeadlineContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.FiresListAt t I.schedule)
    (fun _path => t + I.firingCount)
    (t + I.firingCount)
    B
    hsubset
    (by
      intro _path _hfires
      exact le_rfl)

def intendedWinsRaceAtSuccessContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hNoBad :
      forall omega,
        (L.path omega).NoBadFiresBefore Bad t (t + I.schedule.length)) :
    Probability.SuccessContract L.prob :=
  Probability.SuccessContract.ofEventBound
    L.probAxioms
    (fun omega => (L.path omega).IntendedWinsRaceAt Bad t I)
    B
    (by
      intro omega hnotWin
      apply hsubset
      intro hfires
      exact hnotWin
        (Network.Path.intendedWinsRaceAt_of_parts
          (hstart omega) hfires (hNoBad omega)))

def intendedWinsRaceCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).IntendedWinsRaceAt Bad t I) ⊆
          B.event) :
    Probability.CompletionContract L.prob :=
  L.pathCompletionContract_ofWitnessEventBound
    (fun path => path.IntendedWinsRaceAt Bad t I)
    (fun path => path.state (t + I.schedule.length) = z1)
    B
    hsubset
    (by
      intro path hwin
      exact path.state_after_intendedWinsRaceAt Bad I hwin)

def intendedWinsRaceSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).IntendedWinsRaceAt Bad t I) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.intendedWinsRaceCompletionContract_ofEventBound Bad I t B hsubset)

def intendedWinsRaceCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).IntendedWinsRaceAt Bad t I) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state (t + I.schedule.length) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.pathCorrectnessContract_ofWitnessEventBound
    (fun path => path.IntendedWinsRaceAt Bad t I)
    done
    correct
    B
    hsubset
    (by
      intro path hwin hdone
      exact hcorrect path
        (path.state_after_intendedWinsRaceAt Bad I hwin)
        hdone)

def intendedWinsRaceDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).IntendedWinsRaceAt Bad t I) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.IntendedWinsRaceAt Bad t I)
    (fun _path => t + I.firingCount)
    (t + I.firingCount)
    B
    hsubset
    (by
      intro _path _hwin
      exact le_rfl)

def intendedRaceCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.CompletionContract L.prob :=
  (IntendedRaceBound.mk B hsubset :
    IntendedRaceBound L R I t).toCompletionContract hstart

def intendedRaceSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.intendedRaceCompletionContract_ofEventBound R I t B hsubset hstart)

def intendedRaceCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hcorrect :
      forall path,
        path.state (t + I.schedule.length) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  Probability.CorrectnessContract.ofEventBound
    L.probAxioms
    (fun omega => done (L.path omega))
    (fun omega => correct (L.path omega))
    B
    (by
      intro omega hwrong
      apply hsubset
      intro hWins
      have hFires :
          (L.path omega).FiresListAt t I.schedule :=
        R.firesListAt_of_winsListAt (L.path omega) hWins
      have hDone :
          (L.path omega).state (t + I.schedule.length) = z1 :=
        (L.path omega).state_after_intended_of_firesListAt
          I (hstart omega) hFires
      exact hwrong.2 (hcorrect (L.path omega) hDone hwrong.1))

def intendedRaceDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {z0 z1 : State S}
    (I : N.IntendedSchedule z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => R.WinsListAt path t I.schedule)
    (fun _path => t + I.firingCount)
    (t + I.firingCount)
    B
    hsubset
    (by
      intro _path _hwin
      exact le_rfl)

def boundedIntendedDoneAtCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I.toIntendedSchedule t) ⊆
          B.event) :
    Probability.CompletionContract L.prob :=
  L.intendedDoneAtCompletionContract_ofEventBound
    I.toIntendedSchedule t B hsubset

def boundedIntendedDoneAtSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I.toIntendedSchedule t) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.boundedIntendedDoneAtCompletionContract_ofEventBound I t B hsubset)

def boundedIntendedDoneAtCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I.toIntendedSchedule t) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.intendedDoneAtCorrectnessContract_ofEventBound
    I.toIntendedSchedule t done correct B hsubset
    (by
      intro path hdoneAt hdone
      exact hcorrect path (by
        simpa [Network.BoundedIntendedSchedule.firingCount,
          Network.BoundedIntendedSchedule.toIntendedSchedule] using hdoneAt) hdone)

def boundedIntendedDoneAtDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ L.intendedDoneAt I.toIntendedSchedule t) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path =>
      path.state (t + I.toIntendedSchedule.schedule.length) = z1)
    (fun _path => t + I.firingCount)
    (t + bound)
    B
    (by
      simpa [JumpPathLaw.intendedDoneAt] using hsubset)
    (by
      intro _path _hdone
      exact Nat.add_le_add_left I.firingCount_le_bound t)

def boundedIntendedFiresCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B.event) :
    Probability.CompletionContract L.prob :=
  L.intendedFiresCompletionContract_ofEventBound
    I.toIntendedSchedule t B hsubset

def boundedIntendedFiresSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B.event) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.boundedIntendedFiresCompletionContract_ofEventBound I t B hsubset)

def boundedIntendedFiresCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B.event)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.intendedFiresCorrectnessContract_ofEventBound
    I.toIntendedSchedule t done correct B hsubset
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.BoundedIntendedSchedule.firingCount,
          Network.BoundedIntendedSchedule.toIntendedSchedule] using hendpoint) hdone)

def boundedIntendedFiresDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.FiresIntendedContiguouslyAt t I.toIntendedSchedule)
    (fun _path => t + I.firingCount)
    (t + bound)
    B
    hsubset
    (by
      intro _path _hfire
      exact Nat.add_le_add_left I.firingCount_le_bound t)

def boundedIntendedFiresModuleContract_ofEventBounds
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B_corr.event)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofWitnessEventBounds
    (fun path => path.FiresIntendedContiguouslyAt t I.toIntendedSchedule)
    (fun path => path.FiresIntendedContiguouslyAt t I.toIntendedSchedule)
    done
    correct
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    hlive_subset
    hcorr_subset
    (by
      intro path hfire
      exact hdone path
        (path.state_after_boundedIntended_of_firesIntendedContiguouslyAt
          I hfire))
    (by
      intro path hfire hdone_path
      exact hcorrect path
        (path.state_after_boundedIntended_of_firesIntendedContiguouslyAt
          I hfire)
        hdone_path)

def boundedIntendedFiresModuleContract_ofEventBounds_selfBounds
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B_corr.event)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedFiresModuleContract_ofEventBounds
    I
    t
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_subset
    hcorr_subset
    hdone
    hcorrect

def boundedIntendedWinsRaceAtSuccessContract_of_intendedFiresEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t I.toIntendedSchedule) ⊆ B.event)
    (hnotBad : forall i, i ∈ I.schedule -> Not (Bad i)) :
    Probability.SuccessContract L.prob :=
  L.intendedWinsRaceAtSuccessContract_of_intendedFiresEventBound
    Bad I.toIntendedSchedule t B hsubset
    (by
      intro i hi
      exact hnotBad i hi)

def boundedIntendedFiresCompletionContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.CompletionContract L.prob :=
  L.intendedFiresCompletionContract_ofFiresListAtEventBound
    I.toIntendedSchedule t B hsubset hstart

def boundedIntendedFiresSuccessContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.boundedIntendedFiresCompletionContract_ofFiresListAtEventBound
      I t B hsubset hstart)

def boundedIntendedFiresCorrectnessContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.intendedFiresCorrectnessContract_ofFiresListAtEventBound
    I.toIntendedSchedule t done correct B hsubset hstart
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.BoundedIntendedSchedule.firingCount,
          Network.BoundedIntendedSchedule.toIntendedSchedule] using hendpoint) hdone)

def boundedIntendedFiresDeadlineContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.FiresListAt t I.schedule)
    (fun _path => t + I.firingCount)
    (t + bound)
    B
    hsubset
    (by
      intro _path _hfire
      exact Nat.add_le_add_left I.firingCount_le_bound t)

def boundedIntendedWinsRaceAtSuccessContract_ofFiresListAtEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hNoBad :
      forall omega,
        (L.path omega).NoBadFiresBefore Bad t (t + bound)) :
    Probability.SuccessContract L.prob :=
  Probability.SuccessContract.ofEventBound
    L.probAxioms
    (fun omega =>
      (L.path omega).IntendedWinsRaceAt Bad t I.toIntendedSchedule)
    B
    (by
      intro omega hnotWin
      apply hsubset
      intro hfires
      exact hnotWin
        (Network.Path.intendedWinsRaceAt_of_bounded_parts
          I (hstart omega) hfires (hNoBad omega)))

def boundedIntendedFiresModuleContract_ofFiresListAtEventBounds
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofEventBounds
    done
    correct
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    (by
      intro omega hnotDone
      apply hlive_subset
      intro hfire
      exact hnotDone
        (hdone (L.path omega)
          ((L.path omega).state_after_boundedIntended_of_firesListAt
            I (hstart omega) hfire)))
    (by
      intro omega hwrong
      apply hcorr_subset
      intro hfire
      exact hwrong.2
        (hcorrect (L.path omega)
          ((L.path omega).state_after_boundedIntended_of_firesListAt
            I (hstart omega) hfire)
          hwrong.1))

def boundedIntendedFiresModuleContract_ofFiresListAtEventBounds_selfBounds
    (L : JumpPathLaw N Omega)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t I.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedFiresModuleContract_ofFiresListAtEventBounds
    I
    t
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_subset
    hcorr_subset
    hstart
    hdone
    hcorrect

def boundedIntendedWinsRaceCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B.event) :
    Probability.CompletionContract L.prob :=
  L.intendedWinsRaceCompletionContract_ofEventBound
    Bad I.toIntendedSchedule t B hsubset

def boundedIntendedWinsRaceSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B.event) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.boundedIntendedWinsRaceCompletionContract_ofEventBound
      Bad I t B hsubset)

def boundedIntendedWinsRaceCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B.event)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.intendedWinsRaceCorrectnessContract_ofEventBound
    Bad I.toIntendedSchedule t done correct B hsubset
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.BoundedIntendedSchedule.firingCount,
          Network.BoundedIntendedSchedule.toIntendedSchedule] using hendpoint) hdone)

def boundedIntendedWinsRaceDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.IntendedWinsRaceAt Bad t I.toIntendedSchedule)
    (fun _path => t + I.firingCount)
    (t + bound)
    B
    hsubset
    (by
      intro _path _hwin
      exact Nat.add_le_add_left I.firingCount_le_bound t)

def boundedIntendedWinsRaceModuleContract_ofEventBounds
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B_corr.event)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofWitnessEventBounds
    (fun path => path.IntendedWinsRaceAt Bad t I.toIntendedSchedule)
    (fun path => path.IntendedWinsRaceAt Bad t I.toIntendedSchedule)
    done
    correct
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    hlive_subset
    hcorr_subset
    (by
      intro path hwin
      exact hdone path
        (path.state_after_boundedIntendedWinsRaceAt Bad I hwin))
    (by
      intro path hwin hdone_path
      exact hcorrect path
        (path.state_after_boundedIntendedWinsRaceAt Bad I hwin)
        hdone_path)

def boundedIntendedWinsRaceModuleContract_ofEventBounds_selfBounds
    (L : JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t I.toIntendedSchedule) ⊆ B_corr.event)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedWinsRaceModuleContract_ofEventBounds
    Bad
    I
    t
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_subset
    hcorr_subset
    hdone
    hcorrect

def boundedIntendedRaceCompletionContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.CompletionContract L.prob :=
  L.intendedRaceCompletionContract_ofEventBound
    R I.toIntendedSchedule t B hsubset hstart

def boundedIntendedRaceSuccessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0) :
    Probability.SuccessContract L.prob :=
  Probability.CompletionContract.toSuccessContract
    (L.boundedIntendedRaceCompletionContract_ofEventBound
      R I t B hsubset hstart)

def boundedIntendedRaceCorrectnessContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.intendedRaceCorrectnessContract_ofEventBound
    R I.toIntendedSchedule t done correct B hsubset hstart
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.BoundedIntendedSchedule.firingCount,
          Network.BoundedIntendedSchedule.toIntendedSchedule] using hendpoint) hdone)

def boundedIntendedRaceDeadlineContract_ofEventBound
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.pathDeadlineContract_ofWitnessEventBound
    (fun path => R.WinsListAt path t I.schedule)
    (fun _path => t + I.firingCount)
    (t + bound)
    B
    hsubset
    (by
      intro _path _hwin
      exact Nat.add_le_add_left I.firingCount_le_bound t)

def boundedIntendedRaceModuleContract_ofEventBounds
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.pathModuleContract_ofEventBounds
    done
    correct
    liveBound
    corrBound
    B_live
    B_corr
    hlive_bound
    hcorr_bound
    (by
      intro omega hnotDone
      apply hlive_subset
      intro hwins
      have hfires : (L.path omega).FiresListAt t I.schedule :=
        R.firesListAt_of_winsListAt (L.path omega) hwins
      exact hnotDone
        (hdone (L.path omega)
          ((L.path omega).state_after_boundedIntended_of_firesListAt
            I (hstart omega) hfires)))
    (by
      intro omega hwrong
      apply hcorr_subset
      intro hwins
      have hfires : (L.path omega).FiresListAt t I.schedule :=
        R.firesListAt_of_winsListAt (L.path omega) hwins
      exact hwrong.2
        (hcorrect (L.path omega)
          ((L.path omega).state_after_boundedIntended_of_firesListAt
            I (hstart omega) hfires)
          hwrong.1))

def boundedIntendedRaceModuleContract_ofEventBounds_selfBounds
    (L : JumpPathLaw N Omega)
    (R : RacePredicate N)
    {bound : Nat} {z0 z1 : State S}
    (I : N.BoundedIntendedSchedule bound z0 z1) (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (L.path omega) t I.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = z0)
    (hdone :
      forall path,
        path.state (t + I.firingCount) = z1 -> done path)
    (hcorrect :
      forall path,
        path.state (t + I.firingCount) = z1 ->
          done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedRaceModuleContract_ofEventBounds
    R
    I
    t
    done
    correct
    B_live.bound
    B_corr.bound
    B_live
    B_corr
    le_rfl
    le_rfl
    hlive_subset
    hcorr_subset
    hstart
    hdone
    hcorrect

end JumpPathLaw

namespace InitialJumpPathLaw

variable {S : Type u} {N : Network.{u, v} S}
variable {Omega : Type w} {z0 z1 : State S}

def intendedFiresCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresIntendedContiguouslyAt 0 I) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.intendedFiresCompletionContract_ofEventBound I 0 B hsubset

def intendedFiresSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresIntendedContiguouslyAt 0 I) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.intendedFiresCompletionAtZero_ofEventBound I B hsubset)

def intendedFiresCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresIntendedContiguouslyAt 0 I) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.intendedFiresCorrectnessContract_ofEventBound
    I 0 done correct B hsubset
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.IntendedSchedule.firingCount] using hendpoint) hdone)

def intendedFiresDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresIntendedContiguouslyAt 0 I) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.FiresIntendedContiguouslyAt 0 I)
    (fun _path => I.firingCount)
    I.firingCount
    B
    hsubset
    (by
      intro _path _hfire
      exact le_rfl)

def intendedFiresCompletionAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresListAt 0 I.schedule) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.intendedFiresCompletionContract_ofFiresListAtEventBound
    I 0 B hsubset X.initial

def intendedFiresSuccessAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresListAt 0 I.schedule) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.intendedFiresCompletionAtZero_ofFiresListAtEventBound I B hsubset)

def intendedFiresCorrectnessAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresListAt 0 I.schedule) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.intendedFiresCorrectnessContract_ofFiresListAtEventBound
    I 0 done correct B hsubset X.initial
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.IntendedSchedule.firingCount] using hendpoint) hdone)

def intendedFiresDeadlineAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).FiresListAt 0 I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.FiresListAt 0 I.schedule)
    (fun _path => I.firingCount)
    I.firingCount
    B
    hsubset
    (by
      intro _path _hfire
      exact le_rfl)

def intendedWinsRaceCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).IntendedWinsRaceAt Bad 0 I) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.intendedWinsRaceCompletionContract_ofEventBound Bad I 0 B hsubset

def intendedWinsRaceSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).IntendedWinsRaceAt Bad 0 I) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.intendedWinsRaceCompletionAtZero_ofEventBound Bad I B hsubset)

def intendedWinsRaceCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    (I : N.IntendedSchedule z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).IntendedWinsRaceAt Bad 0 I) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.intendedWinsRaceCorrectnessContract_ofEventBound
    Bad I 0 done correct B hsubset
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.IntendedSchedule.firingCount] using hendpoint) hdone)

def intendedWinsRaceDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (X.law.path omega).IntendedWinsRaceAt Bad 0 I) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.IntendedWinsRaceAt Bad 0 I)
    (fun _path => I.firingCount)
    I.firingCount
    B
    hsubset
    (by
      intro _path _hwin
      exact le_rfl)

def intendedRaceCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.intendedRaceCompletionContract_ofEventBound
    R I 0 B hsubset X.initial

def intendedRaceSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.intendedRaceCompletionAtZero_ofEventBound R I B hsubset)

def intendedRaceCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.intendedRaceCorrectnessContract_ofEventBound
    R I 0 done correct B hsubset X.initial
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa [Network.IntendedSchedule.firingCount] using hendpoint) hdone)

def intendedRaceDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.pathDeadlineContract_ofWitnessEventBound
    (fun path => R.WinsListAt path 0 I.schedule)
    (fun _path => I.firingCount)
    I.firingCount
    B
    hsubset
    (by
      intro _path _hwin
      exact le_rfl)

def intendedDoneAtCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ X.law.intendedDoneAt I 0) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.intendedDoneAtCompletionContract_ofEventBound I 0 B hsubset

def intendedDoneAtSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ X.law.intendedDoneAt I 0) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.intendedDoneAtCompletionAtZero_ofEventBound I B hsubset)

def intendedDoneAtCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ X.law.intendedDoneAt I 0) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.intendedDoneAtCorrectnessContract_ofEventBound
    I 0 done correct B hsubset
    (by
      intro path hdoneAt hdone
      exact hcorrect path (by
        simpa [Network.IntendedSchedule.firingCount] using hdoneAt) hdone)

def intendedDoneAtDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (I : N.IntendedSchedule z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈ X.law.intendedDoneAt I 0) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.pathDeadlineContract_ofWitnessEventBound
    (fun path => path.state I.firingCount = z1)
    (fun _path => I.firingCount)
    I.firingCount
    B
    (by
      intro omega hnotEndpoint
      apply hsubset
      intro hdone
      exact hnotEndpoint (by
        simpa [JumpPathLaw.intendedDoneAt,
          Network.IntendedSchedule.firingCount] using hdone))
    (by
      intro _path _hendpoint
      exact le_rfl)

def boundedIntendedDoneAtCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈
          X.law.intendedDoneAt I.toIntendedSchedule 0) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.boundedIntendedDoneAtCompletionContract_ofEventBound
    I 0 B hsubset

def boundedIntendedDoneAtSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈
          X.law.intendedDoneAt I.toIntendedSchedule 0) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.boundedIntendedDoneAtCompletionAtZero_ofEventBound I B hsubset)

def boundedIntendedDoneAtCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈
          X.law.intendedDoneAt I.toIntendedSchedule 0) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.boundedIntendedDoneAtCorrectnessContract_ofEventBound
    I 0 done correct B hsubset
    (by
      intro path hdoneAt hdone
      exact hcorrect path (by
        simpa using hdoneAt) hdone)

def boundedIntendedDoneAtDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => omega ∈
          X.law.intendedDoneAt I.toIntendedSchedule 0) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.boundedIntendedDoneAtDeadlineContract_ofEventBound
    I 0 B hsubset

def boundedIntendedFiresCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresIntendedContiguouslyAt
            0 I.toIntendedSchedule) ⊆ B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.boundedIntendedFiresCompletionContract_ofEventBound
    I 0 B hsubset

def boundedIntendedFiresSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresIntendedContiguouslyAt
            0 I.toIntendedSchedule) ⊆ B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.boundedIntendedFiresCompletionAtZero_ofEventBound I B hsubset)

def boundedIntendedFiresCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresIntendedContiguouslyAt
            0 I.toIntendedSchedule) ⊆ B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.boundedIntendedFiresCorrectnessContract_ofEventBound
    I 0 done correct B hsubset
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa using hendpoint) hdone)

def boundedIntendedFiresDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresIntendedContiguouslyAt
            0 I.toIntendedSchedule) ⊆ B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.boundedIntendedFiresDeadlineContract_ofEventBound
    I 0 B hsubset

def boundedIntendedFiresCompletionAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresListAt 0 I.schedule) ⊆ B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.boundedIntendedFiresCompletionContract_ofFiresListAtEventBound
    I 0 B hsubset X.initial

def boundedIntendedFiresSuccessAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresListAt 0 I.schedule) ⊆ B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.boundedIntendedFiresCompletionAtZero_ofFiresListAtEventBound
      I B hsubset)

def boundedIntendedFiresCorrectnessAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresListAt 0 I.schedule) ⊆ B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.boundedIntendedFiresCorrectnessContract_ofFiresListAtEventBound
    I 0 done correct B hsubset X.initial
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa using hendpoint) hdone)

def boundedIntendedFiresDeadlineAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresListAt 0 I.schedule) ⊆ B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.boundedIntendedFiresDeadlineContract_ofFiresListAtEventBound
    I 0 B hsubset

def boundedIntendedWinsRaceAtSuccessAtZero_ofFiresListAtEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).FiresListAt 0 I.schedule) ⊆ B.event)
    (hNoBad :
      forall omega,
        (X.law.path omega).NoBadFiresBefore Bad 0 bound) :
    Probability.SuccessContract X.law.prob :=
  X.law.boundedIntendedWinsRaceAtSuccessContract_ofFiresListAtEventBound
    Bad I 0 B hsubset X.initial
    (by
      intro omega
      simpa using hNoBad omega)

def boundedIntendedWinsRaceCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).IntendedWinsRaceAt
            Bad 0 I.toIntendedSchedule) ⊆ B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.boundedIntendedWinsRaceCompletionContract_ofEventBound
    Bad I 0 B hsubset

def boundedIntendedWinsRaceSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).IntendedWinsRaceAt
            Bad 0 I.toIntendedSchedule) ⊆ B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.boundedIntendedWinsRaceCompletionAtZero_ofEventBound
      Bad I B hsubset)

def boundedIntendedWinsRaceCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).IntendedWinsRaceAt
            Bad 0 I.toIntendedSchedule) ⊆ B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.boundedIntendedWinsRaceCorrectnessContract_ofEventBound
    Bad I 0 done correct B hsubset
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa using hendpoint) hdone)

def boundedIntendedWinsRaceDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (Bad : N.BadIndexSet)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (X.law.path omega).IntendedWinsRaceAt
            Bad 0 I.toIntendedSchedule) ⊆ B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.boundedIntendedWinsRaceDeadlineContract_ofEventBound
    Bad I 0 B hsubset

def boundedIntendedRaceCompletionAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event) :
    Probability.CompletionContract X.law.prob :=
  X.law.boundedIntendedRaceCompletionContract_ofEventBound
    R I 0 B hsubset X.initial

def boundedIntendedRaceSuccessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event) :
    Probability.SuccessContract X.law.prob :=
  Probability.CompletionContract.toSuccessContract
    (X.boundedIntendedRaceCompletionAtZero_ofEventBound R I B hsubset)

def boundedIntendedRaceCorrectnessAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state I.firingCount = z1 ->
          done path -> correct path) :
    Probability.CorrectnessContract X.law.prob :=
  X.law.boundedIntendedRaceCorrectnessContract_ofEventBound
    R I 0 done correct B hsubset X.initial
    (by
      intro path hendpoint hdone
      exact hcorrect path (by
        simpa using hendpoint) hdone)

def boundedIntendedRaceDeadlineAtZero_ofEventBound
    (X : InitialJumpPathLaw N z0 Omega)
    (R : RacePredicate N)
    {bound : Nat}
    (I : N.BoundedIntendedSchedule bound z0 z1)
    (B : Probability.EventBound X.law.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => R.WinsListAt (X.law.path omega) 0 I.schedule) ⊆
          B.event) :
    Probability.DeadlineContract X.law.prob :=
  X.law.boundedIntendedRaceDeadlineContract_ofEventBound
    R I 0 B hsubset

end InitialJumpPathLaw

end Stochastic

end Ripple.sCRNUniversality

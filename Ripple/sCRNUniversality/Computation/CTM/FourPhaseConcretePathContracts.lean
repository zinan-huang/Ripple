import Ripple.sCRNUniversality.Computation.CTM.FourPhaseConcreteModule
import Ripple.sCRNUniversality.Probability.PathContracts

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseConcrete

namespace ConcreteGoodStepSchedule

universe u v w x

variable {Q : Type u} {s : Nat}
variable {CSp : Type v} [Fintype CSp]
variable {N : Network.{v, w} CSp}
variable {enc : MicroCfg Q s -> State CSp}
variable {Foot : MicroCfg Q s -> MicroCfg Q s -> CSp -> Prop}
variable {Lbound : Nat} {c c' : MicroCfg Q s}
variable {Omega : Type x}

def boundedIntendedFiresCompletionContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event) :
    Probability.CompletionContract L.prob :=
  L.boundedIntendedFiresCompletionContract_ofEventBound
    Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedFiresSuccessContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.boundedIntendedFiresSuccessContract_ofEventBound
    Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedFiresCorrectnessContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.boundedIntendedFiresCorrectnessContract_ofEventBound
    Sched.toBoundedIntendedSchedule t done correct B hsubset hcorrect

def boundedIntendedFiresDeadlineContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.boundedIntendedFiresDeadlineContract_ofEventBound
    Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedFiresModuleContract_ofEventBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_corr.event)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedFiresModuleContract_ofEventBounds
    Sched.toBoundedIntendedSchedule t done correct
    liveBound corrBound B_live B_corr
    hlive_bound hcorr_bound hlive_subset hcorr_subset
    hdone hcorrect

def boundedIntendedFiresModuleContract_ofEventBounds_selfBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_corr.event)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedFiresModuleContract_ofEventBounds_selfBounds
    Sched.toBoundedIntendedSchedule t done correct
    B_live B_corr hlive_subset hcorr_subset hdone hcorrect

def boundedIntendedWinsRaceAtSuccessContract_of_intendedFiresEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresIntendedContiguouslyAt
            t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event)
    (hnotBad : forall i, i ∈ Sched.schedule -> Not (Bad i)) :
    Probability.SuccessContract L.prob :=
  L.boundedIntendedWinsRaceAtSuccessContract_of_intendedFiresEventBound
    Bad Sched.toBoundedIntendedSchedule t B hsubset
    (by
      intro i hi
      exact hnotBad i (by
        simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using hi))

def boundedIntendedFiresCompletionContract_ofFiresListAtEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c) :
    Probability.CompletionContract L.prob :=
  L.boundedIntendedFiresCompletionContract_ofFiresListAtEventBound
    Sched.toBoundedIntendedSchedule t B
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hsubset)
    hstart

def boundedIntendedFiresSuccessContract_ofFiresListAtEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c) :
    Probability.SuccessContract L.prob :=
  L.boundedIntendedFiresSuccessContract_ofFiresListAtEventBound
    Sched.toBoundedIntendedSchedule t B
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hsubset)
    hstart

def boundedIntendedFiresCorrectnessContract_ofFiresListAtEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.boundedIntendedFiresCorrectnessContract_ofFiresListAtEventBound
    Sched.toBoundedIntendedSchedule t done correct B
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hsubset)
    hstart
    hcorrect

def boundedIntendedFiresDeadlineContract_ofFiresListAtEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.boundedIntendedFiresDeadlineContract_ofFiresListAtEventBound
    Sched.toBoundedIntendedSchedule t B
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hsubset)

def boundedIntendedWinsRaceAtSuccessContract_ofFiresListAtEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hNoBad :
      forall omega,
        (L.path omega).NoBadFiresBefore Bad t (t + Lbound)) :
    Probability.SuccessContract L.prob :=
  L.boundedIntendedWinsRaceAtSuccessContract_ofFiresListAtEventBound
    Bad Sched.toBoundedIntendedSchedule t B
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hsubset)
    hstart
    hNoBad

def boundedIntendedFiresModuleContract_ofFiresListAtEventBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedFiresModuleContract_ofFiresListAtEventBounds
    Sched.toBoundedIntendedSchedule t done correct
    liveBound corrBound B_live B_corr
    hlive_bound hcorr_bound
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hlive_subset)
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hcorr_subset)
    hstart
    hdone
    hcorrect

def boundedIntendedFiresModuleContract_ofFiresListAtEventBounds_selfBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega => (L.path omega).FiresListAt t Sched.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedFiresModuleContract_ofFiresListAtEventBounds_selfBounds
    Sched.toBoundedIntendedSchedule t done correct
    B_live B_corr
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hlive_subset)
    (by
      simpa [ConcreteGoodStepSchedule.toBoundedIntendedSchedule] using
        hcorr_subset)
    hstart hdone hcorrect

def boundedIntendedWinsRaceCompletionContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event) :
    Probability.CompletionContract L.prob :=
  L.boundedIntendedWinsRaceCompletionContract_ofEventBound
    Bad Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedWinsRaceSuccessContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event) :
    Probability.SuccessContract L.prob :=
  L.boundedIntendedWinsRaceSuccessContract_ofEventBound
    Bad Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedWinsRaceCorrectnessContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.boundedIntendedWinsRaceCorrectnessContract_ofEventBound
    Bad Sched.toBoundedIntendedSchedule t done correct B hsubset hcorrect

def boundedIntendedWinsRaceDeadlineContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.boundedIntendedWinsRaceDeadlineContract_ofEventBound
    Bad Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedWinsRaceModuleContract_ofEventBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_corr.event)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedWinsRaceModuleContract_ofEventBounds
    Bad Sched.toBoundedIntendedSchedule t done correct
    liveBound corrBound B_live B_corr
    hlive_bound hcorr_bound hlive_subset hcorr_subset
    hdone hcorrect

def boundedIntendedWinsRaceModuleContract_ofEventBounds_selfBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (Bad : N.BadIndexSet)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).IntendedWinsRaceAt
            Bad t Sched.toBoundedIntendedSchedule.toIntendedSchedule) ⊆
          B_corr.event)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedWinsRaceModuleContract_ofEventBounds_selfBounds
    Bad Sched.toBoundedIntendedSchedule t done correct
    B_live B_corr hlive_subset hcorr_subset hdone hcorrect

def boundedIntendedRaceCompletionContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (R : Stochastic.RacePredicate N)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c) :
    Probability.CompletionContract L.prob :=
  L.boundedIntendedRaceCompletionContract_ofEventBound
    R Sched.toBoundedIntendedSchedule t B hsubset hstart

def boundedIntendedRaceSuccessContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (R : Stochastic.RacePredicate N)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c) :
    Probability.SuccessContract L.prob :=
  L.boundedIntendedRaceSuccessContract_ofEventBound
    R Sched.toBoundedIntendedSchedule t B hsubset hstart

def boundedIntendedRaceCorrectnessContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (R : Stochastic.RacePredicate N)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' ->
          done path -> correct path) :
    Probability.CorrectnessContract L.prob :=
  L.boundedIntendedRaceCorrectnessContract_ofEventBound
    R Sched.toBoundedIntendedSchedule t done correct B hsubset hstart hcorrect

def boundedIntendedRaceDeadlineContract_ofEventBound
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (R : Stochastic.RacePredicate N)
    (t : Nat)
    (B : Probability.EventBound L.prob)
    (hsubset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B.event) :
    Probability.DeadlineContract L.prob :=
  L.boundedIntendedRaceDeadlineContract_ofEventBound
    R Sched.toBoundedIntendedSchedule t B hsubset

def boundedIntendedRaceModuleContract_ofEventBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (R : Stochastic.RacePredicate N)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (liveBound corrBound : ENNReal)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_bound : B_live.bound <= liveBound)
    (hcorr_bound : B_corr.bound <= corrBound)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedRaceModuleContract_ofEventBounds
    R Sched.toBoundedIntendedSchedule t done correct
    liveBound corrBound B_live B_corr
    hlive_bound hcorr_bound hlive_subset hcorr_subset
    hstart hdone hcorrect

def boundedIntendedRaceModuleContract_ofEventBounds_selfBounds
    (Sched : ConcreteGoodStepSchedule N enc Foot Lbound c c')
    (L : Stochastic.JumpPathLaw N Omega)
    (R : Stochastic.RacePredicate N)
    (t : Nat)
    (done correct : N.Path -> Prop)
    (B_live B_corr : Probability.EventBound L.prob)
    (hlive_subset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B_live.event)
    (hcorr_subset :
      Probability.ErrorEvent
        (fun omega =>
          R.WinsListAt
            (L.path omega) t Sched.toBoundedIntendedSchedule.schedule) ⊆
          B_corr.event)
    (hstart : forall omega, (L.path omega).state t = enc c)
    (hdone :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path)
    (hcorrect :
      forall path,
        path.state (t + Sched.toBoundedIntendedSchedule.firingCount) =
          enc c' -> done path -> correct path) :
    Probability.ModuleContract L.prob :=
  L.boundedIntendedRaceModuleContract_ofEventBounds_selfBounds
    R Sched.toBoundedIntendedSchedule t done correct
    B_live B_corr hlive_subset hcorr_subset hstart hdone hcorrect

end ConcreteGoodStepSchedule

end FourPhaseConcrete

end CTM

end Ripple.sCRNUniversality

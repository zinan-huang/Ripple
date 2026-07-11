import Ripple.sCRNUniversality.Computation.CRNRealization
import Ripple.sCRNUniversality.Core.Schedule

namespace Ripple.sCRNUniversality

universe u v w

namespace StepwiseRealization

variable {A : DetSystem.{u}} {S : Type v} [Fintype S]
variable {N : Network.{v, w} S}

/--
Package the deterministic schedule chosen by a one-step realization.

This is only a scheduled `Exec` witness; it does not assert that arbitrary
paths or stochastic executions follow the schedule.
-/
noncomputable def intendedSchedule_of_step
    (R : StepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.IntendedSchedule (R.enc x) (R.enc y) where
  schedule := Classical.choose (R.step_exec h)
  exec := Classical.choose_spec (R.step_exec h)

theorem exec_of_intendedSchedule_of_step
    (R : StepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Exec (R.enc x) (R.enc y)
      (R.intendedSchedule_of_step h).schedule :=
  (R.intendedSchedule_of_step h).exec

theorem intended_reaches_of_step
    (R : StepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.intendedSchedule_of_step h).reaches

/--
Package the deterministic schedule chosen by `exec_of_steps`.

This is a deterministic reachability witness, not a scheduler-fairness or
stochastic completion claim.
-/
noncomputable def intendedSchedule_of_steps
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.IntendedSchedule (R.enc x) (R.enc y) where
  schedule := Classical.choose (R.exec_of_steps h)
  exec := Classical.choose_spec (R.exec_of_steps h)

theorem exec_of_intendedSchedule_of_steps
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Exec (R.enc x) (R.enc y)
      (R.intendedSchedule_of_steps h).schedule :=
  (R.intendedSchedule_of_steps h).exec

theorem intended_reaches_of_steps
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.intendedSchedule_of_steps h).reaches

theorem state_after_step_of_intendedWinsRaceAt
    (R : StepwiseRealization A N) {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t (R.intendedSchedule_of_step h)) :
    path.state (t + (R.intendedSchedule_of_step h).firingCount) =
      R.enc y := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.intendedSchedule_of_step h)
      hwin

theorem state_after_steps_of_intendedWinsRaceAt
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t (R.intendedSchedule_of_steps h)) :
    path.state (t + (R.intendedSchedule_of_steps h).firingCount) =
      R.enc y := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.intendedSchedule_of_steps h)
      hwin

noncomputable def intendedSchedule_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps (sim.step_ok h)

theorem exec_of_intendedSchedule_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_kStepSim_step
        (sim := sim) R h).schedule :=
  (intendedSchedule_of_kStepSim_step (sim := sim) R h).exec

theorem intended_reaches_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_kStepSim_step (sim := sim) R h).reaches

theorem state_after_kStepSim_step_of_intendedWinsRaceAt
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_kStepSim_step (sim := sim) R h)) :
    path.state
        (t +
          (intendedSchedule_of_kStepSim_step
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_kStepSim_step (sim := sim) R h)
      hwin

noncomputable def intendedSchedule_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps (KStepSim.steps? (sim := sim) h)

theorem exec_of_intendedSchedule_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_kStepSim_steps
        (sim := sim) R h).schedule :=
  (intendedSchedule_of_kStepSim_steps (sim := sim) R h).exec

theorem intended_reaches_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_kStepSim_steps (sim := sim) R h).reaches

theorem state_after_kStepSim_steps_of_intendedWinsRaceAt
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_kStepSim_steps (sim := sim) R h)) :
    path.state
        (t +
          (intendedSchedule_of_kStepSim_steps
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_kStepSim_steps (sim := sim) R h)
      hwin

noncomputable def intendedSchedule_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps
    (sim.run_ok 1 (DetSystem.steps?_one_of_step? A h))

theorem exec_of_intendedSchedule_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_runSim_step
        (sim := sim) R h).schedule :=
  (intendedSchedule_of_runSim_step (sim := sim) R h).exec

theorem intended_reaches_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_runSim_step (sim := sim) R h).reaches

theorem state_after_runSim_step_of_intendedWinsRaceAt
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_runSim_step (sim := sim) R h)) :
    path.state
        (t +
          (intendedSchedule_of_runSim_step
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_runSim_step (sim := sim) R h)
      hwin

noncomputable def intendedSchedule_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps (sim.run_ok n h)

theorem exec_of_intendedSchedule_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_runSim_steps
        (sim := sim) R h).schedule :=
  (intendedSchedule_of_runSim_steps (sim := sim) R h).exec

theorem intended_reaches_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_runSim_steps (sim := sim) R h).reaches

theorem state_after_runSim_steps_of_intendedWinsRaceAt
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : StepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_runSim_steps (sim := sim) R h)) :
    path.state
        (t +
          (intendedSchedule_of_runSim_steps
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_runSim_steps (sim := sim) R h)
      hwin

end StepwiseRealization

namespace InvariantStepwiseRealization

variable {A : DetSystem.{u}} {S : Type v} [Fintype S]
variable {N : Network.{v, w} S} {Inv : A.Cfg -> Prop}

/--
Package the deterministic schedule chosen by an invariant one-step
realization. The invariant hypothesis is the same one required by
`step_exec`.
-/
noncomputable def intendedSchedule_of_step
    (R : InvariantStepwiseRealization A N Inv) {x y : A.Cfg}
    (hx : Inv x) (h : A.step? x = some y) :
    N.IntendedSchedule (R.enc x) (R.enc y) where
  schedule := Classical.choose (R.step_exec hx h)
  exec := Classical.choose_spec (R.step_exec hx h)

theorem exec_of_intendedSchedule_of_step
    (R : InvariantStepwiseRealization A N Inv) {x y : A.Cfg}
    (hx : Inv x) (h : A.step? x = some y) :
    N.Exec (R.enc x) (R.enc y)
      (R.intendedSchedule_of_step hx h).schedule :=
  (R.intendedSchedule_of_step hx h).exec

theorem intended_reaches_of_step
    (R : InvariantStepwiseRealization A N Inv) {x y : A.Cfg}
    (hx : Inv x) (h : A.step? x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.intendedSchedule_of_step hx h).reaches

noncomputable def intendedSchedule_of_steps
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg}
    (hx : Inv x) (h : A.steps? n x = some y) :
    N.IntendedSchedule (R.enc x) (R.enc y) where
  schedule := Classical.choose (R.exec_of_steps hx h)
  exec := Classical.choose_spec (R.exec_of_steps hx h)

theorem exec_of_intendedSchedule_of_steps
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg}
    (hx : Inv x) (h : A.steps? n x = some y) :
    N.Exec (R.enc x) (R.enc y)
      (R.intendedSchedule_of_steps hx h).schedule :=
  (R.intendedSchedule_of_steps hx h).exec

theorem intended_reaches_of_steps
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg}
    (hx : Inv x) (h : A.steps? n x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.intendedSchedule_of_steps hx h).reaches

theorem state_after_step_of_intendedWinsRaceAt
    (R : InvariantStepwiseRealization A N Inv) {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hx : Inv x) (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t (R.intendedSchedule_of_step hx h)) :
    path.state (t + (R.intendedSchedule_of_step hx h).firingCount) =
      R.enc y := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.intendedSchedule_of_step hx h)
      hwin

theorem state_after_steps_of_intendedWinsRaceAt
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hx : Inv x) (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t (R.intendedSchedule_of_steps hx h)) :
    path.state (t + (R.intendedSchedule_of_steps hx h).firingCount) =
      R.enc y := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (R.intendedSchedule_of_steps hx h)
      hwin

noncomputable def intendedSchedule_of_kStepSim_step
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps hx (sim.step_ok h)

theorem exec_of_intendedSchedule_of_kStepSim_step
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_kStepSim_step
        (sim := sim) R hx h).schedule :=
  (intendedSchedule_of_kStepSim_step
    (sim := sim) R hx h).exec

theorem intended_reaches_of_kStepSim_step
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_kStepSim_step
    (sim := sim) R hx h).reaches

theorem state_after_kStepSim_step_of_intendedWinsRaceAt
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_kStepSim_step
          (sim := sim) R hx h)) :
    path.state
        (t +
          (intendedSchedule_of_kStepSim_step
            (sim := sim) R hx h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_kStepSim_step
        (sim := sim) R hx h)
      hwin

noncomputable def intendedSchedule_of_kStepSim_steps
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps hx (KStepSim.steps? (sim := sim) h)

theorem exec_of_intendedSchedule_of_kStepSim_steps
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_kStepSim_steps
        (sim := sim) R hx h).schedule :=
  (intendedSchedule_of_kStepSim_steps
    (sim := sim) R hx h).exec

theorem intended_reaches_of_kStepSim_steps
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_kStepSim_steps
    (sim := sim) R hx h).reaches

theorem state_after_kStepSim_steps_of_intendedWinsRaceAt
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_kStepSim_steps
          (sim := sim) R hx h)) :
    path.state
        (t +
          (intendedSchedule_of_kStepSim_steps
            (sim := sim) R hx h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_kStepSim_steps
        (sim := sim) R hx h)
      hwin

noncomputable def intendedSchedule_of_runSim_step
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps hx
    (sim.run_ok 1 (DetSystem.steps?_one_of_step? A h))

theorem exec_of_intendedSchedule_of_runSim_step
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_runSim_step
        (sim := sim) R hx h).schedule :=
  (intendedSchedule_of_runSim_step
    (sim := sim) R hx h).exec

theorem intended_reaches_of_runSim_step
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_runSim_step
    (sim := sim) R hx h).reaches

theorem state_after_runSim_step_of_intendedWinsRaceAt
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hx : InvB (sim.enc x))
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_runSim_step
          (sim := sim) R hx h)) :
    path.state
        (t +
          (intendedSchedule_of_runSim_step
            (sim := sim) R hx h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_runSim_step
        (sim := sim) R hx h)
      hwin

noncomputable def intendedSchedule_of_runSim_steps
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {n : Nat} {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.IntendedSchedule
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.intendedSchedule_of_steps hx (sim.run_ok n h)

theorem exec_of_intendedSchedule_of_runSim_steps
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {n : Nat} {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (intendedSchedule_of_runSim_steps
        (sim := sim) R hx h).schedule :=
  (intendedSchedule_of_runSim_steps
    (sim := sim) R hx h).exec

theorem intended_reaches_of_runSim_steps
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {n : Nat} {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (intendedSchedule_of_runSim_steps
    (sim := sim) R hx h).reaches

theorem state_after_runSim_steps_of_intendedWinsRaceAt
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    (sim : RunSim A B)
    (R : InvariantStepwiseRealization B N InvB)
    {n : Nat} {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_runSim_steps
          (sim := sim) R hx h)) :
    path.state
        (t +
          (intendedSchedule_of_runSim_steps
            (sim := sim) R hx h).firingCount) =
      R.enc (sim.enc y) := by
  simpa [Network.IntendedSchedule.firingCount] using
    path.state_after_intendedWinsRaceAt Bad
      (intendedSchedule_of_runSim_steps
        (sim := sim) R hx h)
      hwin

end InvariantStepwiseRealization

namespace BoundedStepwiseRealization

variable {A : DetSystem.{u}} {S : Type v} [Fintype S]
variable {N : Network.{v, w} S}

/--
Package the bounded deterministic schedule chosen by a one-step bounded
realization.
-/
noncomputable def boundedIntendedSchedule_of_step
    (R : BoundedStepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.BoundedIntendedSchedule R.step_len_bound (R.enc x) (R.enc y) where
  schedule := Classical.choose (R.step_exec_bounded h)
  exec := (Classical.choose_spec (R.step_exec_bounded h)).1
  length_bound := (Classical.choose_spec (R.step_exec_bounded h)).2

theorem exec_of_boundedIntendedSchedule_of_step
    (R : BoundedStepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Exec (R.enc x) (R.enc y)
      (R.boundedIntendedSchedule_of_step h).schedule :=
  (R.boundedIntendedSchedule_of_step h).exec

theorem boundedIntendedSchedule_firingCount_le_of_step
    (R : BoundedStepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    (R.boundedIntendedSchedule_of_step h).firingCount <=
      R.step_len_bound :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (R.boundedIntendedSchedule_of_step h)

theorem boundedIntended_reaches_of_step
    (R : BoundedStepwiseRealization A N) {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.boundedIntendedSchedule_of_step h).reaches

/--
Package the bounded deterministic schedule chosen by `exec_of_steps_bounded`.
-/
noncomputable def boundedIntendedSchedule_of_steps
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.BoundedIntendedSchedule
      (R.step_len_bound * n) (R.enc x) (R.enc y) where
  schedule := Classical.choose (R.exec_of_steps_bounded h)
  exec := (Classical.choose_spec (R.exec_of_steps_bounded h)).1
  length_bound := (Classical.choose_spec (R.exec_of_steps_bounded h)).2

theorem exec_of_boundedIntendedSchedule_of_steps
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Exec (R.enc x) (R.enc y)
      (R.boundedIntendedSchedule_of_steps h).schedule :=
  (R.boundedIntendedSchedule_of_steps h).exec

theorem boundedIntendedSchedule_firingCount_le_of_steps
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    (R.boundedIntendedSchedule_of_steps h).firingCount <=
      R.step_len_bound * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (R.boundedIntendedSchedule_of_steps h)

theorem boundedFiringCount_le_of_steps
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    (R.boundedIntendedSchedule_of_steps h).firingCount <=
      R.step_len_bound * n :=
  R.boundedIntendedSchedule_firingCount_le_of_steps h

theorem boundedIntended_reaches_of_steps
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.boundedIntendedSchedule_of_steps h).reaches

theorem state_after_step_of_boundedIntendedWinsRaceAt
    (R : BoundedStepwiseRealization A N) {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.boundedIntendedSchedule_of_step h).toIntendedSchedule) :
    path.state
        (t + (R.boundedIntendedSchedule_of_step h).firingCount) =
      R.enc y :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (R.boundedIntendedSchedule_of_step h)
    hwin

theorem state_after_steps_of_boundedIntendedWinsRaceAt
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (R.boundedIntendedSchedule_of_steps h).toIntendedSchedule) :
    path.state
        (t + (R.boundedIntendedSchedule_of_steps h).firingCount) =
      R.enc y :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (R.boundedIntendedSchedule_of_steps h)
    hwin

noncomputable def boundedIntendedSchedule_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.BoundedIntendedSchedule
      (R.step_len_bound * k)
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) := by
  simpa [BoundedStepwiseRealization.ofKStepSim] using
    ((BoundedStepwiseRealization.ofKStepSim
      (A := A) (N := N) sim R).boundedIntendedSchedule_of_step h)

theorem exec_of_boundedIntendedSchedule_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (boundedIntendedSchedule_of_kStepSim_step
        (sim := sim) R h).schedule :=
  (boundedIntendedSchedule_of_kStepSim_step
    (sim := sim) R h).exec

theorem boundedIntendedSchedule_firingCount_le_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    (boundedIntendedSchedule_of_kStepSim_step
      (sim := sim) R h).firingCount <=
      R.step_len_bound * k :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (boundedIntendedSchedule_of_kStepSim_step (sim := sim) R h)

theorem boundedIntended_reaches_of_kStepSim_step
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (boundedIntendedSchedule_of_kStepSim_step (sim := sim) R h).reaches

theorem state_after_kStepSim_step_of_boundedIntendedWinsRaceAt
    {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (boundedIntendedSchedule_of_kStepSim_step
          (sim := sim) R h).toIntendedSchedule) :
    path.state
        (t +
          (boundedIntendedSchedule_of_kStepSim_step
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (boundedIntendedSchedule_of_kStepSim_step (sim := sim) R h)
    hwin

noncomputable def boundedIntendedSchedule_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.BoundedIntendedSchedule
      ((R.step_len_bound * k) * n)
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) := by
  simpa [BoundedStepwiseRealization.ofKStepSim] using
    ((BoundedStepwiseRealization.ofKStepSim
      (A := A) (N := N) sim R).boundedIntendedSchedule_of_steps h)

theorem exec_of_boundedIntendedSchedule_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (boundedIntendedSchedule_of_kStepSim_steps
        (sim := sim) R h).schedule :=
  (boundedIntendedSchedule_of_kStepSim_steps
    (sim := sim) R h).exec

theorem boundedIntendedSchedule_firingCount_le_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    (boundedIntendedSchedule_of_kStepSim_steps
      (sim := sim) R h).firingCount <=
      (R.step_len_bound * k) * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (boundedIntendedSchedule_of_kStepSim_steps (sim := sim) R h)

theorem boundedIntended_reaches_of_kStepSim_steps
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (boundedIntendedSchedule_of_kStepSim_steps (sim := sim) R h).reaches

theorem state_after_kStepSim_steps_of_boundedIntendedWinsRaceAt
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (boundedIntendedSchedule_of_kStepSim_steps
          (sim := sim) R h).toIntendedSchedule) :
    path.state
        (t +
          (boundedIntendedSchedule_of_kStepSim_steps
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (boundedIntendedSchedule_of_kStepSim_steps (sim := sim) R h)
    hwin

noncomputable def boundedIntendedSchedule_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.BoundedIntendedSchedule
      (R.step_len_bound * sim.time 1)
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.boundedIntendedSchedule_of_steps
    (sim.run_ok 1 (DetSystem.steps?_one_of_step? A h))

theorem exec_of_boundedIntendedSchedule_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (boundedIntendedSchedule_of_runSim_step
        (sim := sim) R h).schedule :=
  (boundedIntendedSchedule_of_runSim_step
    (sim := sim) R h).exec

theorem boundedIntendedSchedule_firingCount_le_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    (boundedIntendedSchedule_of_runSim_step
      (sim := sim) R h).firingCount <=
      R.step_len_bound * sim.time 1 :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (boundedIntendedSchedule_of_runSim_step (sim := sim) R h)

theorem boundedIntended_reaches_of_runSim_step
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.step? x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (boundedIntendedSchedule_of_runSim_step (sim := sim) R h).reaches

theorem state_after_runSim_step_of_boundedIntendedWinsRaceAt
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.step? x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (boundedIntendedSchedule_of_runSim_step
          (sim := sim) R h).toIntendedSchedule) :
    path.state
        (t +
          (boundedIntendedSchedule_of_runSim_step
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (boundedIntendedSchedule_of_runSim_step (sim := sim) R h)
    hwin

noncomputable def boundedIntendedSchedule_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.BoundedIntendedSchedule
      (R.step_len_bound * sim.time n)
      (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.boundedIntendedSchedule_of_steps (sim.run_ok n h)

theorem exec_of_boundedIntendedSchedule_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y))
      (boundedIntendedSchedule_of_runSim_steps
        (sim := sim) R h).schedule :=
  (boundedIntendedSchedule_of_runSim_steps
    (sim := sim) R h).exec

theorem boundedIntendedSchedule_firingCount_le_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    (boundedIntendedSchedule_of_runSim_steps
      (sim := sim) R h).firingCount <=
      R.step_len_bound * sim.time n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (boundedIntendedSchedule_of_runSim_steps (sim := sim) R h)

theorem boundedIntended_reaches_of_runSim_steps
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (boundedIntendedSchedule_of_runSim_steps (sim := sim) R h).reaches

theorem state_after_runSim_steps_of_boundedIntendedWinsRaceAt
    {B : DetSystem.{u}}
    (sim : RunSim A B) (R : BoundedStepwiseRealization B N)
    {n : Nat} {x y : A.Cfg}
    {path : N.Path} {Bad : N.BadIndexSet} {t : Nat}
    (h : A.steps? n x = some y)
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (boundedIntendedSchedule_of_runSim_steps
          (sim := sim) R h).toIntendedSchedule) :
    path.state
        (t +
          (boundedIntendedSchedule_of_runSim_steps
            (sim := sim) R h).firingCount) =
      R.enc (sim.enc y) :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (boundedIntendedSchedule_of_runSim_steps (sim := sim) R h)
    hwin

end BoundedStepwiseRealization

end Ripple.sCRNUniversality

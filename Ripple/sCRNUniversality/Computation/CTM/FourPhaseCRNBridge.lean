import Ripple.sCRNUniversality.Computation.CTM.FourPhaseSystem
import Ripple.sCRNUniversality.Computation.CRNRealization
import Ripple.sCRNUniversality.Core.Schedule

namespace Ripple.sCRNUniversality

namespace CTM

universe u v w

variable {Q : Type u} {s : Nat}
variable {S : Type v} [Fintype S]
variable {N : Network.{v, w} S}

def crnRealization_of_fourPhase
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N) :
    StepwiseRealization (M.detSystem (s := s)) N :=
  StepwiseRealization.ofKStepSim (fourPhaseKStepSim (s := s) M) R

@[simp]
theorem crnRealization_of_fourPhase_enc
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    (cfg : Cfg Q Bool s) :
    (crnRealization_of_fourPhase (s := s) M R).enc cfg =
      R.enc (MicroCfg.ofCTM cfg) := by
  rfl

theorem crn_exec_of_step
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists is : List N.I,
      N.Exec (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) is :=
  R.exec_of_steps (fourPhase_boundary_step (s := s) M h)

/--
Package the deterministic scheduled execution chosen by `crn_exec_of_step`.

This is a one-CTM-step intended schedule for the supplied realization. It does
not assert that arbitrary CRN paths follow this schedule.
-/
noncomputable def crn_intendedSchedule_of_step
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    N.IntendedSchedule
      (R.enc (MicroCfg.ofCTM cfg))
      (R.enc (MicroCfg.ofCTM cfg')) where
  schedule := Classical.choose (crn_exec_of_step (s := s) M R h)
  exec := Classical.choose_spec (crn_exec_of_step (s := s) M R h)

theorem crn_intended_reaches_of_step
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  (crn_intendedSchedule_of_step (s := s) M R h).reaches

theorem state_after_ctm_step_of_crn_intendedWinsRaceAt
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    {path : N.Path}
    {Bad : N.BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (crn_intendedSchedule_of_step (s := s) M R h)) :
    path.state
        (t + (crn_intendedSchedule_of_step (s := s) M R h).firingCount) =
      R.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_intendedWinsRaceAt Bad
    (crn_intendedSchedule_of_step (s := s) M R h)
    hwin

theorem crn_exec_of_steps
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List N.I,
      N.Exec (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) is :=
  R.exec_of_steps (fourPhaseKStepSim_steps (s := s) M h)

/--
Package the deterministic scheduled execution chosen by `crn_exec_of_steps`.

This is an intended `Network.Exec` witness obtained from the CTM/four-phase
simulation and the supplied realization `R`. It is not a statement that an
arbitrary scheduler/path follows this schedule, nor a stochastic/CTMC
completion claim.
-/
noncomputable def crn_intendedSchedule_of_steps
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.IntendedSchedule
      (R.enc (MicroCfg.ofCTM cfg))
      (R.enc (MicroCfg.ofCTM cfg')) where
  schedule := Classical.choose (crn_exec_of_steps (s := s) M R h)
  exec := Classical.choose_spec (crn_exec_of_steps (s := s) M R h)

/--
Safer public spelling of `crn_reaches_of_steps`.

The reachability witness is the intended deterministic schedule above; no
autonomous scheduler safety, fairness, or stochastic race probability is
asserted.
-/
theorem crn_intended_reaches_of_steps
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  (crn_intendedSchedule_of_steps (s := s) M R h).reaches

theorem state_after_ctm_steps_of_crn_intendedWinsRaceAt
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : N.Path}
    {Bad : N.BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (crn_intendedSchedule_of_steps (s := s) M R h)) :
    path.state
        (t + (crn_intendedSchedule_of_steps (s := s) M R h).firingCount) =
      R.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_intendedWinsRaceAt Bad
    (crn_intendedSchedule_of_steps (s := s) M R h)
    hwin

theorem crn_reaches_of_steps
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  R.reaches_of_steps (fourPhaseKStepSim_steps (s := s) M h)

theorem crn_coverable_of_step_covers
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  Network.coverable_of_reaches_of_covers
    (crn_intended_reaches_of_step (s := s) M R h)
    hCovers

theorem crn_coverable_of_step_of_le
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_step_covers (s := s) M R h hTarget

theorem crn_coverableFrom_of_step_covers
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_step_covers (s := s) M R h hCovers

theorem crn_coverableFrom_of_step_of_le
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_step_of_le (s := s) M R h hTarget

theorem crn_speciesCoverableFrom_of_step_coord [DecidableEq S]
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {species : S} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount : amount <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (crn_intended_reaches_of_step (s := s) M R h)
    hamount

theorem crn_speciesCoverableFrom_one_of_step_pos [DecidableEq S]
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {species : S}
    (h : M.step? cfg = some cfg')
    (hpos : 0 < R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (crn_intended_reaches_of_step (s := s) M R h)
    hpos

theorem crn_coverable_of_steps_covers
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  Network.coverable_of_reaches_of_covers
    (crn_reaches_of_steps (s := s) M R h)
    hCovers

theorem crn_coverable_of_steps_of_le
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget : forall species, target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_steps_covers (s := s) M R h hTarget

theorem crn_coverableFrom_of_steps_covers
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_steps_covers (s := s) M R h hCovers

theorem crn_coverableFrom_of_steps_of_le
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_steps_of_le (s := s) M R h hTarget

theorem crn_speciesCoverableFrom_of_steps_coord [DecidableEq S]
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {species : S} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount : amount <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (crn_reaches_of_steps (s := s) M R h)
    hamount

theorem crn_speciesCoverableFrom_one_of_steps_pos [DecidableEq S]
    (M : Binary Q)
    (R : StepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {species : S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos : 0 < R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (crn_reaches_of_steps (s := s) M R h)
    hpos

def boundedCRNRealization_of_fourPhase
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N) :
    BoundedStepwiseRealization (M.detSystem (s := s)) N :=
  BoundedStepwiseRealization.ofKStepSim (fourPhaseKStepSim (s := s) M) R

@[simp]
theorem boundedCRNRealization_of_fourPhase_enc
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    (cfg : Cfg Q Bool s) :
    (boundedCRNRealization_of_fourPhase (s := s) M R).enc cfg =
      R.enc (MicroCfg.ofCTM cfg) := by
  rfl

@[simp]
theorem boundedCRNRealization_of_fourPhase_step_len_bound
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N) :
    (boundedCRNRealization_of_fourPhase (s := s) M R).step_len_bound =
      R.step_len_bound * 4 := by
  rfl

theorem crn_exec_of_steps_bounded
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List N.I,
      N.Exec (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <= (R.step_len_bound * 4) * n :=
  BoundedStepwiseRealization.exec_of_kStepSim_steps_bounded
    (sim := fourPhaseKStepSim (s := s) M) R h

theorem crn_exec_of_step_bounded
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists is : List N.I,
      N.Exec (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <= R.step_len_bound * 4 :=
  R.exec_of_steps_bounded (fourPhase_boundary_step (s := s) M h)

noncomputable def crn_boundedIntendedSchedule_of_step
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    N.BoundedIntendedSchedule (R.step_len_bound * 4)
      (R.enc (MicroCfg.ofCTM cfg))
      (R.enc (MicroCfg.ofCTM cfg')) where
  schedule := Classical.choose (crn_exec_of_step_bounded (s := s) M R h)
  exec := (Classical.choose_spec
    (crn_exec_of_step_bounded (s := s) M R h)).1
  length_bound := (Classical.choose_spec
    (crn_exec_of_step_bounded (s := s) M R h)).2

theorem crn_boundedIntendedSchedule_firingCount_le_of_step
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (crn_boundedIntendedSchedule_of_step (s := s) M R h).firingCount <=
      R.step_len_bound * 4 :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (crn_boundedIntendedSchedule_of_step (s := s) M R h)

theorem crn_boundedIntended_reaches_of_step
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  (crn_boundedIntendedSchedule_of_step (s := s) M R h).reaches

theorem state_after_ctm_step_of_crn_boundedIntendedWinsRaceAt
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s}
    {path : N.Path}
    {Bad : N.BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (crn_boundedIntendedSchedule_of_step
          (s := s) M R h).toIntendedSchedule) :
    path.state
        (t +
          (crn_boundedIntendedSchedule_of_step (s := s) M R h).firingCount) =
      R.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (crn_boundedIntendedSchedule_of_step (s := s) M R h)
    hwin

theorem crn_coverable_of_bounded_step_covers
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  Network.coverable_of_reaches_of_covers
    (crn_boundedIntended_reaches_of_step (s := s) M R h)
    hCovers

theorem crn_coverable_of_bounded_step_of_le
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_bounded_step_covers (s := s) M R h hTarget

theorem crn_coverableFrom_of_bounded_step_covers
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_bounded_step_covers (s := s) M R h hCovers

theorem crn_coverableFrom_of_bounded_step_of_le
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_bounded_step_of_le (s := s) M R h hTarget

theorem crn_speciesCoverableFrom_of_bounded_step_coord [DecidableEq S]
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {species : S} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount : amount <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (crn_boundedIntended_reaches_of_step (s := s) M R h)
    hamount

theorem crn_speciesCoverableFrom_one_of_bounded_step_pos [DecidableEq S]
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {cfg cfg' : Cfg Q Bool s} {species : S}
    (h : M.step? cfg = some cfg')
    (hpos : 0 < R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (crn_boundedIntended_reaches_of_step (s := s) M R h)
    hpos

noncomputable def crn_boundedIntendedSchedule_of_steps
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.BoundedIntendedSchedule ((R.step_len_bound * 4) * n)
      (R.enc (MicroCfg.ofCTM cfg))
      (R.enc (MicroCfg.ofCTM cfg')) where
  schedule := Classical.choose (crn_exec_of_steps_bounded (s := s) M R h)
  exec := (Classical.choose_spec
    (crn_exec_of_steps_bounded (s := s) M R h)).1
  length_bound := (Classical.choose_spec
    (crn_exec_of_steps_bounded (s := s) M R h)).2

theorem crn_boundedIntendedSchedule_firingCount_le_of_steps
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (crn_boundedIntendedSchedule_of_steps (s := s) M R h).firingCount <=
      (R.step_len_bound * 4) * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (crn_boundedIntendedSchedule_of_steps (s := s) M R h)

theorem crn_boundedFiringCount_le_of_steps
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (crn_boundedIntendedSchedule_of_steps (s := s) M R h).firingCount <=
      (R.step_len_bound * 4) * n :=
  crn_boundedIntendedSchedule_firingCount_le_of_steps (s := s) M R h

theorem crn_boundedIntended_reaches_of_steps
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  (crn_boundedIntendedSchedule_of_steps (s := s) M R h).reaches

theorem state_after_ctm_steps_of_crn_boundedIntendedWinsRaceAt
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : N.Path}
    {Bad : N.BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (crn_boundedIntendedSchedule_of_steps
          (s := s) M R h).toIntendedSchedule) :
    path.state
        (t +
          (crn_boundedIntendedSchedule_of_steps (s := s) M R h).firingCount) =
      R.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (crn_boundedIntendedSchedule_of_steps (s := s) M R h)
    hwin

theorem crn_reaches_of_bounded_steps
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  R.reaches_of_steps (fourPhaseKStepSim_steps (s := s) M h)

theorem crn_coverable_of_bounded_steps_covers
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  Network.coverable_of_reaches_of_covers
    (crn_reaches_of_bounded_steps (s := s) M R h)
    hCovers

theorem crn_coverable_of_bounded_steps_of_le
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_bounded_steps_covers (s := s) M R h hTarget

theorem crn_coverableFrom_of_bounded_steps_covers
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_bounded_steps_covers (s := s) M R h hCovers

theorem crn_coverableFrom_of_bounded_steps_of_le
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_bounded_steps_of_le (s := s) M R h hTarget

theorem crn_speciesCoverableFrom_of_bounded_steps_coord [DecidableEq S]
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {species : S} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount : amount <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (crn_reaches_of_bounded_steps (s := s) M R h)
    hamount

theorem crn_speciesCoverableFrom_one_of_bounded_steps_pos [DecidableEq S]
    (M : Binary Q)
    (R : BoundedStepwiseRealization (fourPhaseSystem (s := s) M) N)
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {species : S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos : 0 < R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (crn_reaches_of_bounded_steps (s := s) M R h)
    hpos

def CanonicalMicroCfg (cfg : MicroCfg Q s) : Prop :=
  MicroState.Canonical cfg.state

theorem crn_exec_of_steps_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List N.I,
      N.Exec (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) is :=
  InvariantStepwiseRealization.exec_of_kStepSim_steps
    (sim := fourPhaseKStepSim (s := s) M)
    R
    (MicroCfg.ofCTM_state_canonical cfg)
    h

theorem crn_exec_of_step_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    exists is : List N.I,
      N.Exec (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) is := by
  have hsteps :
      (M.detSystem (s := s)).steps? 1 cfg = some cfg' :=
    DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h
  exact crn_exec_of_steps_canonical (s := s) M R hsteps

noncomputable def crn_intendedSchedule_of_step_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    N.IntendedSchedule
      (R.enc (MicroCfg.ofCTM cfg))
      (R.enc (MicroCfg.ofCTM cfg')) where
  schedule := Classical.choose
    (crn_exec_of_step_canonical (s := s) M R h)
  exec := Classical.choose_spec
    (crn_exec_of_step_canonical (s := s) M R h)

theorem crn_intended_reaches_of_step_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  (crn_intendedSchedule_of_step_canonical (s := s) M R h).reaches

theorem state_after_ctm_step_of_crn_intendedWinsRaceAt_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s}
    {path : N.Path}
    {Bad : N.BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (crn_intendedSchedule_of_step_canonical (s := s) M R h)) :
    path.state
        (t +
          (crn_intendedSchedule_of_step_canonical
            (s := s) M R h).firingCount) =
      R.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_intendedWinsRaceAt Bad
    (crn_intendedSchedule_of_step_canonical (s := s) M R h)
    hwin

theorem crn_coverable_of_step_canonical_covers
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  Network.coverable_of_reaches_of_covers
    (crn_intended_reaches_of_step_canonical (s := s) M R h)
    hCovers

theorem crn_coverable_of_step_canonical_of_le
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_step_canonical_covers (s := s) M R h hTarget

theorem crn_coverableFrom_of_step_canonical_covers
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_step_canonical_covers (s := s) M R h hCovers

theorem crn_coverableFrom_of_step_canonical_of_le
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_step_canonical_of_le (s := s) M R h hTarget

theorem crn_speciesCoverableFrom_of_step_canonical_coord [DecidableEq S]
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s} {species : S} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount : amount <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (crn_intended_reaches_of_step_canonical (s := s) M R h)
    hamount

theorem crn_speciesCoverableFrom_one_of_step_canonical_pos [DecidableEq S]
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {cfg cfg' : Cfg Q Bool s} {species : S}
    (h : M.step? cfg = some cfg')
    (hpos : 0 < R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (crn_intended_reaches_of_step_canonical (s := s) M R h)
    hpos

noncomputable def crn_intendedSchedule_of_steps_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.IntendedSchedule
      (R.enc (MicroCfg.ofCTM cfg))
      (R.enc (MicroCfg.ofCTM cfg')) where
  schedule := Classical.choose
    (crn_exec_of_steps_canonical (s := s) M R h)
  exec := Classical.choose_spec
    (crn_exec_of_steps_canonical (s := s) M R h)

theorem crn_intended_reaches_of_steps_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  (crn_intendedSchedule_of_steps_canonical (s := s) M R h).reaches

theorem state_after_ctm_steps_of_crn_intendedWinsRaceAt_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    {path : N.Path}
    {Bad : N.BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (crn_intendedSchedule_of_steps_canonical (s := s) M R h)) :
    path.state
        (t +
          (crn_intendedSchedule_of_steps_canonical
            (s := s) M R h).firingCount) =
      R.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_intendedWinsRaceAt Bad
    (crn_intendedSchedule_of_steps_canonical (s := s) M R h)
    hwin

theorem crn_reaches_of_steps_canonical
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    N.Reaches (R.enc (MicroCfg.ofCTM cfg)) (R.enc (MicroCfg.ofCTM cfg')) :=
  InvariantStepwiseRealization.reaches_of_kStepSim_steps
    (sim := fourPhaseKStepSim (s := s) M)
    R
    (MicroCfg.ofCTM_state_canonical cfg)
    h

theorem crn_coverable_of_steps_canonical_covers
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  Network.coverable_of_reaches_of_covers
    (crn_reaches_of_steps_canonical (s := s) M R h)
    hCovers

theorem crn_coverable_of_steps_canonical_of_le
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_steps_canonical_covers (s := s) M R h hTarget

theorem crn_coverableFrom_of_steps_canonical_covers
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers : Covers (R.enc (MicroCfg.ofCTM cfg')) target) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_steps_canonical_covers (s := s) M R h hCovers

theorem crn_coverableFrom_of_steps_canonical_of_le
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {target : State S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.CoverableFrom (R.enc (MicroCfg.ofCTM cfg)) target :=
  crn_coverable_of_steps_canonical_of_le (s := s) M R h hTarget

theorem crn_speciesCoverableFrom_of_steps_canonical_coord [DecidableEq S]
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {species : S} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount : amount <= R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom (R.enc (MicroCfg.ofCTM cfg)) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (crn_reaches_of_steps_canonical (s := s) M R h)
    hamount

theorem crn_speciesCoverableFrom_one_of_steps_canonical_pos [DecidableEq S]
    (M : Binary Q)
    (R :
      InvariantStepwiseRealization
        (fourPhaseSystem (s := s) M) N
        (CanonicalMicroCfg (Q := Q) (s := s)))
    {n : Nat} {cfg cfg' : Cfg Q Bool s} {species : S}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos : 0 < R.enc (MicroCfg.ofCTM cfg') species) :
    N.SpeciesCoverableFrom
      (R.enc (MicroCfg.ofCTM cfg)) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (crn_reaches_of_steps_canonical (s := s) M R h)
    hpos

end CTM

end Ripple.sCRNUniversality

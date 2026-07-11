import Ripple.sCRNUniversality.Computation.CTM.FourPhaseWellFormedModule
import Ripple.sCRNUniversality.Computation.CTM.ReadNetwork
import Ripple.sCRNUniversality.Computation.CTM.EraseNetwork
import Ripple.sCRNUniversality.Computation.CTM.ShiftNetwork
import Ripple.sCRNUniversality.Computation.CTM.WriteNetwork

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseMacroModule

universe u

def network {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    Network (FourPhaseSpecies Q) :=
  phaseParallel4
    (ReadNetwork.network (s := s) M)
    (EraseNetwork.network Q s)
    (ShiftGadget.network Q s)
    (WriteNetwork.network Q)

def IsReadIndex {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (network (s := s) M).I) : Prop :=
  exists ir : (ReadNetwork.network (s := s) M).I,
    i = Sum.inl (Sum.inl ir)

def IsEraseIndex {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (network (s := s) M).I) : Prop :=
  exists ie : (EraseNetwork.network Q s).I,
    i = Sum.inl (Sum.inr ie)

def IsShiftIndex {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (network (s := s) M).I) : Prop :=
  exists ishift : (ShiftGadget.network Q s).I,
    i = Sum.inr (Sum.inl ishift)

def IsWriteIndex {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    (i : (network (s := s) M).I) : Prop :=
  exists iw : (WriteNetwork.network Q).I,
    i = Sum.inr (Sum.inr iw)

def IsPhaseIndex {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (phase : Phase4)
    (i : (network (s := s) M).I) : Prop :=
  match phase with
  | Phase4.read => IsReadIndex (s := s) M i
  | Phase4.erase => IsEraseIndex (s := s) M i
  | Phase4.shift => IsShiftIndex (s := s) M i
  | Phase4.write => IsWriteIndex (s := s) M i

theorem network_allUnitRate {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).allUnitRate := by
  unfold network
  exact phaseParallel4_allUnitRate
    (ReadNetwork.network_allUnitRate (s := s) M)
    (EraseNetwork.network_allUnitRate (Q := Q) s)
    (ShiftGadget.network_allUnitRate Q s)
    (WriteNetwork.network_allUnitRate Q)

theorem network_hasPositiveRates {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate
    (network_allUnitRate (s := s) M)

theorem network_equalRates {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (network (s := s) M).equalRates :=
  Network.equalRates_of_allUnitRate
    (network_allUnitRate (s := s) M)

def module {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    WellFormedFourPhaseModule (s := s) M where
  N := network (s := s) M
  step_exec := by
    intro c c' hc hstep
    cases hphase : c.state.phase with
    | read =>
        rcases ReadNetwork.exec_of_phaseStep?_read
          (s := s) M hc.1 hphase hstep with
          ⟨is, hExec, _hLen⟩
        exact ⟨is.map (fun i => Sum.inl (Sum.inl i)),
          phaseParallel4_exec_read hExec⟩
    | erase =>
        rcases EraseNetwork.exec_of_phaseStep?_erase
          (s := s) M hc hphase hstep with
          ⟨is, hExec, _hLen⟩
        exact ⟨is.map (fun i => Sum.inl (Sum.inr i)),
          phaseParallel4_exec_erase hExec⟩
    | shift =>
        rcases ShiftNetwork.exec_of_phaseStep?_shift
          (s := s) M hc hphase hstep with
          ⟨is, hExec, _hLen⟩
        exact ⟨is.map (fun i => Sum.inr (Sum.inl i)),
          phaseParallel4_exec_shift hExec⟩
    | write =>
        rcases WriteNetwork.exec_of_phaseStep?_write
          (s := s) M hc hphase hstep with
          ⟨is, hExec, _hLen⟩
        exact ⟨is.map (fun i => Sum.inr (Sum.inr i)),
          phaseParallel4_exec_write hExec⟩

def boundedModule {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    BoundedWellFormedFourPhaseModule (s := s) M where
  N := network (s := s) M
  step_len_bound := 1
  step_exec_bounded := by
    intro c c' hc hstep
    cases hphase : c.state.phase with
    | read =>
        rcases ReadNetwork.exec_of_phaseStep?_read
          (s := s) M hc.1 hphase hstep with
          ⟨is, hExec, hLen⟩
        exact ⟨is.map (fun i => Sum.inl (Sum.inl i)),
          phaseParallel4_exec_read hExec, by simp [List.length_map, hLen]⟩
    | erase =>
        rcases EraseNetwork.exec_of_phaseStep?_erase
          (s := s) M hc hphase hstep with
          ⟨is, hExec, hLen⟩
        exact ⟨is.map (fun i => Sum.inl (Sum.inr i)),
          phaseParallel4_exec_erase hExec, by simp [List.length_map, hLen]⟩
    | shift =>
        rcases ShiftNetwork.exec_of_phaseStep?_shift
          (s := s) M hc hphase hstep with
          ⟨is, hExec, hLen⟩
        exact ⟨is.map (fun i => Sum.inr (Sum.inl i)),
          phaseParallel4_exec_shift hExec, by simp [List.length_map, hLen]⟩
    | write =>
        rcases WriteNetwork.exec_of_phaseStep?_write
          (s := s) M hc hphase hstep with
          ⟨is, hExec, hLen⟩
        exact ⟨is.map (fun i => Sum.inr (Sum.inr i)),
          phaseParallel4_exec_write hExec, by simp [List.length_map, hLen]⟩

structure FourPhaseMacroReady
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  det : BoundedWellFormedFourPhaseModule.{u, u} (s := s) M
  allUnitRate : det.N.allUnitRate
  equalRates : det.N.equalRates
  hasPositiveRates : det.N.hasPositiveRates

/--
Alias emphasizing that `FourPhaseMacroReady` contains deterministic macro
correctness plus static rate-shape predicates, not stochastic correctness.
-/
abbrev FourPhaseMacroStaticReady
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) :=
  FourPhaseMacroReady (s := s) M

def macroReady {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    FourPhaseMacroReady (s := s) M where
  det := boundedModule (s := s) M
  allUnitRate := by
    change (network (s := s) M).allUnitRate
    exact network_allUnitRate (s := s) M
  equalRates := by
    change (network (s := s) M).equalRates
    exact network_equalRates (s := s) M
  hasPositiveRates := by
    change (network (s := s) M).hasPositiveRates
    exact network_hasPositiveRates (s := s) M

/-- Safer spelling of `macroReady`. -/
def macroStaticReady {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    FourPhaseMacroStaticReady (s := s) M :=
  macroReady (s := s) M

/-- Alias emphasizing that this is the deterministic macro network. -/
abbrev macroNetwork {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    Network (FourPhaseSpecies Q) :=
  network (s := s) M

/-- Static unit-rate predicate for the deterministic macro network. -/
theorem macroNetwork_static_allUnitRate
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (macroNetwork (s := s) M).allUnitRate :=
  network_allUnitRate (s := s) M

/-- Static positive-rate predicate for the deterministic macro network. -/
theorem macroNetwork_static_hasPositiveRates
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (macroNetwork (s := s) M).hasPositiveRates :=
  network_hasPositiveRates (s := s) M

/-- Static equal-rate predicate for the deterministic macro network. -/
theorem macroNetwork_static_equalRates
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (macroNetwork (s := s) M).equalRates :=
  network_equalRates (s := s) M

theorem exec_of_ctm_steps {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  (module (s := s) M).exec_of_ctm_steps h

theorem intended_exec_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  exec_of_ctm_steps (s := s) M h

noncomputable def intendedSchedule_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).IntendedSchedule
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  let hExec := exec_of_ctm_steps (s := s) M h
  exact
    { schedule := Classical.choose hExec
      exec := Classical.choose_spec hExec }

theorem exec_of_intendedSchedule_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).Exec
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (intendedSchedule_of_ctm_steps (s := s) M h).schedule :=
  (intendedSchedule_of_ctm_steps (s := s) M h).exec

theorem reaches_of_ctm_steps {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  (module (s := s) M).reaches_of_ctm_steps h

theorem intended_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  reaches_of_ctm_steps (s := s) M h

theorem exec_of_ctm_steps_bounded
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <= 4 * n := by
  rcases (boundedModule (s := s) M).exec_of_ctm_steps_bounded h with
    ⟨is, hExec, hLen⟩
  have hLen' : is.length <= 1 * (4 * n) := by
    simpa [boundedModule] using hLen
  exact ⟨is, hExec, by simpa using hLen'⟩

theorem intended_exec_of_ctm_steps_bounded
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <= 4 * n :=
  exec_of_ctm_steps_bounded (s := s) M h

theorem intended_firingCount_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List (network (s := s) M).I,
      (network (s := s) M).Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <= 4 * n :=
  exec_of_ctm_steps_bounded (s := s) M h

noncomputable def boundedIntendedSchedule_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).BoundedIntendedSchedule (4 * n)
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  let hExec := exec_of_ctm_steps_bounded (s := s) M h
  exact
    { schedule := Classical.choose hExec
      exec := (Classical.choose_spec hExec).1
      length_bound := (Classical.choose_spec hExec).2 }

theorem exec_of_boundedIntendedSchedule_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).Exec
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (boundedIntendedSchedule_of_ctm_steps (s := s) M h).schedule :=
  (boundedIntendedSchedule_of_ctm_steps (s := s) M h).exec

def toBoundedStepwiseRealization
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    BoundedStepwiseRealization
      (M.detSystem (s := s)) (network (s := s) M) where
  enc := fun cfg => FourPhaseEncoding.enc (MicroCfg.ofCTM cfg)
  step_len_bound := 4
  step_exec_bounded := by
    intro cfg cfg' hstep
    have hsteps :
        (M.detSystem (s := s)).steps? 1 cfg = some cfg' :=
      DetSystem.steps?_one_of_step? (M.detSystem (s := s)) hstep
    simpa using exec_of_ctm_steps_bounded (s := s) M hsteps

@[simp]
theorem toBoundedStepwiseRealization_step_len_bound
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) :
    (toBoundedStepwiseRealization (s := s) M).step_len_bound = 4 := by
  rfl

@[simp]
theorem toBoundedStepwiseRealization_enc
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q) (cfg : Cfg Q Bool s) :
    (toBoundedStepwiseRealization (s := s) M).enc cfg =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg) := by
  rfl

noncomputable def intendedSchedule_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).IntendedSchedule
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  intendedSchedule_of_ctm_steps (s := s) M
    (DetSystem.steps?_one_of_step? (M.detSystem (s := s)) h)

theorem exec_of_intendedSchedule_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).Exec
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (intendedSchedule_of_ctm_step (s := s) M h).schedule :=
  (intendedSchedule_of_ctm_step (s := s) M h).exec

theorem intended_reaches_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  (intendedSchedule_of_ctm_step (s := s) M h).reaches

noncomputable def boundedIntendedSchedule_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).BoundedIntendedSchedule 4
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) := by
  let hExec := (toBoundedStepwiseRealization (s := s) M).step_exec_bounded h
  exact
    { schedule := Classical.choose hExec
      exec := (Classical.choose_spec hExec).1
      length_bound := (Classical.choose_spec hExec).2 }

theorem exec_of_boundedIntendedSchedule_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).Exec
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
      (boundedIntendedSchedule_of_ctm_step (s := s) M h).schedule :=
  (boundedIntendedSchedule_of_ctm_step (s := s) M h).exec

theorem boundedIntendedSchedule_firingCount_le_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (boundedIntendedSchedule_of_ctm_step (s := s) M h).firingCount <= 4 :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (boundedIntendedSchedule_of_ctm_step (s := s) M h)

theorem boundedIntendedSchedule_reaches_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  (boundedIntendedSchedule_of_ctm_step (s := s) M h).reaches

theorem reaches_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  intended_reaches_of_ctm_step (s := s) M h

theorem state_after_ctm_step_of_intendedWinsRaceAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {path : (network (s := s) M).Path}
    {Bad : (network (s := s) M).BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_ctm_step (s := s) M h)) :
    path.state
        (t + (intendedSchedule_of_ctm_step (s := s) M h).firingCount) =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_intendedWinsRaceAt Bad
    (intendedSchedule_of_ctm_step (s := s) M h)
    hwin

theorem state_after_bounded_ctm_step_of_intendedWinsRaceAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {path : (network (s := s) M).Path}
    {Bad : (network (s := s) M).BadIndexSet}
    {t : Nat}
    (h : M.step? cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (boundedIntendedSchedule_of_ctm_step (s := s) M h).toIntendedSchedule) :
    path.state
        (t + (boundedIntendedSchedule_of_ctm_step (s := s) M h).firingCount) =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (boundedIntendedSchedule_of_ctm_step (s := s) M h)
    hwin

theorem coverable_of_ctm_step_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  Network.coverable_of_reaches_of_covers
    (intended_reaches_of_ctm_step (s := s) M h)
    hCovers

theorem coverable_of_ctm_step_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  coverable_of_ctm_step_covers (s := s) M h hTarget

theorem coverableFrom_of_ctm_step_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  coverable_of_ctm_step_covers (s := s) M h hCovers

theorem coverableFrom_of_ctm_step_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : M.step? cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  coverable_of_ctm_step_of_le (s := s) M h hTarget

theorem speciesCoverableFrom_of_ctm_step_coord
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q} {amount : Nat}
    (h : M.step? cfg = some cfg')
    (hamount :
      amount <=
        FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (intended_reaches_of_ctm_step (s := s) M h)
    hamount

theorem speciesCoverableFrom_one_of_ctm_step_pos
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q}
    (h : M.step? cfg = some cfg')
    (hpos :
      0 < FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (intended_reaches_of_ctm_step (s := s) M h)
    hpos

theorem tape_speciesCoverableFrom_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      FourPhaseSpecies.tape
      (Encoding.base3Val cfg'.tape) :=
  speciesCoverableFrom_of_ctm_step_coord
    (s := s) M h (by simp [MicroCfg.ofCTM])

theorem tapeBar_speciesCoverableFrom_of_ctm_step
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : M.step? cfg = some cfg') :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      FourPhaseSpecies.tapeBar
      (FourPhaseEncoding.maxTape s - Encoding.base3Val cfg'.tape) :=
  speciesCoverableFrom_of_ctm_step_coord
    (s := s) M h (by simp [MicroCfg.ofCTM])

theorem boundedIntendedSchedule_firingCount_le_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (boundedIntendedSchedule_of_ctm_steps (s := s) M h).firingCount <=
      4 * n :=
  Network.BoundedIntendedSchedule.firingCount_le_bound
    (boundedIntendedSchedule_of_ctm_steps (s := s) M h)

theorem boundedIntendedSchedule_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  (boundedIntendedSchedule_of_ctm_steps (s := s) M h).reaches

theorem state_after_ctm_steps_of_intendedWinsRaceAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {path : (network (s := s) M).Path}
    {Bad : (network (s := s) M).BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (intendedSchedule_of_ctm_steps (s := s) M h)) :
    path.state
        (t + (intendedSchedule_of_ctm_steps (s := s) M h).schedule.length) =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_intendedWinsRaceAt Bad
    (intendedSchedule_of_ctm_steps (s := s) M h)
    hwin

theorem state_after_bounded_ctm_steps_of_intendedWinsRaceAt
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {path : (network (s := s) M).Path}
    {Bad : (network (s := s) M).BadIndexSet}
    {t : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hwin :
      path.IntendedWinsRaceAt Bad t
        (boundedIntendedSchedule_of_ctm_steps (s := s) M h).toIntendedSchedule) :
    path.state
        (t + (boundedIntendedSchedule_of_ctm_steps (s := s) M h).firingCount) =
      FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') :=
  path.state_after_boundedIntendedWinsRaceAt Bad
    (boundedIntendedSchedule_of_ctm_steps (s := s) M h)
    hwin

theorem coverable_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  Network.coverable_of_reaches_of_covers
    (reaches_of_ctm_steps (s := s) M h)
    hCovers

theorem coverable_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  coverable_of_ctm_steps_covers (s := s) M h hTarget

theorem coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg'))
        target) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  coverable_of_ctm_steps_covers (s := s) M h hCovers

theorem coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {target : State (FourPhaseSpecies Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).CoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      target :=
  coverable_of_ctm_steps_of_le (s := s) M h hTarget

theorem speciesCoverableFrom_of_ctm_steps_coord
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q} {amount : Nat}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hamount :
      amount <=
        FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (reaches_of_ctm_steps (s := s) M h)
    hamount

theorem speciesCoverableFrom_one_of_ctm_steps_pos
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    {species : FourPhaseSpecies Q}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hpos :
      0 < FourPhaseEncoding.enc (MicroCfg.ofCTM cfg') species) :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (reaches_of_ctm_steps (s := s) M h)
    hpos

theorem tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      FourPhaseSpecies.tape
      (Encoding.base3Val cfg'.tape) :=
  speciesCoverableFrom_of_ctm_steps_coord
    (s := s) M h (by simp [MicroCfg.ofCTM])

theorem tapeBar_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : Binary Q)
    {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (network (s := s) M).SpeciesCoverableFrom
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      FourPhaseSpecies.tapeBar
      (FourPhaseEncoding.maxTape s - Encoding.base3Val cfg'.tape) :=
  speciesCoverableFrom_of_ctm_steps_coord
    (s := s) M h (by simp [MicroCfg.ofCTM])

end FourPhaseMacroModule

end CTM

end Ripple.sCRNUniversality

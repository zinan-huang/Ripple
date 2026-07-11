import Ripple.sCRNUniversality.Computation.CTM.FourPhaseTapeInvariant

namespace Ripple.sCRNUniversality

namespace CTM

universe u v

structure WellFormedFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  N : Network.{u, v} (FourPhaseSpecies Q)
  step_exec :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List N.I,
          N.Exec (FourPhaseEncoding.enc c) (FourPhaseEncoding.enc c') is

namespace WellFormedFourPhaseModule

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toInvariantStepwiseRealization
    (G : WellFormedFourPhaseModule (s := s) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.N
      (GadgetMicroCfgWF (Q := Q) (s := s)) where
  enc := FourPhaseEncoding.enc
  step_exec := by
    intro c c' hc hstep
    exact G.step_exec hc hstep
  step_preserves := by
    intro c c' hc hstep
    exact phaseStep?_preserves_gadgetWF (s := s) M hc hstep

@[simp]
theorem toInvariantStepwiseRealization_enc
    (G : WellFormedFourPhaseModule (s := s) M) (c : MicroCfg Q s) :
    G.toInvariantStepwiseRealization.enc c = FourPhaseEncoding.enc c := by
  rfl

theorem exec_of_ctm_steps
    (G : WellFormedFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is :=
  InvariantStepwiseRealization.exec_of_kStepSim_steps
    (sim := fourPhaseKStepSim (s := s) M)
    G.toInvariantStepwiseRealization
    (MicroCfg.ofCTM_gadgetWF cfg)
    h

theorem reaches_of_ctm_steps
    (G : WellFormedFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  InvariantStepwiseRealization.reaches_of_kStepSim_steps
    (sim := fourPhaseKStepSim (s := s) M)
    G.toInvariantStepwiseRealization
    (MicroCfg.ofCTM_gadgetWF cfg)
    h

end WellFormedFourPhaseModule

structure BoundedWellFormedFourPhaseModule
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : Binary Q) where
  N : Network.{u, v} (FourPhaseSpecies Q)
  step_len_bound : Nat
  step_exec_bounded :
    forall {c c' : MicroCfg Q s},
      GadgetMicroCfgWF c ->
      phaseStep? (s := s) M c = some c' ->
        exists is : List N.I,
          N.Exec (FourPhaseEncoding.enc c) (FourPhaseEncoding.enc c') is /\
            is.length <= step_len_bound

namespace BoundedWellFormedFourPhaseModule

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
variable {M : Binary Q}

def toWellFormedFourPhaseModule
    (G : BoundedWellFormedFourPhaseModule (s := s) M) :
    WellFormedFourPhaseModule (s := s) M where
  N := G.N
  step_exec := by
    intro c c' hc hstep
    rcases G.step_exec_bounded hc hstep with ⟨is, hExec, _hLen⟩
    exact ⟨is, hExec⟩

def toInvariantStepwiseRealization
    (G : BoundedWellFormedFourPhaseModule (s := s) M) :
    InvariantStepwiseRealization
      (fourPhaseSystem (s := s) M) G.N
      (GadgetMicroCfgWF (Q := Q) (s := s)) :=
  G.toWellFormedFourPhaseModule.toInvariantStepwiseRealization

theorem exec_of_fourPhase_steps_bounded
    (G : BoundedWellFormedFourPhaseModule (s := s) M)
    {n : Nat} {c c' : MicroCfg Q s}
    (hc : GadgetMicroCfgWF c)
    (h : (fourPhaseSystem (s := s) M).steps? n c = some c') :
    exists is : List G.N.I,
      G.N.Exec (FourPhaseEncoding.enc c) (FourPhaseEncoding.enc c') is /\
        is.length <= G.step_len_bound * n := by
  induction n generalizing c c' with
  | zero =>
      have hSome : (some c : Option (MicroCfg Q s)) = some c' := by
        exact h
      cases hSome
      exact ⟨[], ExecOf.nil (FourPhaseEncoding.enc c), by simp⟩
  | succ n ih =>
      cases hstep : (fourPhaseSystem (s := s) M).step? c with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some c₁ =>
          have hc₁ : GadgetMicroCfgWF c₁ := by
            exact phaseStep?_preserves_gadgetWF (s := s) M hc
              (by simpa [fourPhaseSystem] using hstep)
          have htail :
              (fourPhaseSystem (s := s) M).steps? n c₁ = some c' := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          have hphase :
              phaseStep? (s := s) M c = some c₁ := by
            simpa [fourPhaseSystem] using hstep
          rcases G.step_exec_bounded hc hphase with
            ⟨is, hExecStep, hLenStep⟩
          rcases ih hc₁ htail with ⟨js, hExecTail, hLenTail⟩
          refine ⟨is ++ js, ExecOf.append hExecStep hExecTail, ?_⟩
          have hLen :
              (is ++ js).length <=
                G.step_len_bound + G.step_len_bound * n := by
            simpa [List.length_append] using
              Nat.add_le_add hLenStep hLenTail
          simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using hLen

theorem exec_of_ctm_steps_bounded
    (G : BoundedWellFormedFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists is : List G.N.I,
      G.N.Exec
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
        (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) is /\
        is.length <= G.step_len_bound * (4 * n) :=
  G.exec_of_fourPhase_steps_bounded
    (MicroCfg.ofCTM_gadgetWF cfg)
    (fourPhaseKStepSim_steps (s := s) M h)

theorem reaches_of_ctm_steps
    (G : BoundedWellFormedFourPhaseModule (s := s) M)
    {n : Nat} {cfg cfg' : Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    G.N.Reaches
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg))
      (FourPhaseEncoding.enc (MicroCfg.ofCTM cfg')) :=
  G.toWellFormedFourPhaseModule.reaches_of_ctm_steps h

end BoundedWellFormedFourPhaseModule

end CTM

end Ripple.sCRNUniversality

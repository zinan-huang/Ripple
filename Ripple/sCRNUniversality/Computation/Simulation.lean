import Ripple.sCRNUniversality.Computation.DetSystem

namespace Ripple.sCRNUniversality

structure KStepSim (A B : DetSystem) (k : Nat) where
  enc : A.Cfg -> B.Cfg
  step_ok :
    forall {c c' : A.Cfg}, A.step? c = some c' ->
      B.steps? k (enc c) = some (enc c')
  halt_ok :
    forall {c : A.Cfg}, A.step? c = none ->
      B.step? (enc c) = none

namespace KStepSim

theorem steps? {A B : DetSystem} {k n : Nat}
    (sim : KStepSim A B k) {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    B.steps? (k * n) (sim.enc x) = some (sim.enc y) := by
  revert x
  induction n with
  | zero =>
      intro x h
      simp [DetSystem.steps?] at h
      cases h
      rfl
  | succ n ih =>
      intro x h
      cases hstep : A.step? x with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some x₁ =>
          have htail : A.steps? n x₁ = some y := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          have hfirst : B.steps? k (sim.enc x) = some (sim.enc x₁) :=
            sim.step_ok hstep
          have hrest : B.steps? (k * n) (sim.enc x₁) = some (sim.enc y) :=
            ih htail
          have happ :
              B.steps? (k + k * n) (sim.enc x) = some (sim.enc y) :=
            DetSystem.steps?_append B hfirst hrest
          simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using happ

def trans {A B C : DetSystem} {k l : Nat}
    (AB : KStepSim A B k) (BC : KStepSim B C l) :
    KStepSim A C (l * k) where
  enc := fun c => BC.enc (AB.enc c)
  step_ok := by
    intro _c _c' hstep
    exact KStepSim.steps? (sim := BC) (AB.step_ok hstep)
  halt_ok := by
    intro c hhalt
    exact BC.halt_ok (AB.halt_ok hhalt)

end KStepSim

structure RunSim (A B : DetSystem) where
  enc : A.Cfg -> B.Cfg
  time : Nat -> Nat
  run_ok :
    forall (n : Nat) {c c' : A.Cfg}, A.steps? n c = some c' ->
      B.steps? (time n) (enc c) = some (enc c')

namespace KStepSim

def toRunSim {A B : DetSystem} {k : Nat}
    (sim : KStepSim A B k) : RunSim A B where
  enc := sim.enc
  time := fun n => k * n
  run_ok := by
    intro _n _c _c' h
    exact sim.steps? h

end KStepSim

namespace RunSim

def trans {A B C : DetSystem}
    (AB : RunSim A B) (BC : RunSim B C) :
    RunSim A C where
  enc := fun c => BC.enc (AB.enc c)
  time := fun n => BC.time (AB.time n)
  run_ok := by
    intro n _c _c' h
    exact BC.run_ok (AB.time n) (AB.run_ok n h)

end RunSim

end Ripple.sCRNUniversality

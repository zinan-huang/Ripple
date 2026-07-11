import Ripple.sCRNUniversality.Computation.Simulation
import Ripple.sCRNUniversality.Core.Embedding
import Ripple.sCRNUniversality.Core.Run

namespace Ripple.sCRNUniversality

universe u v w x

structure StepwiseRealization (A : DetSystem.{u})
    {S : Type v} [Fintype S] (N : Network.{v, w} S) where
  enc : A.Cfg -> State S
  step_exec :
    forall {x y : A.Cfg}, A.step? x = some y ->
      exists is : List N.I, N.Exec (enc x) (enc y) is

structure BoundedStepwiseRealization (A : DetSystem.{u})
    {S : Type v} [Fintype S] (N : Network.{v, w} S) where
  enc : A.Cfg -> State S
  step_len_bound : Nat
  step_exec_bounded :
    forall {x y : A.Cfg}, A.step? x = some y ->
      exists is : List N.I,
        N.Exec (enc x) (enc y) is /\ is.length <= step_len_bound

structure InvariantStepwiseRealization (A : DetSystem.{u})
    {S : Type v} [Fintype S] (N : Network.{v, w} S)
    (Inv : A.Cfg -> Prop) where
  enc : A.Cfg -> State S
  step_exec :
    forall {x y : A.Cfg}, Inv x -> A.step? x = some y ->
      exists is : List N.I, N.Exec (enc x) (enc y) is
  step_preserves :
    forall {x y : A.Cfg}, Inv x -> A.step? x = some y -> Inv y

namespace StepwiseRealization

variable {A : DetSystem.{u}} {S : Type v} [Fintype S]
variable {N : Network.{v, w} S}
variable {T : Type x} [Fintype T] [DecidableEq T]

def embed_of_injective
    (R : StepwiseRealization A N) (e : S -> T) (he : Function.Injective e) :
    StepwiseRealization A (Network.embed e N) where
  enc := fun c => State.embed e (R.enc c)
  step_exec := by
    intro _x _y hstep
    rcases R.step_exec hstep with ⟨is, hExec⟩
    exact ⟨is, Network.embed_exec_of_injective (e := e) (N := N) he hExec⟩

def embedSpecies_of_injective
    (R : StepwiseRealization A N) (e : S -> T) (he : Function.Injective e) :
    StepwiseRealization A (Network.embed e N) :=
  R.embed_of_injective e he

def parallel_left
    (R : StepwiseRealization A N) (M : Network S) :
    StepwiseRealization A (N.parallel M) where
  enc := R.enc
  step_exec := by
    intro _x _y hstep
    rcases R.step_exec hstep with ⟨is, hExec⟩
    exact ⟨is.map Sum.inl, Network.parallel_exec_inl N M hExec⟩

def parallel_right
    (R : StepwiseRealization A N) (M : Network S) :
    StepwiseRealization A (M.parallel N) where
  enc := R.enc
  step_exec := by
    intro _x _y hstep
    rcases R.step_exec hstep with ⟨is, hExec⟩
    exact ⟨is.map Sum.inr, Network.parallel_exec_inr M N hExec⟩

def parallel_inl
    (R : StepwiseRealization A N) (M : Network S) :
    StepwiseRealization A (N.parallel M) :=
  R.parallel_left M

def parallel_inr
    (R : StepwiseRealization A N) (M : Network S) :
    StepwiseRealization A (M.parallel N) :=
  R.parallel_right M

theorem exec_of_steps
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    exists is : List N.I, N.Exec (R.enc x) (R.enc y) is := by
  induction n generalizing x y with
  | zero =>
      have hSome : (some x : Option A.Cfg) = some y := by
        simpa [DetSystem.steps?, DetSystem.iter] using h
      cases hSome
      exact ⟨[], ExecOf.nil (R.enc x)⟩
  | succ n ih =>
      cases hstep : A.step? x with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some x₁ =>
          have htail : A.steps? n x₁ = some y := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          rcases R.step_exec hstep with ⟨is, hExecStep⟩
          rcases ih htail with ⟨js, hExecTail⟩
          exact ⟨is ++ js, ExecOf.append hExecStep hExecTail⟩

def ofKStepSim {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N) :
    StepwiseRealization A N where
  enc := fun c => R.enc (sim.enc c)
  step_exec := by
    intro _x _y hstep
    exact R.exec_of_steps (sim.step_ok hstep)

def comp_kStepSim {B : DetSystem.{u}} {k : Nat}
    (R : StepwiseRealization B N) (sim : KStepSim A B k) :
    StepwiseRealization A N :=
  ofKStepSim sim R

def compKStep {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N) :
    StepwiseRealization A N :=
  ofKStepSim sim R

theorem reaches_of_steps
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc x) (R.enc y) := by
  rcases R.exec_of_steps h with ⟨is, hExec⟩
  exact ⟨is, hExec⟩

theorem embedSpecies_reaches_of_steps_of_injective
    (R : StepwiseRealization A N)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    (Network.embed e N).Reaches
      (State.embed e (R.enc x))
      (State.embed e (R.enc y)) :=
  (R.embedSpecies_of_injective e he).reaches_of_steps h

theorem embedSpecies_speciesCoverableFrom_of_steps_coord_of_injective
    (R : StepwiseRealization A N)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg} {s : S} {k : Nat}
    (h : A.steps? n x = some y)
    (hk : k <= R.enc y s) :
    (Network.embed e N).SpeciesCoverableFrom
      (State.embed e (R.enc x)) (e s) k := by
  have hReach :
      (Network.embed e N).Reaches
        (State.embed e (R.enc x))
        (State.embed e (R.enc y)) :=
    R.embedSpecies_reaches_of_steps_of_injective e he h
  have hk' : k <= State.embed e (R.enc y) (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he (R.enc y) s] using hk
  exact Network.speciesCoverableFrom_of_reaches_coord hReach hk'

theorem embedSpecies_speciesCoverableFrom_one_of_steps_pos_of_injective
    (R : StepwiseRealization A N)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg} {s : S}
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc y s) :
    (Network.embed e N).SpeciesCoverableFrom
      (State.embed e (R.enc x)) (e s) := by
  have hReach :
      (Network.embed e N).Reaches
        (State.embed e (R.enc x))
        (State.embed e (R.enc y)) :=
    R.embedSpecies_reaches_of_steps_of_injective e he h
  have hpos' : 0 < State.embed e (R.enc y) (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he (R.enc y) s] using hpos
  exact Network.speciesCoverableFrom_one_of_reaches_pos hReach hpos'

theorem exec_of_kStepSim_steps {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    exists is : List N.I,
      N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y)) is :=
  R.exec_of_steps (KStepSim.steps? (sim := sim) h)

theorem reaches_of_kStepSim_steps {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  R.reaches_of_steps (KStepSim.steps? (sim := sim) h)

theorem coverable_of_steps_covers
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {target : State S}
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc y) target) :
    N.CoverableFrom (R.enc x) target :=
  Network.coverable_of_reaches_of_covers (R.reaches_of_steps h) hCovers

theorem coverable_of_steps_of_le
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {target : State S}
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc y s) :
    N.CoverableFrom (R.enc x) target :=
  R.coverable_of_steps_covers h hTarget

theorem coverableFrom_of_steps_covers
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {target : State S}
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc y) target) :
    N.CoverableFrom (R.enc x) target :=
  R.coverable_of_steps_covers h hCovers

theorem coverableFrom_of_steps_of_le
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {target : State S}
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc y s) :
    N.CoverableFrom (R.enc x) target :=
  R.coverable_of_steps_of_le h hTarget

theorem coverable_of_kStepSim_steps_covers {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg} {target : State S}
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc (sim.enc y)) target) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  Network.coverable_of_reaches_of_covers
    (reaches_of_kStepSim_steps (sim := sim) R h)
    hCovers

theorem coverable_of_kStepSim_steps_of_le {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg} {target : State S}
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc (sim.enc y) s) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  coverable_of_kStepSim_steps_covers (sim := sim) R h hTarget

theorem coverableFrom_of_kStepSim_steps_covers {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg} {target : State S}
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc (sim.enc y)) target) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  coverable_of_kStepSim_steps_covers (sim := sim) R h hCovers

theorem coverableFrom_of_kStepSim_steps_of_le {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg} {target : State S}
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc (sim.enc y) s) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  coverable_of_kStepSim_steps_of_le (sim := sim) R h hTarget

theorem speciesCoverableFrom_of_steps_coord [DecidableEq S]
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {s : S} {k : Nat}
    (h : A.steps? n x = some y)
    (hk : k <= R.enc y s) :
    N.SpeciesCoverableFrom (R.enc x) s k :=
  Network.speciesCoverableFrom_of_reaches_coord (R.reaches_of_steps h) hk

theorem speciesCoverableFrom_one_of_steps_pos [DecidableEq S]
    (R : StepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {s : S}
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc y s) :
    N.SpeciesCoverableFrom (R.enc x) s :=
  Network.speciesCoverableFrom_one_of_reaches_pos (R.reaches_of_steps h) hpos

theorem speciesCoverableFrom_of_kStepSim_steps_coord [DecidableEq S]
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg} {s : S} {m : Nat}
    (h : A.steps? n x = some y)
    (hm : m <= R.enc (sim.enc y) s) :
    N.SpeciesCoverableFrom (R.enc (sim.enc x)) s m :=
  Network.speciesCoverableFrom_of_reaches_coord
    (reaches_of_kStepSim_steps (sim := sim) R h)
    hm

theorem speciesCoverableFrom_one_of_kStepSim_steps_pos [DecidableEq S]
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    {x y : A.Cfg} {s : S}
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc (sim.enc y) s) :
    N.SpeciesCoverableFrom (R.enc (sim.enc x)) s :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (reaches_of_kStepSim_steps (sim := sim) R h)
    hpos

theorem parallel_reaches_of_kStepSim_steps_then_right
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    (M : Network.{v, w} S)
    {x y : A.Cfg} {z₂ : State S}
    (h : A.steps? n x = some y)
    (hM : M.Reaches (R.enc (sim.enc y)) z₂) :
    (N.parallel M).Reaches (R.enc (sim.enc x)) z₂ :=
  Network.parallel_reaches_left_then_right N M
    (reaches_of_kStepSim_steps (sim := sim) R h)
    hM

theorem parallel_coverable_of_kStepSim_steps_then_right_covers
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    (M : Network.{v, w} S)
    {x y : A.Cfg} {z₂ target : State S}
    (h : A.steps? n x = some y)
    (hM : M.Reaches (R.enc (sim.enc y)) z₂)
    (hCovers : Covers z₂ target) :
    (N.parallel M).CoverableFrom (R.enc (sim.enc x)) target :=
  Network.coverable_of_reaches_of_covers
    (parallel_reaches_of_kStepSim_steps_then_right
      (sim := sim) R M h hM)
    hCovers

theorem parallel_speciesCoverableFrom_of_kStepSim_steps_then_right_not_touches
    [DecidableEq S] {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : StepwiseRealization B N)
    (M : Network.{v, w} S)
    {x y : A.Cfg} {z₂ : State S} {s : S} {m : Nat}
    (h : A.steps? n x = some y)
    (hM : M.Reaches (R.enc (sim.enc y)) z₂)
    (hMnt : forall i : M.I, ¬ (M.rxn i).Touches s)
    (hm : m <= R.enc (sim.enc y) s) :
    (N.parallel M).SpeciesCoverableFrom (R.enc (sim.enc x)) s m := by
  have hPar :
      (N.parallel M).Reaches (R.enc (sim.enc x)) z₂ :=
    parallel_reaches_of_kStepSim_steps_then_right
      (sim := sim) R M h hM
  have hcoord : z₂ s = R.enc (sim.enc y) s :=
    Network.Reaches.coord_eq_of_not_touches hM hMnt
  exact Network.speciesCoverableFrom_of_reaches_coord hPar (by
    rw [hcoord]
    exact hm)

end StepwiseRealization

namespace InvariantStepwiseRealization

variable {A : DetSystem.{u}} {S : Type v} [Fintype S]
variable {N : Network.{v, w} S} {Inv : A.Cfg -> Prop}
variable {T : Type x} [Fintype T] [DecidableEq T]

theorem exec_of_steps
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg}
    (hx : Inv x)
    (h : A.steps? n x = some y) :
    exists is : List N.I, N.Exec (R.enc x) (R.enc y) is := by
  induction n generalizing x y with
  | zero =>
      have hSome : (some x : Option A.Cfg) = some y := by
        simpa [DetSystem.steps?, DetSystem.iter] using h
      cases hSome
      exact ⟨[], ExecOf.nil (R.enc x)⟩
  | succ n ih =>
      cases hstep : A.step? x with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some x₁ =>
          have hx₁ : Inv x₁ := R.step_preserves hx hstep
          have htail : A.steps? n x₁ = some y := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          rcases R.step_exec hx hstep with ⟨is, hExecStep⟩
          rcases ih hx₁ htail with ⟨js, hExecTail⟩
          exact ⟨is ++ js, ExecOf.append hExecStep hExecTail⟩

theorem reaches_of_steps
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg}
    (hx : Inv x)
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc x) (R.enc y) := by
  rcases R.exec_of_steps hx h with ⟨is, hExec⟩
  exact ⟨is, hExec⟩

theorem coverable_of_steps_covers
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg} {target : State S}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc y) target) :
    N.CoverableFrom (R.enc x) target :=
  Network.coverable_of_reaches_of_covers (R.reaches_of_steps hx h) hCovers

theorem coverable_of_steps_of_le
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg} {target : State S}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc y s) :
    N.CoverableFrom (R.enc x) target :=
  R.coverable_of_steps_covers hx h hTarget

theorem coverableFrom_of_steps_covers
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg} {target : State S}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc y) target) :
    N.CoverableFrom (R.enc x) target :=
  R.coverable_of_steps_covers hx h hCovers

theorem coverableFrom_of_steps_of_le
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg} {target : State S}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc y s) :
    N.CoverableFrom (R.enc x) target :=
  R.coverable_of_steps_of_le hx h hTarget

theorem speciesCoverableFrom_of_steps_coord [DecidableEq S]
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg} {s : S} {k : Nat}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hk : k <= R.enc y s) :
    N.SpeciesCoverableFrom (R.enc x) s k :=
  Network.speciesCoverableFrom_of_reaches_coord (R.reaches_of_steps hx h) hk

theorem speciesCoverableFrom_one_of_steps_pos [DecidableEq S]
    (R : InvariantStepwiseRealization A N Inv)
    {n : Nat} {x y : A.Cfg} {s : S}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc y s) :
    N.SpeciesCoverableFrom (R.enc x) s :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (R.reaches_of_steps hx h)
    hpos

theorem exec_of_kStepSim_steps {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    exists is : List N.I,
      N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y)) is :=
  R.exec_of_steps hx (KStepSim.steps? (sim := sim) h)

theorem reaches_of_kStepSim_steps {B : DetSystem.{u}} {InvB : B.Cfg -> Prop}
    {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) := by
  rcases exec_of_kStepSim_steps (sim := sim) R hx h with ⟨is, hExec⟩
  exact ⟨is, hExec⟩

theorem coverableFrom_of_kStepSim_steps_covers
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg} {target : State S}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc (sim.enc y)) target) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  Network.coverable_of_reaches_of_covers
    (reaches_of_kStepSim_steps (sim := sim) R hx h)
    hCovers

theorem coverableFrom_of_kStepSim_steps_of_le
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg} {target : State S}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc (sim.enc y) s) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  coverableFrom_of_kStepSim_steps_covers
    (sim := sim) R hx h hTarget

theorem speciesCoverableFrom_of_kStepSim_steps_coord [DecidableEq S]
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg} {s : S} {m : Nat}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y)
    (hm : m <= R.enc (sim.enc y) s) :
    N.SpeciesCoverableFrom (R.enc (sim.enc x)) s m :=
  Network.speciesCoverableFrom_of_reaches_coord
    (reaches_of_kStepSim_steps (sim := sim) R hx h)
    hm

theorem speciesCoverableFrom_one_of_kStepSim_steps_pos [DecidableEq S]
    {B : DetSystem.{u}} {InvB : B.Cfg -> Prop} {k n : Nat}
    (sim : KStepSim A B k)
    (R : InvariantStepwiseRealization B N InvB)
    {x y : A.Cfg} {s : S}
    (hx : InvB (sim.enc x))
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc (sim.enc y) s) :
    N.SpeciesCoverableFrom (R.enc (sim.enc x)) s :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (reaches_of_kStepSim_steps (sim := sim) R hx h)
    hpos

def embed_of_injective
    (R : InvariantStepwiseRealization A N Inv)
    (e : S -> T) (he : Function.Injective e) :
    InvariantStepwiseRealization A (Network.embed e N) Inv where
  enc := fun c => State.embed e (R.enc c)
  step_exec := by
    intro _x _y hx hstep
    rcases R.step_exec hx hstep with ⟨is, hExec⟩
    exact ⟨is, Network.embed_exec_of_injective (e := e) (N := N) he hExec⟩
  step_preserves := by
    intro _x _y hx hstep
    exact R.step_preserves hx hstep

def embedSpecies_of_injective
    (R : InvariantStepwiseRealization A N Inv)
    (e : S -> T) (he : Function.Injective e) :
    InvariantStepwiseRealization A (Network.embed e N) Inv :=
  R.embed_of_injective e he

theorem embedSpecies_reaches_of_steps_of_injective
    (R : InvariantStepwiseRealization A N Inv)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg}
    (hx : Inv x)
    (h : A.steps? n x = some y) :
    (Network.embed e N).Reaches
      (State.embed e (R.enc x))
      (State.embed e (R.enc y)) :=
  (R.embedSpecies_of_injective e he).reaches_of_steps hx h

theorem embedSpecies_speciesCoverableFrom_of_steps_coord_of_injective
    (R : InvariantStepwiseRealization A N Inv)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg} {s : S} {k : Nat}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hk : k <= R.enc y s) :
    (Network.embed e N).SpeciesCoverableFrom
      (State.embed e (R.enc x)) (e s) k := by
  have hk' : k <= State.embed e (R.enc y) (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he (R.enc y) s] using hk
  exact
    (R.embedSpecies_of_injective e he).speciesCoverableFrom_of_steps_coord
      hx h hk'

theorem embedSpecies_speciesCoverableFrom_one_of_steps_pos_of_injective
    (R : InvariantStepwiseRealization A N Inv)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg} {s : S}
    (hx : Inv x)
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc y s) :
    (Network.embed e N).SpeciesCoverableFrom
      (State.embed e (R.enc x)) (e s) := by
  have hpos' : 0 < State.embed e (R.enc y) (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he (R.enc y) s] using hpos
  exact
    (R.embedSpecies_of_injective e he).speciesCoverableFrom_one_of_steps_pos
      hx h hpos'

end InvariantStepwiseRealization

namespace BoundedStepwiseRealization

variable {A : DetSystem.{u}} {S : Type v} [Fintype S]
variable {N : Network.{v, w} S}
variable {T : Type x} [Fintype T] [DecidableEq T]

def weakenBound
    (R : BoundedStepwiseRealization A N) {L : Nat}
    (hL : R.step_len_bound <= L) :
    BoundedStepwiseRealization A N where
  enc := R.enc
  step_len_bound := L
  step_exec_bounded := by
    intro _x _y hstep
    rcases R.step_exec_bounded hstep with ⟨is, hExec, hLen⟩
    exact ⟨is, hExec, le_trans hLen hL⟩

def toStepwiseRealization
    (R : BoundedStepwiseRealization A N) : StepwiseRealization A N where
  enc := R.enc
  step_exec := by
    intro _x _y hstep
    rcases R.step_exec_bounded hstep with ⟨is, hExec, _hLen⟩
    exact ⟨is, hExec⟩

def embed_of_injective
    (R : BoundedStepwiseRealization A N) (e : S -> T)
    (he : Function.Injective e) :
    BoundedStepwiseRealization A (Network.embed e N) where
  enc := fun c => State.embed e (R.enc c)
  step_len_bound := R.step_len_bound
  step_exec_bounded := by
    intro _x _y hstep
    rcases R.step_exec_bounded hstep with ⟨is, hExec, hLen⟩
    exact ⟨is, Network.embed_exec_of_injective (e := e) (N := N) he hExec, hLen⟩

def embedSpecies_of_injective
    (R : BoundedStepwiseRealization A N) (e : S -> T)
    (he : Function.Injective e) :
    BoundedStepwiseRealization A (Network.embed e N) :=
  R.embed_of_injective e he

def parallel_left
    (R : BoundedStepwiseRealization A N) (M : Network S) :
    BoundedStepwiseRealization A (N.parallel M) where
  enc := R.enc
  step_len_bound := R.step_len_bound
  step_exec_bounded := by
    intro _x _y hstep
    rcases R.step_exec_bounded hstep with ⟨is, hExec, hLen⟩
    exact ⟨is.map Sum.inl, Network.parallel_exec_inl N M hExec, by
      simpa using hLen⟩

def parallel_right
    (R : BoundedStepwiseRealization A N) (M : Network S) :
    BoundedStepwiseRealization A (M.parallel N) where
  enc := R.enc
  step_len_bound := R.step_len_bound
  step_exec_bounded := by
    intro _x _y hstep
    rcases R.step_exec_bounded hstep with ⟨is, hExec, hLen⟩
    exact ⟨is.map Sum.inr, Network.parallel_exec_inr M N hExec, by
      simpa using hLen⟩

theorem exec_of_steps_bounded
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    exists is : List N.I,
      N.Exec (R.enc x) (R.enc y) is /\
        is.length <= R.step_len_bound * n := by
  induction n generalizing x y with
  | zero =>
      have hSome : (some x : Option A.Cfg) = some y := by
        simpa [DetSystem.steps?, DetSystem.iter] using h
      cases hSome
      exact ⟨[], ExecOf.nil (R.enc x), by simp⟩
  | succ n ih =>
      cases hstep : A.step? x with
      | none =>
          simp [DetSystem.steps?, DetSystem.iter, hstep] at h
      | some x₁ =>
          have htail : A.steps? n x₁ = some y := by
            simpa [DetSystem.steps?, DetSystem.iter, hstep] using h
          rcases R.step_exec_bounded hstep with ⟨is, hExecStep, hLenStep⟩
          rcases ih htail with ⟨js, hExecTail, hLenTail⟩
          refine ⟨is ++ js, ExecOf.append hExecStep hExecTail, ?_⟩
          have hLen :
              (is ++ js).length <=
                R.step_len_bound + R.step_len_bound * n := by
            simpa [List.length_append] using
              Nat.add_le_add hLenStep hLenTail
          simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using hLen

theorem reaches_of_steps
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc x) (R.enc y) :=
  (R.toStepwiseRealization).reaches_of_steps h

theorem coverableFrom_of_steps_covers
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {target : State S}
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc y) target) :
    N.CoverableFrom (R.enc x) target :=
  Network.coverable_of_reaches_of_covers (R.reaches_of_steps h) hCovers

theorem coverableFrom_of_steps_of_le
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {target : State S}
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc y s) :
    N.CoverableFrom (R.enc x) target :=
  R.coverableFrom_of_steps_covers h hTarget

theorem speciesCoverableFrom_of_steps_coord [DecidableEq S]
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {s : S} {k : Nat}
    (h : A.steps? n x = some y)
    (hk : k <= R.enc y s) :
    N.SpeciesCoverableFrom (R.enc x) s k :=
  Network.speciesCoverableFrom_of_reaches_coord (R.reaches_of_steps h) hk

theorem speciesCoverableFrom_one_of_steps_pos [DecidableEq S]
    (R : BoundedStepwiseRealization A N) {n : Nat} {x y : A.Cfg}
    {s : S}
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc y s) :
    N.SpeciesCoverableFrom (R.enc x) s :=
  Network.speciesCoverableFrom_one_of_reaches_pos (R.reaches_of_steps h) hpos

theorem embedSpecies_reaches_of_steps_of_injective
    (R : BoundedStepwiseRealization A N)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    (Network.embed e N).Reaches
      (State.embed e (R.enc x))
      (State.embed e (R.enc y)) :=
  (R.embedSpecies_of_injective e he).reaches_of_steps h

theorem embedSpecies_speciesCoverableFrom_of_steps_coord_of_injective
    (R : BoundedStepwiseRealization A N)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg} {s : S} {k : Nat}
    (h : A.steps? n x = some y)
    (hk : k <= R.enc y s) :
    (Network.embed e N).SpeciesCoverableFrom
      (State.embed e (R.enc x)) (e s) k := by
  have hk' : k <= State.embed e (R.enc y) (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he (R.enc y) s] using hk
  exact
    (R.embedSpecies_of_injective e he).speciesCoverableFrom_of_steps_coord
      h hk'

theorem embedSpecies_speciesCoverableFrom_one_of_steps_pos_of_injective
    (R : BoundedStepwiseRealization A N)
    (e : S -> T) (he : Function.Injective e)
    {n : Nat} {x y : A.Cfg} {s : S}
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc y s) :
    (Network.embed e N).SpeciesCoverableFrom
      (State.embed e (R.enc x)) (e s) := by
  have hpos' : 0 < State.embed e (R.enc y) (e s) := by
    simpa [State.embed_apply_of_injective (e := e) he (R.enc y) s] using hpos
  exact
    (R.embedSpecies_of_injective e he).speciesCoverableFrom_one_of_steps_pos
      h hpos'

def ofKStepSim {B : DetSystem.{u}} {k : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N) :
    BoundedStepwiseRealization A N where
  enc := fun c => R.enc (sim.enc c)
  step_len_bound := R.step_len_bound * k
  step_exec_bounded := by
    intro _x _y hstep
    exact R.exec_of_steps_bounded (sim.step_ok hstep)

theorem exec_of_kStepSim_steps_bounded {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    exists is : List N.I,
      N.Exec (R.enc (sim.enc x)) (R.enc (sim.enc y)) is /\
        is.length <= (R.step_len_bound * k) * n :=
  (ofKStepSim (A := A) (N := N) sim R).exec_of_steps_bounded h

theorem reaches_of_kStepSim_steps {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg}
    (h : A.steps? n x = some y) :
    N.Reaches (R.enc (sim.enc x)) (R.enc (sim.enc y)) :=
  (ofKStepSim (A := A) (N := N) sim R).reaches_of_steps h

theorem coverableFrom_of_kStepSim_steps_covers {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg} {target : State S}
    (h : A.steps? n x = some y)
    (hCovers : Covers (R.enc (sim.enc y)) target) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  (ofKStepSim (A := A) (N := N) sim R).coverableFrom_of_steps_covers h hCovers

theorem coverableFrom_of_kStepSim_steps_of_le {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg} {target : State S}
    (h : A.steps? n x = some y)
    (hTarget : forall s, target s <= R.enc (sim.enc y) s) :
    N.CoverableFrom (R.enc (sim.enc x)) target :=
  coverableFrom_of_kStepSim_steps_covers (sim := sim) R h hTarget

theorem speciesCoverableFrom_of_kStepSim_steps_coord [DecidableEq S]
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg} {s : S} {m : Nat}
    (h : A.steps? n x = some y)
    (hm : m <= R.enc (sim.enc y) s) :
    N.SpeciesCoverableFrom (R.enc (sim.enc x)) s m :=
  Network.speciesCoverableFrom_of_reaches_coord
    (reaches_of_kStepSim_steps (sim := sim) R h)
    hm

theorem speciesCoverableFrom_one_of_kStepSim_steps_pos [DecidableEq S]
    {B : DetSystem.{u}} {k n : Nat}
    (sim : KStepSim A B k) (R : BoundedStepwiseRealization B N)
    {x y : A.Cfg} {s : S}
    (h : A.steps? n x = some y)
    (hpos : 0 < R.enc (sim.enc y) s) :
    N.SpeciesCoverableFrom (R.enc (sim.enc x)) s :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (reaches_of_kStepSim_steps (sim := sim) R h)
    hpos

end BoundedStepwiseRealization

end Ripple.sCRNUniversality

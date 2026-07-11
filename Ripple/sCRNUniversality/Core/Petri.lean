import Ripple.sCRNUniversality.Core.Run

namespace Ripple.sCRNUniversality

structure PetriNet (S : Type u) where
  I : Type v
  [fintypeI : Fintype I]
  pre : I -> Complex S
  post : I -> Complex S

attribute [instance] PetriNet.fintypeI

namespace PetriNet

variable {S : Type u}

def enabled (P : PetriNet S) (i : P.I) (z : State S) : Prop :=
  forall s, P.pre i s <= z s

def fire (P : PetriNet S) (i : P.I) (z : State S) : State S :=
  fun s => z s - P.pre i s + P.post i s

def StepAt (P : PetriNet S) (i : P.I) (z z' : State S) : Prop :=
  P.enabled i z /\ z' = P.fire i z

def Step (P : PetriNet S) (z z' : State S) : Prop :=
  exists i : P.I, P.StepAt i z z'

abbrev Exec (P : PetriNet S) : State S -> State S -> List P.I -> Prop :=
  ExecOf P.StepAt

def Reaches (P : PetriNet S) (z z' : State S) : Prop :=
  exists is : List P.I, Exec P z z' is

def CoverableFrom (P : PetriNet S) (z0 target : State S) : Prop :=
  exists z, P.Reaches z0 z /\ Covers z target

def EnabledAt (P : PetriNet S) (z : State S) (i : P.I) : Prop :=
  P.enabled i z

def Terminal (P : PetriNet S) (z : State S) : Prop :=
  forall i : P.I, Not (P.EnabledAt z i)

def SpeciesCoverableFrom [DecidableEq S]
    (P : PetriNet S) (z0 : State S) (s : S) (n : Nat := 1) : Prop :=
  P.CoverableFrom z0 (State.single s n)

def parallel (P Q : PetriNet S) : PetriNet S where
  I := Sum P.I Q.I
  fintypeI := inferInstance
  pre := Sum.elim P.pre Q.pre
  post := Sum.elim P.post Q.post

theorem enabledAt_iff_enabled (P : PetriNet S) (z : State S) (i : P.I) :
    P.EnabledAt z i <-> P.enabled i z := by
  rfl

theorem reaches_refl (P : PetriNet S) (z : State S) :
    P.Reaches z z := by
  exact ⟨[], ExecOf.nil z⟩

theorem step_iff_exists_stepAt (P : PetriNet S) (z z' : State S) :
    P.Step z z' <-> exists i : P.I, P.StepAt i z z' := by
  rfl

theorem reaches_of_exec {P : PetriNet S} {z z' : State S} {is : List P.I}
    (h : P.Exec z z' is) :
    P.Reaches z z' := by
  exact ⟨is, h⟩

theorem exec_singleton_of_stepAt
    {P : PetriNet S} {i : P.I} {z z' : State S}
    (h : P.StepAt i z z') :
    P.Exec z z' [i] :=
  ExecOf.cons h (ExecOf.nil z')

theorem exec_pair_of_stepAt
    {P : PetriNet S} {i j : P.I}
    {z₀ z₁ z₂ : State S}
    (h₁ : P.StepAt i z₀ z₁)
    (h₂ : P.StepAt j z₁ z₂) :
    P.Exec z₀ z₂ [i, j] :=
  ExecOf.cons h₁ (ExecOf.cons h₂ (ExecOf.nil z₂))

theorem exec_triple_of_stepAt
    {P : PetriNet S} {i j k : P.I}
    {z₀ z₁ z₂ z₃ : State S}
    (h₁ : P.StepAt i z₀ z₁)
    (h₂ : P.StepAt j z₁ z₂)
    (h₃ : P.StepAt k z₂ z₃) :
    P.Exec z₀ z₃ [i, j, k] :=
  ExecOf.cons h₁ (ExecOf.cons h₂ (ExecOf.cons h₃ (ExecOf.nil z₃)))

theorem reaches_trans {P : PetriNet S} {z0 z1 z2 : State S}
    (h01 : P.Reaches z0 z1) (h12 : P.Reaches z1 z2) :
    P.Reaches z0 z2 := by
  rcases h01 with ⟨is, hIs⟩
  rcases h12 with ⟨js, hJs⟩
  exact ⟨is ++ js, ExecOf.append hIs hJs⟩

theorem reaches_of_stepAt
    {P : PetriNet S} {i : P.I} {z z' : State S}
    (h : P.StepAt i z z') :
    P.Reaches z z' :=
  ⟨[i], exec_singleton_of_stepAt h⟩

theorem stepAt_reaches
    {P : PetriNet S} {i : P.I} {z z' : State S}
    (h : P.StepAt i z z') :
    P.Reaches z z' :=
  reaches_of_stepAt h

theorem step_reaches
    (P : PetriNet S) {z z' : State S}
    (h : P.Step z z') :
    P.Reaches z z' := by
  rcases h with ⟨_i, hStepAt⟩
  exact reaches_of_stepAt hStepAt

theorem coverable_of_reaches_of_covers
    {P : PetriNet S} {z0 z target : State S}
    (hReach : P.Reaches z0 z) (hCovers : Covers z target) :
    P.CoverableFrom z0 target := by
  exact ⟨z, hReach, hCovers⟩

theorem coverable_of_reaches
    {P : PetriNet S} {z0 target : State S}
    (hReach : P.Reaches z0 target) :
    P.CoverableFrom z0 target := by
  exact coverable_of_reaches_of_covers hReach (Covers.refl target)

theorem coverable_of_initial_covers
    {P : PetriNet S} {z0 target : State S}
    (hCovers : Covers z0 target) :
    P.CoverableFrom z0 target :=
  coverable_of_reaches_of_covers (reaches_refl P z0) hCovers

namespace CoverableFrom

theorem mono_target
    {P : PetriNet S} {z0 target target' : State S}
    (hCoverable : P.CoverableFrom z0 target)
    (hTarget : Covers target target') :
    P.CoverableFrom z0 target' := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact ⟨z, hReach, Covers.trans hCovers hTarget⟩

theorem of_reaches_left
    {P : PetriNet S} {z0 z1 target : State S}
    (hLeft : P.Reaches z0 z1)
    (hCoverable : P.CoverableFrom z1 target) :
    P.CoverableFrom z0 target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact ⟨z, reaches_trans hLeft hReach, hCovers⟩

end CoverableFrom

theorem exists_stepAt_iff_enabledAt
    {P : PetriNet S} {i : P.I} {z : State S} :
    (exists z', P.StepAt i z z') <-> P.EnabledAt z i := by
  constructor
  · rintro ⟨_z', hStep⟩
    exact hStep.1
  · intro hEnabled
    exact ⟨P.fire i z, hEnabled, rfl⟩

theorem terminal_iff_no_stepAt
    {P : PetriNet S} {z : State S} :
    P.Terminal z <-> forall i z', Not (P.StepAt i z z') := by
  constructor
  · intro hTerminal i z' hStep
    exact hTerminal i hStep.1
  · intro hNoStep i hEnabled
    exact hNoStep i (P.fire i z) ⟨hEnabled, rfl⟩

theorem terminal_iff_no_step
    {P : PetriNet S} {z : State S} :
    P.Terminal z <-> forall z', Not (P.Step z z') := by
  constructor
  · intro hTerminal z' hStep
    rcases hStep with ⟨i, hStepAt⟩
    exact hTerminal i hStepAt.1
  · intro hNoStep i hEnabled
    exact hNoStep (P.fire i z) ⟨i, hEnabled, rfl⟩

theorem not_terminal_of_stepAt
    {P : PetriNet S} {i : P.I} {z z' : State S}
    (h : P.StepAt i z z') :
    Not (P.Terminal z) := by
  intro hTerminal
  exact hTerminal i h.1

theorem enabled_of_covers
    {P : PetriNet S} {i : P.I} {z w : State S}
    (hEnabled : P.enabled i z) (hCovers : Covers w z) :
    P.enabled i w := by
  intro s
  exact le_trans (hEnabled s) (hCovers s)

theorem fire_covers_fire_of_covers
    {P : PetriNet S} {i : P.I} {z w : State S}
    (hCovers : Covers w z) :
    Covers (P.fire i w) (P.fire i z) := by
  intro s
  have hsub : z s - P.pre i s <= w s - P.pre i s :=
    Nat.sub_le_sub_right (hCovers s) (P.pre i s)
  exact Nat.add_le_add_right hsub (P.post i s)

theorem enabled_add_right
    {P : PetriNet S} {i : P.I} {z extra : State S}
    (hEnabled : P.enabled i z) :
    P.enabled i (State.add z extra) := by
  intro s
  exact le_trans (hEnabled s) (Nat.le_add_right (z s) (extra s))

theorem enabled_add_left
    {P : PetriNet S} {i : P.I} {z extra : State S}
    (hEnabled : P.enabled i z) :
    P.enabled i (State.add extra z) := by
  simpa [State.add_comm] using
    (enabled_add_right (extra := extra) hEnabled)

theorem fire_add_right_of_enabled
    {P : PetriNet S} {i : P.I} {z extra : State S}
    (hEnabled : P.enabled i z) :
    P.fire i (State.add z extra) = State.add (P.fire i z) extra := by
  funext s
  dsimp [PetriNet.fire, State.add]
  have hpre : P.pre i s <= z s := hEnabled s
  omega

theorem fire_add_left_of_enabled
    {P : PetriNet S} {i : P.I} {z extra : State S}
    (hEnabled : P.enabled i z) :
    P.fire i (State.add extra z) = State.add extra (P.fire i z) := by
  simpa [State.add_comm] using
    (fire_add_right_of_enabled (extra := extra) hEnabled)

namespace StepAt

theorem add_right
    {P : PetriNet S} {i : P.I} {z z' extra : State S}
    (hStep : P.StepAt i z z') :
    P.StepAt i (State.add z extra) (State.add z' extra) := by
  refine ⟨enabled_add_right hStep.1, ?_⟩
  rw [hStep.2, fire_add_right_of_enabled hStep.1]

theorem add_left
    {P : PetriNet S} {i : P.I} {z z' extra : State S}
    (hStep : P.StepAt i z z') :
    P.StepAt i (State.add extra z) (State.add extra z') := by
  refine ⟨enabled_add_left hStep.1, ?_⟩
  rw [hStep.2, fire_add_left_of_enabled hStep.1]

theorem lift_covers
    {P : PetriNet S} {i : P.I} {z z' w : State S}
    (hStep : P.StepAt i z z') (hCovers : Covers w z) :
    exists w', P.StepAt i w w' /\ Covers w' z' := by
  refine ⟨P.fire i w, ?_, ?_⟩
  · exact ⟨enabled_of_covers hStep.1 hCovers, rfl⟩
  · rw [hStep.2]
    exact fire_covers_fire_of_covers hCovers

end StepAt

namespace Step

theorem add_right
    {P : PetriNet S} {z z' extra : State S}
    (hStep : P.Step z z') :
    P.Step (State.add z extra) (State.add z' extra) := by
  rcases hStep with ⟨i, hStepAt⟩
  exact ⟨i, StepAt.add_right hStepAt⟩

theorem add_left
    {P : PetriNet S} {z z' extra : State S}
    (hStep : P.Step z z') :
    P.Step (State.add extra z) (State.add extra z') := by
  rcases hStep with ⟨i, hStepAt⟩
  exact ⟨i, StepAt.add_left hStepAt⟩

end Step

namespace Exec

theorem add_right
    {P : PetriNet S} {z z' extra : State S} {is : List P.I}
    (hExec : P.Exec z z' is) :
    P.Exec (State.add z extra) (State.add z' extra) is := by
  induction hExec with
  | nil z =>
      exact ExecOf.nil (State.add z extra)
  | cons hStep _hTail ih =>
      exact ExecOf.cons (StepAt.add_right hStep) ih

theorem add_left
    {P : PetriNet S} {z z' extra : State S} {is : List P.I}
    (hExec : P.Exec z z' is) :
    P.Exec (State.add extra z) (State.add extra z') is := by
  simpa [State.add_comm] using
    (add_right (extra := extra) hExec)

theorem indices_eq_nil_of_terminal
    {P : PetriNet S} {z z' : State S} {is : List P.I}
    (hTerminal : P.Terminal z)
    (hExec : P.Exec z z' is) :
    is = [] := by
  cases is with
  | nil =>
      rfl
  | cons i is =>
      rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hStep, _hTail⟩
      exact False.elim
        ((terminal_iff_no_stepAt.mp hTerminal) i zMid hStep)

theorem eq_of_terminal
    {P : PetriNet S} {z z' : State S} {is : List P.I}
    (hTerminal : P.Terminal z)
    (hExec : P.Exec z z' is) :
    z' = z := by
  have hNil : is = [] := indices_eq_nil_of_terminal hTerminal hExec
  subst hNil
  exact (ExecOf.nil_iff.mp hExec).symm

theorem eq_nil_of_terminal
    {P : PetriNet S} {z z' : State S} {is : List P.I}
    (hTerminal : P.Terminal z)
    (hExec : P.Exec z z' is) :
    z' = z /\ is = [] :=
  ⟨eq_of_terminal hTerminal hExec,
    indices_eq_nil_of_terminal hTerminal hExec⟩

theorem lift_covers
    {P : PetriNet S} {z z' w : State S} {is : List P.I}
    (hExec : P.Exec z z' is) (hCovers : Covers w z) :
    exists w', P.Exec w w' is /\ Covers w' z' := by
  exact ExecOf.lift_rel
    (R := Covers)
    (stepAt := P.StepAt)
    (fun {i a b w} hStep hRel => PetriNet.StepAt.lift_covers hStep hRel)
    hExec
    hCovers

end Exec

namespace Reaches

theorem add_right
    {P : PetriNet S} {z z' extra : State S}
    (hReach : P.Reaches z z') :
    P.Reaches (State.add z extra) (State.add z' extra) := by
  rcases hReach with ⟨is, hExec⟩
  exact ⟨is, Exec.add_right hExec⟩

theorem add_left
    {P : PetriNet S} {z z' extra : State S}
    (hReach : P.Reaches z z') :
    P.Reaches (State.add extra z) (State.add extra z') := by
  rcases hReach with ⟨is, hExec⟩
  exact ⟨is, Exec.add_left hExec⟩

theorem eq_of_terminal
    {P : PetriNet S} {z z' : State S}
    (hTerminal : P.Terminal z)
    (hReach : P.Reaches z z') :
    z' = z := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.eq_of_terminal hTerminal hExec

theorem lift_covers
    {P : PetriNet S} {z z' w : State S}
    (hReach : P.Reaches z z') (hCovers : Covers w z) :
    exists w', P.Reaches w w' /\ Covers w' z' := by
  rcases hReach with ⟨is, hExec⟩
  rcases Exec.lift_covers hExec hCovers with ⟨w', hExec', hCovers'⟩
  exact ⟨w', ⟨is, hExec'⟩, hCovers'⟩

end Reaches

theorem coverableFrom_terminal_iff
    {P : PetriNet S} {z target : State S}
    (hTerminal : P.Terminal z) :
    P.CoverableFrom z target <-> Covers z target := by
  constructor
  · rintro ⟨z', hReach, hCovers⟩
    have hEq : z' = z := Reaches.eq_of_terminal hTerminal hReach
    subst hEq
    exact hCovers
  · intro hCovers
    exact coverable_of_reaches_of_covers (reaches_refl P z) hCovers

theorem coverable_lift_initial
    {P : PetriNet S} {z0 w0 target : State S}
    (hInitial : Covers w0 z0)
    (hCoverable : P.CoverableFrom z0 target) :
    P.CoverableFrom w0 target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  rcases Reaches.lift_covers hReach hInitial with
    ⟨w, hReach', hCovers'⟩
  exact ⟨w, hReach', Covers.trans hCovers' hCovers⟩

namespace CoverableFrom

theorem add_right
    {P : PetriNet S} {z0 target extra : State S}
    (hCoverable : P.CoverableFrom z0 target) :
    P.CoverableFrom (State.add z0 extra) (State.add target extra) := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add z extra,
      Reaches.add_right hReach,
      Covers.add hCovers (Covers.refl extra)⟩

theorem add_left
    {P : PetriNet S} {z0 target extra : State S}
    (hCoverable : P.CoverableFrom z0 target) :
    P.CoverableFrom (State.add extra z0) (State.add extra target) := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add extra z,
      by
        simpa [State.add_comm] using
          (Reaches.add_right (extra := extra) hReach),
      Covers.add (Covers.refl extra) hCovers⟩

theorem initial_add_right
    {P : PetriNet S} {z0 target extra : State S}
    (hCoverable : P.CoverableFrom z0 target) :
    P.CoverableFrom (State.add z0 extra) target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add z extra,
      Reaches.add_right hReach,
      Covers.add_left hCovers⟩

theorem initial_add_left
    {P : PetriNet S} {z0 target extra : State S}
    (hCoverable : P.CoverableFrom z0 target) :
    P.CoverableFrom (State.add extra z0) target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add extra z,
      by
        simpa [State.add_comm] using
          (Reaches.add_right (extra := extra) hReach),
      Covers.add_right hCovers⟩

end CoverableFrom

theorem speciesCoverableFrom_iff [DecidableEq S]
    {P : PetriNet S} {z0 : State S} {s : S} {n : Nat} :
    P.SpeciesCoverableFrom z0 s n <->
      exists z, P.Reaches z0 z /\ n <= z s := by
  constructor
  · rintro ⟨z, hReach, hCovers⟩
    exact ⟨z, hReach, Covers.single_iff.mp hCovers⟩
  · rintro ⟨z, hReach, hn⟩
    exact ⟨z, hReach, Covers.single_iff.mpr hn⟩

theorem speciesCoverableFrom_of_reaches_coord [DecidableEq S]
    {P : PetriNet S} {z0 z : State S} {s : S} {n : Nat}
    (hReach : P.Reaches z0 z) (hn : n <= z s) :
    P.SpeciesCoverableFrom z0 s n := by
  exact speciesCoverableFrom_iff.mpr ⟨z, hReach, hn⟩

theorem speciesCoverableFrom_one_of_reaches_pos [DecidableEq S]
    {P : PetriNet S} {z0 z : State S} {s : S}
    (hReach : P.Reaches z0 z) (hpos : 0 < z s) :
    P.SpeciesCoverableFrom z0 s :=
  speciesCoverableFrom_of_reaches_coord hReach (Nat.succ_le_of_lt hpos)

theorem speciesCoverableFrom_initial_add_right [DecidableEq S]
    {P : PetriNet S} {z0 extra : State S} {s : S} {n : Nat}
    (hCoverable : P.SpeciesCoverableFrom z0 s n) :
    P.SpeciesCoverableFrom (State.add z0 extra) s n :=
  CoverableFrom.initial_add_right hCoverable

theorem speciesCoverableFrom_initial_add_left [DecidableEq S]
    {P : PetriNet S} {z0 extra : State S} {s : S} {n : Nat}
    (hCoverable : P.SpeciesCoverableFrom z0 s n) :
    P.SpeciesCoverableFrom (State.add extra z0) s n :=
  CoverableFrom.initial_add_left hCoverable

namespace SpeciesCoverableFrom

theorem exists_reaches_coord [DecidableEq S]
    {P : PetriNet S} {z0 : State S} {s : S} {n : Nat}
    (h : P.SpeciesCoverableFrom z0 s n) :
    exists z, P.Reaches z0 z /\ n <= z s :=
  speciesCoverableFrom_iff.mp h

end SpeciesCoverableFrom

theorem speciesCoverableFrom_terminal_iff [DecidableEq S]
    {P : PetriNet S} {z : State S} {s : S} {n : Nat}
    (hTerminal : P.Terminal z) :
    P.SpeciesCoverableFrom z s n <-> n <= z s := by
  constructor
  · intro h
    exact Covers.single_iff.mp
      ((coverableFrom_terminal_iff hTerminal).mp h)
  · intro hn
    exact (coverableFrom_terminal_iff hTerminal).mpr
      (Covers.single_iff.mpr hn)

theorem parallel_stepAt_inl
    (P Q : PetriNet S) {i : P.I} {z z' : State S} :
    (P.parallel Q).StepAt (Sum.inl i) z z' <-> P.StepAt i z z' := by
  rfl

theorem parallel_stepAt_inr
    (P Q : PetriNet S) {i : Q.I} {z z' : State S} :
    (P.parallel Q).StepAt (Sum.inr i) z z' <-> Q.StepAt i z z' := by
  rfl

theorem parallel_step_iff_or
    (P Q : PetriNet S) {z z' : State S} :
    (P.parallel Q).Step z z' <-> P.Step z z' \/ Q.Step z z' := by
  constructor
  · rintro ⟨i, hStep⟩
    cases i with
    | inl i =>
        exact Or.inl ⟨i, hStep⟩
    | inr i =>
        exact Or.inr ⟨i, hStep⟩
  · rintro (h | h)
    · rcases h with ⟨i, hStep⟩
      exact ⟨Sum.inl i, hStep⟩
    · rcases h with ⟨i, hStep⟩
      exact ⟨Sum.inr i, hStep⟩

theorem parallel_exec_inl
    (P Q : PetriNet S) {z z' : State S} {is : List P.I}
    (h : P.Exec z z' is) :
    (P.parallel Q).Exec z z' (is.map Sum.inl) := by
  induction is generalizing z with
  | nil =>
      exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
  | cons i is ih =>
      rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
      exact ExecOf.cons hStep (ih hTail)

theorem parallel_exec_inr
    (P Q : PetriNet S) {z z' : State S} {is : List Q.I}
    (h : Q.Exec z z' is) :
    (P.parallel Q).Exec z z' (is.map Sum.inr) := by
  induction is generalizing z with
  | nil =>
      exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
  | cons i is ih =>
      rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
      exact ExecOf.cons hStep (ih hTail)

theorem parallel_exec_inl_iff
    (P Q : PetriNet S) {z z' : State S} {is : List P.I} :
    (P.parallel Q).Exec z z' (is.map Sum.inl) <-> P.Exec z z' is := by
  constructor
  · intro h
    induction is generalizing z with
    | nil =>
        exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
    | cons i is ih =>
        rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
        exact ExecOf.cons hStep (ih hTail)
  · intro h
    exact parallel_exec_inl P Q h

theorem parallel_exec_inr_iff
    (P Q : PetriNet S) {z z' : State S} {is : List Q.I} :
    (P.parallel Q).Exec z z' (is.map Sum.inr) <-> Q.Exec z z' is := by
  constructor
  · intro h
    induction is generalizing z with
    | nil =>
        exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
    | cons i is ih =>
        rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
        exact ExecOf.cons hStep (ih hTail)
  · intro h
    exact parallel_exec_inr P Q h

theorem parallel_exec_inl_append_inr
    (P Q : PetriNet S) {z0 z1 z2 : State S}
    {is : List P.I} {js : List Q.I}
    (hP : P.Exec z0 z1 is) (hQ : Q.Exec z1 z2 js) :
    (P.parallel Q).Exec z0 z2 (is.map Sum.inl ++ js.map Sum.inr) :=
  ExecOf.append (parallel_exec_inl P Q hP) (parallel_exec_inr P Q hQ)

theorem parallel_exec_inr_append_inl
    (P Q : PetriNet S) {z0 z1 z2 : State S}
    {is : List Q.I} {js : List P.I}
    (hQ : Q.Exec z0 z1 is) (hP : P.Exec z1 z2 js) :
    (P.parallel Q).Exec z0 z2 (is.map Sum.inr ++ js.map Sum.inl) :=
  ExecOf.append (parallel_exec_inr P Q hQ) (parallel_exec_inl P Q hP)

theorem parallel_reaches_inl
    (P Q : PetriNet S) {z z' : State S}
    (h : P.Reaches z z') :
    (P.parallel Q).Reaches z z' := by
  rcases h with ⟨is, hExec⟩
  exact ⟨is.map Sum.inl, parallel_exec_inl P Q hExec⟩

theorem parallel_reaches_inr
    (P Q : PetriNet S) {z z' : State S}
    (h : Q.Reaches z z') :
    (P.parallel Q).Reaches z z' := by
  rcases h with ⟨is, hExec⟩
  exact ⟨is.map Sum.inr, parallel_exec_inr P Q hExec⟩

theorem parallel_reaches_left_then_right
    (P Q : PetriNet S) {z0 z1 z2 : State S}
    (hP : P.Reaches z0 z1) (hQ : Q.Reaches z1 z2) :
    (P.parallel Q).Reaches z0 z2 := by
  rcases hP with ⟨is, hExecP⟩
  rcases hQ with ⟨js, hExecQ⟩
  exact ⟨is.map Sum.inl ++ js.map Sum.inr,
    parallel_exec_inl_append_inr P Q hExecP hExecQ⟩

theorem parallel_reaches_right_then_left
    (P Q : PetriNet S) {z0 z1 z2 : State S}
    (hQ : Q.Reaches z0 z1) (hP : P.Reaches z1 z2) :
    (P.parallel Q).Reaches z0 z2 := by
  rcases hQ with ⟨is, hExecQ⟩
  rcases hP with ⟨js, hExecP⟩
  exact ⟨is.map Sum.inr ++ js.map Sum.inl,
    parallel_exec_inr_append_inl P Q hExecQ hExecP⟩

theorem parallel_coverable_inl
    (P Q : PetriNet S) {z0 target : State S}
    (h : P.CoverableFrom z0 target) :
    (P.parallel Q).CoverableFrom z0 target := by
  rcases h with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_inl P Q hReach, hCovers⟩

theorem parallel_coverable_inr
    (P Q : PetriNet S) {z0 target : State S}
    (h : Q.CoverableFrom z0 target) :
    (P.parallel Q).CoverableFrom z0 target := by
  rcases h with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_inr P Q hReach, hCovers⟩

theorem parallel_coverable_left_then_right
    (P Q : PetriNet S) {z0 z1 target : State S}
    (hP : P.Reaches z0 z1)
    (hQ : Q.CoverableFrom z1 target) :
    (P.parallel Q).CoverableFrom z0 target := by
  rcases hQ with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_left_then_right P Q hP hReach, hCovers⟩

theorem parallel_coverable_right_then_left
    (P Q : PetriNet S) {z0 z1 target : State S}
    (hQ : Q.Reaches z0 z1)
    (hP : P.CoverableFrom z1 target) :
    (P.parallel Q).CoverableFrom z0 target := by
  rcases hP with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_right_then_left P Q hQ hReach, hCovers⟩

theorem parallel_speciesCoverableFrom_inl [DecidableEq S]
    (P Q : PetriNet S) {z0 : State S} {s : S} {n : Nat}
    (h : P.SpeciesCoverableFrom z0 s n) :
    (P.parallel Q).SpeciesCoverableFrom z0 s n :=
  parallel_coverable_inl P Q h

theorem parallel_speciesCoverableFrom_inr [DecidableEq S]
    (P Q : PetriNet S) {z0 : State S} {s : S} {n : Nat}
    (h : Q.SpeciesCoverableFrom z0 s n) :
    (P.parallel Q).SpeciesCoverableFrom z0 s n :=
  parallel_coverable_inr P Q h

theorem parallel_terminal_iff_and
    (P Q : PetriNet S) {z : State S} :
    (P.parallel Q).Terminal z <-> P.Terminal z /\ Q.Terminal z := by
  constructor
  · intro hTerminal
    constructor
    · intro i hEnabled
      exact hTerminal (Sum.inl i) hEnabled
    · intro i hEnabled
      exact hTerminal (Sum.inr i) hEnabled
  · rintro ⟨hP, hQ⟩ i
    cases i with
    | inl i =>
        exact hP i
    | inr i =>
        exact hQ i

theorem parallel_terminal_of_terminal
    (P Q : PetriNet S) {z : State S}
    (hP : P.Terminal z) (hQ : Q.Terminal z) :
    (P.parallel Q).Terminal z :=
  (parallel_terminal_iff_and P Q).mpr ⟨hP, hQ⟩

end PetriNet

namespace Network

variable {S : Type u}

def toPetri (N : Network S) : PetriNet S where
  I := N.I
  pre := fun i => (N.rxn i).l
  post := fun i => (N.rxn i).r

theorem toPetri_step_iff (N : Network S) (z z' : State S) :
    (N.toPetri).Step z z' <-> N.Step z z' := by
  constructor
  · intro h
    rcases h with ⟨i, hEnabled, hFire⟩
    exact ⟨i, hEnabled, hFire⟩
  · intro h
    rcases h with ⟨i, hEnabled, hFire⟩
    exact ⟨i, hEnabled, hFire⟩

theorem toPetri_stepAt_iff (N : Network S) (i : N.I) (z z' : State S) :
    (N.toPetri).StepAt i z z' <-> N.StepAt i z z' := by
  rfl

theorem toPetri_exec_iff (N : Network S) {z z' : State S} {is : List N.I} :
    (N.toPetri).Exec z z' is <-> N.Exec z z' is := by
  exact ExecOf.congr_step (fun i z z' => toPetri_stepAt_iff N i z z')

theorem toPetri_reaches_iff (N : Network S) (z z' : State S) :
    (N.toPetri).Reaches z z' <-> N.Reaches z z' := by
  constructor
  · intro h
    rcases h with ⟨is, hExec⟩
    exact ⟨is, (toPetri_exec_iff N).mp hExec⟩
  · intro h
    rcases h with ⟨is, hExec⟩
    exact ⟨is, (toPetri_exec_iff N).mpr hExec⟩

theorem toPetri_coverable_iff (N : Network S) (z0 target : State S) :
    (N.toPetri).CoverableFrom z0 target <-> N.CoverableFrom z0 target := by
  constructor
  · intro h
    rcases h with ⟨z, hReach, hCover⟩
    exact ⟨z, (toPetri_reaches_iff N z0 z).mp hReach, hCover⟩
  · intro h
    rcases h with ⟨z, hReach, hCover⟩
    exact ⟨z, (toPetri_reaches_iff N z0 z).mpr hReach, hCover⟩

theorem toPetri_enabledAt_iff (N : Network S) (z : State S) (i : N.I) :
    (N.toPetri).EnabledAt z i <-> N.EnabledAt z i := by
  rfl

theorem toPetri_terminal_iff (N : Network S) (z : State S) :
    (N.toPetri).Terminal z <-> N.Terminal z := by
  constructor
  · intro hTerminal i hEnabled
    exact hTerminal i hEnabled
  · intro hTerminal i hEnabled
    exact hTerminal i hEnabled

theorem toPetri_speciesCoverableFrom_iff [DecidableEq S]
    (N : Network S) (z0 : State S) (s : S) (n : Nat) :
    (N.toPetri).SpeciesCoverableFrom z0 s n <->
      N.SpeciesCoverableFrom z0 s n := by
  exact toPetri_coverable_iff N z0 (State.single s n)

theorem toPetri_speciesCoverableFrom [DecidableEq S]
    (N : Network S) {z0 : State S} {s : S} {n : Nat}
    (h : N.SpeciesCoverableFrom z0 s n) :
    (N.toPetri).SpeciesCoverableFrom z0 s n :=
  (toPetri_speciesCoverableFrom_iff N z0 s n).mpr h

theorem speciesCoverableFrom_of_toPetri [DecidableEq S]
    (N : Network S) {z0 : State S} {s : S} {n : Nat}
    (h : (N.toPetri).SpeciesCoverableFrom z0 s n) :
    N.SpeciesCoverableFrom z0 s n :=
  (toPetri_speciesCoverableFrom_iff N z0 s n).mp h

theorem toPetri_parallel_stepAt_iff
    (N M : Network S)
    (i : (N.parallel M).I) (z z' : State S) :
    ((N.parallel M).toPetri).StepAt i z z' <->
      ((N.toPetri).parallel (M.toPetri)).StepAt i z z' := by
  cases i with
  | inl i =>
      rfl
  | inr i =>
      rfl

theorem toPetri_parallel_exec_iff
    (N M : Network S)
    {z z' : State S} {is : List (N.parallel M).I} :
    ((N.parallel M).toPetri).Exec z z' is <->
      ((N.toPetri).parallel (M.toPetri)).Exec z z' is := by
  exact ExecOf.congr_step
    (fun i z z' => toPetri_parallel_stepAt_iff N M i z z')

theorem toPetri_parallel_reaches_iff
    (N M : Network S) (z z' : State S) :
    ((N.parallel M).toPetri).Reaches z z' <->
      ((N.toPetri).parallel (M.toPetri)).Reaches z z' := by
  constructor
  · rintro ⟨is, hExec⟩
    exact ⟨is, (toPetri_parallel_exec_iff N M).mp hExec⟩
  · rintro ⟨is, hExec⟩
    exact ⟨is, (toPetri_parallel_exec_iff N M).mpr hExec⟩

theorem toPetri_parallel_coverable_iff
    (N M : Network S) (z0 target : State S) :
    ((N.parallel M).toPetri).CoverableFrom z0 target <->
      ((N.toPetri).parallel (M.toPetri)).CoverableFrom z0 target := by
  constructor
  · rintro ⟨z, hReach, hCovers⟩
    exact ⟨z, (toPetri_parallel_reaches_iff N M z0 z).mp hReach, hCovers⟩
  · rintro ⟨z, hReach, hCovers⟩
    exact ⟨z, (toPetri_parallel_reaches_iff N M z0 z).mpr hReach, hCovers⟩

end Network

end Ripple.sCRNUniversality

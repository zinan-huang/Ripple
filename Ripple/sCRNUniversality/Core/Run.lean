import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Relation
import Ripple.sCRNUniversality.Core.Network

namespace Ripple.sCRNUniversality

inductive ExecOf {I : Type u} {Alpha : Type v}
    (stepAt : I -> Alpha -> Alpha -> Prop) :
    Alpha -> Alpha -> List I -> Prop
  | nil (z : Alpha) : ExecOf stepAt z z []
  | cons {z zMid zEnd : Alpha} {i : I} {is : List I}
      (h : stepAt i z zMid)
      (tail : ExecOf stepAt zMid zEnd is) :
      ExecOf stepAt z zEnd (i :: is)

namespace ExecOf

@[simp]
theorem nil_iff {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop} {a b : Alpha} :
    ExecOf stepAt a b [] <-> a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact ExecOf.nil a

theorem cons_iff {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop}
    {a c : Alpha} {i : I} {is : List I} :
    ExecOf stepAt a c (i :: is) <->
      exists b, stepAt i a b /\ ExecOf stepAt b c is := by
  constructor
  · intro h
    cases h with
    | cons hStep hTail =>
        exact ⟨_, hStep, hTail⟩
  · rintro ⟨b, hStep, hTail⟩
    exact ExecOf.cons hStep hTail

@[simp]
theorem singleton_iff {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop}
    {a b : Alpha} {i : I} :
    ExecOf stepAt a b [i] <-> stepAt i a b := by
  constructor
  · intro h
    rcases cons_iff.mp h with ⟨mid, hStep, hTail⟩
    have hEq : mid = b := nil_iff.mp hTail
    subst hEq
    exact hStep
  · intro h
    exact ExecOf.cons h (ExecOf.nil b)

theorem append {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop}
    {a b c : Alpha} {is js : List I}
    (h₁ : ExecOf stepAt a b is)
    (h₂ : ExecOf stepAt b c js) :
    ExecOf stepAt a c (is ++ js) := by
  induction h₁ with
  | nil _ =>
      simpa using h₂
  | cons hStep _tail ih =>
      exact ExecOf.cons hStep (ih h₂)

theorem split_append {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop}
    {a c : Alpha} {is js : List I} :
    ExecOf stepAt a c (is ++ js) <->
      exists b, ExecOf stepAt a b is /\ ExecOf stepAt b c js := by
  induction is generalizing a with
  | nil =>
      constructor
      · intro h
        exact ⟨a, ExecOf.nil a, h⟩
      · rintro ⟨b, hLeft, hRight⟩
        have hEq : a = b := nil_iff.mp hLeft
        subst hEq
        exact hRight
  | cons i is ih =>
      constructor
      · intro h
        rcases cons_iff.mp h with ⟨mid, hStep, hTail⟩
        rcases ih.mp hTail with ⟨b, hLeft, hRight⟩
        exact ⟨b, ExecOf.cons hStep hLeft, hRight⟩
      · rintro ⟨b, hLeft, hRight⟩
        rcases cons_iff.mp hLeft with ⟨mid, hStep, hTail⟩
        exact ExecOf.cons hStep (ih.mpr ⟨b, hTail, hRight⟩)

theorem congr_step {I : Type u} {Alpha : Type v}
    {stepA stepB : I -> Alpha -> Alpha -> Prop}
    (hstep : forall i z z', stepA i z z' <-> stepB i z z') :
    forall {z z' : Alpha} {is : List I},
      ExecOf stepA z z' is <-> ExecOf stepB z z' is := by
  intro z z' is
  constructor
  · intro h
    induction h with
    | nil z =>
        exact ExecOf.nil z
    | cons hStep _tail ih =>
        exact ExecOf.cons ((hstep _ _ _).mp hStep) ih
  · intro h
    induction h with
    | nil z =>
        exact ExecOf.nil z
    | cons hStep _tail ih =>
        exact ExecOf.cons ((hstep _ _ _).mpr hStep) ih

theorem map_index {I : Type u} {K : Type v} {Alpha : Type w} {Beta : Type x}
    {stepA : I -> Alpha -> Alpha -> Prop}
    {stepB : K -> Beta -> Beta -> Prop}
    (fI : I -> K) (fAlpha : Alpha -> Beta)
    (hstep : forall i a b, stepA i a b -> stepB (fI i) (fAlpha a) (fAlpha b)) :
    forall {a b : Alpha} {is : List I},
      ExecOf stepA a b is ->
        ExecOf stepB (fAlpha a) (fAlpha b) (is.map fI) := by
  intro a b is h
  induction h with
  | nil z =>
      exact ExecOf.nil (fAlpha z)
  | cons hStep _tail ih =>
      exact ExecOf.cons (hstep _ _ _ hStep) ih

theorem lift_rel {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop} {R : Alpha -> Alpha -> Prop}
    (hlift :
      forall {i a b w}, stepAt i a b -> R w a ->
        exists w', stepAt i w w' /\ R w' b) :
    forall {a b w : Alpha} {is : List I},
      ExecOf stepAt a b is -> R w a ->
        exists w', ExecOf stepAt w w' is /\ R w' b := by
  intro a b w is hExec hRel
  induction hExec generalizing w with
  | nil a =>
      exact ⟨w, ExecOf.nil w, hRel⟩
  | cons hStep _tail ih =>
      rcases hlift hStep hRel with ⟨wMid, hStep', hRel'⟩
      rcases ih hRel' with ⟨wEnd, hTail', hRelEnd⟩
      exact ⟨wEnd, ExecOf.cons hStep' hTail', hRelEnd⟩

theorem preserves {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop} {P : Alpha -> Prop}
    (hstep : forall {i a b}, stepAt i a b -> P a -> P b) :
    forall {a b : Alpha} {is : List I},
      ExecOf stepAt a b is -> P a -> P b := by
  intro a b is hExec hP
  induction hExec with
  | nil _ =>
      exact hP
  | cons hStep _tail ih =>
      exact ih (hstep hStep hP)

theorem unique_of_functional {I : Type u} {Alpha : Type v}
    {stepAt : I -> Alpha -> Alpha -> Prop}
    (hfun :
      forall {i a b c}, stepAt i a b -> stepAt i a c -> b = c) :
    forall {a b c : Alpha} {is : List I},
      ExecOf stepAt a b is -> ExecOf stepAt a c is -> b = c := by
  intro a b c is hb hc
  induction is generalizing a b c with
  | nil =>
      have hbEq : a = b := nil_iff.mp hb
      have hcEq : a = c := nil_iff.mp hc
      exact hbEq.symm.trans hcEq
  | cons i is ih =>
      rcases cons_iff.mp hb with ⟨bMid, hbStep, hbTail⟩
      rcases cons_iff.mp hc with ⟨cMid, hcStep, hcTail⟩
      have hMid : bMid = cMid := hfun hbStep hcStep
      subst hMid
      exact ih hbTail hcTail

end ExecOf

namespace Reaction

variable {S : Type u}

def Untouches (rho : Reaction S) (P : S -> Prop) : Prop :=
  forall s, P s -> ¬ rho.Touches s

end Reaction

namespace Network

variable {S : Type u}

def Untouches (N : Network S) (P : S -> Prop) : Prop :=
  forall i : N.I, (N.rxn i).Untouches P

def StepAt (N : Network S) (i : N.I) (z z' : State S) : Prop :=
  (N.rxn i).FiresTo z z'

def Step (N : Network S) (z z' : State S) : Prop :=
  exists i : N.I, N.StepAt i z z'

abbrev Exec (N : Network S) : State S -> State S -> List N.I -> Prop :=
  ExecOf N.StepAt

def Reaches (N : Network S) (z z' : State S) : Prop :=
  exists is : List N.I, Exec N z z' is

def EnabledAt (N : Network S) (z : State S) (i : N.I) : Prop :=
  (N.rxn i).enabled z

def Terminal (N : Network S) (z : State S) : Prop :=
  forall i : N.I, Not (N.EnabledAt z i)

def StepInvariant (N : Network S) (P : State S -> Prop) : Prop :=
  forall {i : N.I} {z z' : State S}, N.StepAt i z z' -> P z -> P z'

def ReachableFrom (N : Network S) (z0 target : State S) : Prop :=
  N.Reaches z0 target

def CoverableFrom (N : Network S) (z0 target : State S) : Prop :=
  exists z, N.Reaches z0 z /\ Covers z target

def SpeciesCoverableFrom [DecidableEq S]
    (N : Network S) (z0 : State S) (s : S) (n : Nat := 1) : Prop :=
  N.CoverableFrom z0 (State.single s n)

theorem reaches_refl (N : Network S) (z : State S) : N.Reaches z z := by
  exact Exists.intro [] (ExecOf.nil z)

theorem step_iff_exists_stepAt (N : Network S) (z z' : State S) :
    N.Step z z' <-> exists i : N.I, N.StepAt i z z' := by
  rfl

theorem reaches_of_exec {N : Network S} {z z' : State S} {is : List N.I}
    (h : N.Exec z z' is) : N.Reaches z z' := by
  exact ⟨is, h⟩

theorem exec_singleton_of_stepAt
    {N : Network S} {i : N.I} {z z' : State S}
    (h : N.StepAt i z z') :
    N.Exec z z' [i] :=
  ExecOf.cons h (ExecOf.nil z')

theorem exec_singleton_of_firesTo
    {N : Network S} {i : N.I} {z z' : State S}
    (h : (N.rxn i).FiresTo z z') :
    N.Exec z z' [i] :=
  exec_singleton_of_stepAt h

theorem exec_pair_of_stepAt
    {N : Network S} {i j : N.I}
    {z₀ z₁ z₂ : State S}
    (h₁ : N.StepAt i z₀ z₁)
    (h₂ : N.StepAt j z₁ z₂) :
    N.Exec z₀ z₂ [i, j] :=
  ExecOf.cons h₁ (ExecOf.cons h₂ (ExecOf.nil z₂))

theorem exec_triple_of_stepAt
    {N : Network S} {i j k : N.I}
    {z₀ z₁ z₂ z₃ : State S}
    (h₁ : N.StepAt i z₀ z₁)
    (h₂ : N.StepAt j z₁ z₂)
    (h₃ : N.StepAt k z₂ z₃) :
    N.Exec z₀ z₃ [i, j, k] :=
  ExecOf.cons h₁ (ExecOf.cons h₂ (ExecOf.cons h₃ (ExecOf.nil z₃)))

theorem reaches_trans {N : Network S} {z0 z1 z2 : State S}
    (h01 : N.Reaches z0 z1) (h12 : N.Reaches z1 z2) :
    N.Reaches z0 z2 := by
  rcases h01 with ⟨is, hIs⟩
  rcases h12 with ⟨js, hJs⟩
  exact ⟨is ++ js, ExecOf.append hIs hJs⟩

theorem coverable_of_reaches_of_covers {N : Network S} {z0 z target : State S}
    (hReach : N.Reaches z0 z) (hCovers : Covers z target) :
    N.CoverableFrom z0 target := by
  exact ⟨z, hReach, hCovers⟩

theorem coverable_of_reaches {N : Network S} {z0 target : State S}
    (hReach : N.Reaches z0 target) : N.CoverableFrom z0 target := by
  exact coverable_of_reaches_of_covers hReach (Covers.refl target)

theorem coverable_of_initial_covers {N : Network S} {z0 target : State S}
    (hCovers : Covers z0 target) :
    N.CoverableFrom z0 target :=
  coverable_of_reaches_of_covers (reaches_refl N z0) hCovers

namespace CoverableFrom

theorem mono_target {N : Network S} {z0 target target' : State S}
    (hCoverable : N.CoverableFrom z0 target)
    (hTarget : Covers target target') :
    N.CoverableFrom z0 target' := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact ⟨z, hReach, Covers.trans hCovers hTarget⟩

theorem of_reaches_left {N : Network S} {z0 z1 target : State S}
    (hLeft : N.Reaches z0 z1)
    (hCoverable : N.CoverableFrom z1 target) :
    N.CoverableFrom z0 target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact ⟨z, reaches_trans hLeft hReach, hCovers⟩

end CoverableFrom

theorem reaches_of_stepAt {N : Network S} {i : N.I} {z z' : State S}
    (h : N.StepAt i z z') : N.Reaches z z' := by
  exact ⟨[i], exec_singleton_of_stepAt h⟩

theorem stepAt_reaches {N : Network S} {i : N.I} {z z' : State S}
    (h : N.StepAt i z z') : N.Reaches z z' :=
  reaches_of_stepAt h

theorem step_reaches (N : Network S) {z z' : State S}
    (h : N.Step z z') : N.Reaches z z' := by
  rcases h with ⟨_i, hStepAt⟩
  exact reaches_of_stepAt hStepAt

theorem exists_stepAt_iff_enabledAt {N : Network S} {i : N.I} {z : State S} :
    (exists z', N.StepAt i z z') <-> N.EnabledAt z i := by
  constructor
  · rintro ⟨_z', hStep⟩
    exact hStep.1
  · intro h
    exact ⟨(N.rxn i).fire z, h, rfl⟩

theorem terminal_iff_no_stepAt {N : Network S} {z : State S} :
    N.Terminal z <-> forall i z', Not (N.StepAt i z z') := by
  constructor
  · intro hTerminal i z' hStep
    exact hTerminal i hStep.1
  · intro hNoStep i hEnabled
    exact hNoStep i ((N.rxn i).fire z) ⟨hEnabled, rfl⟩

theorem not_terminal_of_stepAt {N : Network S} {i : N.I} {z z' : State S}
    (h : N.StepAt i z z') : ¬ N.Terminal z := by
  intro hTerminal
  exact hTerminal i h.enabled

namespace StepInvariant

theorem exec {N : Network S} {P : State S -> Prop}
    (hInv : N.StepInvariant P) {z z' : State S} {is : List N.I}
    (hExec : N.Exec z z' is) (hP : P z) :
    P z' :=
  ExecOf.preserves (stepAt := N.StepAt) hInv hExec hP

theorem reaches {N : Network S} {P : State S -> Prop}
    (hInv : N.StepInvariant P) {z z' : State S}
    (hReach : N.Reaches z z') (hP : P z) :
    P z' := by
  rcases hReach with ⟨is, hExec⟩
  exact hInv.exec hExec hP

end StepInvariant

namespace StepAt

theorem add_right {N : Network S} {i : N.I} {z z' extra : State S}
    (hStep : N.StepAt i z z') :
    N.StepAt i (State.add z extra) (State.add z' extra) :=
  Reaction.FiresTo.add_right hStep

theorem add_left {N : Network S} {i : N.I} {z z' extra : State S}
    (hStep : N.StepAt i z z') :
    N.StepAt i (State.add extra z) (State.add extra z') :=
  Reaction.FiresTo.add_left hStep

theorem lift_covers {N : Network S} {i : N.I} {z z' w : State S}
    (hStep : N.StepAt i z z') (hCovers : Covers w z) :
    exists w', N.StepAt i w w' /\ Covers w' z' :=
  Reaction.FiresTo.lift_covers hStep hCovers

end StepAt

namespace Step

theorem add_right {N : Network S} {z z' extra : State S}
    (hStep : N.Step z z') :
    N.Step (State.add z extra) (State.add z' extra) := by
  rcases hStep with ⟨i, hStepAt⟩
  exact ⟨i, StepAt.add_right hStepAt⟩

theorem add_left {N : Network S} {z z' extra : State S}
    (hStep : N.Step z z') :
    N.Step (State.add extra z) (State.add extra z') := by
  rcases hStep with ⟨i, hStepAt⟩
  exact ⟨i, StepAt.add_left hStepAt⟩

end Step

namespace Exec

theorem indices_eq_nil_of_terminal
    {N : Network S} {z z' : State S} {is : List N.I}
    (hTerminal : N.Terminal z)
    (hExec : N.Exec z z' is) :
    is = [] := by
  cases is with
  | nil =>
      rfl
  | cons i is =>
      rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hStep, _hTail⟩
      exact False.elim ((terminal_iff_no_stepAt.mp hTerminal) i zMid hStep)

theorem eq_of_terminal
    {N : Network S} {z z' : State S} {is : List N.I}
    (hTerminal : N.Terminal z)
    (hExec : N.Exec z z' is) :
    z' = z := by
  have hNil : is = [] := indices_eq_nil_of_terminal hTerminal hExec
  subst hNil
  exact (ExecOf.nil_iff.mp hExec).symm

theorem eq_nil_of_terminal
    {N : Network S} {z z' : State S} {is : List N.I}
    (hTerminal : N.Terminal z)
    (hExec : N.Exec z z' is) :
    z' = z /\ is = [] :=
  ⟨eq_of_terminal hTerminal hExec,
    indices_eq_nil_of_terminal hTerminal hExec⟩

theorem preserves {N : Network S} {P : State S -> Prop}
    (hstep : forall {i z z'}, N.StepAt i z z' -> P z -> P z') :
    forall {z z' : State S} {is : List N.I},
      N.Exec z z' is -> P z -> P z' := by
  intro z z' is hExec hP
  exact ExecOf.preserves (stepAt := N.StepAt) hstep hExec hP

theorem lift_covers {N : Network S} {z z' w : State S} {is : List N.I}
    (hExec : N.Exec z z' is) (hCovers : Covers w z) :
    exists w', N.Exec w w' is /\ Covers w' z' := by
  exact ExecOf.lift_rel
    (R := Covers)
    (stepAt := N.StepAt)
    (fun {i a b w} hStep hRel => Network.StepAt.lift_covers hStep hRel)
    hExec
    hCovers

theorem add_right
    {N : Network S} {z z' extra : State S} {is : List N.I}
    (hExec : N.Exec z z' is) :
    N.Exec (State.add z extra) (State.add z' extra) is := by
  induction hExec with
  | nil z =>
      exact ExecOf.nil (State.add z extra)
  | cons hStep _hTail ih =>
      exact ExecOf.cons (StepAt.add_right hStep) ih

theorem add_left
    {N : Network S} {z z' extra : State S} {is : List N.I}
    (hExec : N.Exec z z' is) :
    N.Exec (State.add extra z) (State.add extra z') is := by
  simpa [State.add_comm] using
    (add_right (extra := extra) hExec)

theorem coord_eq_of_forall_mem_not_touches
    {N : Network S} {z z' : State S} {is : List N.I} {s : S}
    (hExec : N.Exec z z' is)
    (hNotTouches : forall i, i ∈ is -> ¬ (N.rxn i).Touches s) :
    z' s = z s := by
  induction is generalizing z with
  | nil =>
      have hEq : z = z' := ExecOf.nil_iff.mp hExec
      exact congrArg (fun x => x s) hEq.symm
  | cons i is ih =>
      rcases ExecOf.cons_iff.mp hExec with ⟨zMid, hStep, hTail⟩
      have hMid : zMid s = z s :=
        hStep.eq_on_not_touches (hNotTouches i List.mem_cons_self)
      have hTailCoord : z' s = zMid s := ih hTail (by
        intro j hj
        exact hNotTouches j (List.mem_cons_of_mem i hj))
      exact hTailCoord.trans hMid

theorem coord_eq_of_not_touches
    {N : Network S} {z z' : State S} {is : List N.I} {s : S}
    (hExec : N.Exec z z' is)
    (hN : forall i : N.I, ¬ (N.rxn i).Touches s) :
    z' s = z s :=
  coord_eq_of_forall_mem_not_touches hExec (fun i _hi => hN i)

theorem eq_on_of_untouches
    {N : Network S} {z z' : State S} {is : List N.I}
    {P : S -> Prop}
    (hExec : N.Exec z z' is)
    (hN : N.Untouches P) :
    forall s, P s -> z' s = z s := by
  intro s hs
  exact coord_eq_of_not_touches hExec (fun i => hN i s hs)

end Exec

namespace Reaches

theorem eq_of_terminal
    {N : Network S} {z z' : State S}
    (hTerminal : N.Terminal z)
    (hReach : N.Reaches z z') :
    z' = z := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.eq_of_terminal hTerminal hExec

theorem preserves {N : Network S} {P : State S -> Prop}
    (hstep : forall {i z z'}, N.StepAt i z z' -> P z -> P z')
    {z z' : State S} (hReach : N.Reaches z z') (hP : P z) :
    P z' := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.preserves hstep hExec hP

theorem lift_covers {N : Network S} {z z' w : State S}
    (hReach : N.Reaches z z') (hCovers : Covers w z) :
    exists w', N.Reaches w w' /\ Covers w' z' := by
  rcases hReach with ⟨is, hExec⟩
  rcases Exec.lift_covers hExec hCovers with ⟨w', hExec', hCovers'⟩
  exact ⟨w', ⟨is, hExec'⟩, hCovers'⟩

theorem add_right
    {N : Network S} {z z' extra : State S}
    (hReach : N.Reaches z z') :
    N.Reaches (State.add z extra) (State.add z' extra) := by
  rcases hReach with ⟨is, hExec⟩
  exact ⟨is, Exec.add_right hExec⟩

theorem add_left
    {N : Network S} {z z' extra : State S}
    (hReach : N.Reaches z z') :
    N.Reaches (State.add extra z) (State.add extra z') := by
  rcases hReach with ⟨is, hExec⟩
  exact ⟨is, Exec.add_left hExec⟩

theorem coord_eq_of_not_touches
    {N : Network S} {z z' : State S} {s : S}
    (hReach : N.Reaches z z')
    (hN : forall i : N.I, ¬ (N.rxn i).Touches s) :
    z' s = z s := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.coord_eq_of_not_touches hExec hN

theorem eq_on_of_untouches
    {N : Network S} {z z' : State S}
    {P : S -> Prop}
    (hReach : N.Reaches z z')
    (hN : N.Untouches P) :
    forall s, P s -> z' s = z s := by
  rcases hReach with ⟨is, hExec⟩
  exact Exec.eq_on_of_untouches hExec hN

end Reaches

theorem coverableFrom_terminal_iff
    {N : Network S} {z target : State S}
    (hTerminal : N.Terminal z) :
    N.CoverableFrom z target <-> Covers z target := by
  constructor
  · rintro ⟨z', hReach, hCovers⟩
    have hEq : z' = z := Reaches.eq_of_terminal hTerminal hReach
    subst hEq
    exact hCovers
  · intro hCovers
    exact coverable_of_reaches_of_covers (reaches_refl N z) hCovers

theorem coverable_lift_initial {N : Network S} {z0 w0 target : State S}
    (hInitial : Covers w0 z0) (hCoverable : N.CoverableFrom z0 target) :
    N.CoverableFrom w0 target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  rcases Reaches.lift_covers hReach hInitial with ⟨w, hReach', hCovers'⟩
  exact ⟨w, hReach', Covers.trans hCovers' hCovers⟩

namespace CoverableFrom

theorem add_right
    {N : Network S} {z0 target extra : State S}
    (hCoverable : N.CoverableFrom z0 target) :
    N.CoverableFrom (State.add z0 extra) (State.add target extra) := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add z extra,
      Reaches.add_right hReach,
      Covers.add hCovers (Covers.refl extra)⟩

theorem add_left
    {N : Network S} {z0 target extra : State S}
    (hCoverable : N.CoverableFrom z0 target) :
    N.CoverableFrom (State.add extra z0) (State.add extra target) := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add extra z,
      by
        simpa [State.add_comm] using
          (Reaches.add_right (extra := extra) hReach),
      Covers.add (Covers.refl extra) hCovers⟩

theorem initial_add_right
    {N : Network S} {z0 target extra : State S}
    (hCoverable : N.CoverableFrom z0 target) :
    N.CoverableFrom (State.add z0 extra) target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add z extra,
      Reaches.add_right hReach,
      Covers.add_left hCovers⟩

theorem initial_add_left
    {N : Network S} {z0 target extra : State S}
    (hCoverable : N.CoverableFrom z0 target) :
    N.CoverableFrom (State.add extra z0) target := by
  rcases hCoverable with ⟨z, hReach, hCovers⟩
  exact
    ⟨State.add extra z,
      by
        simpa [State.add_comm] using
          (Reaches.add_right (extra := extra) hReach),
      Covers.add_right hCovers⟩

end CoverableFrom

theorem speciesCoverableFrom_iff [DecidableEq S]
    {N : Network S} {z0 : State S} {s : S} {n : Nat} :
    N.SpeciesCoverableFrom z0 s n <->
      exists z, N.Reaches z0 z /\ n <= z s := by
  constructor
  · rintro ⟨z, hReach, hCovers⟩
    exact ⟨z, hReach, (Covers.single_iff.mp hCovers)⟩
  · rintro ⟨z, hReach, hn⟩
    exact ⟨z, hReach, Covers.single_iff.mpr hn⟩

theorem speciesCoverableFrom_of_reaches_coord [DecidableEq S]
    {N : Network S} {z0 z : State S} {s : S} {n : Nat}
    (hReach : N.Reaches z0 z) (hn : n <= z s) :
    N.SpeciesCoverableFrom z0 s n := by
  exact speciesCoverableFrom_iff.mpr ⟨z, hReach, hn⟩

theorem speciesCoverableFrom_one_of_reaches_pos [DecidableEq S]
    {N : Network S} {z0 z : State S} {s : S}
    (hReach : N.Reaches z0 z) (hpos : 0 < z s) :
    N.SpeciesCoverableFrom z0 s := by
  exact speciesCoverableFrom_of_reaches_coord hReach (Nat.succ_le_of_lt hpos)

theorem speciesCoverableFrom_initial_add_right [DecidableEq S]
    {N : Network S} {z0 extra : State S} {s : S} {n : Nat}
    (hCoverable : N.SpeciesCoverableFrom z0 s n) :
    N.SpeciesCoverableFrom (State.add z0 extra) s n :=
  CoverableFrom.initial_add_right hCoverable

theorem speciesCoverableFrom_initial_add_left [DecidableEq S]
    {N : Network S} {z0 extra : State S} {s : S} {n : Nat}
    (hCoverable : N.SpeciesCoverableFrom z0 s n) :
    N.SpeciesCoverableFrom (State.add extra z0) s n :=
  CoverableFrom.initial_add_left hCoverable

namespace SpeciesCoverableFrom

theorem exists_reaches_coord [DecidableEq S]
    {N : Network S} {z0 : State S} {s : S} {n : Nat}
    (h : N.SpeciesCoverableFrom z0 s n) :
    exists z, N.Reaches z0 z /\ n <= z s :=
  speciesCoverableFrom_iff.mp h

end SpeciesCoverableFrom

def parallel (N M : Network S) : Network S where
  I := Sum N.I M.I
  fintypeI := inferInstance
  rxn := Sum.elim N.rxn M.rxn

def sigma {A : Type v} [Fintype A] (Ns : A -> Network S) : Network S where
  I := Sigma (fun a => (Ns a).I)
  fintypeI := inferInstance
  rxn
    | ⟨a, i⟩ => (Ns a).rxn i

@[simp]
theorem sigma_rxn {A : Type v} [Fintype A] (Ns : A -> Network S)
    (a : A) (i : (Ns a).I) :
    (Network.sigma Ns).rxn ⟨a, i⟩ = (Ns a).rxn i := by
  rfl

theorem sigma_stepAt {A : Type v} [Fintype A] (Ns : A -> Network S)
    {a : A} {i : (Ns a).I} {z z' : State S} :
    (Network.sigma Ns).StepAt ⟨a, i⟩ z z' <->
      (Ns a).StepAt i z z' := by
  rfl

theorem sigma_enabledAt {A : Type v} [Fintype A] (Ns : A -> Network S)
    {a : A} {i : (Ns a).I} {z : State S} :
    (Network.sigma Ns).EnabledAt z ⟨a, i⟩ <->
      (Ns a).EnabledAt z i := by
  rfl

theorem sigma_step_iff_exists {A : Type v} [Fintype A]
    (Ns : A -> Network S) {z z' : State S} :
    (Network.sigma Ns).Step z z' <->
      exists a : A, (Ns a).Step z z' := by
  constructor
  · rintro ⟨⟨a, i⟩, hStep⟩
    exact ⟨a, i, (sigma_stepAt Ns).1 hStep⟩
  · rintro ⟨a, i, hStep⟩
    exact ⟨⟨a, i⟩, (sigma_stepAt Ns).2 hStep⟩

theorem sigma_terminal_iff_forall {A : Type v} [Fintype A]
    (Ns : A -> Network S) {z : State S} :
    (Network.sigma Ns).Terminal z <->
      forall a : A, (Ns a).Terminal z := by
  constructor
  · intro hTerminal a i hEnabled
    exact hTerminal ⟨a, i⟩ hEnabled
  · intro hTerminal i
    rcases i with ⟨a, i⟩
    exact hTerminal a i

theorem sigma_stepInvariant_iff {A : Type v} [Fintype A]
    (Ns : A -> Network S) (P : State S -> Prop) :
    (Network.sigma Ns).StepInvariant P <->
      forall a : A, (Ns a).StepInvariant P := by
  constructor
  · intro hInv a i z z' hStep hP
    exact hInv ((sigma_stepAt Ns).2 hStep) hP
  · intro hInv i z z' hStep hP
    rcases i with ⟨a, i⟩
    exact hInv a ((sigma_stepAt Ns).1 hStep) hP

theorem sigma_exec {A : Type v} [Fintype A] (Ns : A -> Network S)
    (a : A) {z z' : State S} {is : List (Ns a).I}
    (h : (Ns a).Exec z z' is) :
    (Network.sigma Ns).Exec z z'
      (is.map (fun i => Sigma.mk a i)) := by
  exact ExecOf.map_index (fun i => Sigma.mk a i) (fun z => z)
    (by
      intro i z z' hStep
      exact (sigma_stepAt Ns).2 hStep)
    h

theorem sigma_exec_iff {A : Type v} [Fintype A]
    (Ns : A -> Network S) (a : A)
    {z z' : State S} {is : List (Ns a).I} :
    (Network.sigma Ns).Exec z z'
      (is.map (fun i => Sigma.mk a i)) <->
      (Ns a).Exec z z' is := by
  constructor
  · intro h
    induction is generalizing z with
    | nil =>
        exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
    | cons i is ih =>
        rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
        exact ExecOf.cons ((Network.sigma_stepAt Ns).1 hStep) (ih hTail)
  · intro h
    exact sigma_exec Ns a h

theorem sigma_reaches_of_exec {A : Type v} [Fintype A]
    (Ns : A -> Network S) (a : A)
    {z z' : State S} {is : List (Ns a).I}
    (h : (Ns a).Exec z z' is) :
    (Network.sigma Ns).Reaches z z' :=
  Network.reaches_of_exec (Network.sigma_exec Ns a h)

theorem sigma_reaches {A : Type v} [Fintype A]
    (Ns : A -> Network S) (a : A)
    {z z' : State S}
    (h : (Ns a).Reaches z z') :
    (Network.sigma Ns).Reaches z z' := by
  rcases h with ⟨is, hExec⟩
  exact sigma_reaches_of_exec Ns a hExec

theorem sigma_coverable {A : Type v} [Fintype A]
    (Ns : A -> Network S) (a : A)
    {z0 target : State S}
    (h : (Ns a).CoverableFrom z0 target) :
    (Network.sigma Ns).CoverableFrom z0 target := by
  rcases h with ⟨z, hReach, hCovers⟩
  exact ⟨z, sigma_reaches Ns a hReach, hCovers⟩

theorem sigma_speciesCoverableFrom [DecidableEq S]
    {A : Type v} [Fintype A]
    (Ns : A -> Network S) (a : A)
    {z0 : State S} {s : S} {n : Nat}
    (h : (Ns a).SpeciesCoverableFrom z0 s n) :
    (Network.sigma Ns).SpeciesCoverableFrom z0 s n :=
  sigma_coverable Ns a h

theorem parallel_stepAt_inl (N M : Network S) {i : N.I} {z z' : State S} :
    (N.parallel M).StepAt (Sum.inl i) z z' <-> N.StepAt i z z' := by
  rfl

theorem parallel_stepAt_inr (N M : Network S) {i : M.I} {z z' : State S} :
    (N.parallel M).StepAt (Sum.inr i) z z' <-> M.StepAt i z z' := by
  rfl

theorem parallel_enabledAt_inl (N M : Network S) {i : N.I} {z : State S} :
    (N.parallel M).EnabledAt z (Sum.inl i) <-> N.EnabledAt z i := by
  rfl

theorem parallel_enabledAt_inr (N M : Network S) {i : M.I} {z : State S} :
    (N.parallel M).EnabledAt z (Sum.inr i) <-> M.EnabledAt z i := by
  rfl

theorem parallel_enabledAt_cases
    (N M : Network S) {i : (N.parallel M).I} {z : State S} :
    (N.parallel M).EnabledAt z i <->
      match i with
      | Sum.inl j => N.EnabledAt z j
      | Sum.inr j => M.EnabledAt z j := by
  cases i <;> rfl

theorem parallel_step_iff_or (N M : Network S) {z z' : State S} :
    (N.parallel M).Step z z' <-> N.Step z z' \/ M.Step z z' := by
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

theorem parallel_terminal_iff_and (N M : Network S) {z : State S} :
    (N.parallel M).Terminal z <-> N.Terminal z /\ M.Terminal z := by
  constructor
  · intro hTerminal
    constructor
    · intro i hEnabled
      exact hTerminal (Sum.inl i) hEnabled
    · intro i hEnabled
      exact hTerminal (Sum.inr i) hEnabled
  · rintro ⟨hN, hM⟩ i
    cases i with
    | inl i =>
        exact hN i
    | inr i =>
        exact hM i

theorem parallel_terminal_of_terminal (N M : Network S) {z : State S}
    (hN : N.Terminal z) (hM : M.Terminal z) :
    (N.parallel M).Terminal z :=
  (parallel_terminal_iff_and N M).mpr ⟨hN, hM⟩

theorem parallel_stepInvariant_iff (N M : Network S) (P : State S -> Prop) :
    (N.parallel M).StepInvariant P <->
      N.StepInvariant P /\ M.StepInvariant P := by
  constructor
  · intro hInv
    constructor
    · intro i z z' hStep hP
      exact hInv ((parallel_stepAt_inl N M).mpr hStep) hP
    · intro i z z' hStep hP
      exact hInv ((parallel_stepAt_inr N M).mpr hStep) hP
  · rintro ⟨hN, hM⟩ i z z' hStep hP
    cases i with
    | inl i =>
        exact hN ((parallel_stepAt_inl N M).mp hStep) hP
    | inr i =>
        exact hM ((parallel_stepAt_inr N M).mp hStep) hP

theorem terminal_left_of_parallel_terminal (N M : Network S) {z : State S}
    (h : (N.parallel M).Terminal z) :
    N.Terminal z :=
  ((parallel_terminal_iff_and N M).mp h).1

theorem terminal_right_of_parallel_terminal (N M : Network S) {z : State S}
    (h : (N.parallel M).Terminal z) :
    M.Terminal z :=
  ((parallel_terminal_iff_and N M).mp h).2

theorem parallel_exec_inl (N M : Network S) {z z' : State S} {is : List N.I}
    (h : N.Exec z z' is) :
    (N.parallel M).Exec z z' (is.map Sum.inl) := by
  exact ExecOf.map_index Sum.inl (fun z => z)
    (by
      intro i a b hStep
      exact hStep)
    h

theorem parallel_exec_inr (N M : Network S) {z z' : State S} {is : List M.I}
    (h : M.Exec z z' is) :
    (N.parallel M).Exec z z' (is.map Sum.inr) := by
  exact ExecOf.map_index Sum.inr (fun z => z)
    (by
      intro i a b hStep
      exact hStep)
    h

theorem parallel_exec_inl_iff
    (N M : Network S) {z z' : State S} {is : List N.I} :
    (N.parallel M).Exec z z' (is.map Sum.inl) <-> N.Exec z z' is := by
  constructor
  · intro h
    induction is generalizing z with
    | nil =>
        exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
    | cons i is ih =>
        rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
        exact ExecOf.cons hStep (ih hTail)
  · intro h
    exact parallel_exec_inl N M h

theorem parallel_exec_inr_iff
    (N M : Network S) {z z' : State S} {is : List M.I} :
    (N.parallel M).Exec z z' (is.map Sum.inr) <-> M.Exec z z' is := by
  constructor
  · intro h
    induction is generalizing z with
    | nil =>
        exact ExecOf.nil_iff.mpr (ExecOf.nil_iff.mp h)
    | cons i is ih =>
        rcases ExecOf.cons_iff.mp h with ⟨zMid, hStep, hTail⟩
        exact ExecOf.cons hStep (ih hTail)
  · intro h
    exact parallel_exec_inr N M h

theorem parallel_reaches_of_inl_exec_iff
    (N M : Network S) {z z' : State S} :
    (exists is : List N.I,
      (N.parallel M).Exec z z' (is.map Sum.inl)) <-> N.Reaches z z' := by
  constructor
  · rintro ⟨is, hExec⟩
    exact ⟨is, (parallel_exec_inl_iff N M).mp hExec⟩
  · rintro ⟨is, hExec⟩
    exact ⟨is, (parallel_exec_inl_iff N M).mpr hExec⟩

theorem parallel_reaches_of_inr_exec_iff
    (N M : Network S) {z z' : State S} :
    (exists is : List M.I,
      (N.parallel M).Exec z z' (is.map Sum.inr)) <-> M.Reaches z z' := by
  constructor
  · rintro ⟨is, hExec⟩
    exact ⟨is, (parallel_exec_inr_iff N M).mp hExec⟩
  · rintro ⟨is, hExec⟩
    exact ⟨is, (parallel_exec_inr_iff N M).mpr hExec⟩

theorem parallel_exec_inl_append_inr
    (N M : Network S) {z0 z1 z2 : State S}
    {is : List N.I} {js : List M.I}
    (hN : N.Exec z0 z1 is) (hM : M.Exec z1 z2 js) :
    (N.parallel M).Exec z0 z2 (is.map Sum.inl ++ js.map Sum.inr) :=
  ExecOf.append (parallel_exec_inl N M hN) (parallel_exec_inr N M hM)

theorem parallel_exec_inr_append_inl
    (N M : Network S) {z0 z1 z2 : State S}
    {is : List M.I} {js : List N.I}
    (hM : M.Exec z0 z1 is) (hN : N.Exec z1 z2 js) :
    (N.parallel M).Exec z0 z2 (is.map Sum.inr ++ js.map Sum.inl) :=
  ExecOf.append (parallel_exec_inr N M hM) (parallel_exec_inl N M hN)

theorem parallel_reaches_inl (N M : Network S) {z z' : State S}
    (h : N.Reaches z z') :
    (N.parallel M).Reaches z z' := by
  rcases h with ⟨is, hExec⟩
  exact ⟨is.map Sum.inl, parallel_exec_inl N M hExec⟩

theorem parallel_reaches_inr (N M : Network S) {z z' : State S}
    (h : M.Reaches z z') :
    (N.parallel M).Reaches z z' := by
  rcases h with ⟨is, hExec⟩
  exact ⟨is.map Sum.inr, parallel_exec_inr N M hExec⟩

theorem parallel_reaches_left_then_right
    (N M : Network S) {z0 z1 z2 : State S}
    (hN : N.Reaches z0 z1) (hM : M.Reaches z1 z2) :
    (N.parallel M).Reaches z0 z2 := by
  rcases hN with ⟨is, hExecN⟩
  rcases hM with ⟨js, hExecM⟩
  exact ⟨is.map Sum.inl ++ js.map Sum.inr,
    parallel_exec_inl_append_inr N M hExecN hExecM⟩

theorem parallel_reaches_right_then_left
    (N M : Network S) {z0 z1 z2 : State S}
    (hM : M.Reaches z0 z1) (hN : N.Reaches z1 z2) :
    (N.parallel M).Reaches z0 z2 := by
  rcases hM with ⟨is, hExecM⟩
  rcases hN with ⟨js, hExecN⟩
  exact ⟨is.map Sum.inr ++ js.map Sum.inl,
    parallel_exec_inr_append_inl N M hExecM hExecN⟩

theorem parallel_reaches_left_then_right_coord_eq_of_right_not_touches
    (N M : Network S) {z0 z1 z2 : State S} {s : S}
    (hN : N.Reaches z0 z1)
    (hM : M.Reaches z1 z2)
    (hMnt : forall i : M.I, ¬ (M.rxn i).Touches s) :
    (N.parallel M).Reaches z0 z2 ∧ z2 s = z1 s := by
  exact ⟨parallel_reaches_left_then_right N M hN hM,
    Reaches.coord_eq_of_not_touches hM hMnt⟩

theorem parallel_reaches_left_then_right_coord_eq_of_left_not_touches
    (N M : Network S) {z0 z1 z2 : State S} {s : S}
    (hN : N.Reaches z0 z1)
    (hM : M.Reaches z1 z2)
    (hNnt : forall i : N.I, ¬ (N.rxn i).Touches s) :
    (N.parallel M).Reaches z0 z2 ∧ z1 s = z0 s := by
  exact ⟨parallel_reaches_left_then_right N M hN hM,
    Reaches.coord_eq_of_not_touches hN hNnt⟩

theorem parallel_reaches_left_then_right_coord_eq_of_both_not_touches
    (N M : Network S) {z0 z1 z2 : State S} {s : S}
    (hN : N.Reaches z0 z1)
    (hM : M.Reaches z1 z2)
    (hNnt : forall i : N.I, ¬ (N.rxn i).Touches s)
    (hMnt : forall i : M.I, ¬ (M.rxn i).Touches s) :
    (N.parallel M).Reaches z0 z2 ∧ z2 s = z0 s := by
  refine ⟨parallel_reaches_left_then_right N M hN hM, ?_⟩
  exact (Reaches.coord_eq_of_not_touches hM hMnt).trans
    (Reaches.coord_eq_of_not_touches hN hNnt)

theorem parallel_forall_not_touches {N M : Network S} {s : S}
    (hN : forall i : N.I, ¬ (N.rxn i).Touches s)
    (hM : forall i : M.I, ¬ (M.rxn i).Touches s) :
    forall i : (N.parallel M).I, ¬ ((N.parallel M).rxn i).Touches s := by
  intro i
  cases i with
  | inl i =>
      exact hN i
  | inr i =>
      exact hM i

theorem parallel_forall_not_touches_iff {N M : Network S} {s : S} :
    (forall i : (N.parallel M).I, ¬ ((N.parallel M).rxn i).Touches s) <->
      (forall i : N.I, ¬ (N.rxn i).Touches s) /\
        (forall i : M.I, ¬ (M.rxn i).Touches s) := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro i
      exact h (Sum.inr i)
  · rintro ⟨hN, hM⟩
    exact parallel_forall_not_touches hN hM

theorem sigma_forall_not_touches
    {A : Type v} [Fintype A] {Ns : A -> Network S} {s : S}
    (h : forall a, forall i : (Ns a).I,
      ¬ ((Ns a).rxn i).Touches s) :
    forall idx : (Network.sigma Ns).I,
      ¬ ((Network.sigma Ns).rxn idx).Touches s := by
  intro idx
  rcases idx with ⟨a, i⟩
  exact h a i

theorem sigma_forall_not_touches_iff
    {A : Type v} [Fintype A] {Ns : A -> Network S} {s : S} :
    (forall idx : (Network.sigma Ns).I,
      ¬ ((Network.sigma Ns).rxn idx).Touches s) <->
      forall a, forall i : (Ns a).I,
        ¬ ((Ns a).rxn i).Touches s := by
  constructor
  · intro h a i
    exact h ⟨a, i⟩
  · exact sigma_forall_not_touches

theorem parallel_exec_coord_eq_of_not_touches
    {N M : Network S} {z z' : State S} {is : List (N.parallel M).I} {s : S}
    (hExec : (N.parallel M).Exec z z' is)
    (hN : forall i : N.I, ¬ (N.rxn i).Touches s)
    (hM : forall i : M.I, ¬ (M.rxn i).Touches s) :
    z' s = z s :=
  Exec.coord_eq_of_not_touches hExec (parallel_forall_not_touches hN hM)

theorem parallel_reaches_coord_eq_of_not_touches
    {N M : Network S} {z z' : State S} {s : S}
    (hReach : (N.parallel M).Reaches z z')
    (hN : forall i : N.I, ¬ (N.rxn i).Touches s)
    (hM : forall i : M.I, ¬ (M.rxn i).Touches s) :
    z' s = z s :=
  Reaches.coord_eq_of_not_touches hReach (parallel_forall_not_touches hN hM)

theorem sigma_exec_coord_eq_of_not_touches
    {A : Type v} [Fintype A] {Ns : A -> Network S}
    {z z' : State S} {is : List (Network.sigma Ns).I} {s : S}
    (hExec : (Network.sigma Ns).Exec z z' is)
    (h : forall a, forall i : (Ns a).I,
      ¬ ((Ns a).rxn i).Touches s) :
    z' s = z s :=
  Exec.coord_eq_of_not_touches hExec (sigma_forall_not_touches h)

theorem sigma_reaches_coord_eq_of_not_touches
    {A : Type v} [Fintype A] {Ns : A -> Network S}
    {z z' : State S} {s : S}
    (hReach : (Network.sigma Ns).Reaches z z')
    (h : forall a, forall i : (Ns a).I,
      ¬ ((Ns a).rxn i).Touches s) :
    z' s = z s :=
  Reaches.coord_eq_of_not_touches hReach (sigma_forall_not_touches h)

theorem parallel_coverable_inl
    (N M : Network S) {z0 target : State S}
    (h : N.CoverableFrom z0 target) :
    (N.parallel M).CoverableFrom z0 target := by
  rcases h with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_inl N M hReach, hCovers⟩

theorem parallel_coverable_inr
    (N M : Network S) {z0 target : State S}
    (h : M.CoverableFrom z0 target) :
    (N.parallel M).CoverableFrom z0 target := by
  rcases h with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_inr N M hReach, hCovers⟩

theorem parallel_coverable_left_then_right
    (N M : Network S) {z0 z1 target : State S}
    (hN : N.Reaches z0 z1) (hM : M.CoverableFrom z1 target) :
    (N.parallel M).CoverableFrom z0 target := by
  rcases hM with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_left_then_right N M hN hReach, hCovers⟩

theorem parallel_coverable_right_then_left
    (N M : Network S) {z0 z1 target : State S}
    (hM : M.Reaches z0 z1) (hN : N.CoverableFrom z1 target) :
    (N.parallel M).CoverableFrom z0 target := by
  rcases hN with ⟨z, hReach, hCovers⟩
  exact ⟨z, parallel_reaches_right_then_left N M hM hReach, hCovers⟩

theorem parallel_speciesCoverableFrom_inl [DecidableEq S]
    (N M : Network S) {z0 : State S} {s : S} {n : Nat}
    (h : N.SpeciesCoverableFrom z0 s n) :
    (N.parallel M).SpeciesCoverableFrom z0 s n :=
  parallel_coverable_inl N M h

theorem parallel_speciesCoverableFrom_inr [DecidableEq S]
    (N M : Network S) {z0 : State S} {s : S} {n : Nat}
    (h : M.SpeciesCoverableFrom z0 s n) :
    (N.parallel M).SpeciesCoverableFrom z0 s n :=
  parallel_coverable_inr N M h

theorem exec_unique {N : Network S} {z z1 z2 : State S} {is : List N.I}
    (h1 : N.Exec z z1 is) (h2 : N.Exec z z2 is) :
    z1 = z2 :=
  ExecOf.unique_of_functional
    (stepAt := N.StepAt)
    (fun {_i _a _b _c} hb hc => Reaction.FiresTo.unique hb hc)
    h1 h2

end Network

end Ripple.sCRNUniversality

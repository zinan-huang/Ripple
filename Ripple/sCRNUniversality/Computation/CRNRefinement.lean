import Ripple.sCRNUniversality.Computation.CRNRealization

namespace Ripple.sCRNUniversality

universe u v w x y z

structure NetworkRefinement
    {S : Type u} {T : Type v}
    (Nhi : Network.{u, w} S) (Nlo : Network.{v, x} T) where
  enc : State S -> State T
  step_exec :
    forall {i : Nhi.I} {a b : State S},
      Nhi.StepAt i a b ->
        exists is : List Nlo.I, Nlo.Exec (enc a) (enc b) is

namespace NetworkRefinement

variable {S : Type u} {T : Type v} {U : Type y}
variable {Nhi : Network.{u, w} S}
variable {Nmid : Network.{v, x} T}
variable {Nlo : Network.{y, z} U}

theorem exec
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    exists js : List Nmid.I,
      Nmid.Exec (R.enc a) (R.enc b) js := by
  induction hExec with
  | nil a =>
      exact ⟨[], ExecOf.nil (R.enc a)⟩
  | cons hStep _tail ih =>
      rcases R.step_exec hStep with ⟨js₁, hExec₁⟩
      rcases ih with ⟨js₂, hExec₂⟩
      exact ⟨js₁ ++ js₂, ExecOf.append hExec₁ hExec₂⟩

theorem reaches
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nmid.Reaches (R.enc a) (R.enc b) := by
  rcases hReach with ⟨is, hExec⟩
  rcases R.exec hExec with ⟨js, hExec'⟩
  exact ⟨js, hExec'⟩

theorem coverable_of_reaches_covers
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hCovers : Covers (R.enc b) target) :
    Nmid.CoverableFrom (R.enc a) target :=
  Network.coverable_of_reaches_of_covers (R.reaches hReach) hCovers

theorem coverable_of_reaches_of_le
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hTarget : forall t, target t <= R.enc b t) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverable_of_reaches_covers hReach hTarget

theorem coverableFrom_of_reaches_of_le
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hTarget : forall t, target t <= R.enc b t) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverable_of_reaches_of_le hReach hTarget

theorem speciesCoverableFrom_of_reaches_coord [DecidableEq T]
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {species : T} {amount : Nat}
    (hReach : Nhi.Reaches a b)
    (hamount : amount <= R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (R.reaches hReach)
    hamount

theorem speciesCoverableFrom_one_of_reaches_pos [DecidableEq T]
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {species : T}
    (hReach : Nhi.Reaches a b)
    (hpos : 0 < R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (R.reaches hReach)
    hpos

/-- Forward-only execution transport for a network refinement. -/
theorem forward_exec
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    exists js : List Nmid.I,
      Nmid.Exec (R.enc a) (R.enc b) js :=
  R.exec hExec

/-- Forward-only reachability transport for a network refinement. -/
theorem forward_reaches
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nmid.Reaches (R.enc a) (R.enc b) :=
  R.reaches hReach

/-- Alternative spelling emphasizing forward-only reachability transport. -/
theorem reaches_forward
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nmid.Reaches (R.enc a) (R.enc b) :=
  R.reaches hReach

/-- Forward-only coverability consequence from a refined reachability witness. -/
theorem forward_coverable_of_reaches_covers
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hCovers : Covers (R.enc b) target) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverable_of_reaches_covers hReach hCovers

theorem forward_coverable_of_reaches_of_le
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hTarget : forall t, target t <= R.enc b t) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverable_of_reaches_of_le hReach hTarget

theorem forward_coverableFrom_of_reaches_of_le
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hTarget : forall t, target t <= R.enc b t) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverableFrom_of_reaches_of_le hReach hTarget

theorem forward_speciesCoverableFrom_of_reaches_coord [DecidableEq T]
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {species : T} {amount : Nat}
    (hReach : Nhi.Reaches a b)
    (hamount : amount <= R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species amount :=
  R.speciesCoverableFrom_of_reaches_coord hReach hamount

theorem forward_speciesCoverableFrom_one_of_reaches_pos [DecidableEq T]
    (R : NetworkRefinement Nhi Nmid)
    {a b : State S} {species : T}
    (hReach : Nhi.Reaches a b)
    (hpos : 0 < R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species :=
  R.speciesCoverableFrom_one_of_reaches_pos hReach hpos

def refl (N : Network.{u, w} S) :
    NetworkRefinement N N where
  enc := id
  step_exec := by
    intro i a b hStep
    exact ⟨[i], ExecOf.cons hStep (ExecOf.nil b)⟩

def trans
    (R₁ : NetworkRefinement Nhi Nmid)
    (R₂ : NetworkRefinement Nmid Nlo) :
    NetworkRefinement Nhi Nlo where
  enc := fun a => R₂.enc (R₁.enc a)
  step_exec := by
    intro _i _a _b hStep
    rcases R₁.step_exec hStep with ⟨js, hExecMid⟩
    exact R₂.exec hExecMid

end NetworkRefinement

structure BoundedNetworkRefinement
    {S : Type u} {T : Type v}
    (Nhi : Network.{u, w} S) (Nlo : Network.{v, x} T) where
  enc : State S -> State T
  step_len_bound : Nat
  step_exec_bounded :
    forall {i : Nhi.I} {a b : State S},
      Nhi.StepAt i a b ->
        exists is : List Nlo.I,
          Nlo.Exec (enc a) (enc b) is /\ is.length <= step_len_bound

namespace BoundedNetworkRefinement

variable {S : Type u} {T : Type v} {U : Type y}
variable {Nhi : Network.{u, w} S}
variable {Nmid : Network.{v, x} T}
variable {Nlo : Network.{y, z} U}

def toNetworkRefinement
    (R : BoundedNetworkRefinement Nhi Nmid) :
    NetworkRefinement Nhi Nmid where
  enc := R.enc
  step_exec := by
    intro _i _a _b hStep
    rcases R.step_exec_bounded hStep with ⟨is, hExec, _hLen⟩
    exact ⟨is, hExec⟩

theorem exec
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    exists js : List Nmid.I,
      Nmid.Exec (R.enc a) (R.enc b) js :=
  R.toNetworkRefinement.exec hExec

theorem reaches
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S}
    (hReach : Nhi.Reaches a b) :
    Nmid.Reaches (R.enc a) (R.enc b) :=
  R.toNetworkRefinement.reaches hReach

theorem coverableFrom_of_reaches_covers
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hCovers : Covers (R.enc b) target) :
    Nmid.CoverableFrom (R.enc a) target :=
  Network.coverable_of_reaches_of_covers (R.reaches hReach) hCovers

theorem coverableFrom_of_reaches_of_le
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hTarget : forall t, target t <= R.enc b t) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverableFrom_of_reaches_covers hReach hTarget

theorem speciesCoverableFrom_of_reaches_coord [DecidableEq T]
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {species : T} {amount : Nat}
    (hReach : Nhi.Reaches a b)
    (hamount : amount <= R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species amount :=
  Network.speciesCoverableFrom_of_reaches_coord
    (R.reaches hReach)
    hamount

theorem speciesCoverableFrom_one_of_reaches_pos [DecidableEq T]
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {species : T}
    (hReach : Nhi.Reaches a b)
    (hpos : 0 < R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species :=
  Network.speciesCoverableFrom_one_of_reaches_pos
    (R.reaches hReach)
    hpos

theorem forward_coverableFrom_of_reaches_covers
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hCovers : Covers (R.enc b) target) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverableFrom_of_reaches_covers hReach hCovers

theorem forward_coverableFrom_of_reaches_of_le
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {target : State T}
    (hReach : Nhi.Reaches a b)
    (hTarget : forall t, target t <= R.enc b t) :
    Nmid.CoverableFrom (R.enc a) target :=
  R.coverableFrom_of_reaches_of_le hReach hTarget

theorem forward_speciesCoverableFrom_of_reaches_coord [DecidableEq T]
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {species : T} {amount : Nat}
    (hReach : Nhi.Reaches a b)
    (hamount : amount <= R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species amount :=
  R.speciesCoverableFrom_of_reaches_coord hReach hamount

theorem forward_speciesCoverableFrom_one_of_reaches_pos [DecidableEq T]
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {species : T}
    (hReach : Nhi.Reaches a b)
    (hpos : 0 < R.enc b species) :
    Nmid.SpeciesCoverableFrom (R.enc a) species :=
  R.speciesCoverableFrom_one_of_reaches_pos hReach hpos

theorem exec_bounded
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    exists js : List Nmid.I,
      Nmid.Exec (R.enc a) (R.enc b) js /\
        js.length <= R.step_len_bound * is.length := by
  induction hExec with
  | nil a =>
      exact ⟨[], ExecOf.nil (R.enc a), by simp⟩
  | cons hStep _tail ih =>
      rcases R.step_exec_bounded hStep with ⟨js₁, hExec₁, hLen₁⟩
      rcases ih with ⟨js₂, hExec₂, hLen₂⟩
      refine ⟨js₁ ++ js₂, ExecOf.append hExec₁ hExec₂, ?_⟩
      simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using (Nat.add_le_add hLen₁ hLen₂)

/--
Bounded forward execution transport, stated as a firing-count bound.

`js.length` is the number of concrete reactions in the produced deterministic
schedule. This is not stochastic time.
-/
theorem forward_firingCount_exec_bounded
    (R : BoundedNetworkRefinement Nhi Nmid)
    {a b : State S} {is : List Nhi.I}
    (hExec : Nhi.Exec a b is) :
    exists js : List Nmid.I,
      Nmid.Exec (R.enc a) (R.enc b) js /\
        js.length <= R.step_len_bound * is.length :=
  R.exec_bounded hExec

def refl (N : Network.{u, w} S) :
    BoundedNetworkRefinement N N where
  enc := id
  step_len_bound := 1
  step_exec_bounded := by
    intro i a b hStep
    exact ⟨[i], ExecOf.cons hStep (ExecOf.nil b), by simp⟩

def trans
    (R₁ : BoundedNetworkRefinement Nhi Nmid)
    (R₂ : BoundedNetworkRefinement Nmid Nlo) :
    BoundedNetworkRefinement Nhi Nlo where
  enc := fun a => R₂.enc (R₁.enc a)
  step_len_bound := R₂.step_len_bound * R₁.step_len_bound
  step_exec_bounded := by
    intro _i _a _b hStep
    rcases R₁.step_exec_bounded hStep with ⟨js, hExecMid, hLenMid⟩
    rcases R₂.exec_bounded hExecMid with ⟨ks, hExecLow, hLenLow⟩
    refine ⟨ks, hExecLow, ?_⟩
    have hMul :
        R₂.step_len_bound * js.length <=
          R₂.step_len_bound * R₁.step_len_bound :=
      Nat.mul_le_mul_left R₂.step_len_bound hLenMid
    exact le_trans hLenLow hMul

end BoundedNetworkRefinement

namespace StepwiseRealization

variable {A : DetSystem.{u}}
variable {S : Type v} [Fintype S] {T : Type x} [Fintype T]
variable {Nhi : Network.{v, w} S} {Nlo : Network.{x, y} T}

def refineNetwork
    (R : StepwiseRealization A Nhi)
    (F : NetworkRefinement Nhi Nlo) :
    StepwiseRealization A Nlo where
  enc := fun a => F.enc (R.enc a)
  step_exec := by
    intro _a _b hstep
    rcases R.step_exec hstep with ⟨is, hExec⟩
    exact F.exec hExec

end StepwiseRealization

namespace InvariantStepwiseRealization

variable {A : DetSystem.{u}} {Inv : A.Cfg -> Prop}
variable {S : Type v} [Fintype S] {T : Type x} [Fintype T]
variable {Nhi : Network.{v, w} S} {Nlo : Network.{x, y} T}

def refineNetwork
    (R : InvariantStepwiseRealization A Nhi Inv)
    (F : NetworkRefinement Nhi Nlo) :
    InvariantStepwiseRealization A Nlo Inv where
  enc := fun a => F.enc (R.enc a)
  step_exec := by
    intro _a _b hInv hstep
    rcases R.step_exec hInv hstep with ⟨is, hExec⟩
    exact F.exec hExec
  step_preserves := R.step_preserves

end InvariantStepwiseRealization

namespace BoundedStepwiseRealization

variable {A : DetSystem.{u}}
variable {S : Type v} [Fintype S] {T : Type x} [Fintype T]
variable {Nhi : Network.{v, w} S} {Nlo : Network.{x, y} T}

def refineBoundedNetwork
    (R : BoundedStepwiseRealization A Nhi)
    (F : BoundedNetworkRefinement Nhi Nlo) :
    BoundedStepwiseRealization A Nlo where
  enc := fun a => F.enc (R.enc a)
  step_len_bound := F.step_len_bound * R.step_len_bound
  step_exec_bounded := by
    intro _a _b hstep
    rcases R.step_exec_bounded hstep with ⟨is, hExec, hLen⟩
    rcases F.exec_bounded hExec with ⟨js, hExec', hLen'⟩
    refine ⟨js, hExec', ?_⟩
    have hMul :
        F.step_len_bound * is.length <=
          F.step_len_bound * R.step_len_bound :=
      Nat.mul_le_mul_left F.step_len_bound hLen
    exact le_trans hLen' hMul

end BoundedStepwiseRealization

end Ripple.sCRNUniversality

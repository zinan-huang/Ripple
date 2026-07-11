/-
  Cascade shift: per-molecule tape tripling via bimolecular micro-reactions.
  Species: 0=ctrlA, 1=ctrlB, 2=ctrlC, 3=ctrlR, 4=tape, 5=shifted
  Reactions: A(0+4→1+5), B(1→2+5), C(2→0+5), R(3+5→3+4)
  Key: at each micro-step, exactly one reaction enabled. Fully deterministic.
-/
import Ripple.sCRNUniversality.Core.Run
import Mathlib.Tactic.FinCases

namespace Ripple.sCRNUniversality.CTM.CascadeShift

inductive Sp | cA | cB | cC | cR | tape | shifted
  deriving DecidableEq, Repr
instance : Fintype Sp :=
  ⟨{.cA, .cB, .cC, .cR, .tape, .shifted}, by intro x; cases x <;> simp⟩

private def mkR (l r : Sp → Nat) : Reaction Sp := { l, r, k := 1 }

open Sp in
def rxnA := mkR (fun | cA => 1 | tape => 1 | _ => 0)
                  (fun | cB => 1 | shifted => 1 | _ => 0)
open Sp in
def rxnB := mkR (fun | cB => 1 | _ => 0) (fun | cC => 1 | shifted => 1 | _ => 0)
open Sp in
def rxnC := mkR (fun | cC => 1 | _ => 0) (fun | cA => 1 | shifted => 1 | _ => 0)
open Sp in
def rxnR := mkR (fun | cR => 1 | shifted => 1 | _ => 0)
                  (fun | cR => 1 | tape => 1 | _ => 0)

inductive Ix | a | b | c | r deriving DecidableEq, Repr
instance : Fintype Ix := ⟨{.a, .b, .c, .r}, by intro x; cases x <;> simp⟩

def net : Network Sp where
  I := Ix; fintypeI := inferInstance
  rxn | .a => rxnA | .b => rxnB | .c => rxnC | .r => rxnR

open Sp in
def enc (ctrl : Ix) (t s : Nat) : State Sp := fun
  | cA => if ctrl = .a then 1 else 0
  | cB => if ctrl = .b then 1 else 0
  | cC => if ctrl = .c then 1 else 0
  | cR => if ctrl = .r then 1 else 0
  | tape => t
  | shifted => s

theorem deterministic (ctrl : Ix) (t s : Nat)
    (hActive : match ctrl with | .a => 0 < t | .b => True | .c => True | .r => 0 < s)
    (i j : Ix) (hi : net.EnabledAt (enc ctrl t s) i) (hj : net.EnabledAt (enc ctrl t s) j) :
    i = j := by
  cases ctrl <;> cases i <;> cases j <;> try rfl
  all_goals (exfalso; simp only [net, Network.EnabledAt, Reaction.enabled] at hi hj)
  all_goals (
    first
    | (have := hi .cA; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cB; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cC; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cR; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .tape; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .shifted; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hj .cA; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hj .cB; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hj .cC; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hj .cR; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hj .tape; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hj .shifted; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide))

theorem terminal_mult_done (s : Nat) : net.Terminal (enc .a 0 s) := by
  intro i hi
  cases i <;> simp only [net, Network.EnabledAt, Reaction.enabled] at hi <;> (
    first
    | (have := hi .cA; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cB; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cC; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cR; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .tape; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .shifted; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide))

theorem terminal_restore_done (t : Nat) : net.Terminal (enc .r t 0) := by
  intro i hi
  cases i <;> simp only [net, Network.EnabledAt, Reaction.enabled] at hi <;> (
    first
    | (have := hi .cA; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cB; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cC; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .cR; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .tape; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide)
    | (have := hi .shifted; simp only [enc, rxnA, rxnB, rxnC, rxnR, mkR] at this; revert this; decide))

private theorem step_a (t s : Nat) (ht : 0 < t) :
    net.StepAt .a (enc .a t s) (enc .b (t - 1) (s + 1)) := by
  refine ⟨?_, ?_⟩
  · intro sp; cases sp <;> simp only [net, rxnA, mkR, enc] <;> (try decide) <;> omega
  · funext sp; cases sp <;> simp only [Reaction.fire, net, rxnA, mkR, enc] <;> (try decide) <;> omega

private theorem step_b (t s : Nat) :
    net.StepAt .b (enc .b t s) (enc .c t (s + 1)) := by
  refine ⟨?_, ?_⟩
  · intro sp; cases sp <;> simp only [net, rxnB, mkR, enc] <;> (try decide) <;> omega
  · funext sp; cases sp <;> simp only [Reaction.fire, net, rxnB, mkR, enc] <;> (try decide) <;> omega

private theorem step_c (t s : Nat) :
    net.StepAt .c (enc .c t s) (enc .a t (s + 1)) := by
  refine ⟨?_, ?_⟩
  · intro sp; cases sp <;> simp only [net, rxnC, mkR, enc] <;> (try decide) <;> omega
  · funext sp; cases sp <;> simp only [Reaction.fire, net, rxnC, mkR, enc] <;> (try decide) <;> omega

private theorem step_r (t s : Nat) (hs : 0 < s) :
    net.StepAt .r (enc .r t s) (enc .r (t + 1) (s - 1)) := by
  refine ⟨?_, ?_⟩
  · intro sp; cases sp <;> simp only [net, rxnR, mkR, enc] <;> (try decide) <;> omega
  · funext sp; cases sp <;> simp only [Reaction.fire, net, rxnR, mkR, enc] <;> (try decide) <;> omega

private theorem one_mult_cycle (t s : Nat) (ht : 0 < t) :
    net.Reaches (enc .a t s) (enc .a (t - 1) (s + 3)) :=
  ⟨[.a, .b, .c], ExecOf.cons (step_a t s ht)
    (ExecOf.cons (step_b (t - 1) (s + 1))
      (ExecOf.cons (step_c (t - 1) (s + 2)) (ExecOf.nil _)))⟩

theorem multiply_reaches (T S : Nat) :
    net.Reaches (enc .a T S) (enc .a 0 (S + 3 * T)) := by
  induction T generalizing S with
  | zero => simpa using ⟨[], ExecOf.nil _⟩
  | succ n ih =>
    obtain ⟨is₁, h₁⟩ := one_mult_cycle (n + 1) S (by omega)
    obtain ⟨is₂, h₂⟩ := ih (S + 3)
    have hSimp1 : n + 1 - 1 = n := by omega
    have hSimp2 : S + 3 + 3 * n = S + 3 * (n + 1) := by omega
    rw [hSimp1] at h₁
    rw [hSimp2] at h₂
    exact ⟨is₁ ++ is₂, ExecOf.append h₁ h₂⟩

theorem restore_reaches (T S : Nat) :
    net.Reaches (enc .r T S) (enc .r (T + S) 0) := by
  induction S generalizing T with
  | zero => simpa using ⟨[], ExecOf.nil _⟩
  | succ n ih =>
    have hStep : net.Reaches (enc .r T (n + 1)) (enc .r (T + 1) n) :=
      ⟨[.r], ExecOf.cons (step_r T (n + 1) (by omega)) (ExecOf.nil _)⟩
    obtain ⟨is₁, h₁⟩ := hStep
    obtain ⟨is₂, h₂⟩ := ih (T + 1)
    have hSimp : T + 1 + n = T + (n + 1) := by omega
    rw [hSimp] at h₂
    exact ⟨is₁ ++ is₂, ExecOf.append h₁ h₂⟩

theorem cascade_effect (T : Nat) :
    net.Reaches (enc .a T 0) (enc .a 0 (3 * T)) ∧
    net.Reaches (enc .r 0 (3 * T)) (enc .r (3 * T) 0) := by
  constructor
  · have := multiply_reaches T 0; simpa using this
  · simpa using restore_reaches 0 (3 * T)

end Ripple.sCRNUniversality.CTM.CascadeShift

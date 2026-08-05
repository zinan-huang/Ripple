/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BiKernel
import Tri.Decay

/-!
# Adaptive Byzantine Tri: controlled-kernel foundation

The state stores honest `X` and Byzantine counts; honest `Y` is the conserved
remainder. A control is a complete response table indexed by the current
unordered triple composition. A history-dependent strategy selects that table
from the complete past and current state before the next random triple is
drawn. Thus the selected action may depend on the current composition, but not
on a future random sample.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

/-- Honest `X` and Byzantine populations, with honest `Y` derived from total
population `n`. -/
def State (n B : ℕ) :=
  {q : Fin (n + 1) × Fin (B + 1) //
    (q.1 : ℕ) + (q.2 : ℕ) ≤ n}

noncomputable instance stateDecidableEq (n B : ℕ) :
    DecidableEq (State n B) :=
  Classical.decEq _

noncomputable instance stateFintype (n B : ℕ) :
    Fintype (State n B) := by
  unfold State
  infer_instance

namespace State

def x (s : State n B) : ℕ := s.1.1
def z (s : State n B) : ℕ := s.1.2
def y (s : State n B) : ℕ := n - (x s + z s)

@[simp] theorem xz_le (s : State n B) : x s + z s ≤ n :=
  s.2

@[simp] theorem total (s : State n B) :
    x s + y s + z s = n := by
  have h := xz_le s
  unfold y
  omega

@[simp] theorem x_le (s : State n B) : x s ≤ n := by
  have h := xz_le s
  omega

@[simp] theorem z_le_budget (s : State n B) : z s ≤ B := by
  unfold z
  exact Nat.le_of_lt_succ s.1.2.isLt

@[simp] theorem z_le_population (s : State n B) : z s ≤ n := by
  have h := xz_le s
  omega

/-- Convert one honest `Y` to honest `X`. -/
def up (s : State n B) (hy : 0 < y s) : State n B := by
  refine ⟨(⟨x s + 1, ?_⟩, s.1.2), ?_⟩
  · have ht := total s
    omega
  · change x s + 1 + z s ≤ n
    have ht := total s
    omega

/-- Convert one honest `X` to honest `Y`. -/
def down (s : State n B) (hx : 0 < x s) : State n B := by
  refine ⟨(⟨x s - 1, ?_⟩, s.1.2), ?_⟩
  · have hxle := x_le s
    omega
  · change x s - 1 + z s ≤ n
    have hxz := xz_le s
    omega

@[simp] theorem up_x (s : State n B) (hy : 0 < y s) :
    x (up s hy) = x s + 1 :=
  rfl

@[simp] theorem down_x (s : State n B) (hx : 0 < x s) :
    x (down s hx) = x s - 1 :=
  rfl

@[simp] theorem up_z (s : State n B) (hy : 0 < y s) :
    z (up s hy) = z s :=
  rfl

@[simp] theorem down_z (s : State n B) (hx : 0 < x s) :
    z (down s hx) = z s :=
  rfl

end State

/-- The ten unordered compositions of an `X/Y/Z` triple. -/
inductive TripleComp
  | xxx
  | xxy
  | xxz
  | xyy
  | xyz
  | xzz
  | yyy
  | yyz
  | yzz
  | zzz
  deriving DecidableEq, Fintype, Repr

namespace TripleComp

def weight (x y z : ℕ) : TripleComp → ℕ
  | .xxx => Nat.choose x 3
  | .xxy => Nat.choose x 2 * y
  | .xxz => Nat.choose x 2 * z
  | .xyy => x * Nat.choose y 2
  | .xyz => x * y * z
  | .xzz => x * Nat.choose z 2
  | .yyy => Nat.choose y 3
  | .yyz => Nat.choose y 2 * z
  | .yzz => y * Nat.choose z 2
  | .zzz => Nat.choose z 3

def weightAt (s : State n B) (k : TripleComp) : ℕ :=
  weight (State.x s) (State.y s) (State.z s) k

/-- Multivariate degree-three Vandermonde identity. -/
theorem sum_weight (x y z : ℕ) :
    ∑ k : TripleComp, weight x y z k =
      Nat.choose (x + y + z) 3 := by
  calc
    ∑ k : TripleComp, weight x y z k =
        Nat.choose x 3 + Nat.choose x 2 * y +
          Nat.choose x 2 * z + x * Nat.choose y 2 +
          x * y * z + x * Nat.choose z 2 +
          Nat.choose y 3 + Nat.choose y 2 * z +
          y * Nat.choose z 2 + Nat.choose z 3 := by
            rw [show (Finset.univ : Finset TripleComp) =
              {TripleComp.xxx, TripleComp.xxy, TripleComp.xxz,
                TripleComp.xyy, TripleComp.xyz, TripleComp.xzz,
                TripleComp.yyy, TripleComp.yyz, TripleComp.yzz,
                TripleComp.zzz} from rfl]
            simp [weight]
            ring
    _ = Nat.choose (x + y) 3 + Nat.choose (x + y) 2 * z +
          (x + y) * Nat.choose z 2 + Nat.choose z 3 := by
            rw [choose_three_split x y, pair_two_split x y]
            ring
    _ = Nat.choose (x + y + z) 3 := by
          simpa only [Nat.add_assoc] using
            (choose_three_split (x + y) z).symm

end TripleComp

/-- Uniform unordered-triple composition scheduler. -/
noncomputable def triplePMF
    (s : State n B) (h3 : 3 ≤ n) : PMF TripleComp :=
  PMF.ofFintype
    (fun k =>
      (TripleComp.weightAt s k : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞))
    (by
      have hpos : 0 < Nat.choose n 3 := choose_three_pos h3
      have hne : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      have hsum :
          ∑ k : TripleComp, TripleComp.weightAt s k =
            Nat.choose n 3 := by
        unfold TripleComp.weightAt
        rw [TripleComp.sum_weight, State.total]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [show ∑ k : TripleComp,
          ((TripleComp.weightAt s k : ℕ) : ℝ≥0∞) =
          ((∑ k : TripleComp,
            TripleComp.weightAt s k : ℕ) : ℝ≥0∞) by
            push_cast
            rfl]
      rw [hsum, ← div_eq_mul_inv]
      exact ENNReal.div_self hne htop)

@[simp] theorem triplePMF_apply
    (s : State n B) (h3 : 3 ≤ n) (k : TripleComp) :
    triplePMF s h3 k =
      (TripleComp.weightAt s k : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) :=
  rfl

theorem triplePMF_zero_of_weight_zero
    {s : State n B} {h3 : 3 ≤ n} {k : TripleComp}
    (hk : TripleComp.weightAt s k = 0) :
    triplePMF s h3 k = 0 := by
  rw [triplePMF_apply, hk]
  simp

/-- Net change of the honest `X` population. -/
inductive Action
  | down
  | stay
  | up
  deriving DecidableEq, Fintype, Repr

namespace Action

/-- Exact count-level quotient of Byzantine presentations by their effect on
honest populations. -/
def Legal : TripleComp → Action → Prop
  | .xxx, .stay => True
  | .xxy, .up => True
  | .xxz, .stay => True
  | .xyy, .down => True
  | .xyz, .down => True
  | .xyz, .stay => True
  | .xyz, .up => True
  | .xzz, .down => True
  | .xzz, .stay => True
  | .yyy, .stay => True
  | .yyz, .stay => True
  | .yzz, .stay => True
  | .yzz, .up => True
  | .zzz, .stay => True
  | _, _ => False

instance legalDecidable (k : TripleComp) (a : Action) :
    Decidable (Legal k a) := by
  cases k <;> cases a <;> unfold Legal <;> infer_instance

def nextX (x : ℕ) : Action → ℕ
  | .down => x - 1
  | .stay => x
  | .up => x + 1

def Enabled (s : State n B) : Action → Prop
  | .down => 0 < State.x s
  | .stay => True
  | .up => 0 < State.y s

def transfer (s : State n B) :
    (a : Action) → Enabled s a → State n B
  | .down, h => State.down s h
  | .stay, _ => s
  | .up, h => State.up s h

@[simp] theorem transfer_x
    (s : State n B) (a : Action) (ha : Enabled s a) :
    State.x (transfer s a ha) = nextX (State.x s) a := by
  cases a <;> rfl

@[simp] theorem transfer_z
    (s : State n B) (a : Action) (ha : Enabled s a) :
    State.z (transfer s a ha) = State.z s := by
  cases a <;> rfl

end Action

/-- Complete count-level response table for one raw interaction. -/
structure Control where
  xyz : Action
  xzzDown : Bool
  yzzUp : Bool
  deriving DecidableEq, Fintype, Repr

namespace Control

def action (u : Control) : TripleComp → Action
  | .xxx => .stay
  | .xxy => .up
  | .xxz => .stay
  | .xyy => .down
  | .xyz => u.xyz
  | .xzz => if u.xzzDown then .down else .stay
  | .yyy => .stay
  | .yyz => .stay
  | .yzz => if u.yzzUp then .up else .stay
  | .zzz => .stay

@[simp] theorem action_legal (u : Control) (k : TripleComp) :
    Action.Legal k (action u k) := by
  rcases u with ⟨a, xd, yu⟩
  cases a <;> cases xd <;> cases yu <;> cases k <;>
    simp [action, Action.Legal]

def neutral : Control :=
  ⟨.stay, false, false⟩

/-- The adverse table used in the paper: `XYZ` and `XZZ` move toward `Y`,
while `YZZ` is prevented from helping `X`. -/
def worst : Control :=
  ⟨.down, true, false⟩

theorem action_enabled_of_weight_ne_zero
    (u : Control) (s : State n B) (k : TripleComp)
    (hk : TripleComp.weightAt s k ≠ 0) :
    Action.Enabled s (action u k) := by
  rcases u with ⟨a, xd, yu⟩
  cases a <;> cases xd <;> cases yu <;> cases k <;>
    simp [action, Action.Enabled, TripleComp.weightAt,
      TripleComp.weight] at hk ⊢ <;>
    omega

end Control

/-- Total invariant-preserving state update. Zero-weight impossible
compositions are sent to the current state. -/
noncomputable def nextState
    (u : Control) (s : State n B) (k : TripleComp) : State n B :=
  if hk : TripleComp.weightAt s k = 0 then
    s
  else
    Action.transfer s (u.action k)
      (u.action_enabled_of_weight_ne_zero s k hk)

@[simp] theorem nextState_x_of_weight_ne_zero
    (u : Control) (s : State n B) (k : TripleComp)
    (hk : TripleComp.weightAt s k ≠ 0) :
    State.x (nextState u s k) =
      Action.nextX (State.x s) (u.action k) := by
  simp [nextState, hk]

@[simp] theorem nextState_z
    (u : Control) (s : State n B) (k : TripleComp) :
    State.z (nextState u s k) = State.z s := by
  unfold nextState
  split_ifs <;> simp

@[simp] theorem nextState_total
    (u : Control) (s : State n B) (k : TripleComp) :
    State.x (nextState u s k) +
        State.y (nextState u s k) +
        State.z (nextState u s k) = n :=
  State.total _

/-- One physical state step under a fixed response table. -/
noncomputable def movePMF
    (u : Control) (s : State n B) (h3 : 3 ≤ n) : PMF Action :=
  (triplePMF s h3).map u.action

/-- One physical state step under a fixed response table. -/
noncomputable def step
    (u : Control) (s : State n B) (h3 : 3 ≤ n) : PMF (State n B) :=
  (triplePMF s h3).map (nextState u s)

/-- Byzantine count is conserved by every fixed-control step. -/
theorem step_map_z
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    (step u s h3).map State.z = PMF.pure (State.z s) := by
  unfold step
  rw [PMF.map_comp]
  rw [show State.z ∘ nextState u s = (fun _ => State.z s) by
    funext k
    simp [Function.comp_apply]]
  exact PMF.map_const _ _

private theorem map_change_on_zero_mass
    {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a, f a ≠ g a → p a = 0) :
    p.map f = p.map g := by
  ext z
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases hfg : f a = g a
  · rw [hfg]
  · rw [h a hfg]
    simp

/-- The physical kernel's `X` marginal is the selected-action kernel followed
by the corresponding count update. -/
theorem step_map_x
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    (step u s h3).map State.x =
      (movePMF u s h3).map (Action.nextX (State.x s)) := by
  unfold step movePMF
  rw [PMF.map_comp, PMF.map_comp]
  apply map_change_on_zero_mass
  intro k hkdiff
  by_cases hk : TripleComp.weightAt s k = 0
  · exact triplePMF_zero_of_weight_zero hk
  · exfalso
    apply hkdiff
    simp only [Function.comp_apply]
    exact nextState_x_of_weight_ne_zero u s k hk

/-! ## Exact fixed-control up/down masses -/

def upWeight (u : Control) (s : State n B) : ℕ :=
  Nat.choose (State.x s) 2 * State.y s +
    (match u.xyz with
      | .up => State.x s * State.y s * State.z s
      | _ => 0) +
    (if u.yzzUp then
      State.y s * Nat.choose (State.z s) 2
    else 0)

def downWeight (u : Control) (s : State n B) : ℕ :=
  State.x s * Nat.choose (State.y s) 2 +
    (match u.xyz with
      | .down => State.x s * State.y s * State.z s
      | _ => 0) +
    (if u.xzzDown then
      State.x s * Nat.choose (State.z s) 2
    else 0)

theorem movePMF_up
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    movePMF u s h3 .up =
      (upWeight u s : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rcases u with ⟨a, xd, yu⟩
  cases a <;> cases xd <;> cases yu <;>
    unfold movePMF <;>
    rw [PMF.map_apply, tsum_fintype] <;>
    rw [show (Finset.univ : Finset TripleComp) =
      {TripleComp.xxx, TripleComp.xxy, TripleComp.xxz,
        TripleComp.xyy, TripleComp.xyz, TripleComp.xzz,
        TripleComp.yyy, TripleComp.yyz, TripleComp.yzz,
        TripleComp.zzz} from rfl] <;>
    simp [Control.action, upWeight, TripleComp.weightAt,
      TripleComp.weight, triplePMF_apply, div_eq_mul_inv] <;>
    ring

theorem movePMF_down
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    movePMF u s h3 .down =
      (downWeight u s : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rcases u with ⟨a, xd, yu⟩
  cases a <;> cases xd <;> cases yu <;>
    unfold movePMF <;>
    rw [PMF.map_apply, tsum_fintype] <;>
    rw [show (Finset.univ : Finset TripleComp) =
      {TripleComp.xxx, TripleComp.xxy, TripleComp.xxz,
        TripleComp.xyy, TripleComp.xyz, TripleComp.xzz,
        TripleComp.yyy, TripleComp.yyz, TripleComp.yzz,
        TripleComp.zzz} from rfl] <;>
    simp [Control.action, downWeight, TripleComp.weightAt,
      TripleComp.weight, triplePMF_apply, div_eq_mul_inv] <;>
    ring

theorem step_x_up_mass
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    ((step u s h3).map State.x) (State.x s + 1) =
      (upWeight u s : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  have hdown : State.x s + 1 ≠ State.x s - 1 := by omega
  calc
    ((step u s h3).map State.x) (State.x s + 1) =
        ((movePMF u s h3).map
          (Action.nextX (State.x s))) (State.x s + 1) := by
            rw [step_map_x]
    _ = movePMF u s h3 .up := by
          rw [PMF.map_apply, tsum_fintype]
          rw [show (Finset.univ : Finset Action) =
            {Action.down, Action.stay, Action.up} from rfl]
          simp [Action.nextX, hdown]
    _ = (upWeight u s : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) :=
      movePMF_up u s h3

theorem step_x_down_mass
    (u : Control) (s : State n B) (h3 : 3 ≤ n)
    (hx : 0 < State.x s) :
    ((step u s h3).map State.x) (State.x s - 1) =
      (downWeight u s : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  have hstay' : State.x s - 1 ≠ State.x s := by omega
  calc
    ((step u s h3).map State.x) (State.x s - 1) =
        ((movePMF u s h3).map
          (Action.nextX (State.x s))) (State.x s - 1) := by
            rw [step_map_x]
    _ = movePMF u s h3 .down := by
          rw [PMF.map_apply, tsum_fintype]
          rw [show (Finset.univ : Finset Action) =
            {Action.down, Action.stay, Action.up} from rfl]
          simp [Action.nextX, hstay']
    _ = (downWeight u s : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) :=
      movePMF_down u s h3

/-! ## Paper worst-case envelope -/

def worstUpWeight (s : State n B) : ℕ :=
  Nat.choose (State.x s) 2 * State.y s

def worstDownWeight (s : State n B) : ℕ :=
  State.x s * Nat.choose (State.y s + State.z s) 2

def aggregateUpWeight (s : State n B) : ℕ :=
  Nat.choose (State.x s) 2 * (State.y s + State.z s)

@[simp] theorem upWeight_worst (s : State n B) :
    upWeight Control.worst s = worstUpWeight s := by
  simp [upWeight, Control.worst, worstUpWeight]

@[simp] theorem downWeight_worst (s : State n B) :
    downWeight Control.worst s = worstDownWeight s := by
  unfold downWeight Control.worst worstDownWeight
  simp only [ite_true]
  rw [pair_two_split]
  ring

theorem worstUpWeight_le
    (u : Control) (s : State n B) :
    worstUpWeight s ≤ upWeight u s := by
  rcases u with ⟨a, xd, yu⟩
  cases a <;> cases xd <;> cases yu <;>
    simp [worstUpWeight, upWeight] <;>
    omega

theorem downWeight_le_worst
    (u : Control) (s : State n B) :
    downWeight u s ≤ worstDownWeight s := by
  have hxyz :
      (match u.xyz with
        | .down => State.x s * State.y s * State.z s
        | _ => 0) ≤
        State.x s * State.y s * State.z s := by
    cases u.xyz <;> simp
  have hxzz :
      (if u.xzzDown then
        State.x s * Nat.choose (State.z s) 2
      else 0) ≤
        State.x s * Nat.choose (State.z s) 2 := by
    cases u.xzzDown <;> simp
  calc
    downWeight u s ≤
        State.x s * Nat.choose (State.y s) 2 +
          State.x s * State.y s * State.z s +
          State.x s * Nat.choose (State.z s) 2 := by
            unfold downWeight
            exact add_le_add (add_le_add le_rfl hxyz) hxzz
    _ = State.x s *
          (Nat.choose (State.y s) 2 +
            State.y s * State.z s +
            Nat.choose (State.z s) 2) := by
          ring
    _ = worstDownWeight s := by
          unfold worstDownWeight
          rw [pair_two_split]

theorem movePMF_worst_up_le
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    movePMF Control.worst s h3 .up ≤ movePMF u s h3 .up := by
  rw [movePMF_up, movePMF_up]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast worstUpWeight_le u s)
    (Nat.choose n 3 : ℝ≥0∞)

theorem movePMF_down_le_worst
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    movePMF u s h3 .down ≤ movePMF Control.worst s h3 .down := by
  rw [movePMF_down, movePMF_down]
  rw [downWeight_worst]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast downWeight_le_worst u s)
    (Nat.choose n 3 : ℝ≥0∞)

theorem worst_nextX_le
    (u : Control) (s : State n B) (k : TripleComp) :
    Action.nextX (State.x s) (Control.worst.action k) ≤
      Action.nextX (State.x s) (u.action k) := by
  rcases u with ⟨a, xd, yu⟩
  cases a <;> cases xd <;> cases yu <;> cases k <;>
    simp [Control.action, Control.worst, Action.nextX] <;>
    omega

/-- Every antitone badness potential of honest `X` has no larger one-step
expectation under an arbitrary response than under the adverse response. -/
theorem step_expect_x_le_worst
    (u : Control) (s : State n B) (h3 : 3 ≤ n)
    (V : ℕ → ℝ≥0∞) (hV : Antitone V) :
    expect (step u s h3) (fun t => V (State.x t)) ≤
      expect (step Control.worst s h3) (fun t => V (State.x t)) := by
  unfold step
  rw [expect_map, expect_map]
  unfold expect
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : TripleComp.weightAt s k = 0
  · rw [triplePMF_zero_of_weight_zero hk]
    simp
  · gcongr
    change
      V (State.x (nextState u s k)) ≤
        V (State.x (nextState Control.worst s k))
    rw [nextState_x_of_weight_ne_zero u s k hk,
      nextState_x_of_weight_ne_zero Control.worst s k hk]
    exact hV (worst_nextX_le u s k)

/-- Division-free statement of the effective favorable rate `y / (y + z)`. -/
theorem worstUp_effectiveRate_cross
    (s : State n B) :
    (State.y s + State.z s) * worstUpWeight s =
      State.y s * aggregateUpWeight s := by
  unfold worstUpWeight aggregateUpWeight
  ring

/-! ## Genuine history-dependent adversaries -/

structure Record (n B : ℕ) where
  before : State n B
  control : Control
  comp : TripleComp
  after : State n B

abbrev History (n B : ℕ) := List (Record n B)

/-- Deterministic adaptive adversary. It chooses a complete composition-indexed
response table from the prior transcript and current state. -/
structure Strategy (n B : ℕ) where
  choose : History n B → State n B → Control

noncomputable def recordOf
    (u : Control) (s : State n B) (k : TripleComp) : Record n B :=
  { before := s
    control := u
    comp := k
    after := nextState u s k }

noncomputable def fixedEventStep
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    PMF (Record n B) :=
  (triplePMF s h3).map (recordOf u s)

noncomputable def adaptiveStep
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n) : PMF (State n B) :=
  step (σ.choose hist s) s h3

noncomputable def adaptiveEventStep
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n) : PMF (Record n B) :=
  fixedEventStep (σ.choose hist s) s h3

theorem fixedEventStep_map_after
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    (fixedEventStep u s h3).map Record.after = step u s h3 := by
  unfold fixedEventStep step recordOf
  rw [PMF.map_comp]
  rfl

theorem adaptiveEventStep_map_after
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n) :
    (adaptiveEventStep σ hist s h3).map Record.after =
      adaptiveStep σ hist s h3 :=
  fixedEventStep_map_after (σ.choose hist s) s h3

/-- Exact finite-horizon state law for a genuinely history-dependent
strategy. This is intentionally not an iterate of a homogeneous kernel. -/
noncomputable def controlledLaw
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ℕ → History n B → State n B → PMF (State n B)
  | 0, _, s => PMF.pure s
  | T + 1, hist, s =>
      (adaptiveEventStep σ hist s h3).bind
        (fun e => controlledLaw σ h3 T (e :: hist) e.after)

theorem adaptiveStep_map_z
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n) :
    (adaptiveStep σ hist s h3).map State.z =
      PMF.pure (State.z s) :=
  step_map_z (σ.choose hist s) s h3

/-- The one-step adverse envelope is uniform over every generated history. -/
theorem adaptiveStep_expect_x_le_worst
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n)
    (V : ℕ → ℝ≥0∞) (hV : Antitone V) :
    expect (adaptiveStep σ hist s h3)
        (fun t => V (State.x t)) ≤
      expect (step Control.worst s h3)
        (fun t => V (State.x t)) :=
  step_expect_x_le_worst (σ.choose hist s) s h3 V hV

/-! ## Theorem 4 regions -/

def HonestXConsensus (s : State n B) : Prop :=
  State.y s = 0

def StrongXEntry (s : State n B) : Prop :=
  n ≤ State.x s + 2 * State.z s

def RelaxedXConsensus (s : State n B) : Prop :=
  n ≤ State.x s + 8 * State.z s

theorem strongXEntry_relaxed
    (s : State n B) (h : StrongXEntry s) :
    RelaxedXConsensus s := by
  unfold StrongXEntry RelaxedXConsensus at *
  omega

end Tri.Byzantine

#print axioms Tri.Byzantine.TripleComp.sum_weight
#print axioms Tri.Byzantine.step_map_z
#print axioms Tri.Byzantine.step_x_up_mass
#print axioms Tri.Byzantine.step_x_down_mass
#print axioms Tri.Byzantine.step_expect_x_le_worst
#print axioms Tri.Byzantine.worstUp_effectiveRate_cross
#print axioms Tri.Byzantine.adaptiveEventStep_map_after
#print axioms Tri.Byzantine.adaptiveStep_expect_x_le_worst

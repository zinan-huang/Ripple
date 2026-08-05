/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Kernel

/-!
# The infection-initiated Tri interaction kernel

The state records active and inactive populations of both opinions.  One raw
interaction is classified into ten disjoint semantic events: four all-active
triple types, five mixed activation types, and one all-inactive self-loop.
-/

namespace Tri

open scoped ENNReal

/-- Counts for the infection-initiated protocol. -/
structure InfectionCfg where
  ax : ℕ
  ay : ℕ
  ix : ℕ
  iy : ℕ
  deriving DecidableEq, Repr

namespace InfectionCfg

def active (s : InfectionCfg) : ℕ := s.ax + s.ay
def inactive (s : InfectionCfg) : ℕ := s.ix + s.iy
def total (s : InfectionCfg) : ℕ := s.active + s.inactive
def Inv (n : ℕ) (s : InfectionCfg) : Prop := s.total = n

end InfectionCfg

/-- The ten semantically distinct outcomes of one infection interaction. -/
inductive InfectionEvent
  | activeXXX
  | activeXXY
  | activeXYY
  | activeYYY
  | activateOneX
  | activateOneY
  | activateTwoXX
  | activateTwoXY
  | activateTwoYY
  | inactiveOnly
  deriving DecidableEq, Fintype, Repr

namespace InfectionEvent

/-- Number of unordered physical triples inducing each semantic event. -/
def weight (s : InfectionCfg) : InfectionEvent → ℕ
  | .activeXXX => Nat.choose s.ax 3
  | .activeXXY => Nat.choose s.ax 2 * s.ay
  | .activeXYY => s.ax * Nat.choose s.ay 2
  | .activeYYY => Nat.choose s.ay 3
  | .activateOneX => Nat.choose s.active 2 * s.ix
  | .activateOneY => Nat.choose s.active 2 * s.iy
  | .activateTwoXX => s.active * Nat.choose s.ix 2
  | .activateTwoXY => s.active * s.ix * s.iy
  | .activateTwoYY => s.active * Nat.choose s.iy 2
  | .inactiveOnly => Nat.choose s.inactive 3

/-- State update.  Natural subtraction occurs only on event branches whose
weight is zero when the required reactants are absent. -/
def next (s : InfectionCfg) : InfectionEvent → InfectionCfg
  | .activeXXX | .activeYYY | .inactiveOnly => s
  | .activeXXY => ⟨s.ax + 1, s.ay - 1, s.ix, s.iy⟩
  | .activeXYY => ⟨s.ax - 1, s.ay + 1, s.ix, s.iy⟩
  | .activateOneX => ⟨s.ax + 1, s.ay, s.ix - 1, s.iy⟩
  | .activateOneY => ⟨s.ax, s.ay + 1, s.ix, s.iy - 1⟩
  | .activateTwoXX => ⟨s.ax + 2, s.ay, s.ix - 2, s.iy⟩
  | .activateTwoXY => ⟨s.ax + 1, s.ay + 1, s.ix - 1, s.iy - 1⟩
  | .activateTwoYY => ⟨s.ax, s.ay + 2, s.ix, s.iy - 2⟩

end InfectionEvent

/-- Vandermonde's degree-three identity with both sides arranged for active /
inactive splitting. -/
theorem choose_three_add (a i : ℕ) :
    Nat.choose a 3 + Nat.choose a 2 * i +
        a * Nat.choose i 2 + Nat.choose i 3 =
      Nat.choose (a + i) 3 := by
  simpa only [Nat.add_assoc] using (choose_three_split a i).symm

/-- Degree-two Vandermonde identity. -/
theorem choose_two_add (x y : ℕ) :
    Nat.choose x 2 + x * y + Nat.choose y 2 =
      Nat.choose (x + y) 2 := by
  induction y with
  | zero => simp
  | succ y ih =>
      rw [show x + (y + 1) = (x + y) + 1 by omega,
        Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_succ_succ, Nat.choose_one_right, ← ih]
      ring

/-- The ten event weights partition all unordered triples. -/
theorem infection_sum_weight (s : InfectionCfg) :
    ∑ e : InfectionEvent, InfectionEvent.weight s e =
      Nat.choose s.total 3 := by
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  simp [InfectionEvent.weight]
  have hactive := choose_three_split s.ax s.ay
  have hinactive := choose_three_split s.ix s.iy
  have htwo := choose_two_add s.ix s.iy
  have hall := choose_three_add s.active s.inactive
  simp only [InfectionCfg.active, InfectionCfg.inactive,
    InfectionCfg.total] at hactive hinactive htwo hall ⊢
  rw [← hall, hactive, hinactive, ← htwo]
  ring

/-- The normalized distribution of semantic infection events. -/
noncomputable def infectionEventPMF
    (s : InfectionCfg) (h : 3 ≤ s.total) : PMF InfectionEvent :=
  PMF.ofFintype
    (fun e =>
      (InfectionEvent.weight s e : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞))
    (by
      have hpos : 0 < Nat.choose s.total 3 := choose_three_pos h
      have hne : ((Nat.choose s.total 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop : ((Nat.choose s.total 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [show ∑ e : InfectionEvent,
          ((InfectionEvent.weight s e : ℕ) : ℝ≥0∞) =
          ((∑ e : InfectionEvent, InfectionEvent.weight s e : ℕ) : ℝ≥0∞) by
            push_cast; rfl]
      rw [infection_sum_weight, ← div_eq_mul_inv]
      exact ENNReal.div_self hne htop)

@[simp] theorem infectionEventPMF_apply
    (s : InfectionCfg) (h : 3 ≤ s.total) (e : InfectionEvent) :
    infectionEventPMF s h e =
      (InfectionEvent.weight s e : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞) :=
  rfl

/-- One raw infection interaction on the count state. -/
noncomputable def infectionStep
    (s : InfectionCfg) (h : 3 ≤ s.total) : PMF InfectionCfg :=
  (infectionEventPMF s h).map (InfectionEvent.next s)

/-- Every positive-mass infection event preserves total population. -/
theorem InfectionEvent.next_inv
    (n : ℕ) (s : InfectionCfg) (e : InfectionEvent)
    (hs : s.Inv n) (he : InfectionEvent.weight s e ≠ 0) :
    (InfectionEvent.next s e).Inv n := by
  rcases s with ⟨ax, ay, ix, iy⟩
  simp only [InfectionCfg.Inv, InfectionCfg.total, InfectionCfg.active,
    InfectionCfg.inactive] at hs ⊢
  cases e with
  | activeXXX => simpa only [InfectionEvent.next] using hs
  | activeXXY =>
      have hay : ay ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      simp only [InfectionEvent.next]
      omega
  | activeXYY =>
      have hax : ax ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).1
      simp only [InfectionEvent.next]
      omega
  | activeYYY => simpa only [InfectionEvent.next] using hs
  | activateOneX =>
      have hix : ix ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      simp only [InfectionEvent.next]
      omega
  | activateOneY =>
      have hiy : iy ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      simp only [InfectionEvent.next]
      omega
  | activateTwoXX =>
      have hchoose : Nat.choose ix 2 ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      have hix : 2 ≤ ix := Nat.choose_ne_zero_iff.mp hchoose
      simp only [InfectionEvent.next]
      omega
  | activateTwoXY =>
      have hmul : (ax + ay) * ix * iy ≠ 0 := by
        simpa only [InfectionEvent.weight, InfectionCfg.active] using he
      have hix : ix ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (Nat.mul_ne_zero_iff.mp hmul).1).2
      have hiy : iy ≠ 0 := (Nat.mul_ne_zero_iff.mp hmul).2
      simp only [InfectionEvent.next]
      omega
  | activateTwoYY =>
      have hchoose : Nat.choose iy 2 ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa only [InfectionEvent.weight] using he)).2
      have hiy : 2 ≤ iy := Nat.choose_ne_zero_iff.mp hchoose
      simp only [InfectionEvent.next]
      omega
  | inactiveOnly => simpa only [InfectionEvent.next] using hs

/-- Infection configurations with fixed total population. -/
abbrev InfectionState (n : ℕ) := {s : InfectionCfg // s.Inv n}

/-- A total update on the invariant subtype.  Zero-weight impossible events are
sent back to the current state. -/
noncomputable def InfectionEvent.nextState
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent) :
    InfectionState n :=
  if he : InfectionEvent.weight s.1 e = 0 then
    s
  else
    ⟨InfectionEvent.next s.1 e,
      InfectionEvent.next_inv n s.1 e s.2 he⟩

/-- One infection interaction lifted to the fixed-population subtype. -/
noncomputable def infectionStateStep
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionState n) :
    PMF (InfectionState n) :=
  (infectionEventPMF s.1 (by
    have hs := s.2
    simp only [InfectionCfg.Inv] at hs
    omega)).map (InfectionEvent.nextState s)

/-- All molecules are active `X`. -/
def InfectionXConsensus {n : ℕ} (s : InfectionState n) : Prop :=
  s.1.ax = n ∧ s.1.ay = 0 ∧ s.1.ix = 0 ∧ s.1.iy = 0

/-- All-`X` consensus is absorbing for the infection kernel. -/
theorem infectionStateStep_consensus
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionState n)
    (hs : InfectionXConsensus s) :
    infectionStateStep n h3 s = PMF.pure s := by
  have hconst : ∀ e, InfectionEvent.nextState s e = s := by
    intro e
    unfold InfectionEvent.nextState
    split_ifs with he
    · rfl
    · apply Subtype.ext
      rcases s with ⟨⟨ax, ay, ix, iy⟩, hinv⟩
      simp only [InfectionXConsensus] at hs
      rcases hs with ⟨rfl, rfl, rfl, rfl⟩
      cases e <;>
        simp [InfectionEvent.weight, InfectionCfg.active,
          InfectionEvent.next] at he ⊢
  unfold infectionStateStep
  rw [show InfectionEvent.nextState s = (fun _ => s) from funext hconst]
  ext z
  rw [PMF.map_apply, PMF.pure_apply]
  by_cases hz : z = s
  · subst z
    simp only [if_true]
    exact PMF.tsum_coe _
  · simp only [if_neg hz, tsum_zero]

end Tri

#print axioms Tri.infection_sum_weight
#print axioms Tri.infectionEventPMF_apply
#print axioms Tri.InfectionEvent.next_inv
#print axioms Tri.infectionStateStep_consensus

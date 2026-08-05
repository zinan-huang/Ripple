/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineRateAdapter
import Tri.ByzantineEntry
import Tri.BellmanDomination
import Tri.BinaryMonotone

/-!
# Phase-I Byzantine rung: Bellman local interface

This file records the ordered fixed-Byzantine-count level used by the Phase-I
Bellman transfer, discharges the domination hypothesis from the existing
pointwise worst-response lemma, and proves the reference-kernel stochastic
monotonicity over this ordered fiber.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B z : ℕ}

/-- Physical states with a fixed Byzantine count.  The Phase-I Bellman order
is by honest `X` count inside this conserved fiber. -/
abbrev Phase1Level (n B z : ℕ) :=
  {s : State n B // State.z s = z}

instance phase1LevelPreorder : Preorder (Phase1Level n B z) where
  le s t := State.x s.1 ≤ State.x t.1
  lt s t := State.x s.1 < State.x t.1
  le_refl _ := le_rfl
  le_trans _ _ _ hst htu := hst.trans htu
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

/-- Fixed-`z` levels are uniquely determined by their honest `X` count. -/
theorem phase1Level_ext_x (q r : Phase1Level n B z)
    (hx : State.x q.1 = State.x r.1) :
    q = r := by
  apply Subtype.ext
  apply Subtype.ext
  cases q with
  | mk qs hq =>
  cases r with
  | mk rs hr =>
  cases qs with
  | mk qp hqp =>
  cases rs with
  | mk rp hrp =>
  cases qp with
  | mk qx qz =>
  cases rp with
  | mk rx rz =>
  simp [State.x, State.z] at hx hq hr ⊢
  constructor
  · exact Fin.ext hx
  · apply Fin.ext
    omega

/-- The canonical point of the same fixed-`z` fiber with honest `X` count `x`. -/
noncomputable def phase1LevelWithX
    (base : Phase1Level n B z) (x : ℕ) (hxz : x + z ≤ n) :
    Phase1Level n B z := by
  refine ⟨⟨(⟨x, by omega⟩, base.1.1.2), ?_⟩, ?_⟩
  · change x + State.z base.1 ≤ n
    rw [base.2]
    exact hxz
  · change State.z base.1 = z
    exact base.2

@[simp] theorem phase1LevelWithX_x
    (base : Phase1Level n B z) (x : ℕ) (hxz : x + z ≤ n) :
    State.x (phase1LevelWithX base x hxz).1 = x :=
  rfl

@[simp] theorem phase1LevelWithX_z
    (base : Phase1Level n B z) (x : ℕ) (hxz : x + z ≤ n) :
    State.z (phase1LevelWithX base x hxz).1 = z :=
  base.2

/-- The top canonical point in a nonempty fixed-`z` fiber. -/
noncomputable def phase1LevelTop (base : Phase1Level n B z) :
    Phase1Level n B z :=
  phase1LevelWithX base (n - z) (by
    have hzpop : z ≤ n := by
      rw [← base.2]
      exact State.z_le_population base.1
    omega)

/-- Any monotone observable on the fixed fiber can be read as a monotone
observable of the honest `X` count.  Outside the physical fiber, we clamp to
the top fiber point. -/
noncomputable def phase1FiberValue
    (base : Phase1Level n B z) (f : Phase1Level n B z → ℝ≥0∞)
    (x : ℕ) : ℝ≥0∞ :=
  if hxz : x + z ≤ n then
    f (phase1LevelWithX base x hxz)
  else
    f (phase1LevelTop base)

theorem phase1FiberValue_eq_of_level
    (base : Phase1Level n B z) (f : Phase1Level n B z → ℝ≥0∞)
    (q : Phase1Level n B z) :
    phase1FiberValue base f (State.x q.1) = f q := by
  have hxz : State.x q.1 + z ≤ n := by
    have hxz' := State.xz_le q.1
    have hzq : State.z q.1 = z := q.2
    omega
  rw [phase1FiberValue, dif_pos hxz]
  congr 1
  exact phase1Level_ext_x
    (phase1LevelWithX base (State.x q.1) hxz) q rfl

theorem phase1FiberValue_mono
    (base : Phase1Level n B z) (f : Phase1Level n B z → ℝ≥0∞)
    (hf : Monotone f) :
    Monotone (phase1FiberValue base f) := by
  intro x y hxy
  by_cases hyz : y + z ≤ n
  · have hxz : x + z ≤ n := by omega
    simp [phase1FiberValue, hxz, hyz]
    exact hf (by
      change x ≤ y
      exact hxy)
  · by_cases hxz : x + z ≤ n
    · simp [phase1FiberValue, hxz, hyz]
      exact hf (by
        change x ≤ n - z
        have hzpop : z ≤ n := by
          rw [← base.2]
          exact State.z_le_population base.1
        omega)
    · simp [phase1FiberValue, hxz, hyz]

/-- Three-atom stochastic comparison, stated directly for four ordered values.
This is the local birth-death monotonicity core used by the fixed-`z`
Byzantine reference kernel. -/
theorem adjacent_three_value_expect_le
    {p0 p1 p2 q0 q1 q2 : ℝ≥0∞}
    (hp : p0 + p1 + p2 = 1)
    (hq : q0 + q1 + q2 = 1)
    (hcross : p2 + q0 ≤ 1)
    {v0 v1 v2 v3 : ℝ≥0∞}
    (h01 : v0 ≤ v1) (h12 : v1 ≤ v2) (h23 : v2 ≤ v3) :
    p0 * v0 + p1 * v1 + p2 * v2 ≤
      q0 * v1 + q1 * v2 + q2 * v3 := by
  have hp2 : p2 ≤ 1 := by
    rw [← hp]
    exact le_add_left le_rfl
  have hq0 : q0 ≤ 1 := by
    rw [← hq]
    exact le_add_right (le_add_right le_rfl)
  have hp2top : p2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hp2
  have hq0top : q0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hq0
  have hq0le : q0 ≤ p0 + p1 := by
    apply (ENNReal.add_le_add_iff_right hp2top).mp
    calc
      q0 + p2 = p2 + q0 := add_comm _ _
      _ ≤ 1 := hcross
      _ = (p0 + p1) + p2 := hp.symm
  let d : ℝ≥0∞ := (p0 + p1) - q0
  have hp01 : q0 + d = p0 + p1 := by
    exact add_tsub_cancel_of_le hq0le
  have hdq : d + p2 = q1 + q2 := by
    apply (ENNReal.add_right_inj hq0top).mp
    calc
      q0 + (d + p2) = (q0 + d) + p2 := by ring
      _ = (p0 + p1) + p2 := by rw [hp01]
      _ = 1 := hp
      _ = q0 + (q1 + q2) := by rw [← hq]; ring
  calc
    p0 * v0 + p1 * v1 + p2 * v2 ≤
        p0 * v1 + p1 * v1 + p2 * v2 := by
      gcongr
    _ = (p0 + p1) * v1 + p2 * v2 := by ring
    _ = (q0 + d) * v1 + p2 * v2 := by rw [hp01]
    _ = q0 * v1 + d * v1 + p2 * v2 := by ring
    _ ≤ q0 * v1 + d * v2 + p2 * v2 := by
      gcongr
    _ = q0 * v1 + (d + p2) * v2 := by ring
    _ = q0 * v1 + (q1 + q2) * v2 := by rw [hdq]
    _ = q0 * v1 + q1 * v2 + q2 * v2 := by ring
    _ ≤ q0 * v1 + q1 * v2 + q2 * v3 := by
      gcongr

/-- The canonical fixed-fiber `X`-marginal kernel, clamped to a pure state
outside the physical fixed-`z` fiber. -/
noncomputable def phase1XStep
    (h3 : 3 ≤ n) (base : Phase1Level n B z) (x : ℕ) : PMF ℕ :=
  if hxz : x + z ≤ n then
    (step Control.worst (phase1LevelWithX base x hxz).1 h3).map State.x
  else
    PMF.pure x

theorem phase1XStep_of_level
    (h3 : 3 ≤ n) (base q : Phase1Level n B z) :
    phase1XStep h3 base (State.x q.1) =
      (step Control.worst q.1 h3).map State.x := by
  have hxz : State.x q.1 + z ≤ n := by
    have hxz' := State.xz_le q.1
    have hzq : State.z q.1 = z := q.2
    omega
  rw [phase1XStep, dif_pos hxz]
  have hlev := phase1Level_ext_x
    (phase1LevelWithX base (State.x q.1) hxz) q rfl
  rw [hlev]

/-- Count-level crossing bound for adjacent fixed-`z` states under the
paper-worst response.  The up mass sees only honest `Y`, so it is bounded by
the aggregate minority count; the upper down mass is exactly aggregate. -/
theorem phase1_adjacent_cross_count_le
    (base : Phase1Level n B z) {x : ℕ}
    (hx : x + z ≤ n) (hxsucc : x + 1 + z ≤ n) :
    worstUpWeight (phase1LevelWithX base x hx).1 +
        worstDownWeight (phase1LevelWithX base (x + 1) hxsucc).1 ≤
      Nat.choose n 3 := by
  let s := (phase1LevelWithX base x hx).1
  let t := (phase1LevelWithX base (x + 1) hxsucc).1
  let m := State.y s + State.z s
  have hsx : State.x s = x := rfl
  have htx : State.x t = x + 1 := rfl
  have hsz : State.z s = z := phase1LevelWithX_z base x hx
  have htz : State.z t = z := phase1LevelWithX_z base (x + 1) hxsucc
  have hsTotal : x + m = n := by
    dsimp [m]
    have ht := State.total s
    omega
  have htAggSucc : State.y t + State.z t + 1 = m := by
    have hsT := State.total s
    have htT := State.total t
    dsimp [m] at *
    omega
  have hup_le :
      worstUpWeight s ≤ Nat.choose x 2 * m := by
    unfold worstUpWeight
    dsimp only [s]
    rw [hsx]
    exact Nat.mul_le_mul_left (Nat.choose x 2)
      (Nat.le_add_right _ _)
  by_cases hx0 : x = 0
  · have hup0 : worstUpWeight s = 0 := by
      unfold worstUpWeight
      rw [hsx, hx0]
      simp
    have htAggN : State.y t + State.z t = n - 1 := by omega
    have hdown_eq :
        worstDownWeight t = Nat.choose (n - 1) 2 := by
      unfold worstDownWeight
      rw [htx, hx0, htAggN]
      simp
    have hchoose : Nat.choose (n - 1) 2 ≤ Nat.choose n 3 := by
      have hnpos : 0 < n := by omega
      rw [show n = (n - 1) + 1 by omega]
      have hpascal :
          Nat.choose ((n - 1) + 1) 3 =
            Nat.choose (n - 1) 2 + Nat.choose (n - 1) 3 :=
        Nat.choose_succ_succ (n - 1) 2
      rw [hpascal]
      exact Nat.le_add_right _ _
    calc
      worstUpWeight s + worstDownWeight t =
          Nat.choose (n - 1) 2 := by rw [hup0, hdown_eq, zero_add]
      _ ≤ Nat.choose n 3 := hchoose
  · have hxpos : 0 < x := by omega
    by_cases hm2 : 2 ≤ m
    · have hbase := adjacent_cross_count_le (x - 1) (m - 2)
      have hbase' :
          Nat.choose x 2 * m +
              (x + 1) * Nat.choose (m - 1) 2 ≤
            Nat.choose n 3 := by
        simpa [show x - 1 + 1 = x by omega,
          show x - 1 + 2 = x + 1 by omega,
          show m - 2 + 2 = m by omega,
          show m - 2 + 1 = m - 1 by omega,
          hsTotal] using hbase
      calc
        worstUpWeight s + worstDownWeight t ≤
            Nat.choose x 2 * m +
              (x + 1) * Nat.choose (m - 1) 2 := by
          unfold worstDownWeight
          rw [htx, show State.y t + State.z t = m - 1 by omega]
          exact add_le_add hup_le le_rfl
        _ ≤ Nat.choose n 3 := hbase'
    · have hm : m = 1 := by
        have hmpos : 0 < m := by
          have ht := State.total t
          dsimp [m] at *
          omega
        omega
      have htAgg0 : State.y t + State.z t = 0 := by
        omega
      have hdown0 : worstDownWeight t = 0 := by
        unfold worstDownWeight
        rw [htAgg0]
        simp
      have hn_eq : n = x + 1 := by omega
      have hchoose : Nat.choose x 2 ≤ Nat.choose n 3 := by
        rw [hn_eq]
        have hpascal :
            Nat.choose (x + 1) 3 =
              Nat.choose x 2 + Nat.choose x 3 :=
          Nat.choose_succ_succ x 2
        rw [hpascal]
        exact Nat.le_add_right _ _
      calc
        worstUpWeight s + worstDownWeight t =
            worstUpWeight s := by rw [hdown0, add_zero]
        _ ≤ Nat.choose x 2 * m := hup_le
        _ = Nat.choose x 2 := by rw [hm, mul_one]
        _ ≤ Nat.choose n 3 := hchoose

/-- Mass form of the adjacent crossing bound. -/
theorem phase1_adjacent_cross_mass_le_one
    (h3 : 3 ≤ n) (base : Phase1Level n B z) {x : ℕ}
    (hx : x + z ≤ n) (hxsucc : x + 1 + z ≤ n) :
    movePMF Control.worst (phase1LevelWithX base x hx).1 h3 .up +
        movePMF Control.worst
          (phase1LevelWithX base (x + 1) hxsucc).1 h3 .down ≤ 1 := by
  rw [movePMF_up, movePMF_down, upWeight_worst, downWeight_worst,
    ENNReal.div_add_div_same]
  have hcount :=
    phase1_adjacent_cross_count_le
      (base := base) (x := x) hx hxsucc
  calc
    ((worstUpWeight (phase1LevelWithX base x hx).1 : ℝ≥0∞) +
          (worstDownWeight
            (phase1LevelWithX base (x + 1) hxsucc).1 : ℝ≥0∞)) /
        (Nat.choose n 3 : ℝ≥0∞) ≤
        (Nat.choose n 3 : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast hcount
    _ = 1 := by
      apply ENNReal.div_self
      · exact_mod_cast (choose_three_pos h3).ne'
      · exact ENNReal.natCast_ne_top _

/-- At fixed `X=0`, the paper-worst response cannot change the `X` marginal. -/
theorem phase1_worst_x_zero_expect
    (h3 : 3 ≤ n) (s : State n B) (hsx : State.x s = 0)
    (F : ℕ → ℝ≥0∞) :
    expect ((step Control.worst s h3).map State.x) F = F 0 := by
  have hdown : movePMF Control.worst s h3 .down = 0 := by
    rw [movePMF_down, downWeight_worst]
    unfold worstDownWeight
    rw [hsx]
    simp
  have hup : movePMF Control.worst s h3 .up = 0 := by
    rw [movePMF_up, upWeight_worst]
    unfold worstUpWeight
    rw [hsx]
    simp
  have hsum := movePMF_masses_sum Control.worst s h3
  rw [hdown, hup] at hsum
  simp only [zero_add, add_zero] at hsum
  calc
    expect ((step Control.worst s h3).map State.x) F =
        expect (step Control.worst s h3) (fun t => F (State.x t)) := by
      rw [expect_map]
    _ = movePMF Control.worst s h3 .down * F (State.x s - 1) +
          movePMF Control.worst s h3 .stay * F (State.x s) +
          movePMF Control.worst s h3 .up * F (State.x s + 1) := by
      exact expect_step_x_actions Control.worst s h3 F
    _ = F 0 := by
      rw [hdown, hup, hsum, hsx]
      simp

/-- A paper-worst physical step can raise the `X` marginal by at most one in
stochastic order. -/
theorem phase1_worst_x_expect_le_succ
    (h3 : 3 ≤ n) (s : State n B)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect ((step Control.worst s h3).map State.x) F ≤
      F (State.x s + 1) := by
  calc
    expect ((step Control.worst s h3).map State.x) F =
        expect (step Control.worst s h3) (fun t => F (State.x t)) := by
      rw [expect_map]
    _ = movePMF Control.worst s h3 .down * F (State.x s - 1) +
          movePMF Control.worst s h3 .stay * F (State.x s) +
          movePMF Control.worst s h3 .up * F (State.x s + 1) := by
      exact expect_step_x_actions Control.worst s h3 F
    _ ≤ movePMF Control.worst s h3 .down * F (State.x s + 1) +
          movePMF Control.worst s h3 .stay * F (State.x s + 1) +
          movePMF Control.worst s h3 .up * F (State.x s + 1) := by
      gcongr
      · exact hF (by omega)
      · exact hF (by omega)
    _ = F (State.x s + 1) := by
      rw [← add_mul, ← add_mul, movePMF_masses_sum, one_mul]

/-- Adjacent canonical fixed-`z` reference `X` marginals are stochastically
ordered. -/
theorem phase1XStep_expect_le_succ
    (h3 : 3 ≤ n) (base : Phase1Level n B z)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) (x : ℕ) :
    expect (phase1XStep h3 base x) F ≤
      expect (phase1XStep h3 base (x + 1)) F := by
  by_cases hxsucc : x + 1 + z ≤ n
  · have hx : x + z ≤ n := by omega
    simp [phase1XStep, hx, hxsucc]
    let s := (phase1LevelWithX base x hx).1
    let t := (phase1LevelWithX base (x + 1) hxsucc).1
    change
      expect ((step Control.worst s h3).map State.x) F ≤
        expect ((step Control.worst t h3).map State.x) F
    by_cases hx0 : x = 0
    · have hsx : State.x s = 0 := by
        dsimp [s]
        exact hx0
      calc
        expect ((step Control.worst s h3).map State.x) F = F 0 :=
          phase1_worst_x_zero_expect h3 s hsx F
        _ ≤ expect ((step Control.worst t h3).map State.x) F :=
          expect_ge_at_zero ((step Control.worst t h3).map State.x) F hF
    · have hxpos : 0 < x := by omega
      calc
        expect ((step Control.worst s h3).map State.x) F =
            movePMF Control.worst s h3 .down * F (x - 1) +
              movePMF Control.worst s h3 .stay * F x +
              movePMF Control.worst s h3 .up * F (x + 1) := by
          calc
            expect ((step Control.worst s h3).map State.x) F =
                expect (step Control.worst s h3)
                  (fun t => F (State.x t)) := by
              rw [expect_map]
            _ = movePMF Control.worst s h3 .down * F (State.x s - 1) +
                  movePMF Control.worst s h3 .stay * F (State.x s) +
                  movePMF Control.worst s h3 .up *
                    F (State.x s + 1) := by
              exact expect_step_x_actions Control.worst s h3 F
            _ = movePMF Control.worst s h3 .down * F (x - 1) +
                  movePMF Control.worst s h3 .stay * F x +
                  movePMF Control.worst s h3 .up * F (x + 1) := by
              simp [s]
        _ ≤ movePMF Control.worst t h3 .down * F x +
              movePMF Control.worst t h3 .stay * F (x + 1) +
              movePMF Control.worst t h3 .up * F (x + 2) := by
          exact adjacent_three_value_expect_le
            (movePMF_masses_sum Control.worst s h3)
            (movePMF_masses_sum Control.worst t h3)
            (by
              simpa [s, t] using
                phase1_adjacent_cross_mass_le_one
                  (h3 := h3) (base := base) (x := x) hx hxsucc)
            (hF (by omega)) (hF (by omega)) (hF (by omega))
        _ = expect ((step Control.worst t h3).map State.x) F := by
          calc
            movePMF Control.worst t h3 .down * F x +
                movePMF Control.worst t h3 .stay * F (x + 1) +
                movePMF Control.worst t h3 .up * F (x + 2) =
                movePMF Control.worst t h3 .down * F (State.x t - 1) +
                  movePMF Control.worst t h3 .stay * F (State.x t) +
                  movePMF Control.worst t h3 .up *
                    F (State.x t + 1) := by
              simp [t, show x + 1 - 1 = x by omega,
                show x + 1 + 1 = x + 2 by omega]
            _ = expect (step Control.worst t h3)
                (fun u => F (State.x u)) := by
              exact (expect_step_x_actions Control.worst t h3 F).symm
            _ = expect ((step Control.worst t h3).map State.x) F := by
              rw [expect_map]
  · by_cases hx : x + z ≤ n
    · simp [phase1XStep, hx, hxsucc]
      exact phase1_worst_x_expect_le_succ h3
        (phase1LevelWithX base x hx).1 F hF
    · simp [phase1XStep, hx, hxsucc]
      exact hF (Nat.le_succ x)

/-- The canonical fixed-`z` reference `X` marginal is monotone in the starting
honest `X` count. -/
theorem phase1XStep_expect_mono
    (h3 : 3 ≤ n) (base : Phase1Level n B z)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    Monotone fun x => expect (phase1XStep h3 base x) F :=
  monotone_nat_of_le_succ
    (phase1XStep_expect_le_succ h3 base F hF)

/-- One fixed-control transition, kept inside the conserved `z` fiber. -/
noncomputable def phase1LevelNext
    (u : Control) (q : Phase1Level n B z) (k : TripleComp) :
    Phase1Level n B z :=
  ⟨nextState u q.1 k, by simp [q.2]⟩

/-- The paper-worst reference step on the fixed-`z` Phase-I level. -/
noncomputable def phase1ReferenceStep
    (h3 : 3 ≤ n) (q : Phase1Level n B z) :
    PMF (Phase1Level n B z) :=
  (triplePMF q.1 h3).map (phase1LevelNext Control.worst q)

/-- The fixed-fiber reference step has the same `X` marginal as the underlying
paper-worst physical step. -/
theorem phase1ReferenceStep_map_x
    (h3 : 3 ≤ n) (q : Phase1Level n B z) :
    (phase1ReferenceStep h3 q).map (fun r => State.x r.1) =
      (step Control.worst q.1 h3).map State.x := by
  unfold phase1ReferenceStep step phase1LevelNext
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- Expectations on a fixed fiber are expectations of the `X` marginal against
the induced count observable. -/
theorem phase1ReferenceStep_expect_eq_x
    (base : Phase1Level n B z) (h3 : 3 ≤ n)
    (q : Phase1Level n B z)
    (f : Phase1Level n B z → ℝ≥0∞) :
    expect (phase1ReferenceStep h3 q) f =
      expect ((step Control.worst q.1 h3).map State.x)
        (phase1FiberValue base f) := by
  calc
    expect (phase1ReferenceStep h3 q) f =
        expect (phase1ReferenceStep h3 q)
          (fun r => phase1FiberValue base f (State.x r.1)) := by
      congr 1
      funext r
      exact (phase1FiberValue_eq_of_level base f r).symm
    _ = expect ((phase1ReferenceStep h3 q).map
          (fun r => State.x r.1)) (phase1FiberValue base f) := by
      rw [expect_map]
    _ = expect ((step Control.worst q.1 h3).map State.x)
          (phase1FiberValue base f) := by
      rw [phase1ReferenceStep_map_x]

/-- Bellman `hmono` for the Phase-I fixed-`z` reference kernel. -/
theorem phase1ReferenceStep_mono
    (h3 : 3 ≤ n) :
    ∀ f : Phase1Level n B z → ℝ≥0∞, Monotone f →
      Monotone fun q => expect (phase1ReferenceStep h3 q) f := by
  intro f hf q r hqr
  let F : ℕ → ℝ≥0∞ := phase1FiberValue q f
  have hF : Monotone F := phase1FiberValue_mono q f hf
  calc
    expect (phase1ReferenceStep h3 q) f =
        expect (phase1XStep h3 q (State.x q.1)) F := by
      rw [phase1ReferenceStep_expect_eq_x (base := q) h3 q f]
      rw [phase1XStep_of_level h3 q q]
    _ ≤ expect (phase1XStep h3 q (State.x r.1)) F :=
      phase1XStep_expect_mono h3 q F hF hqr
    _ = expect (phase1ReferenceStep h3 r) f := by
      rw [phase1XStep_of_level h3 q r]
      exact (phase1ReferenceStep_expect_eq_x (base := q) h3 r f).symm

/-- The history-dependent controlled step in the Bellman form
`H × L`, with the updated transcript as external history. -/
noncomputable def phase1ControlledStep
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase1Level n B z) :
    PMF (History n B × Phase1Level n B z) :=
  (triplePMF q.1 h3).map fun k =>
    (recordOf (σ.choose hist q.1) q.1 k :: hist,
      phase1LevelNext (σ.choose hist q.1) q k)

/-- Bellman domination hypothesis `hdom` for the Byzantine Phase-I pair.

The proof uses the same random triple on both sides and then applies
`worst_nextX_le` pointwise on every positive-mass composition. -/
theorem phase1_reference_le_controlled
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ∀ hist q (f : Phase1Level n B z → ℝ≥0∞), Monotone f →
      expect (phase1ReferenceStep h3 q) f ≤
        expect (phase1ControlledStep σ h3 hist q) (fun r => f r.2) := by
  intro hist q f hf
  unfold phase1ReferenceStep phase1ControlledStep
  rw [expect_map, expect_map]
  unfold expect
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : TripleComp.weightAt q.1 k = 0
  · rw [triplePMF_zero_of_weight_zero (s := q.1) (h3 := h3) hk]
    simp
  · gcongr
    exact hf (by
      change State.x (nextState Control.worst q.1 k) ≤
        State.x (nextState (σ.choose hist q.1) q.1 k)
      rw [nextState_x_of_weight_ne_zero Control.worst q.1 k hk,
        nextState_x_of_weight_ne_zero (σ.choose hist q.1) q.1 k hk]
      exact worst_nextX_le (σ.choose hist q.1) q.1 k)

namespace Phase1RungExample

private def s : State 4 0 := by
  refine ⟨(⟨2, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def q : Phase1Level 4 0 0 :=
  ⟨s, by rfl⟩

private def sigma : Strategy 4 0 :=
  { choose := fun _ _ => Control.neutral }

example :
    expect (phase1ReferenceStep (n := 4) (B := 0) (z := 0)
        (by norm_num) q)
        (fun r => (State.x r.1 : ℝ≥0∞)) ≤
      expect (phase1ControlledStep sigma (by norm_num) [] q)
        (fun r => (State.x r.2.1 : ℝ≥0∞)) := by
  exact
    phase1_reference_le_controlled
      (n := 4) (B := 0) (z := 0)
      sigma (by norm_num) [] q
      (fun r => (State.x r.1 : ℝ≥0∞))
      (by
        intro a b hab
        change (State.x a.1 : ℝ≥0∞) ≤ (State.x b.1 : ℝ≥0∞)
        exact_mod_cast hab)

example :
    Monotone fun q : Phase1Level 4 0 0 =>
      expect (phase1ReferenceStep (n := 4) (B := 0) (z := 0)
          (by norm_num) q)
        (fun r => (State.x r.1 : ℝ≥0∞)) := by
  exact
    phase1ReferenceStep_mono
      (n := 4) (B := 0) (z := 0)
      (by norm_num)
      (fun r => (State.x r.1 : ℝ≥0∞))
      (by
        intro a b hab
        change (State.x a.1 : ℝ≥0∞) ≤ (State.x b.1 : ℝ≥0∞)
        exact_mod_cast hab)

end Phase1RungExample

end Tri.Byzantine

#print axioms Tri.Byzantine.phase1_reference_le_controlled
#print axioms Tri.Byzantine.phase1_adjacent_cross_count_le
#print axioms Tri.Byzantine.phase1_adjacent_cross_mass_le_one
#print axioms Tri.Byzantine.phase1XStep_expect_mono
#print axioms Tri.Byzantine.phase1ReferenceStep_mono

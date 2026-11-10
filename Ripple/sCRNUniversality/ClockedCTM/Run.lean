/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Assembly

/-!
# The schedule of a CTM run (FIX3-SCWB-T32 §4, list after Lemma 4.5)

A CTM configuration is `(q, w)` with a tape `w : List Bool`; a step reads the first bit `b`,
deletes it, appends `z` and goes to `q'`, where `C.next q b = (q', z)` (`CTM.stepT`).  The tape
`w` of length `s` is stored as `#M = tval w = Σ (w_i + 1) 3^{s - i}` (`tval`).

For tapes of length `s = n + 3` put `p = 3^n`, `m = 9 p = 3^{s-1}`, threshold `T0 = 20 p` and
margin `g = 2 p` (`tape_facts`: the first bit is `0` iff `x + g ≤ T0`, and `x' = 3 (x - (b+1) m)
+ (z + 1)`).  `ctmSched C n c0` is the schedule whose target after `k = 4 j + r` ticks is
`𝒦_{r+1}(c_j)` for `r < 3` and `𝒦_4(q_j, b_j; w_{j+1})` for `r = 3`, with the windows and
potentials of `Window12`–`Window41` and uniform start bounds `Θ12`–`Θ41`.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-! ### Tapes -/

/-- Base-3 value of a tape, digit `bw b ∈ {1, 2}` per bit, most significant first. -/
def tval : List Bool → ℕ
  | [] => 0
  | b :: l => bw b * 3 ^ l.length + tval l

theorem bw_ge (b : Bool) : 1 ≤ bw b := by cases b <;> simp [bw]

theorem bw_le (b : Bool) : bw b ≤ 2 := by cases b <;> simp [bw]

theorem tval_append (l : List Bool) (z : Bool) : tval (l ++ [z]) = 3 * tval l + bw z := by
  induction l with
  | nil => simp [tval]
  | cons b l ih =>
    simp only [List.cons_append, tval, ih, List.length_append, List.length_singleton, pow_succ]
    ring

theorem tval_bounds (l : List Bool) :
    3 ^ l.length ≤ 2 * tval l + 1 ∧ tval l + 1 ≤ 3 ^ l.length := by
  induction l with
  | nil => simp [tval]
  | cons b l ih =>
    simp only [tval, List.length_cons, pow_succ]
    have h1 := bw_ge b
    have h2 := bw_le b
    generalize 3 ^ l.length = P at *
    obtain ⟨ih1, ih2⟩ := ih
    constructor <;> nlinarith

/-- One step of a CTM on `(state, tape)`. -/
def CTM.stepT (C : CTM Q) (c : Q × List Bool) : Q × List Bool :=
  ((C.next c.1 (c.2.headD false)).1, c.2.tail ++ [(C.next c.1 (c.2.headD false)).2])

/-- The CTM configuration after `j` steps from `c0`. -/
def CTM.runT (C : CTM Q) (c0 : Q × List Bool) : ℕ → Q × List Bool
  | 0 => c0
  | j + 1 => C.stepT (C.runT c0 j)

theorem stepT_length {c : Q × List Bool} (h : 1 ≤ c.2.length) :
    (C.stepT c).2.length = c.2.length := by
  simp only [CTM.stepT, List.length_append, List.length_tail, List.length_singleton]
  omega

theorem runT_length {c0 : Q × List Bool} {s : ℕ} (h : c0.2.length = s) (hs : 1 ≤ s) (j : ℕ) :
    (C.runT c0 j).2.length = s := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simp only [CTM.runT]
    rw [stepT_length C (by omega), ih]

/-- Arithmetic of a tape of length `n + 3`: the CTM step on values, the threshold, and size
bounds. -/
theorem tape_facts {n : ℕ} {w : List Bool} (hw : w.length = n + 3) (z : Bool) :
    tval (w.tail ++ [z]) + 3 * bw (w.headD false) * (9 * 3 ^ n) = 3 * tval w + bw z ∧
      (w.headD false = false → tval w + 2 * 3 ^ n ≤ 20 * 3 ^ n) ∧
      (w.headD false = true → 20 * 3 ^ n + 2 * 3 ^ n ≤ tval w) ∧
      9 * 3 ^ n ≤ tval (w.tail ++ [z]) ∧ tval (w.tail ++ [z]) < 3 * (9 * 3 ^ n) ∧
      tval w < 3 * (9 * 3 ^ n) := by
  rcases w with _ | ⟨b, l⟩
  · simp at hw
  simp only [List.length_cons] at hw
  have hl : l.length = n + 2 := by omega
  have hb := tval_bounds l
  rw [hl] at hb
  simp only [List.tail_cons, List.headD_cons, tval, hl, tval_append]
  have e : 3 ^ (n + 2) = 9 * 3 ^ n := by rw [pow_add]; ring
  rw [e] at hb ⊢
  have hz1 := bw_ge z
  have hz2 := bw_le z
  have hp : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  generalize 3 ^ n = p at *
  generalize tval l = t at *
  generalize bw z = bz at *
  obtain ⟨hb1, hb2⟩ := hb
  cases b
  · simp only [show bw false = 1 from rfl]
    refine ⟨by omega, fun _ => by omega, fun h => absurd h (by decide), by omega, by omega,
      by omega⟩
  · simp only [show bw true = 2 from rfl]
    refine ⟨by omega, fun h => absurd h (by decide), fun _ => by omega, by omega, by omega,
      by omega⟩

/-! ### The schedule -/

/-- Configuration for tick count `k`: `c_{⌊k/4⌋}`. -/
def cfg (c0 : Q × List Bool) (k : ℕ) : Q × List Bool := C.runT c0 (k / 4)

/-- Previous configuration `c_{⌊k/4⌋ - 1}` (used for the window `𝒦_4 → 𝒦_1`). -/
def prv (c0 : Q × List Bool) (k : ℕ) : Q × List Bool := C.runT c0 (k / 4 - 1)

/-- Uniform start bound, window `1 → 2`. -/
noncomputable def Θ12 (n : ℕ) : ℝ :=
  1 / (9 * 3 ^ n : ℕ) + aut (9 * 3 ^ n) 1 + hrm (7 * (9 * 3 ^ n)) / (9 * 3 ^ n : ℕ)

/-- Uniform start bound, window `2 → 3`. -/
noncomputable def Θ23 (n : ℕ) : ℝ :=
  1 / (9 * 3 ^ n : ℕ) + aut (9 * 3 ^ n) 1 + hrm (20 * 3 ^ n) / (2 * 3 ^ n : ℕ)

/-- Uniform start bound, window `3 → 4`. -/
noncomputable def Θ34 (n : ℕ) : ℝ :=
  1 / (9 * 3 ^ n : ℕ) + 1 / (2 * 3 ^ n : ℕ) + aut (9 * 3 ^ n) 1 +
    4 / (9 * 3 ^ n : ℕ) * Real.log (1 + (13 * (9 * 3 ^ n) : ℕ)) +
    4 / (9 * 3 ^ n : ℕ) * Real.log (1 + (6 * (9 * 3 ^ n) : ℕ))

/-- Uniform start bound, window `4 → 1`. -/
noncomputable def Θ41 (n : ℕ) : ℝ := 1 / (9 * 3 ^ n : ℕ) + aut (9 * 3 ^ n) 1

/-- Total start bound of one CTM step. -/
noncomputable def Θsum (n : ℕ) : ℝ := Θ12 n + Θ23 n + Θ34 n + Θ41 n

theorem Θ12_nonneg (n : ℕ) : 0 ≤ Θ12 n := by
  unfold Θ12
  have := aut_nonneg (9 * 3 ^ n) 1
  have := hrm_nonneg (7 * (9 * 3 ^ n))
  positivity

theorem Θ23_nonneg (n : ℕ) : 0 ≤ Θ23 n := by
  unfold Θ23
  have := aut_nonneg (9 * 3 ^ n) 1
  have := hrm_nonneg (20 * 3 ^ n)
  positivity

theorem Θ34_nonneg (n : ℕ) : 0 ≤ Θ34 n := by
  unfold Θ34
  have := aut_nonneg (9 * 3 ^ n) 1
  have h1 : 0 ≤ Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (13 * (9 * 3 ^ n)); linarith)
  have h2 : 0 ≤ Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ)) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (6 * (9 * 3 ^ n)); linarith)
  positivity

theorem Θ41_nonneg (n : ℕ) : 0 ≤ Θ41 n := by
  unfold Θ41
  have := aut_nonneg (9 * 3 ^ n) 1
  positivity

theorem cfg_succ {c0 : Q × List Bool} {k : ℕ} (h : k % 4 ≠ 3) : cfg C c0 (k + 1) = cfg C c0 k := by
  unfold cfg; congr 1; omega

theorem cfg_succ_three {c0 : Q × List Bool} {k : ℕ} (h : k % 4 = 3) :
    cfg C c0 (k + 1) = C.stepT (cfg C c0 k) := by
  unfold cfg; rw [show (k + 1) / 4 = k / 4 + 1 by omega]; rfl

theorem prv_succ_three {c0 : Q × List Bool} {k : ℕ} (h : k % 4 = 3) :
    prv C c0 (k + 1) = cfg C c0 k := by
  unfold prv cfg; congr 1; omega

theorem cfg_eq_stepT_prv {c0 : Q × List Bool} {k : ℕ} (hk : k ≠ 0) (h : k % 4 = 0) :
    cfg C c0 k = C.stepT (prv C c0 k) := by
  unfold cfg prv
  obtain ⟨j, hj⟩ : ∃ j, k / 4 = j + 1 := ⟨k / 4 - 1, by omega⟩
  rw [hj, Nat.add_sub_cancel]
  rfl

/-- Window sets. -/
def schW (n : ℕ) (c0 : Q × List Bool) (k : ℕ) (w : State (Sp Q L)) : Prop :=
  if k = 0 then K1 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2) w
  else if k % 4 = 1 then Win12 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2) w ∧
    (w .i = 1 ∨ 1 ≤ w (.s2 (cfg C c0 k).1))
  else if k % 4 = 2 then Win23 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2) w
  else if k % 4 = 3 then Win34 C (9 * 3 ^ n) (20 * 3 ^ n) (2 * 3 ^ n) (cfg C c0 k).1
    ((cfg C c0 k).2.headD false) (tval (cfg C c0 k).2) (tval (C.stepT (cfg C c0 k)).2) w
  else Win41 C (9 * 3 ^ n) (20 * 3 ^ n) (prv C c0 k).1 ((prv C c0 k).2.headD false)
    (tval (cfg C c0 k).2) w

/-- Target classes: `𝒦_{r+1}(c_j)` for `k = 4 j + r`, `r < 3`, and `𝒦_4(q_j, b_j; w_{j+1})`. -/
def schCl (n : ℕ) (c0 : Q × List Bool) (k : ℕ) (w : State (Sp Q L)) : Prop :=
  if k % 4 = 0 then K1 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2) w
  else if k % 4 = 1 then K2 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2) w
  else if k % 4 = 2 then K3 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2) w
  else K4 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 ((cfg C c0 k).2.headD false)
    (tval (C.stepT (cfg C c0 k)).2) w

/-- Potentials. -/
noncomputable def schV (n : ℕ) (c0 : Q × List Bool) (k : ℕ) : State (Sp Q L) → ℝ :=
  if k = 0 then fun _ => 0
  else if k % 4 = 1 then V12 (9 * 3 ^ n) (cfg C c0 k).1
  else if k % 4 = 2 then V23 (9 * 3 ^ n) (20 * 3 ^ n) (cfg C c0 k).1 (tval (cfg C c0 k).2)
  else if k % 4 = 3 then V34 (9 * 3 ^ n) (2 * 3 ^ n) (tval (C.stepT (cfg C c0 k)).2)
    (cfg C c0 k).1 ((cfg C c0 k).2.headD false)
  else V41 C (9 * 3 ^ n) (prv C c0 k).1 ((prv C c0 k).2.headD false)

/-- Start bounds. -/
noncomputable def schΘ (n k : ℕ) : ℝ :=
  if k % 4 = 1 then Θ12 n else if k % 4 = 2 then Θ23 n else if k % 4 = 3 then Θ34 n
  else Θ41 n

theorem schV_nonneg (n : ℕ) (c0 : Q × List Bool) (k : ℕ) (w : State (Sp Q L)) :
    0 ≤ schV C n c0 k w := by
  unfold schV
  split_ifs
  · exact le_refl _
  · exact V12_nonneg _ _ _
  · exact V23_nonneg _ _ _ _ _
  · exact V34_nonneg _ _ _ _ _ _
  · exact V41_nonneg C _ _ _ _

theorem schΘ_nonneg (n k : ℕ) : 0 ≤ schΘ n k := by
  unfold schΘ
  split_ifs
  · exact Θ12_nonneg n
  · exact Θ23_nonneg n
  · exact Θ34_nonneg n
  · exact Θ41_nonneg n

section facts

variable {n : ℕ} {c0 : Q × List Bool} (hc0 : c0.2.length = n + 3)
include hc0

theorem cfg_length (k : ℕ) : (cfg C c0 k).2.length = n + 3 :=
  runT_length C hc0 (by omega) (k / 4)

theorem prv_length (k : ℕ) : (prv C c0 k).2.length = n + 3 :=
  runT_length C hc0 (by omega) (k / 4 - 1)

theorem m_ge : 2 ≤ 9 * 3 ^ n := by have := Nat.one_le_pow n 3 (by norm_num); omega

theorem sch_fire (k : ℕ) (w : State (Sp Q L)) (hW : schW C n c0 k w) (i : Rx Q L)
    (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    schW C n c0 k ((rxn C i).fire w) ∧ schV C n c0 k ((rxn C i).fire w) ≤ schV C n c0 k w := by
  have hm := m_ge hc0
  obtain ⟨hx', -, -, hmx', -, -⟩ := tape_facts (cfg_length C hc0 k)
    (C.next (cfg C c0 k).1 ((cfg C c0 k).2.headD false)).2
  have hmx2 : 9 * 3 ^ n ≤ tval (C.stepT (cfg C c0 k)).2 := hmx'
  unfold schW schV at *
  by_cases hk0 : k = 0
  · simp only [if_pos hk0] at hW ⊢
    refine ⟨?_, le_refl _⟩
    rw [k1_iff_win12] at hW ⊢
    obtain ⟨h1, -, h3⟩ := win12_fire C hW.1 i hi hr
    obtain ⟨hi0, hs0⟩ := hW.2
    have hnot : ¬ (((rxn C i).fire w) .i = 1 ∨ 1 ≤ ((rxn C i).fire w) (.s2 (cfg C c0 k).1)) :=
      fun h => by have := h3.mpr h; omega
    have h1' := h1
    obtain ⟨-, -, hst, -⟩ := h1'
    exact ⟨h1, by omega, by omega⟩
  simp only [if_neg hk0] at hW ⊢
  by_cases h1 : k % 4 = 1
  · simp only [if_pos h1] at hW ⊢
    obtain ⟨h1', h2', h3'⟩ := win12_fire C hW.1 i hi hr
    exact ⟨⟨h1', h3'.mp hW.2⟩, h2'⟩
  simp only [if_neg h1] at hW ⊢
  by_cases h2 : k % 4 = 2
  · simp only [if_pos h2] at hW ⊢
    exact win23_fire C hW i hi hr
  simp only [if_neg h2] at hW ⊢
  by_cases h3 : k % 4 = 3
  · simp only [if_pos h3] at hW ⊢
    exact win34_fire C (by omega) (by omega) hx' hW i hi hr
  simp only [if_neg h3] at hW ⊢
  exact win41_fire C hW i hi hr

theorem sch_cl_iff (k : ℕ) (w : State (Sp Q L)) (hW : schW C n c0 k w) :
    schCl C n c0 k w ↔ schV C n c0 k w = 0 := by
  have hm := m_ge hc0
  obtain ⟨-, -, -, hmx', -, -⟩ := tape_facts (cfg_length C hc0 k)
    (C.next (cfg C c0 k).1 ((cfg C c0 k).2.headD false)).2
  have hmx2 : 9 * 3 ^ n ≤ tval (C.stepT (cfg C c0 k)).2 := hmx'
  unfold schW schV schCl at *
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.zero_mod, eq_self_iff_true, if_true] at hW ⊢
    first
    | exact ⟨fun _ => trivial, fun _ => hW⟩
    | exact ⟨fun _ => rfl, fun _ => hW⟩
    | exact hW
  simp only [if_neg hk0] at hW ⊢
  by_cases h1 : k % 4 = 1
  · simp only [if_pos h1, show ¬ k % 4 = 0 by omega, if_false] at hW ⊢
    exact k2_iff_V12 hm hW.1
  by_cases h2 : k % 4 = 2
  · simp only [if_pos h2, if_neg h1, show ¬ k % 4 = 0 by omega, if_false] at hW ⊢
    exact k3_iff_V23 hm hW
  by_cases h3 : k % 4 = 3
  · simp only [if_pos h3, if_neg h1, if_neg h2, show ¬ k % 4 = 0 by omega, if_false] at hW ⊢
    exact k4_iff_V34 C hm (by have := Nat.one_le_pow n 3 (by norm_num); omega) (by omega) hW
  have h0 : k % 4 = 0 := by omega
  simp only [if_pos h0, if_neg h1, if_neg h2, if_neg h3] at hW ⊢
  rw [cfg_eq_stepT_prv C hk0 h0] at hW ⊢
  exact k1_iff_V41 C hm hW

theorem sch_drift (k : ℕ) (w : State (Sp Q L)) (hW : schW C n c0 k w)
    (hK : ¬ schCl C n c0 k w) : drift C (schV C n c0 k) w ≤ -1 := by
  have hm := m_ge hc0
  obtain ⟨hx', -, -, hmx', -, -⟩ := tape_facts (cfg_length C hc0 k)
    (C.next (cfg C c0 k).1 ((cfg C c0 k).2.headD false)).2
  have hmx2 : 9 * 3 ^ n ≤ tval (C.stepT (cfg C c0 k)).2 := hmx'
  unfold schW schV schCl at *
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.zero_mod, eq_self_iff_true, if_true] at hW hK
    exact absurd hW hK
  simp only [if_neg hk0] at hW ⊢
  by_cases h1 : k % 4 = 1
  · simp only [if_pos h1, show ¬ k % 4 = 0 by omega, if_false] at hW hK ⊢
    exact win12_drift C hm hW.1 hK hW.2
  by_cases h2 : k % 4 = 2
  · simp only [if_pos h2, if_neg h1, show ¬ k % 4 = 0 by omega, if_false] at hW hK ⊢
    exact win23_drift C hm hW hK
  by_cases h3 : k % 4 = 3
  · simp only [if_pos h3, if_neg h1, if_neg h2, show ¬ k % 4 = 0 by omega, if_false] at hW hK ⊢
    exact win34_drift C hm (by have := Nat.one_le_pow n 3 (by norm_num); omega) (by omega) hx'
      hW hK
  have h0 : k % 4 = 0 := by omega
  simp only [if_pos h0, if_neg h1, if_neg h2, if_neg h3] at hW hK ⊢
  rw [cfg_eq_stepT_prv C hk0 h0] at hW hK
  exact win41_drift C hm hW hK

theorem sch_start (k : ℕ) (w : State (Sp Q L)) (hW : schW C n c0 k w)
    (hC : schCl C n c0 k w) :
    schW C n c0 (k + 1) (w + one .i) ∧ schV C n c0 (k + 1) (w + one .i) ≤ schΘ n (k + 1) := by
  have hm := m_ge hc0
  have hp1 : 1 ≤ 3 ^ n := Nat.one_le_pow n 3 (by norm_num)
  obtain ⟨hx', hb0, hb1, hmx', hx'lt, hxlt⟩ := tape_facts (cfg_length C hc0 k)
    (C.next (cfg C c0 k).1 ((cfg C c0 k).2.headD false)).2
  have hmr : (0 : ℝ) < (9 * 3 ^ n : ℕ) := by exact_mod_cast (show 0 < 9 * 3 ^ n by omega)
  unfold schW schV schCl schΘ at *
  simp only [show k + 1 ≠ 0 by omega, if_false]
  by_cases h0 : k % 4 = 0
  · -- `𝒦_1 → Win12`
    simp only [if_pos h0] at hC
    have e1 : (k + 1) % 4 = 1 := by omega
    rw [cfg_succ C (c0 := c0) (k := k) (show k % 4 ≠ 3 by omega)]
    simp only [e1, eq_self_iff_true, if_true]
    obtain ⟨hW1, hV1⟩ := win12_start hC
    have hi0 : w .i = 0 := hC.1 .i trivial (by simp)
    refine ⟨⟨hW1, Or.inl (by simp [hi0])⟩, hV1.trans ?_⟩
    unfold Θ12
    have hT : tval (cfg C c0 k).2 + 20 * 3 ^ n + 9 * 3 ^ n + 1 ≤ 7 * (9 * 3 ^ n) := by omega
    have := hrm_mono hT
    gcongr
  by_cases h1 : k % 4 = 1
  · -- `𝒦_2 → Win23`
    simp only [if_neg h0, if_pos h1] at hC
    have e2 : (k + 1) % 4 = 2 := by omega
    rw [cfg_succ C (c0 := c0) (k := k) (show k % 4 ≠ 3 by omega)]
    simp only [e2, eq_self_iff_true, if_true, show ¬ (2 = 1) by omega, if_false]
    obtain ⟨hW1, hV1⟩ := win23_start hC
    refine ⟨hW1, hV1.trans ?_⟩
    unfold Θ23
    have hgap : 2 * 3 ^ n ≤ gap (20 * 3 ^ n) (tval (cfg C c0 k).2) := by
      unfold gap
      cases hb : (cfg C c0 k).2.headD false
      · have := hb0 hb; split_ifs <;> omega
      · have := hb1 hb; split_ifs <;> omega
    have hc := cmp_le_hrm_div (show 1 ≤ gap (20 * 3 ^ n) (tval (cfg C c0 k).2) by omega)
      (20 * 3 ^ n)
    have hd : hrm (20 * 3 ^ n) / (gap (20 * 3 ^ n) (tval (cfg C c0 k).2) : ℝ) ≤
        hrm (20 * 3 ^ n) / ((2 * 3 ^ n : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (hrm_nonneg _) (by positivity) (by exact_mod_cast hgap)
    linarith
  by_cases h2 : k % 4 = 2
  · -- `𝒦_3 → Win34`
    simp only [if_neg h0, if_neg h1, if_pos h2] at hC
    have e3 : (k + 1) % 4 = 3 := by omega
    rw [cfg_succ C (c0 := c0) (k := k) (show k % 4 ≠ 3 by omega)]
    simp only [e3, eq_self_iff_true, if_true, show ¬ (3 = 1) by omega, show ¬ (3 = 2) by omega,
      if_false]
    obtain ⟨hW1, hV1⟩ := win34_start C (x' := tval (C.stepT (cfg C c0 k)).2)
      (show 1 ≤ 2 * 3 ^ n by omega) hb0 hb1 hC
    refine ⟨hW1, hV1.trans ?_⟩
    unfold Θ34
    have hl1 : Real.log (1 + ((9 * 3 ^ n + 1 + 2 * (20 * 3 ^ n) + 2 * tval (cfg C c0 k).2 : ℕ) : ℝ))
        ≤ Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      have : (9 * 3 ^ n + 1 + 2 * (20 * 3 ^ n) + 2 * tval (cfg C c0 k).2 : ℕ) ≤
          13 * (9 * 3 ^ n) := by omega
      have := (Nat.cast_le (α := ℝ)).mpr this
      linarith
    have hl2 : 0 ≤ Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ)) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (6 * (9 * 3 ^ n)); linarith)
    have hx'r : ((9 * 3 ^ n : ℕ) : ℝ) ≤ (tval (C.stepT (cfg C c0 k)).2 : ℝ) := by
      exact_mod_cast hmx'
    have h4 : 4 / (tval (C.stepT (cfg C c0 k)).2 : ℝ) ≤ 4 / ((9 * 3 ^ n : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hmr hx'r
    have h5 := mul_le_mul_of_nonneg_right h4 hl2
    have h6 := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 4 / ((9 * 3 ^ n : ℕ) : ℝ))
    push_cast at h5 h6 ⊢
    linarith
  · -- `𝒦_4 → Win41`
    have h3 : k % 4 = 3 := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2] at hC
    have e0 : (k + 1) % 4 = 0 := by omega
    simp only [e0, show ¬ (0 = 1) by omega, show ¬ (0 = 2) by omega,
      show ¬ (0 = 3) by omega, if_false]
    rw [prv_succ_three C h3, cfg_succ_three C h3]
    obtain ⟨hW1, hV1⟩ := win41_start C (by omega) hC
    exact ⟨hW1, by unfold Θ41; exact hV1⟩

end facts

/-- **The schedule of the CTM run from `c0`** (tapes of length `n + 3`). -/
noncomputable def ctmSched (n : ℕ) (c0 : Q × List Bool) (hc0 : c0.2.length = n + 3) :
    Sched C L where
  W := schW C n c0
  Cl := schCl C n c0
  V := schV C n c0
  Θ := schΘ n
  V_nonneg := schV_nonneg C n c0
  Θ_nonneg := schΘ_nonneg n
  fire := sch_fire C hc0
  cl_iff := sch_cl_iff C hc0
  drift := sch_drift C hc0
  start := sch_start C hc0

/-! ### Initial state -/

/-- Initial state: `𝒦_1(c0)` (`#S_{q,1} = m`, `#M = val w`, `#T = T0`, `#D = m`, `#B = 1`),
clock at the top, `#A = a f`, `#A* = f`. -/
def initState (n : ℕ) (c0 : Q × List Bool) (a f : ℕ) : State (Sp Q L) := fun s =>
  match s with
  | .s1 q => if q = c0.1 then 9 * 3 ^ n else 0
  | .mem .m => tval c0.2
  | .mem .t => 20 * 3 ^ n
  | .mem .d => 9 * 3 ^ n
  | .mem .b => 1
  | .clk c => if c = Fin.last L then 1 else 0
  | .acc => a * f
  | .accS => f
  | _ => 0

theorem initState_clockAt (n : ℕ) (c0 : Q × List Bool) (a f : ℕ) :
    ClockAt (a * f) f (Fin.last L) (initState (Q := Q) (L := L) n c0 a f) :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem initState_K1 (n : ℕ) (c0 : Q × List Bool) (a f : ℕ) :
    K1 (9 * 3 ^ n) (20 * 3 ^ n) c0.1 (tval c0.2) (rest (initState (L := L) n c0 a f)) := by
  refine ⟨fun s hs hn => ?_, ?_, ?_⟩
  · cases s <;> simp_all [rest, initState, Sp.IsState, Sp.IsClock]
  · simp [rest, initState, Sp.IsClock]
  · simp [MemA, memv, rest, initState, Sp.IsClock]

/-! ### Error and time for the CTM schedule -/

theorem sum_schΘ_le (n t : ℕ) :
    ∑ j ∈ Finset.Ioo 0 (4 * t), schΘ n j ≤ t * Θsum n := by
  have hsub : Finset.Ioo 0 (4 * t) ⊆ Finset.range (4 * t) := by
    intro j hj; simp only [Finset.mem_Ioo] at hj; simp only [Finset.mem_range]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => schΘ_nonneg n j).trans
    (le_of_eq ?_)
  clear hsub
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 4 * (t + 1) = 4 * t + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp [schΘ, Θsum,
      show (4 * t) % 4 = 0 by omega, show (4 * t + 1) % 4 = 1 by omega,
      show (4 * t + 1 + 1) % 4 = 2 by omega, show (4 * t + 1 + 1 + 1) % 4 = 3 by omega] <;>
      ring

/-- **CTM-level error and time bounds** for clock parameters `a ≥ 2`, `f ≥ 1`. -/
theorem ctm_error_time (hL : 1 ≤ L) {n : ℕ} {c0 : Q × List Bool} (hc0 : c0.2.length = n + 3)
    (t : ℕ) {a f : ℕ} (ha : 2 ≤ a) (hf : 1 ≤ f) :
    rawLaw (net C L) (net_hasPositiveRates C L) (initState n c0 a f)
        {ω | ¬ SimOK (ctmSched C n c0 hc0) (4 * t) (initState n c0 a f) ω} ≤
      ENNReal.ofReal ((f : ℝ) / gs a L * (t * Θsum n)) ∧
    expTime C (initState (L := L) n c0 a f) (4 * t) ≤
      ENNReal.ofReal (2 * (4 * t : ℕ) * gs a L / f) := by
  refine ⟨(sched_error_le (ctmSched C n c0 hc0) (4 * t) (by omega) hf hL
    (initState_clockAt n c0 a f) ?_ ?_).trans ?_, expTime_le (4 * t) ha hf hL
      (initState_clockAt n c0 a f)⟩
  · show schW C n c0 0 _
    unfold schW
    rw [if_pos rfl]
    exact initState_K1 n c0 a f
  · show schCl C n c0 0 _
    unfold schCl
    rw [if_pos rfl]
    exact initState_K1 n c0 a f
  · apply ENNReal.ofReal_le_ofReal
    have hG : (0 : ℝ) < gs a L := by linarith [one_le_gs (Nat.cast_nonneg (α := ℝ) a) L]
    exact mul_le_mul_of_nonneg_left (sum_schΘ_le n t) (by positivity)

end Ripple.sCRNUniversality.ClockedCTM

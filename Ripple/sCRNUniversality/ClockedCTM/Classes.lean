/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Network
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Configuration classes and window invariants of `N♯`

`docs/audit/FIX3-SCWB-T32.md` §4.  All predicates here are about the non-clock species of a
state `w`; the clock species are handled separately.  `m = 3^{s-1}` is the number of state
molecules and `T0 = 2·3^{s-1} + 2·3^{s-3}` the threshold count.

* `MemA m T0 x`: the memory class `𝒜(x)` (`M + M* + M† = x`, `T + T* + T† = T0`, `M* = T*`,
  `D + D* = m`, `B + B* = 1`, `K_1 = K_2 = 0`); `MemReset`: `M† = T† = D* = B* = 0`;
* `K1 … K4`: the classes `𝒦_1(q, w)`, `𝒦_2(q, w)`, `𝒦_3(q, w)`, `𝒦_4(q, b; w')`;
* `OnlyState l w`: every state species (`S`, `R`, `U`, `I`) outside `l` has count `0`.

Also the real functions used by the potentials: `aut m j = Σ_{j ≤ k < m} 1/(k(m-k))` (expected
remaining time of the autocatalysis `X + Z → 2Z`, Lemma 1.3(c)) and `hrm n = Σ_{k ≤ n} 1/k`.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} {L : ℕ}

/-- State species `S`, `R`, `U`, `I`. -/
def Sp.IsState : Sp Q L → Prop
  | .s1 _ | .s2 _ | .s3 _ | .rq _ | .u _ _ | .i => True
  | _ => False

/-- Clock species. -/
def Sp.IsClock : Sp Q L → Prop
  | .clk _ | .acc | .accS => True
  | _ => False

/-- Clock labels: tick and clock walk. -/
def Rx.IsClock : Rx Q L → Prop
  | .tick | .up _ | .down _ => True
  | _ => False

instance (s : Sp Q L) : Decidable s.IsClock := by
  cases s <;> simp only [Sp.IsClock] <;> infer_instance

instance (i : Rx Q L) : Decidable i.IsClock := by
  cases i <;> simp only [Rx.IsClock] <;> infer_instance

/-- All state species outside `l` vanish. -/
def OnlyState (l : List (Sp Q L)) (w : State (Sp Q L)) : Prop :=
  ∀ s : Sp Q L, s.IsState → s ∉ l → w s = 0

/-- The memory counts of `w`. -/
def memv (w : State (Sp Q L)) : Mem → ℕ := fun y => w (.mem y)

@[simp] theorem memv_apply (w : State (Sp Q L)) (y : Mem) : memv w y = w (.mem y) := rfl

/-- The memory class `𝒜(x)`. -/
def MemA (m T0 x : ℕ) (v : Mem → ℕ) : Prop :=
  v .m + v .ms + v .md = x ∧ v .t + v .ts + v .td = T0 ∧ v .ms = v .ts ∧ v .d + v .ds = m ∧
    v .b + v .bs = 1 ∧ v .k1 = 0 ∧ v .k2 = 0

/-- Restored memory: `M† = T† = D* = B* = 0`. -/
def MemReset (v : Mem → ℕ) : Prop := v .md = 0 ∧ v .td = 0 ∧ v .ds = 0 ∧ v .bs = 0

/-- Memory of `𝒦_4(·, ·; w')` with `x' = val w'`. -/
def Mem4 (m T0 x' : ℕ) (v : Mem → ℕ) : Prop :=
  v .md = x' ∧ v .td = T0 ∧ v .ds = m ∧ v .bs = 1 ∧ v .m = 0 ∧ v .ms = 0 ∧ v .t = 0 ∧
    v .ts = 0 ∧ v .d = 0 ∧ v .b = 0 ∧ v .k1 = 0 ∧ v .k2 = 0

/-- `𝒦_1(q, w)` with `x = val w`. -/
def K1 (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.s1 q] w ∧ w (.s1 q) = m ∧ MemA m T0 x (memv w)

/-- `𝒦_2(q, w)`. -/
def K2 (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.s2 q] w ∧ w (.s2 q) = m ∧ MemA m T0 x (memv w) ∧ MemReset (memv w)

/-- `𝒦_3(q, w)`. -/
def K3 (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.s3 q] w ∧ w (.s3 q) = m ∧ MemA m T0 x (memv w) ∧ MemReset (memv w) ∧
    (w (.mem .t) = 0 ∨ w (.mem .m) = 0)

/-- `𝒦_4(q, b; w')` with `x' = val w'`. -/
def K4 (m T0 : ℕ) (q : Q) (b : Bool) (x' : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.u q b] w ∧ w (.u q b) = m ∧ Mem4 m T0 x' (memv w)

/-! ### Firing -/

variable [Fintype Q] [DecidableEq Q]

theorem OnlyState.fire {l : List (Sp Q L)} {w : State (Sp Q L)} (h : OnlyState l w)
    (C : CTM Q) (i : Rx Q L) (hout : ∀ s : Sp Q L, s.IsState → s ∉ l → out C i s = 0) :
    OnlyState l ((rxn C i).fire w) := by
  intro s hs hn
  rw [fire_apply, h s hs hn, hout s hs hn]
  simp

theorem OnlyState.zero {l : List (Sp Q L)} {w : State (Sp Q L)} (h : OnlyState l w)
    {s : Sp Q L} (hs : s.IsState) (hn : s ∉ l) : w s = 0 := h s hs hn

theorem rate_eq (C : CTM Q) (i : Rx Q L) (w : State (Sp Q L)) :
    rate C i w = w (src1 i) * w (src2 C i) := rfl

theorem rate_ne_zero_iff (C : CTM Q) (i : Rx Q L) (w : State (Sp Q L)) :
    rate C i w ≠ 0 ↔ w (src1 i) ≠ 0 ∧ w (src2 C i) ≠ 0 := by
  simp [rate_eq]

/-! ### Real functions for the potentials -/

/-- `aut m j = Σ_{j ≤ k < m} 1/(k (m - k))`. -/
noncomputable def aut (m j : ℕ) : ℝ := ∑ k ∈ Finset.Ico j m, 1 / ((k : ℝ) * ((m : ℝ) - k))

theorem aut_eq_add {m j : ℕ} (h : j < m) :
    aut m j = 1 / ((j : ℝ) * ((m : ℝ) - j)) + aut m (j + 1) := by
  unfold aut
  rw [Finset.sum_eq_sum_Ico_succ_bot h]

theorem aut_self (m : ℕ) : aut m m = 0 := by simp [aut]

theorem aut_nonneg (m j : ℕ) : 0 ≤ aut m j := by
  unfold aut
  refine Finset.sum_nonneg fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have : (k : ℝ) < m := by exact_mod_cast hk.2
  positivity

/-- Autocatalysis drift: `j (m - j) (aut m (j+1) - aut m j) = -1` for `1 ≤ j < m`. -/
theorem aut_drift {m j : ℕ} (hj : 1 ≤ j) (h : j < m) :
    ((j * (m - j) : ℕ) : ℝ) * (aut m (j + 1) - aut m j) = -1 := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm : (j : ℝ) < m := by exact_mod_cast h
  have hpos : (0 : ℝ) < (j : ℝ) * ((m : ℝ) - j) := mul_pos (by linarith) (by linarith)
  rw [aut_eq_add h, Nat.cast_mul, Nat.cast_sub h.le,
    show aut m (j + 1) - (1 / ((j : ℝ) * ((m : ℝ) - j)) + aut m (j + 1)) =
      -(1 / ((j : ℝ) * ((m : ℝ) - j))) by ring,
    mul_neg, mul_one_div_cancel hpos.ne']

/-- `hrm n = Σ_{k < n} 1/(k+1)`. -/
noncomputable def hrm (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

theorem hrm_succ (n : ℕ) : hrm (n + 1) = hrm n + 1 / ((n : ℝ) + 1) := by
  simp [hrm, Finset.sum_range_succ]

theorem hrm_nonneg (n : ℕ) : 0 ≤ hrm n :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem hrm_mono {a b : ℕ} (h : a ≤ b) : hrm a ≤ hrm b := by
  unfold hrm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    fun _ _ _ => by positivity

theorem one_le_hrm {n : ℕ} (h : 1 ≤ n) : 1 ≤ hrm n := by
  have h1 : hrm 1 = 1 := by simp [hrm]
  linarith [hrm_mono h]

theorem hrm_eq_zero_iff (n : ℕ) : hrm n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have := one_le_hrm (Nat.one_le_iff_ne_zero.mpr hn)
    linarith
  · rintro rfl; simp [hrm]

theorem aut_pos {m j : ℕ} (hj : 1 ≤ j) (h : j < m) : 0 < aut m j := by
  rw [aut_eq_add h]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm : (j : ℝ) < m := by exact_mod_cast h
  have : 0 < 1 / ((j : ℝ) * ((m : ℝ) - j)) := by
    have : (0 : ℝ) < (j : ℝ) * ((m : ℝ) - j) := mul_pos (by linarith) (by linarith)
    positivity
  linarith [aut_nonneg m (j + 1)]

theorem aut_anti {m j j' : ℕ} (h : j ≤ j') : aut m j' ≤ aut m j := by
  unfold aut
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left h) fun k hk _ => ?_
  rw [Finset.mem_Ico] at hk
  have : (k : ℝ) < m := by exact_mod_cast hk.2
  positivity

theorem aut_eq_zero_of {m j : ℕ} (h : m ≤ j) : aut m j = 0 := by
  simp [aut, Finset.Ico_eq_empty_of_le h]

/-! ### Non-clock drift -/

/-- The non-clock drift `Σ_i α_i(w) (V(w + ν_i) - V(w))` of a potential `V` (unit rate
constants). -/
noncomputable def drift (C : CTM Q) (V : State (Sp Q L) → ℝ) (w : State (Sp Q L)) : ℝ :=
  ∑ i : Rx Q L, if i.IsClock then 0 else (rate C i w : ℝ) * (V ((rxn C i).fire w) - V w)

/-- If no enabled non-clock reaction increases `V`, the drift is at most the sum of the terms
over any set of labels. -/
theorem drift_le_sum (C : CTM Q) (V : State (Sp Q L) → ℝ) (w : State (Sp Q L))
    (h : ∀ i : Rx Q L, ¬ i.IsClock → rate C i w ≠ 0 → V ((rxn C i).fire w) ≤ V w)
    (S : Finset (Rx Q L)) :
    drift C V w ≤ ∑ i ∈ S, (if i.IsClock then 0 else (rate C i w : ℝ) *
      (V ((rxn C i).fire w) - V w)) := by
  unfold drift
  rw [← Finset.sum_add_sum_compl S]
  have : ∑ i ∈ Sᶜ, (if i.IsClock then 0 else (rate C i w : ℝ) *
      (V ((rxn C i).fire w) - V w)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    split_ifs with hc
    · exact le_refl _
    · by_cases hr : rate C i w = 0
      · simp [hr]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith [h i hc hr])
  linarith

end Ripple.sCRNUniversality.ClockedCTM

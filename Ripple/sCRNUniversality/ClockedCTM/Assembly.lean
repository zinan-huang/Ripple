/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Clock

/-!
# Assembly: error and time bounds for a schedule of windows (FIX3-SCWB-T32 §7)

A *schedule* `S : Sched C L` lists, for every tick count `k`, a window set `S.W k`, a target
class `S.Cl k`, a potential `S.V k` and a start bound `S.Θ k`, with the four window properties
proved in `Window12`–`Window41`: closure, target iff potential zero, drift `≤ -1` off the target,
and the start bound after a tick from the previous target.

Along the jump chain `ω` (law `rawLaw (net C L) _ z0`), `traj C z0 n ω` is the state after `n`
jumps and `ticks n ω` the number of tick labels among them.

* `SimOK S N z0 ω`: whenever a tick label is drawn at jump `n + 1` and fewer than `N` ticks
  came before, the state just before it lies in the target class for that tick count.
* `sched_error_le`: `P(¬ SimOK) ≤ (f / G) Σ_{0 < j < N} Θ j` for the clock with `#A = a f`,
  `#A* = f`, `G = 1 + a + ⋯ + a^L`;
* `expTime C z0 N`: expected total holding time (unit rate constants) before the `N`-th tick;
  `expTime_le`: `≤ N · wclk a L L / f ≤ 2 N G / f` for `a ≥ 2`.

Both are proved by Lyapunov drift on an extended state (`lintegral_tsum_cost_le`); this replaces
the random-time-change, tagged-projection and strong-Markov arguments of the paper.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open MeasureTheory Preorder Stochastic Stochastic.MassAction
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-! ### Paths -/

/-- The CRN state after `n` jumps of the path `ω`. -/
noncomputable def traj (z0 : State (Sp Q L)) (n : ℕ) (ω : ℕ → Option (Rx Q L)) :
    State (Sp Q L) :=
  prefixToState (net C L) z0 n (frestrictLe n ω)

/-- The number of tick labels among the first `n` jumps. -/
def ticks : ℕ → (ℕ → Option (Rx Q L)) → ℕ
  | 0, _ => 0
  | n + 1, ω => ticks n ω + if ω (n + 1) = some .tick then 1 else 0

/-- A schedule of windows. -/
structure Sched (C : CTM Q) (L : ℕ) where
  /-- Window set after `k` ticks (for `k = 0`: the initial class). -/
  W : ℕ → State (Sp Q L) → Prop
  /-- Target class after `k` ticks. -/
  Cl : ℕ → State (Sp Q L) → Prop
  /-- Potential of window `k`. -/
  V : ℕ → State (Sp Q L) → ℝ
  /-- Start bound of window `k`. -/
  Θ : ℕ → ℝ
  V_nonneg : ∀ k w, 0 ≤ V k w
  Θ_nonneg : ∀ k, 0 ≤ Θ k
  fire : ∀ k w, W k w → ∀ i : Rx Q L, ¬ i.IsClock → rate C i w ≠ 0 →
    W k ((rxn C i).fire w) ∧ V k ((rxn C i).fire w) ≤ V k w
  cl_iff : ∀ k w, W k w → (Cl k w ↔ V k w = 0)
  drift : ∀ k w, W k w → ¬ Cl k w → drift C (V k) w ≤ -1
  start : ∀ k w, W k w → Cl k w →
    W (k + 1) (w + one .i) ∧ V (k + 1) (w + one .i) ≤ Θ (k + 1)

variable {C}

/-- **Correct simulation up to `N` ticks** along `ω`. -/
def SimOK (S : Sched C L) (N : ℕ) (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) : Prop :=
  ∀ n, ω (n + 1) = some .tick → ticks n ω < N → S.Cl (ticks n ω) (rest (traj C z0 n ω))

theorem Sched.cl_fire (S : Sched C L) {k : ℕ} {w : State (Sp Q L)} (hW : S.W k w)
    (hC : S.Cl k w) {i : Rx Q L} (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    S.Cl k ((rxn C i).fire w) := by
  obtain ⟨hW', hV⟩ := S.fire k w hW i hi hr
  rw [S.cl_iff k _ hW']
  have h0 := (S.cl_iff k w hW).1 hC
  exact le_antisymm (h0 ▸ hV) (S.V_nonneg _ _)

theorem Sched.drift_nonpos (S : Sched C L) {k : ℕ} {w : State (Sp Q L)} (hW : S.W k w) :
    ClockedCTM.drift C (S.V k) w ≤ 0 :=
  (drift_le_sum C _ w (fun i hi hr => (S.fire k w hW i hi hr).2) ∅).trans (by simp)

/-! ### Clock position -/

/-- Position of the clock molecule. -/
def pos (z : State (Sp Q L)) : ℕ := ∑ c : Fin (L + 1), c.val * z (.clk c)

theorem pos_of_clockAt {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)} (h : ClockAt r f c z) :
    pos z = c.val := by
  unfold pos
  simp only [h.2.2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ### One-step drift in real form -/

theorem btot_pos {z : State (Sp Q L)} (hT : ¬ (net C L).Terminal z) : 0 < btot C z := by
  by_contra h0
  apply hT
  intro i hi
  have h1 := (enabled_iff C i z).mp hi
  have h2 : rate C i z ≤ btot C z :=
    Finset.single_le_sum (f := fun i => rate C i z) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

theorem not_terminal_of_clockAt {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) {c : Fin (L + 1)}
    {z : State (Sp Q L)} (h : ClockAt r f c z) : ¬ (net C L).Terminal z := by
  by_cases hc : c.val = 0
  · refine not_terminal_of_rate C (i := .tick) ?_
    rw [rate_tick_of C h, if_pos hc]; omega
  · refine not_terminal_of_rate C (i := .down ⟨c.val - 1, by have := c.isLt; omega⟩) ?_
    rw [rate_down_of C h, if_pos (Fin.ext (by simp only [Fin.val_succ]; omega))]; omega

/-- **Drift in real form.**  If the next value of `Pn` after an enabled label `i` is at most
`ofReal (pn i)` and `c0 + Σ_i rate_i (pn_i - p) ≤ 0`, then the cost `c0 / B` plus the expected
next value is at most `ofReal p`. -/
theorem drift_real {z : State (Sp Q L)} (hT : ¬ (net C L).Terminal z) {cost : ℝ≥0∞}
    {Pn : Option (Rx Q L) → ℝ≥0∞} {p c0 : ℝ} {pn : Rx Q L → ℝ}
    (hcost : cost = ENNReal.ofReal c0 / (btot C z : ℝ≥0∞)) (hc0 : 0 ≤ c0)
    (hPn : ∀ i, rate C i z ≠ 0 → Pn (some i) ≤ ENNReal.ofReal (pn i)) (hpn : ∀ i, 0 ≤ pn i)
    (h : c0 + ∑ i, (rate C i z : ℝ) * (pn i - p) ≤ 0) :
    cost + ∑ o : Option (Rx Q L),
      massActionPMF (net C L) (net_hasPositiveRates C L) z o * Pn o ≤ ENNReal.ofReal p := by
  have hB := btot_pos hT
  have hBr : (0 : ℝ) < btot C z := by exact_mod_cast hB
  have h0 : massActionPMF (net C L) (net_hasPositiveRates C L) z (none : Option (Rx Q L)) = 0 :=
    pmf_none C hT
  have hs : ∀ i : Rx Q L, massActionPMF (net C L) (net_hasPositiveRates C L) z
      (some i : Option (Rx Q L)) = (rate C i z : ℝ≥0∞) / (btot C z : ℝ≥0∞) :=
    fun i => pmf_some C hT i
  rw [Fintype.sum_option, h0, zero_mul, zero_add]
  have hterm : ∀ i : Rx Q L,
      massActionPMF (net C L) (net_hasPositiveRates C L) z (some i : Option (Rx Q L)) *
        Pn (some i) ≤
        ENNReal.ofReal ((rate C i z : ℝ) * pn i / btot C z) := by
    intro i
    rw [hs i]
    by_cases hr : rate C i z = 0
    · simp [hr]
    · calc (rate C i z : ℝ≥0∞) / (btot C z : ℝ≥0∞) * Pn (some i)
          ≤ (rate C i z : ℝ≥0∞) / (btot C z : ℝ≥0∞) * ENNReal.ofReal (pn i) := by
            gcongr; exact hPn i hr
        _ = ENNReal.ofReal ((rate C i z : ℝ) * pn i / btot C z) := by
            rw [ENNReal.ofReal_div_of_pos hBr, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
            simp only [div_eq_mul_inv]
            ring
  have hnn : ∀ i : Rx Q L, 0 ≤ (rate C i z : ℝ) * pn i / btot C z :=
    fun i => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpn i)) hBr.le
  calc cost + ∑ i : Rx Q L,
        massActionPMF (net C L) (net_hasPositiveRates C L) z (some i : Option (Rx Q L)) *
          Pn (some i)
      ≤ ENNReal.ofReal (c0 / btot C z) +
          ∑ i : Rx Q L, ENNReal.ofReal ((rate C i z : ℝ) * pn i / btot C z) := by
        rw [hcost, ENNReal.ofReal_div_of_pos hBr, ENNReal.ofReal_natCast]
        gcongr with i
        exact hterm i
    _ = ENNReal.ofReal (c0 / btot C z + ∑ i : Rx Q L, (rate C i z : ℝ) * pn i / btot C z) := by
        rw [ENNReal.ofReal_add (div_nonneg hc0 hBr.le) (Finset.sum_nonneg fun i _ => hnn i),
          ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
    _ ≤ ENNReal.ofReal p := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.sum_div, ← add_div, div_le_iff₀ hBr]
        have hsum : ∑ i : Rx Q L, (rate C i z : ℝ) * pn i =
            ∑ i : Rx Q L, (rate C i z : ℝ) * (pn i - p) + (btot C z : ℝ) * p := by
          rw [btot, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsum]
        linarith

/-- Splitting a sum over labels into its non-clock and clock parts. -/
theorem sum_split (F : Rx Q L → ℝ) :
    ∑ i, F i = ∑ i, (if i.IsClock then 0 else F i) + ∑ i, (if i.IsClock then F i else 0) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- Values of a function on the clock labels. -/
def clockVal (vt : ℝ) (φ : ℕ → ℝ) : Rx Q L → ℝ
  | .tick => vt
  | .up c => φ (c.val + 1)
  | .down c => φ c.val
  | _ => 0

/-- Clock part of `Σ_i rate_i (pn_i - p)` when `pn` is `clockVal vt φ` on clock labels. -/
theorem clock_part {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)} (h : ClockAt r f c z)
    (vt p : ℝ) (φ : ℕ → ℝ) (g : Rx Q L → ℝ) :
    ∑ i : Rx Q L, (if i.IsClock then (rate C i z : ℝ) *
        ((if i.IsClock then clockVal vt φ i else g i) - p) else 0) =
      (if c.val = 0 then (f : ℝ) * (vt - p) else 0) +
        (if c.val < L then (r : ℝ) * (φ (c.val + 1) - p) else 0) +
        (if 0 < c.val then (f : ℝ) * (φ (c.val - 1) - p) else 0) := by
  have e : ∀ i : Rx Q L, (if i.IsClock then (rate C i z : ℝ) *
      ((if i.IsClock then clockVal vt φ i else g i) - p) else 0) =
      (if i.IsClock then (rate C i z : ℝ) * (clockVal vt φ i - p) else 0) := fun i => by
    split_ifs <;> rfl
  simp only [e]
  rw [clock_sum C h (fun i => clockVal vt φ i - p)]
  simp only [clockVal, dite_eq_ite]

/-! ### Error -/

open Classical in
/-- Update of the tick counter, `none` after a tick from outside the target class. -/
noncomputable def eupd (S : Sched C L) (N : ℕ) :
    Option ℕ → State (Sp Q L) → Option (Rx Q L) → Option ℕ
  | none, _, _ => none
  | some k, z, o =>
    if o = some .tick then (if k < N ∧ ¬ S.Cl k (rest z) then none else some (k + 1))
    else some k

/-- A tick from outside the target class, before `N` ticks. -/
def ErrB (S : Sched C L) (N : ℕ) (y : Option ℕ × State (Sp Q L)) (o : Option (Rx Q L)) :
    Prop :=
  ∃ k, y.1 = some k ∧ k < N ∧ o = some .tick ∧ ¬ S.Cl k (rest y.2)

open Classical in
/-- Error potential. -/
noncomputable def errP (S : Sched C L) (N a f : ℕ) : Option ℕ × State (Sp Q L) → ℝ≥0∞
  | (none, _) => 0
  | (some k, z) =>
    if N ≤ k then 0 else
      if (∃ c, ClockAt (a * f) f c z) ∧ S.W k (rest z) then
        ENNReal.ofReal ((f : ℝ) / gs a L * S.V k (rest z) +
          (if S.Cl k (rest z) then 0 else hclk a L (pos z) / gs a L) +
          (f : ℝ) / gs a L * ∑ j ∈ Finset.Ioo k N, S.Θ j)
      else ⊤

theorem sum_Ioo_succ (Θ : ℕ → ℝ) {k N : ℕ} (h : k + 1 < N) :
    ∑ j ∈ Finset.Ioo k N, Θ j = Θ (k + 1) + ∑ j ∈ Finset.Ioo (k + 1) N, Θ j := by
  have : Finset.Ioo k N = insert (k + 1) (Finset.Ioo (k + 1) N) := by
    ext j; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
  rw [this, Finset.sum_insert (by simp)]

open Classical in
theorem eupd_some (S : Sched C L) (N k : ℕ) (z : State (Sp Q L)) (o : Option (Rx Q L)) :
    eupd S N (some k) z o =
      if o = some .tick then (if k < N ∧ ¬ S.Cl k (rest z) then none else some (k + 1))
      else some k := rfl

open Classical in
/-- **Error drift.** -/
theorem errP_drift (S : Sched C L) (N : ℕ) {a f : ℕ} (ha : 1 ≤ a) (hf : 1 ≤ f) (hL : 1 ≤ L)
    (y : Option ℕ × State (Sp Q L)) :
    (∑ o : Option (Rx Q L), massActionPMF (net C L) (net_hasPositiveRates C L) y.2 o *
        (if ErrB S N y o then 1 else 0)) +
      ∑ o : Option (Rx Q L), massActionPMF (net C L) (net_hasPositiveRates C L) y.2 o *
        errP S N a f (eupd S N y.1 y.2 o, stateStep (net C L) y.2 o) ≤ errP S N a f y := by
  obtain ⟨x, z⟩ := y
  dsimp only
  rcases x with _ | k
  · simp [ErrB, eupd, errP]
  by_cases hk : N ≤ k
  · have h1 : ∀ o, ¬ ErrB S N (some k, z) o := by
      rintro o ⟨k', hk', hlt, -, -⟩
      simp only [Option.some.injEq] at hk'
      omega
    have h2 : ∀ o, errP S N a f (eupd S N (some k) z o, stateStep (net C L) z o) = 0 := by
      intro o
      rw [eupd_some]
      split_ifs <;> simp [errP, show N ≤ k + 1 by omega, hk]
    simp [h1, h2]
  have hkN : k < N := by omega
  by_cases hG : (∃ c, ClockAt (a * f) f c z) ∧ S.W k (rest z)
  swap
  · simp only [errP, if_neg hk, if_neg hG]; exact le_top
  obtain ⟨⟨c, hc⟩, hW⟩ := hG
  have haf : 1 ≤ a * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hT := not_terminal_of_clockAt (C := C) haf hf hc
  have hpos := pos_of_clockAt hc
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = gs (a : ℝ) L := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hGd]; linarith [one_le_gs (Nat.cast_nonneg (α := ℝ) a) L]
  have hGne : G ≠ 0 := hG0.ne'
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (f : ℝ) / G := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  obtain ⟨Sk, hSk⟩ : ∃ Sk : ℝ, Sk = ∑ j ∈ Finset.Ioo k N, S.Θ j := ⟨_, rfl⟩
  have hSk0 : 0 ≤ Sk := by rw [hSk]; exact Finset.sum_nonneg fun j _ => S.Θ_nonneg j
  obtain ⟨w, hw⟩ : ∃ w, w = rest z := ⟨_, rfl⟩
  rw [← hw] at hW
  have hV0 := S.V_nonneg k w
  have hh : ∀ n, 0 ≤ hclk a L n / G :=
    fun n => div_nonneg (hclk_nonneg (Nat.cast_nonneg a) _ _) hG0.le
  have hif : ∀ n, 0 ≤ (if S.Cl k w then (0 : ℝ) else hclk a L n / G) := fun n => by
    split_ifs
    · exact le_refl _
    · exact hh n
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ, φ = fun n =>
      lam * S.V k w + (if S.Cl k w then 0 else hclk a L n / G) + lam * Sk := ⟨_, rfl⟩
  have hφ0 : ∀ n, 0 ≤ φ n := fun n => by
    simp only [hφ]
    have := mul_nonneg hlam0 hV0
    have := mul_nonneg hlam0 hSk0
    linarith [hif n]
  have hP : errP S N a f (some k, z) = ENNReal.ofReal (φ c.val) := by
    simp only [errP, if_neg hk, hpos]
    rw [if_pos ⟨⟨c, hc⟩, hw ▸ hW⟩, hφ, hlam, hGd, hSk, hw]
  rw [hP, ← Finset.sum_add_distrib]
  simp only [← mul_add]
  obtain ⟨vt, hvt⟩ : ∃ vt : ℝ, vt = if S.Cl k w then lam * Sk else 1 := ⟨_, rfl⟩
  have hvt0 : 0 ≤ vt := by
    rw [hvt]
    split_ifs
    · exact mul_nonneg hlam0 hSk0
    · exact zero_le_one
  obtain ⟨gnc, hgnc⟩ : ∃ gnc : Rx Q L → ℝ, gnc = fun i =>
      lam * S.V k ((rxn C i).fire w) + (if S.Cl k w then 0 else hclk a L c.val / G) +
        lam * Sk := ⟨_, rfl⟩
  have hgnc0 : ∀ i, 0 ≤ gnc i := fun i => by
    simp only [hgnc]
    have := mul_nonneg hlam0 (S.V_nonneg k ((rxn C i).fire w))
    have := mul_nonneg hlam0 hSk0
    linarith [hif c.val]
  refine (le_of_eq (zero_add _).symm).trans (drift_real hT (cost := 0) (c0 := 0)
    (p := φ c.val)
    (Pn := fun o => (if ErrB S N (some k, z) o then 1 else 0) +
      errP S N a f (eupd S N (some k) z o, stateStep (net C L) z o))
    (pn := fun i => if i.IsClock then clockVal vt φ i else gnc i) (by simp) le_rfl ?_ ?_ ?_)
  · -- next values
    intro i hr
    beta_reduce
    rw [show stateStep (net C L) z (some i : Option (Rx Q L)) = (rxn C i).fire z from
      stateStep_of_rate C hr]
    by_cases hi : i.IsClock
    · rw [if_pos hi]
      cases i <;> simp only [Rx.IsClock] at hi
      · -- tick
        have hc0 : c.val = 0 := by
          by_contra hne
          rw [rate_tick_of C hc, if_neg hne] at hr
          exact hr rfl
        have hc' := ClockAt.tick (C := C) hf (show ClockAt (a * f) f 0 z by
          rwa [show (0 : Fin (L + 1)) = c from Fin.ext (by simp [hc0])])
        by_cases hCl : S.Cl k w
        · have hnE : ¬ ErrB S N (some k, z) (some .tick) := by
            rintro ⟨k', hk', -, -, hn⟩
            simp only [Option.some.injEq] at hk'
            subst hk'
            exact hn (hw ▸ hCl)
          rw [if_neg hnE, zero_add, eupd_some, if_pos rfl,
            if_neg (fun h => h.2 (hw ▸ hCl))]
          simp only [clockVal, hvt, if_pos hCl]
          by_cases hk1 : N ≤ k + 1
          · simp only [errP, if_pos hk1]; simp
          · have hrest : rest ((rxn C .tick).fire z) = w + one .i := by
              rw [rest_fire_tick, hw]
            obtain ⟨hW1, hV1⟩ := S.start k w hW hCl
            simp only [errP, if_neg hk1]
            rw [if_pos ⟨⟨_, hc'⟩, hrest ▸ hW1⟩, pos_of_clockAt hc', hrest]
            apply ENNReal.ofReal_le_ofReal
            have hS1 : Sk = S.Θ (k + 1) + ∑ j ∈ Finset.Ioo (k + 1) N, S.Θ j := by
              rw [hSk]; exact sum_Ioo_succ S.Θ (by omega)
            simp only [Fin.val_last, hclk_self, zero_div, ite_self, add_zero]
            rw [← hGd, ← hlam, hS1]
            nlinarith [mul_le_mul_of_nonneg_left hV1 hlam0]
        · have hE : ErrB S N (some k, z) (some .tick) := ⟨k, rfl, hkN, rfl, hw ▸ hCl⟩
          rw [if_pos hE, eupd_some, if_pos rfl, if_pos ⟨hkN, hw ▸ hCl⟩]
          simp only [clockVal, hvt, if_neg hCl, errP, add_zero, ENNReal.ofReal_one, le_refl]
      · -- up
        rename_i c'
        have hcc : c'.castSucc = c := by
          by_contra hne
          rw [rate_up_of C hc, if_neg hne] at hr
          exact hr rfl
        have hnE : ¬ ErrB S N (some k, z) (some (.up c')) := by
          rintro ⟨k', -, -, ho, -⟩
          simp at ho
        have hc' := ClockAt.up (C := C) haf (hcc ▸ hc)
        rw [if_neg hnE, zero_add, eupd_some,
          if_neg (show (some (Rx.up c') : Option (Rx Q L)) ≠ some .tick by simp)]
        simp only [errP, if_neg hk]
        rw [if_pos ⟨⟨_, hc'⟩, by rw [rest_fire_up, ← hw]; exact hW⟩, pos_of_clockAt hc',
          rest_fire_up, ← hw, ← hGd, ← hlam, ← hSk]
        simp only [clockVal, hφ, Fin.val_succ, le_refl]
      · -- down
        rename_i c'
        have hcc : c'.succ = c := by
          by_contra hne
          rw [rate_down_of C hc, if_neg hne] at hr
          exact hr rfl
        have hnE : ¬ ErrB S N (some k, z) (some (.down c')) := by
          rintro ⟨k', -, -, ho, -⟩
          simp at ho
        have hc' := ClockAt.down (C := C) hf (hcc ▸ hc)
        rw [if_neg hnE, zero_add, eupd_some,
          if_neg (show (some (Rx.down c') : Option (Rx Q L)) ≠ some .tick by simp)]
        simp only [errP, if_neg hk]
        rw [if_pos ⟨⟨_, hc'⟩, by rw [rest_fire_down, ← hw]; exact hW⟩, pos_of_clockAt hc',
          rest_fire_down, ← hw, ← hGd, ← hlam, ← hSk]
        simp only [clockVal, hφ, Fin.coe_castSucc, le_refl]
    · rw [if_neg hi]
      have hne : (some i : Option (Rx Q L)) ≠ some .tick := fun e => hi (by
        simp only [Option.some.injEq] at e; subst e; simp [Rx.IsClock])
      have hnE : ¬ ErrB S N (some k, z) (some i) := by
        rintro ⟨k', -, -, ho, -⟩
        exact hne ho
      have hr' : rate C i w ≠ 0 := by rw [hw, rate_rest C hi]; exact hr
      obtain ⟨hW', hV'⟩ := S.fire k w hW i hi hr'
      have hc' := hc.fire_nonclock (C := C) hi
      rw [if_neg hnE, zero_add, eupd_some, if_neg hne]
      simp only [errP, if_neg hk]
      rw [rest_fire C hi, ← hw, if_pos ⟨⟨_, hc'⟩, hW'⟩, pos_of_clockAt hc', ← hGd, ← hlam,
        ← hSk]
      apply ENNReal.ofReal_le_ofReal
      simp only [hgnc]
      have : (if S.Cl k ((rxn C i).fire w) then (0 : ℝ) else hclk a L c.val / G) ≤
          (if S.Cl k w then 0 else hclk a L c.val / G) := by
        by_cases hCl : S.Cl k w
        · rw [if_pos (S.cl_fire hW hCl hi hr'), if_pos hCl]
        · rw [if_neg hCl]
          split_ifs
          · exact hh _
          · exact le_refl _
      linarith
  · intro i
    beta_reduce
    split_ifs with hi
    · cases i <;> simp only [clockVal] <;> first | exact hvt0 | exact hφ0 _ | exact le_refl _
    · exact hgnc0 i
  · -- the real inequality
    beta_reduce
    rw [zero_add, sum_split]
    have hnc : ∑ i : Rx Q L, (if i.IsClock then 0 else (rate C i z : ℝ) *
        ((if i.IsClock then clockVal vt φ i else gnc i) - φ c.val)) =
          lam * drift C (S.V k) w := by
      unfold drift
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · simp
      · rw [hw, rate_rest C hi, ← hw]
        simp only [hgnc, hφ]
        ring
    rw [hnc, clock_part hc vt (φ c.val) φ gnc]
    have hgen := hclk_gen (a := (a : ℝ)) (f := (f : ℝ)) (Nat.cast_nonneg a) (Nat.cast_nonneg f)
      hL (show c.val ≤ L by have := c.isLt; omega)
    rw [← hGd] at hgen
    by_cases hCl : S.Cl k w
    · have hd := S.drift_nonpos hW
      have e1 : ∀ n, φ n - φ c.val = 0 := fun n => by simp only [hφ, if_pos hCl]; ring
      have hvt' : vt - φ c.val = -(lam * S.V k w) := by simp only [hvt, hφ, if_pos hCl]; ring
      rw [e1, e1, hvt']
      have h1 : 0 ≤ lam * S.V k w := mul_nonneg hlam0 hV0
      have h2 : lam * drift C (S.V k) w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 hd
      have h3 : 0 ≤ (f : ℝ) * (lam * S.V k w) := mul_nonneg (Nat.cast_nonneg f) h1
      split_ifs <;> first | omega | nlinarith
    · have hd := S.drift k w hW hCl
      have e1 : ∀ n, φ n - φ c.val = hclk a L n / G - hclk a L c.val / G := fun n => by
        simp only [hφ, if_neg hCl]; ring
      have hvt' : vt = 1 := by simp only [hvt, if_neg hCl]
      rw [e1, e1, hvt']
      have hpge : hclk a L c.val / G ≤ φ c.val := by
        simp only [hφ, if_neg hCl]
        nlinarith [mul_nonneg hlam0 hV0, mul_nonneg hlam0 hSk0]
      have hfp := mul_le_mul_of_nonneg_left hpge (Nat.cast_nonneg (α := ℝ) f)
      have hdl : lam * drift C (S.V k) w ≤ -lam := by
        nlinarith [mul_le_mul_of_nonneg_left hd hlam0]
      have hgen' : (if c.val < L then ((a * f : ℕ) : ℝ) * (hclk a L (c.val + 1) / G -
            hclk a L c.val / G) else 0) +
          (if 0 < c.val then (f : ℝ) * (hclk a L (c.val - 1) / G - hclk a L c.val / G)
            else 0) +
          (if c.val = 0 then (f : ℝ) * (0 - hclk a L c.val / G) else 0) ≤
            lam - (if c.val = 0 then (f : ℝ) else 0) := by
        have hdiv := div_le_div_of_nonneg_right hgen hG0.le
        have eq1 : ((if c.val < L then (a : ℝ) * f * (hclk a L (c.val + 1) -
              hclk a L c.val) else 0) +
            (if 0 < c.val then (f : ℝ) * (hclk a L (c.val - 1) - hclk a L c.val) else 0) +
            (if c.val = 0 then (f : ℝ) * (0 - hclk a L c.val) else 0)) / G =
            (if c.val < L then ((a * f : ℕ) : ℝ) * (hclk a L (c.val + 1) / G -
              hclk a L c.val / G) else 0) +
            (if 0 < c.val then (f : ℝ) * (hclk a L (c.val - 1) / G - hclk a L c.val / G)
              else 0) +
            (if c.val = 0 then (f : ℝ) * (0 - hclk a L c.val / G) else 0) := by
          push_cast
          split_ifs <;> field_simp <;> ring
        have eq2 : ((f : ℝ) - (if c.val = 0 then (f : ℝ) * G else 0)) / G =
            lam - (if c.val = 0 then (f : ℝ) else 0) := by
          rw [hlam]
          split_ifs <;> field_simp <;> ring
        rw [← eq1, ← eq2]
        exact hdiv
      split_ifs at hgen' ⊢ <;> first | omega | nlinarith

/-! ### Correct simulation -/

/-- The error flag along a path stays `some (ticks n ω)` while every tick so far was correct. -/
theorem eupd_ext (S : Sched C L) (N : ℕ) (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) :
    ∀ n, (∀ m < n, ω (m + 1) = some .tick → ticks m ω < N →
        S.Cl (ticks m ω) (rest (traj C z0 m ω))) →
      (extState (net C L) z0 (eupd S N) (some 0) n ω).1 = some (ticks n ω) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hok
    rw [extState_succ, ih (fun m hm => hok m (by omega))]
    have hsnd : (extState (net C L) z0 (eupd S N) (some 0) n ω).2 = traj C z0 n ω :=
      extState_snd _ _ _ _ _ _
    rw [hsnd]
    simp only [eupd, ticks]
    by_cases ht : ω (n + 1) = some .tick
    · rw [if_pos ht, if_pos ht, if_neg]
      intro ⟨hlt, hn⟩
      exact hn (hok n (by omega) ht hlt)
    · rw [if_neg ht, if_neg ht]
      simp

theorem not_simOK_subset (S : Sched C L) (N : ℕ) (z0 : State (Sp Q L)) :
    {ω : ℕ → Option (Rx Q L) | ¬ SimOK S N z0 ω} ⊆
      {ω | ∃ n, ErrB S N (extState (net C L) z0 (eupd S N) (some 0) n ω) (ω (n + 1))} := by
  intro ω hω
  by_contra hno
  apply hω
  have key : ∀ n, ∀ m < n, ω (m + 1) = some .tick → ticks m ω < N →
      S.Cl (ticks m ω) (rest (traj C z0 m ω)) := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
      · exact ih m hlt
      · intro ht hlt'
        by_contra hn
        have hsnd : (extState (net C L) z0 (eupd S N) (some 0) m ω).2 = traj C z0 m ω :=
          extState_snd _ _ _ _ _ _
        exact hno ⟨m, ticks m ω, eupd_ext S N z0 ω m ih, hlt', ht, by rw [hsnd]; exact hn⟩
  intro n
  exact key (n + 1) n (by omega)

/-- **Error bound for a schedule.** -/
theorem sched_error_le (S : Sched C L) (N : ℕ) {a f : ℕ} (ha : 1 ≤ a) (hf : 1 ≤ f)
    (hL : 1 ≤ L) {z0 : State (Sp Q L)} (hz0 : ClockAt (a * f) f (Fin.last L) z0)
    (hW0 : S.W 0 (rest z0)) (hC0 : S.Cl 0 (rest z0)) :
    rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | ¬ SimOK S N z0 ω} ≤
      ENNReal.ofReal ((f : ℝ) / gs a L * ∑ j ∈ Finset.Ioo 0 N, S.Θ j) := by
  classical
  refine (measure_mono (not_simOK_subset S N z0)).trans ?_
  refine (measure_exists_le_lintegral (net C L) (net_hasPositiveRates C L) z0 (eupd S N)
    (some 0) (ErrB S N)).trans ?_
  refine (lintegral_tsum_cost_le (net C L) (net_hasPositiveRates C L) z0 (eupd S N) (some 0)
    (errP S N a f) _ (fun y => errP_drift S N ha hf hL y)).trans ?_
  by_cases hN : N ≤ 0
  · simp [errP, hN]
  simp only [errP, if_neg hN]
  rw [if_pos ⟨⟨_, hz0⟩, hW0⟩, if_pos hC0, (S.cl_iff 0 _ hW0).1 hC0]
  apply ENNReal.ofReal_le_ofReal
  simp

/-! ### Time -/

/-- Tick counter for the time bound. -/
def tupd : ℕ → State (Sp Q L) → Option (Rx Q L) → ℕ :=
  fun k _ o => if o = some .tick then k + 1 else k

variable (C) in
/-- **Expected time before the `N`-th tick**: the expected total holding time, for unit rate
constants and unit volume (with rate constant `k` and volume `v` all times scale by `v / k`). -/
noncomputable def expTime (z0 : State (Sp Q L)) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' n, (if ticks n ω < N then
    (((net C L).totalPropensity (traj C z0 n ω) : ℝ≥0∞))⁻¹ else 0)
    ∂(rawLaw (net C L) (net_hasPositiveRates C L) z0)

open Classical in
/-- Time potential. -/
noncomputable def timeP (N a f : ℕ) : ℕ × State (Sp Q L) → ℝ≥0∞
  | (k, z) =>
    if N ≤ k then 0 else
      if ∃ c, ClockAt (a * f) f c z then
        ENNReal.ofReal ((((N - 1 - k : ℕ) : ℝ) * wclk a L L + wclk a L (pos z)) / f)
      else ⊤

/-- Time cost. -/
noncomputable def tcost (N : ℕ) (y : ℕ × State (Sp Q L)) : ℝ≥0∞ :=
  if y.1 < N then ((btot C y.2 : ℝ≥0∞))⁻¹ else 0

theorem timeP_drift (N : ℕ) {a f : ℕ} (ha : 1 ≤ a) (hf : 1 ≤ f) (hL : 1 ≤ L)
    (y : ℕ × State (Sp Q L)) :
    tcost (C := C) N y + ∑ o : Option (Rx Q L),
        massActionPMF (net C L) (net_hasPositiveRates C L) y.2 o *
          timeP N a f (tupd y.1 y.2 o, stateStep (net C L) y.2 o) ≤ timeP N a f y := by
  obtain ⟨k, z⟩ := y
  dsimp only
  by_cases hk : N ≤ k
  · have h2 : ∀ o, timeP (L := L) N a f (tupd k z o, stateStep (net C L) z o) = 0 := by
      intro o
      simp only [tupd]
      split_ifs <;> simp [timeP, show N ≤ k + 1 by omega, hk]
    simp [h2, tcost, show ¬ k < N by omega]
  by_cases hG : ∃ c, ClockAt (a * f) f c z
  swap
  · simp only [timeP, if_neg hk, if_neg hG]; exact le_top
  obtain ⟨c, hc⟩ := hG
  have haf : 1 ≤ a * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hT := not_terminal_of_clockAt (C := C) haf hf hc
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hf' : (f : ℝ) ≠ 0 := hf0.ne'
  have hpos := pos_of_clockAt hc
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨wL, hwL⟩ : ∃ wL : ℝ, wL = wclk (a : ℝ) L L := ⟨_, rfl⟩
  have hwL0 : 0 ≤ wL := by rw [hwL]; exact wclk_nonneg ha0 L L
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((N - 1 - k : ℕ) : ℝ) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact Nat.cast_nonneg _
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ, φ = fun n => (m * wL + wclk a L n) / f := ⟨_, rfl⟩
  have hP : timeP N a f (k, z) = ENNReal.ofReal (φ c.val) := by
    simp only [timeP, if_neg hk, hpos]
    rw [if_pos ⟨c, hc⟩, hφ, hm, hwL]
  rw [hP]
  have hφ0 : ∀ n, 0 ≤ φ n := fun n => by
    simp only [hφ]
    have := wclk_nonneg ha0 L n
    have := mul_nonneg hm0 hwL0
    exact div_nonneg (by linarith) (Nat.cast_nonneg f)
  obtain ⟨vt, hvt⟩ : ∃ vt : ℝ, vt = m * wL / f := ⟨_, rfl⟩
  have hvt0 : 0 ≤ vt := by rw [hvt]; exact div_nonneg (mul_nonneg hm0 hwL0) (Nat.cast_nonneg f)
  refine drift_real hT (c0 := 1) (p := φ c.val)
    (Pn := fun o => timeP N a f (tupd k z o, stateStep (net C L) z o))
    (pn := fun i => if i.IsClock then clockVal vt φ i else φ c.val) ?_ zero_le_one ?_ ?_ ?_
  · simp [tcost, show k < N by omega]
  · intro i hr
    beta_reduce
    rw [show stateStep (net C L) z (some i : Option (Rx Q L)) = (rxn C i).fire z from
      stateStep_of_rate C hr]
    by_cases hi : i.IsClock
    · rw [if_pos hi]
      cases i <;> simp only [Rx.IsClock] at hi
      · -- tick
        have hc0 : c.val = 0 := by
          by_contra hne
          rw [rate_tick_of C hc, if_neg hne] at hr
          exact hr rfl
        have hc' := ClockAt.tick (C := C) hf (show ClockAt (a * f) f 0 z by
          rwa [show (0 : Fin (L + 1)) = c from Fin.ext (by simp [hc0])])
        rw [show tupd k z (some Rx.tick) = k + 1 from if_pos rfl]
        simp only [clockVal]
        by_cases hk1 : N ≤ k + 1
        · simp only [timeP, if_pos hk1]; simp
        · simp only [timeP, if_neg hk1]
          rw [if_pos ⟨_, hc'⟩, pos_of_clockAt hc', Fin.val_last, ← hwL]
          apply le_of_eq
          congr 1
          have h1 : ((N - 1 - (k + 1) : ℕ) : ℝ) + 1 = m := by rw [hm]; norm_cast; omega
          rw [hvt, ← h1]
          ring
      · -- up
        rename_i c'
        have hcc : c'.castSucc = c := by
          by_contra hne
          rw [rate_up_of C hc, if_neg hne] at hr
          exact hr rfl
        have hc' := ClockAt.up (C := C) haf (hcc ▸ hc)
        rw [show tupd k z (some (Rx.up c')) = k from if_neg (by simp)]
        simp only [timeP, if_neg hk]
        rw [if_pos ⟨_, hc'⟩, pos_of_clockAt hc', ← hm, ← hwL]
        simp only [clockVal, hφ, Fin.val_succ, le_refl]
      · -- down
        rename_i c'
        have hcc : c'.succ = c := by
          by_contra hne
          rw [rate_down_of C hc, if_neg hne] at hr
          exact hr rfl
        have hc' := ClockAt.down (C := C) hf (hcc ▸ hc)
        rw [show tupd k z (some (Rx.down c')) = k from if_neg (by simp)]
        simp only [timeP, if_neg hk]
        rw [if_pos ⟨_, hc'⟩, pos_of_clockAt hc', ← hm, ← hwL]
        simp only [clockVal, hφ, Fin.coe_castSucc, le_refl]
    · rw [if_neg hi]
      have hc' := hc.fire_nonclock (C := C) hi
      have hne : (some i : Option (Rx Q L)) ≠ some .tick := fun e => hi (by
        simp only [Option.some.injEq] at e; subst e; simp [Rx.IsClock])
      rw [show tupd k z (some i) = k from if_neg hne]
      simp only [timeP, if_neg hk]
      rw [if_pos ⟨_, hc'⟩, pos_of_clockAt hc', ← hm, ← hwL]
      simp only [hφ, le_refl]
  · intro i
    beta_reduce
    split_ifs with hi
    · cases i <;> simp only [clockVal] <;> first | exact hvt0 | exact hφ0 _ | exact le_refl _
    · exact hφ0 _
  · beta_reduce
    rw [sum_split]
    have hnc : ∑ i : Rx Q L, (if i.IsClock then 0 else (rate C i z : ℝ) *
        ((if i.IsClock then clockVal vt φ i else φ c.val) - φ c.val)) = 0 :=
      Finset.sum_eq_zero fun i _ => by split_ifs <;> simp
    rw [hnc, clock_part hc vt (φ c.val) φ (fun _ => φ c.val)]
    have hgen := wclk_gen (a := (a : ℝ)) (f := (f : ℝ)) hL
      (show c.val ≤ L by have := c.isLt; omega)
    have e1 : ∀ n, φ n - φ c.val = (wclk a L n - wclk a L c.val) / f := fun n => by
      simp only [hφ]; ring
    have e2 : vt - φ c.val = -(wclk a L c.val / f) := by
      simp only [hvt, hφ]; ring
    have hcp : (if c.val = 0 then (f : ℝ) * (vt - φ c.val) else 0) +
        (if c.val < L then ((a * f : ℕ) : ℝ) * (φ (c.val + 1) - φ c.val) else 0) +
        (if 0 < c.val then (f : ℝ) * (φ (c.val - 1) - φ c.val) else 0) = -1 := by
      rw [e1, e1, e2]
      have h' : ((if c.val < L then (a : ℝ) * f * (wclk a L (c.val + 1) - wclk a L c.val)
          else 0) + (if 0 < c.val then (f : ℝ) * (wclk a L (c.val - 1) - wclk a L c.val)
          else 0) - (if c.val = 0 then (f : ℝ) * wclk a L c.val else 0)) / f = -1 := by
        rw [hgen, neg_div, div_self hf']
      rw [← h']
      push_cast
      split_ifs <;> field_simp <;> ring
    rw [hcp]
    norm_num

theorem tupd_ext (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    extState (net C L) z0 tupd 0 n ω = (ticks n ω, traj C z0 n ω) := by
  refine Prod.ext ?_ (extState_snd _ _ _ _ _ _)
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [extState_succ]
    dsimp only
    rw [ih]
    simp only [tupd, ticks]
    split_ifs <;> rfl

/-- **Time bound for the clock.** -/
theorem expTime_le (N : ℕ) {a f : ℕ} (ha : 2 ≤ a) (hf : 1 ≤ f) (hL : 1 ≤ L)
    {z0 : State (Sp Q L)} (hz0 : ClockAt (a * f) f (Fin.last L) z0) :
    expTime C z0 N ≤ ENNReal.ofReal (2 * N * gs a L / f) := by
  have hcast : ∀ m : ℕ, (((m : ℚ≥0)) : ℝ≥0∞) = (m : ℝ≥0∞) := fun m => by
    rw [← ENNReal.coe_nnratCast, NNRat.cast_natCast, ENNReal.coe_natCast]
  have e : expTime C z0 N = ∫⁻ ω, ∑' n, tcost (C := C) N
      (extState (net C L) z0 tupd 0 n ω) ∂(rawLaw (net C L) (net_hasPositiveRates C L) z0) := by
    unfold expTime
    congr 1
    funext ω
    congr 1
    funext n
    rw [tupd_ext, tcost, totalPropensity_eq, hcast]
  rw [e]
  refine (lintegral_tsum_cost_le (net C L) (net_hasPositiveRates C L) z0 tupd 0
    (timeP N a f) (tcost N) (fun y => timeP_drift N (by omega) hf hL y)).trans ?_
  by_cases hN : N ≤ 0
  · simp [timeP, hN]
  simp only [timeP, if_neg hN]
  rw [if_pos ⟨_, hz0⟩, pos_of_clockAt hz0]
  apply ENNReal.ofReal_le_ofReal
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have htop := wclk_top_le (a := (a : ℝ)) (by exact_mod_cast ha) L
  have hN1 : ((N - 1 - 0 : ℕ) : ℝ) + 1 = N := by norm_cast; omega
  rw [div_le_div_iff_of_pos_right hf0, Fin.val_last]
  have hw0 := wclk_nonneg (a := (a : ℝ)) (by positivity) L L
  nlinarith

end Ripple.sCRNUniversality.ClockedCTM

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Occupation-time analysis of the SCWB clock module

Soloveichik, Cook, Winfree, Bruck, "Computation with finite stochastic chemical reaction
networks" (Caltech etr085v2, 2007), Appendix A.1, clock module of Fig. 3.1B: clock positions
`0, …, l-1` (the paper's `C_1, …, C_l`), up rate `a = #A` (`C_c + A → C_{c+1} + A`), down rate
`1` (`#A* = 1`, `C_{c+1} + A* → C_c + A*`), a tick of rate `κ` possible only at position `0`,
and a clock-independent exit of rate `ρ`.  Rates are in units of `k/v`.

For one fixed "outer part" of the state, `w c` is the expected time spent with the clock at
`c` and `e c` the expected number of entries at `c`.  The occupation balance is
`B c · w c = e c + a · w (c-1) + w (c+1)` with `B c = ρ + κ [c = 0] + a [c+1 < l] + [0 < c]`
(`ClockBalance`).  This file proves, for real `w, e`:

* `ClockBalance.flux`: `w m − a w (m−1) = ρ S m + κ w 0 − E m` for `1 ≤ m ≤ l−1`, and the total
  identity `ρ S l + κ w 0 = E l` (`S`, `E` partial sums);
* `ClockBalance.inCone` (cone invariance): if the entry vector satisfies
  `a e (c) ≤ e (c+1)`, so does `w` (replaces the paper's Lemma A.1 and the "memoryless" step of
  Lemma A.4, which is stated there only for the clock started at the top);
* `ClockBalance.tick_le`: `w 0 · (1 + a + ⋯ + a^{l−1}) ≤ S l` and `ρ S l ≤ E l`, so the expected
  number of ticks `κ w 0` is at most `κ μ E l / ρ` with `μ = 1/(1 + ⋯ + a^{l−1})` (replaces
  Lemmas A.1–A.2);
* `ClockBalance.time_le_of_no_exit`: for `ρ = 0`, `κ = 1`, `a ≥ 2`,
  `S l ≤ 2 E l (1 + ⋯ + a^{l−1})` (replaces Lemma A.3).

Paper proofs: `docs/audit/FIX3-SCWB.md` §2.
-/

namespace Ripple.sCRNUniversality.Stochastic.ClockOccupation

open Finset

/-- Total unit-rate exit rate at clock position `c`. -/
def rate (l : ℕ) (a ρ κ : ℝ) (c : ℕ) : ℝ :=
  ρ + (if c = 0 then κ else 0) + (if c + 1 < l then a else 0) + (if 0 < c then 1 else 0)

/-- The occupation balance of the clock within one outer part: for every position `c < l`,
time-weighted outflow equals entries plus clock inflow from `c-1` (up, rate `a`) and from `c+1`
(down, rate `1`). -/
def ClockBalance (l : ℕ) (a ρ κ : ℝ) (w e : ℕ → ℝ) : Prop :=
  ∀ c, c < l → rate l a ρ κ c * w c =
    e c + (if 0 < c then a * w (c - 1) else 0) + (if c + 1 < l then w (c + 1) else 0)

/-- The cone `C_a`: consecutive ratios at least `a`. -/
def InCone (l : ℕ) (a : ℝ) (v : ℕ → ℝ) : Prop :=
  ∀ c, c + 1 < l → a * v c ≤ v (c + 1)

/-- Partial sum `Σ_{c' < m} v c'`. -/
def psum (v : ℕ → ℝ) (m : ℕ) : ℝ := ∑ c ∈ range m, v c

theorem psum_succ (v : ℕ → ℝ) (m : ℕ) : psum v (m + 1) = psum v m + v m := by
  simp [psum, sum_range_succ]

/-- The geometric weight `1 + a + ⋯ + a^{l-1} = 1/μ`. -/
def geomWeight (a : ℝ) (l : ℕ) : ℝ := ∑ c ∈ range l, a ^ c

variable {l : ℕ} {a ρ κ : ℝ} {w e : ℕ → ℝ}

namespace ClockBalance

/-- The flux quantity `u m = ρ S m + κ w 0 − E m`. -/
def u (ρ κ : ℝ) (w e : ℕ → ℝ) (m : ℕ) : ℝ := ρ * psum w m + κ * w 0 - psum e m

theorem u_zero : u ρ κ w e 0 = κ * w 0 := by simp [u, psum]

theorem u_succ_sub (m : ℕ) : u ρ κ w e (m + 1) - u ρ κ w e m = ρ * w m - e m := by
  simp only [u, psum_succ]; ring

/-- **Flux identity** (FIX3-SCWB Lemma 2.1): `w m − a w (m−1) = u m` for `1 ≤ m ≤ l−1`. -/
theorem flux (h : ClockBalance l a ρ κ w e) :
    ∀ m, 1 ≤ m → m + 1 ≤ l → w m - a * w (m - 1) = u ρ κ w e m := by
  intro m hm1 hml
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 := h 0 (by omega)
      have hl1 : 0 + 1 < l := by omega
      norm_num [rate, hl1, u, psum] at h0 ⊢
      linarith
    · have hn' := ih (by omega) (by omega)
      have hc := h n (by omega)
      simp only [rate, show n ≠ 0 by omega, if_false, show n + 1 < l by omega, if_true,
        show 0 < n by omega] at hc
      have hs := u_succ_sub (ρ := ρ) (κ := κ) (w := w) (e := e) n
      simp only [Nat.add_sub_cancel]
      nlinarith [hc, hn', hs]

/-- **Total identity**: `ρ S l + κ w 0 = E l`, i.e. `u l = 0` (needs `2 ≤ l`). -/
theorem total (h : ClockBalance l a ρ κ w e) (hl : 2 ≤ l) : u ρ κ w e l = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hf := flux h n (by omega) (by omega)
  have hc := h n (by omega)
  simp only [rate, show n ≠ 0 by omega, if_false, lt_irrefl, show 0 < n by omega,
    if_true] at hc
  have hs := u_succ_sub (ρ := ρ) (κ := κ) (w := w) (e := e) n
  linarith

/-- Identity (2.3) of FIX3-SCWB: `(ρ + a + 1) u m − a u (m−1) − u (m+1) = e m − a e (m−1)`
for `1 ≤ m ≤ l−1`. -/
theorem three_term (h : ClockBalance l a ρ κ w e) (m : ℕ) (hm1 : 1 ≤ m) (hml : m + 1 ≤ l) :
    (ρ + a + 1) * u ρ κ w e m - a * u ρ κ w e (m - 1) - u ρ κ w e (m + 1) =
      e m - a * e (m - 1) := by
  have hf := flux h m hm1 hml
  have h1 := u_succ_sub (ρ := ρ) (κ := κ) (w := w) (e := e) m
  have h2 := u_succ_sub (ρ := ρ) (κ := κ) (w := w) (e := e) (m - 1)
  rw [Nat.sub_add_cancel hm1] at h2
  linear_combination a * h2 - h1 - ρ * hf

/-- **Cone invariance** (FIX3-SCWB Lemma 2.2). -/
theorem inCone (h : ClockBalance l a ρ κ w e) (hl : 2 ≤ l) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hκ : 0 ≤ κ) (hw0 : 0 ≤ w 0) (he : InCone l a e) : InCone l a w := by
  -- it suffices that `u m ≥ 0` for `1 ≤ m ≤ l - 1`
  suffices hu : ∀ m, 1 ≤ m → m + 1 ≤ l → 0 ≤ u ρ κ w e m by
    intro c hc
    have := flux h (c + 1) (by omega) (by omega)
    have := hu (c + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at *
    linarith
  by_contra hneg
  push Not at hneg
  obtain ⟨m₀, hm₀1, hm₀l, hm₀neg⟩ := hneg
  -- minimum of `u` over `[1, l-1]`
  have hne : (Icc 1 (l - 1)).Nonempty := ⟨1, by simp; omega⟩
  obtain ⟨mmin, hmin_mem, hmin⟩ := (Icc 1 (l - 1)).exists_min_image (u ρ κ w e) hne
  set v := u ρ κ w e mmin with hv
  have hvneg : v < 0 := lt_of_le_of_lt (hmin m₀ (by simp; omega)) hm₀neg
  have hex : ∃ m, 1 ≤ m ∧ m + 1 ≤ l ∧ u ρ κ w e m = v :=
    ⟨mmin, by simp at hmin_mem; omega, by simp at hmin_mem; omega, rfl⟩
  classical
  set m := Nat.find hex with hm_def
  have hm1 : 1 ≤ m := (Nat.find_spec hex).1
  have hml : m + 1 ≤ l := (Nat.find_spec hex).2.1
  have hmv : u ρ κ w e m = v := (Nat.find_spec hex).2.2
  have hge : ∀ j, 1 ≤ j → j + 1 ≤ l → v ≤ u ρ κ w e j :=
    fun j hj1 hjl => hmin j (by simp; omega)
  -- left neighbour is strictly above the minimum
  have hleft : v < u ρ κ w e (m - 1) := by
    rcases Nat.eq_or_lt_of_le hm1 with heq | hlt
    · rw [← heq, Nat.sub_self, u_zero]
      have : 0 ≤ κ * w 0 := mul_nonneg hκ hw0
      linarith
    · have hle := hge (m - 1) (by omega) (by omega)
      have hne' : u ρ κ w e (m - 1) ≠ v := by
        intro hcontra
        have := Nat.find_min hex (show m - 1 < m by omega)
        exact this ⟨by omega, by omega, hcontra⟩
      exact lt_of_le_of_ne hle (Ne.symm hne')
  -- right neighbour is at least the minimum
  have hright : v ≤ u ρ κ w e (m + 1) := by
    rcases Nat.eq_or_lt_of_le hml with heq | hlt
    · rw [heq, total h hl]; linarith
    · exact hge (m + 1) (by omega) (by omega)
  have h3 := three_term h m hm1 hml
  have hem : 0 ≤ e m - a * e (m - 1) := by
    have := he (m - 1) (by omega)
    rw [Nat.sub_add_cancel hm1] at this
    linarith
  rw [hmv] at h3
  nlinarith [mul_lt_mul_of_pos_left hleft ha]

/-- In the cone, `w c ≥ a^c w 0`. -/
theorem pow_mul_le_of_inCone (hc : InCone l a w) (ha : 0 ≤ a) :
    ∀ c, c < l → a ^ c * w 0 ≤ w c := by
  intro c hcl
  induction c with
  | zero => simp
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := hc n (by omega)
    calc a ^ (n + 1) * w 0 = a * (a ^ n * w 0) := by ring
      _ ≤ a * w n := mul_le_mul_of_nonneg_left h1 ha
      _ ≤ w (n + 1) := h2

/-- **Tick bound** (FIX3-SCWB Lemma 2.3): in the cone, `w 0 · (1 + a + ⋯ + a^{l−1}) ≤ S l`, and
`ρ S l ≤ E l`. -/
theorem tick_le (h : ClockBalance l a ρ κ w e) (hl : 2 ≤ l) (hcone : InCone l a w)
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hw0 : 0 ≤ w 0) :
    w 0 * geomWeight a l ≤ psum w l ∧ ρ * psum w l ≤ psum e l := by
  constructor
  · unfold geomWeight psum
    rw [mul_sum]
    refine sum_le_sum fun c hc => ?_
    rw [mul_comm]
    exact pow_mul_le_of_inCone hcone ha c (mem_range.mp hc)
  · have ht := total h hl
    simp only [u] at ht
    nlinarith [mul_nonneg hκ hw0]

/-- **Time bound without clock-independent exit** (FIX3-SCWB Lemma 2.4): if `ρ = 0`, `κ = 1`,
`a ≥ 2` and entries are nonnegative, then `S l ≤ 2 E l (1 + a + ⋯ + a^{l−1})`. -/
theorem time_le_of_no_exit (h : ClockBalance l a 0 1 w e) (hl : 2 ≤ l) (ha : 2 ≤ a)
    (he0 : ∀ c, 0 ≤ e c) :
    psum w l ≤ 2 * psum e l * geomWeight a l := by
  have ht := total h hl
  simp only [u, zero_mul, zero_add, one_mul] at ht
  have hw0 : w 0 = psum e l := by linarith
  have hE0 : ∀ m, 0 ≤ psum e m := fun m => sum_nonneg fun c _ => he0 c
  have hw0nn : 0 ≤ w 0 := hw0 ▸ hE0 l
  -- `(a - 1) w c ≤ w 0 (a^{c+1} − 1)` for `c < l`
  have hbound : ∀ c, c < l → (a - 1) * w c ≤ w 0 * (a ^ (c + 1) - 1) := by
    intro c hcl
    induction c with
    | zero => ring_nf; exact le_refl _
    | succ n ih =>
      have ih' := ih (by omega)
      have hf := flux h (n + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel, u, zero_mul, zero_add, one_mul] at hf
      have hstep : w (n + 1) ≤ a * w n + w 0 := by linarith [hE0 (n + 1)]
      have ha1 : 0 ≤ a - 1 := by linarith
      calc (a - 1) * w (n + 1) ≤ (a - 1) * (a * w n + w 0) :=
            mul_le_mul_of_nonneg_left hstep ha1
        _ = a * ((a - 1) * w n) + (a - 1) * w 0 := by ring
        _ ≤ a * (w 0 * (a ^ (n + 1) - 1)) + (a - 1) * w 0 :=
            add_le_add (mul_le_mul_of_nonneg_left ih' (by linarith)) le_rfl
        _ = w 0 * (a ^ (n + 1 + 1) - 1) := by ring
  have hsum : (a - 1) * psum w l ≤ a * (w 0 * geomWeight a l) := by
    unfold psum geomWeight
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_le_sum fun c hc => ?_
    have := hbound c (mem_range.mp hc)
    rw [pow_succ] at this
    nlinarith [hw0nn]
  have hG : 0 ≤ w 0 * geomWeight a l :=
    mul_nonneg hw0nn (sum_nonneg fun c _ => pow_nonneg (by linarith) c)
  rw [← hw0]
  nlinarith

end ClockBalance

end Ripple.sCRNUniversality.Stochastic.ClockOccupation

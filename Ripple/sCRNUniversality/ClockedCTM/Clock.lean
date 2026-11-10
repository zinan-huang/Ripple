/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Window34

/-!
# The clock of `N♯` (FIX3-SCWB-T32 §2)

* `rest z`: the non-clock part of a state.  Non-clock reactions commute with `rest`
  (`rest_fire`), clock-walk reactions leave it unchanged (`rest_fire_walk`), and the tick adds
  one `I` (`rest_fire_tick`).
* `ClockAt r f c z`: the clock molecule is at position `c ∈ {0, …, L}` (`C_{c+1}`), `#A = r`,
  `#A* = f`.  Every reaction keeps this form (`ClockAt.fire_nonclock`, `.up`, `.down`, `.tick`).
* `clock_sum`: the clock part of a sum over all labels, weighted by the propensities.
* Clock potentials, with `gs a k = 1 + a + ⋯ + a^k` and `G = gs a L`:
  `hclk a L c = Σ_{c < c' ≤ L} gs a (L - c')` (error potential `g = hclk / G`) and
  `wclk a L c = G + Σ_{1 ≤ c' ≤ c} gs a (L - c')` (time potential `V = wclk / f`).
  `hclk_gen`: the clock generator (walk and tick to the top, with value `0` after the tick)
  applied to `hclk` is at most `f - [c = 0] f G`;  `wclk_gen`: applied to `wclk` with the tick
  killing, it equals `-f`.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-! ### The rest projection -/

/-- The non-clock part of a state. -/
def rest (z : State (Sp Q L)) : State (Sp Q L) := fun s => if s.IsClock then 0 else z s

theorem src1_not_clock {i : Rx Q L} (hi : ¬ i.IsClock) : ¬ (src1 i).IsClock := by
  cases i <;> simp_all [src1, Rx.IsClock, Sp.IsClock]

theorem src2_not_clock {i : Rx Q L} (hi : ¬ i.IsClock) : ¬ (src2 C i).IsClock := by
  cases i <;> simp_all [src2, Rx.IsClock, Sp.IsClock]

theorem out_clock {i : Rx Q L} (hi : ¬ i.IsClock) {s : Sp Q L} (hs : s.IsClock) :
    out C i s = 0 := by
  cases s <;> simp [Sp.IsClock] at hs <;> cases i <;> simp_all [out, Rx.IsClock]

theorem rate_rest {i : Rx Q L} (hi : ¬ i.IsClock) (z : State (Sp Q L)) :
    rate C i (rest z) = rate C i z := by
  simp [rate, rest, src1_not_clock hi, src2_not_clock C hi]

theorem fire_clock_eq {i : Rx Q L} (hi : ¬ i.IsClock) (z : State (Sp Q L)) {s : Sp Q L}
    (hs : s.IsClock) : (rxn C i).fire z s = z s := by
  have h1 : s ≠ src1 i := fun h => src1_not_clock hi (h ▸ hs)
  have h2 : s ≠ src2 C i := fun h => src2_not_clock C hi (h ▸ hs)
  simp [fire_apply, h1, h2, out_clock C hi hs]

theorem rest_fire {i : Rx Q L} (hi : ¬ i.IsClock) (z : State (Sp Q L)) :
    rest ((rxn C i).fire z) = (rxn C i).fire (rest z) := by
  funext s
  by_cases hs : s.IsClock
  · simp [rest, hs, fire_apply, out_clock C hi hs]
  · simp [rest, hs, fire_apply, src1_not_clock hi, src2_not_clock C hi]

theorem rest_fire_up (c : Fin L) (z : State (Sp Q L)) :
    rest ((rxn C (.up c)).fire z) = rest z := by
  funext s
  cases s <;> simp [rest, fire_apply, src1, src2, out, Sp.IsClock]

theorem rest_fire_down (c : Fin L) (z : State (Sp Q L)) :
    rest ((rxn C (.down c)).fire z) = rest z := by
  funext s
  cases s <;> simp [rest, fire_apply, src1, src2, out, Sp.IsClock]

theorem rest_fire_tick (z : State (Sp Q L)) :
    rest ((rxn C .tick).fire z) = rest z + one .i := by
  funext s
  cases s <;> simp [rest, fire_apply, src1, src2, out, Sp.IsClock]

/-! ### Clock position -/

/-- The clock molecule is at position `c`, `#A = r`, `#A* = f`. -/
def ClockAt (r f : ℕ) (c : Fin (L + 1)) (z : State (Sp Q L)) : Prop :=
  z .acc = r ∧ z .accS = f ∧ ∀ c' : Fin (L + 1), z (.clk c') = if c' = c then 1 else 0

variable {C}

theorem ClockAt.fire_nonclock {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)}
    (h : ClockAt r f c z) {i : Rx Q L} (hi : ¬ i.IsClock) :
    ClockAt r f c ((rxn C i).fire z) := by
  obtain ⟨ha, hf, hc⟩ := h
  refine ⟨?_, ?_, fun c' => ?_⟩
  · rw [fire_clock_eq C hi z (s := .acc) trivial, ha]
  · rw [fire_clock_eq C hi z (s := .accS) trivial, hf]
  · rw [fire_clock_eq C hi z (s := .clk c') trivial, hc]

theorem ClockAt.up {r f : ℕ} (hr : 1 ≤ r) {c : Fin L} {z : State (Sp Q L)}
    (h : ClockAt r f c.castSucc z) : ClockAt r f c.succ ((rxn C (.up c)).fire z) := by
  obtain ⟨ha, hf, hc⟩ := h
  refine ⟨?_, ?_, fun d => ?_⟩
  · simp [fire_apply, src1, src2, out, ha] <;> omega
  · simp [fire_apply, src1, src2, out, hf]
  · have hd := hc d
    simp only [fire_apply, src1, src2, out, Pi.add_apply, one_apply, Sp.clk.injEq,
      reduceCtorEq, ↓reduceIte, add_zero, hd]
    split_ifs <;> omega

theorem ClockAt.down {r f : ℕ} (hf1 : 1 ≤ f) {c : Fin L} {z : State (Sp Q L)}
    (h : ClockAt r f c.succ z) : ClockAt r f c.castSucc ((rxn C (.down c)).fire z) := by
  obtain ⟨ha, hf, hc⟩ := h
  refine ⟨?_, ?_, fun d => ?_⟩
  · simp [fire_apply, src1, src2, out, ha]
  · simp [fire_apply, src1, src2, out, hf] <;> omega
  · have hd := hc d
    simp only [fire_apply, src1, src2, out, Pi.add_apply, one_apply, Sp.clk.injEq,
      reduceCtorEq, ↓reduceIte, add_zero, hd]
    split_ifs <;> omega

theorem ClockAt.tick {r f : ℕ} (hf1 : 1 ≤ f) {z : State (Sp Q L)}
    (h : ClockAt r f 0 z) : ClockAt r f (Fin.last L) ((rxn C .tick).fire z) := by
  obtain ⟨ha, hf, hc⟩ := h
  refine ⟨?_, ?_, fun d => ?_⟩
  · simp [fire_apply, src1, src2, out, ha]
  · simp [fire_apply, src1, src2, out, hf] <;> omega
  · have hd := hc d
    simp only [fire_apply, src1, src2, out, Pi.add_apply, one_apply, Sp.clk.injEq,
      reduceCtorEq, ↓reduceIte, add_zero, zero_add, hd]
    split_ifs <;> omega

variable (C)

theorem rate_tick_of {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)} (h : ClockAt r f c z) :
    rate C .tick z = if c.val = 0 then f else 0 := by
  simp only [rate, src1, src2, h.2.1, h.2.2]
  by_cases hc : c.val = 0
  · have : (0 : Fin (L + 1)) = c := Fin.ext (by simp [hc])
    simp [this, hc]
  · have : (0 : Fin (L + 1)) ≠ c := fun e => hc (by rw [← e]; rfl)
    simp [this, hc]

theorem rate_up_of {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)} (h : ClockAt r f c z)
    (c' : Fin L) : rate C (.up c') z = if c'.castSucc = c then r else 0 := by
  simp only [rate, src1, src2, h.1, h.2.2]
  split_ifs <;> simp

theorem rate_down_of {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)} (h : ClockAt r f c z)
    (c' : Fin L) : rate C (.down c') z = if c'.succ = c then f else 0 := by
  simp only [rate, src1, src2, h.2.1, h.2.2]
  split_ifs <;> simp

/-! ### Sums over the clock labels -/

/-- The clock labels: tick, walk up, walk down. -/
def clockLabel : Unit ⊕ Fin L ⊕ Fin L → Rx Q L
  | .inl _ => .tick
  | .inr (.inl c) => .up c
  | .inr (.inr c) => .down c

theorem clockLabel_injective : Function.Injective (clockLabel (Q := Q) (L := L)) := by
  rintro (_ | c | c) (_ | d | d) h <;> simp_all [clockLabel]

theorem filter_clock :
    Finset.univ.filter (fun i : Rx Q L => i.IsClock) =
      Finset.univ.map ⟨clockLabel, clockLabel_injective⟩ := by
  ext i
  cases i <;> simp [Rx.IsClock, clockLabel, Sum.exists]

theorem sum_castSucc_ite {M : Type*} [AddCommMonoid M] (c : Fin (L + 1)) (A : Fin L → M) :
    ∑ c' : Fin L, (if c'.castSucc = c then A c' else 0) =
      if h : c.val < L then A ⟨c.val, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c.val, h⟩]
    · rw [if_pos (show (⟨c.val, h⟩ : Fin L).castSucc = c from Fin.ext rfl)]
    · intro b _ hb
      rw [if_neg]
      intro e
      subst e
      exact hb (Fin.ext rfl)
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun b _ => if_neg fun e => h ?_
    subst e; exact b.isLt

theorem sum_succ_ite {M : Type*} [AddCommMonoid M] (c : Fin (L + 1)) (A : Fin L → M) :
    ∑ c' : Fin L, (if c'.succ = c then A c' else 0) =
      if h : 0 < c.val then A ⟨c.val - 1, by have := c.isLt; omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c.val - 1, by have := c.isLt; omega⟩]
    · rw [if_pos (Fin.ext (by simp only [Fin.val_succ]; omega))]
    · intro b _ hb
      rw [if_neg]
      intro e
      subst e
      exact hb (Fin.ext (by simp))
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun b _ => if_neg fun e => h ?_
    subst e; simp

/-- **Clock part of a weighted sum over labels.** -/
theorem clock_sum {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)} (h : ClockAt r f c z)
    (F : Rx Q L → ℝ) :
    ∑ i : Rx Q L, (if i.IsClock then (rate C i z : ℝ) * F i else 0) =
      (if c.val = 0 then (f : ℝ) * F .tick else 0) +
        (if h : c.val < L then (r : ℝ) * F (.up ⟨c.val, h⟩) else 0) +
        (if h : 0 < c.val then
          (f : ℝ) * F (.down ⟨c.val - 1, by have := c.isLt; omega⟩) else 0) := by
  rw [← Finset.sum_filter, filter_clock, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, clockLabel]
  rw [rate_tick_of C h]
  simp only [rate_up_of C h, rate_down_of C h]
  have e1 : ∀ c' : Fin L, ((if c'.castSucc = c then r else 0 : ℕ) : ℝ) * F (.up c') =
      if c'.castSucc = c then (r : ℝ) * F (.up c') else 0 := fun c' => by split_ifs <;> simp
  have e2 : ∀ c' : Fin L, ((if c'.succ = c then f else 0 : ℕ) : ℝ) * F (.down c') =
      if c'.succ = c then (f : ℝ) * F (.down c') else 0 := fun c' => by split_ifs <;> simp
  simp only [e1, e2]
  rw [sum_castSucc_ite c (fun c' => (r : ℝ) * F (.up c')),
    sum_succ_ite c (fun c' => (f : ℝ) * F (.down c'))]
  split_ifs <;> (try simp only [Nat.cast_zero, zero_mul, add_zero, zero_add]) <;> ring

/-! ### Clock potentials -/

/-- `gs a k = 1 + a + ⋯ + a^k`. -/
noncomputable def gs (a : ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), a ^ i

theorem gs_zero (a : ℝ) : gs a 0 = 1 := by simp [gs]

theorem gs_succ (a : ℝ) (k : ℕ) : gs a (k + 1) = 1 + a * gs a k := by
  unfold gs
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  simp only [pow_zero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem one_le_gs {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 1 ≤ gs a k := by
  induction k with
  | zero => simp [gs_zero]
  | succ k ih => rw [gs_succ]; nlinarith

theorem gs_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ gs a k := by
  linarith [one_le_gs ha k]

/-- `G · g(c)`: the clock part of the error potential. -/
noncomputable def hclk (a : ℝ) (L c : ℕ) : ℝ := ∑ j ∈ Finset.Ico c L, gs a (L - 1 - j)

theorem hclk_succ (a : ℝ) {L c : ℕ} (h : c < L) :
    hclk a L c = gs a (L - 1 - c) + hclk a L (c + 1) := by
  unfold hclk
  rw [Finset.sum_eq_sum_Ico_succ_bot h]

theorem hclk_self (a : ℝ) (L : ℕ) : hclk a L L = 0 := by simp [hclk]

theorem hclk_nonneg {a : ℝ} (ha : 0 ≤ a) (L c : ℕ) : 0 ≤ hclk a L c :=
  Finset.sum_nonneg fun _ _ => gs_nonneg ha _

/-- `f · V(c)`: the time potential. -/
noncomputable def wclk (a : ℝ) (L c : ℕ) : ℝ := gs a L + ∑ j ∈ Finset.range c, gs a (L - 1 - j)

theorem wclk_succ (a : ℝ) (L c : ℕ) : wclk a L (c + 1) = wclk a L c + gs a (L - 1 - c) := by
  simp [wclk, Finset.sum_range_succ, add_assoc]

theorem wclk_nonneg {a : ℝ} (ha : 0 ≤ a) (L c : ℕ) : 0 ≤ wclk a L c :=
  add_nonneg (gs_nonneg ha _) (Finset.sum_nonneg fun _ _ => gs_nonneg ha _)

/-- **Clock generator on `hclk`** (walk up at rate `a f`, down at rate `f`, tick from `0` to
the top where `hclk = 0`). -/
theorem hclk_gen {a f : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f) {L c : ℕ} (hL : 1 ≤ L) (hc : c ≤ L) :
    (if c < L then a * f * (hclk a L (c + 1) - hclk a L c) else 0) +
      (if 0 < c then f * (hclk a L (c - 1) - hclk a L c) else 0) +
      (if c = 0 then f * (0 - hclk a L c) else 0) ≤ f - (if c = 0 then f * gs a L else 0) := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · have h0 := hclk_succ a (show 0 < L' + 1 by omega)
    have hg := gs_succ a L'
    have hn := hclk_nonneg ha (L' + 1) 1
    have hgn := gs_nonneg ha L'
    simp only [show L' + 1 - 1 - 0 = L' by omega, zero_add] at h0
    rw [if_pos (show 0 < L' + 1 by omega), if_neg (lt_irrefl 0), if_pos rfl, if_pos rfl, h0, hg]
    simp only [zero_add] at *
    nlinarith [mul_nonneg hf hn, mul_nonneg hf hgn]
  · rcases Nat.lt_or_ge c (L' + 1) with hlt | hge
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      have h1 := hclk_succ a hlt
      have h2 := hclk_succ a (show c' < L' + 1 by omega)
      have hg := gs_succ a (L' + 1 - 1 - (c' + 1))
      rw [show L' + 1 - 1 - (c' + 1) + 1 = L' + 1 - 1 - c' by omega] at hg
      rw [if_pos hlt, if_pos hc0, if_neg (show ¬ (c' + 1 = 0) by omega),
        if_neg (show ¬ (c' + 1 = 0) by omega), show c' + 1 - 1 = c' by omega, h2, h1, hg]
      linarith
    · have hcL : c = L' + 1 := le_antisymm hc hge
      subst hcL
      have h2 := hclk_succ a (show L' < L' + 1 by omega)
      rw [if_neg (lt_irrefl _), if_pos hc0, if_neg (show ¬ (L' + 1 = 0) by omega),
        if_neg (show ¬ (L' + 1 = 0) by omega), show L' + 1 - 1 = L' by omega, h2,
        show L' + 1 - 1 - L' = 0 by omega, gs_zero, hclk_self]
      linarith

/-- **Clock generator on `wclk`** (tick killing): exactly `-f`. -/
theorem wclk_gen {a f : ℝ} {L c : ℕ} (hL : 1 ≤ L) (hc : c ≤ L) :
    (if c < L then a * f * (wclk a L (c + 1) - wclk a L c) else 0) +
      (if 0 < c then f * (wclk a L (c - 1) - wclk a L c) else 0) -
      (if c = 0 then f * wclk a L c else 0) = -f := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · have hg := gs_succ a L'
    rw [if_pos (show 0 < L' + 1 by omega), if_neg (lt_irrefl 0), if_pos rfl, wclk_succ]
    simp only [show L' + 1 - 1 - 0 = L' by omega, wclk, Finset.range_zero, Finset.sum_empty,
      add_zero, hg]
    ring
  · rcases Nat.lt_or_ge c (L' + 1) with hlt | hge
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      have hg := gs_succ a (L' + 1 - 1 - (c' + 1))
      rw [show L' + 1 - 1 - (c' + 1) + 1 = L' + 1 - 1 - c' by omega] at hg
      rw [if_pos hlt, if_pos hc0, if_neg (show ¬ (c' + 1 = 0) by omega),
        show c' + 1 - 1 = c' by omega,
        wclk_succ a _ (c' + 1), wclk_succ a _ c', hg]
      ring
    · have hcL : c = L' + 1 := le_antisymm hc hge
      subst hcL
      rw [if_neg (lt_irrefl _), if_pos hc0, if_neg (show ¬ (L' + 1 = 0) by omega),
        show L' + 1 - 1 = L' by omega,
        wclk_succ a _ L', show L' + 1 - 1 - L' = 0 by omega, gs_zero]
      ring

/-- `Σ_{j < L} gs a (L - 1 - j) ≤ gs a L` for `a ≥ 2`, so `wclk a L L ≤ 2 G`. -/
theorem wclk_top_le {a : ℝ} (ha : 2 ≤ a) (L : ℕ) : wclk a L L ≤ 2 * gs a L := by
  have key : ∀ L : ℕ, ∑ j ∈ Finset.range L, gs a (L - 1 - j) ≤ gs a L - 1 := by
    intro L
    induction L with
    | zero => simp [gs_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ', show n + 1 - 1 - 0 = n by omega]
      have e : ∀ j ∈ Finset.range n, gs a (n + 1 - 1 - (j + 1)) = gs a (n - 1 - j) :=
        fun j _ => by congr 1; omega
      rw [Finset.sum_congr rfl e, gs_succ]
      have := one_le_gs (by linarith : (0 : ℝ) ≤ a) n
      nlinarith [mul_nonneg (sub_nonneg.2 ha) (gs_nonneg (by linarith : (0 : ℝ) ≤ a) n)]
  unfold wclk
  linarith [key L]

end Ripple.sCRNUniversality.ClockedCTM

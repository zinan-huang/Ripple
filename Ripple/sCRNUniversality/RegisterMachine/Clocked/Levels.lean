/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.RegisterMachine.Clocked.Occupation
import Ripple.sCRNUniversality.Stochastic.ClockOccupation

/-!
# Level structure of the occupation measure (FIX3-SCWB §3)

For the clocked network `net M L` started at `enc a σ₀` with the clock at the top position
(`σ₀.2 = Fin.last L`):

* `occ_split`: the occupation of `(k, (x, c))` is the entry mass `eE k (x, c)` (machine reactions
  from level `k - 1`, or the initial state) plus the clock inflow `clock_part`;
* `exit_le_one`, `eE_total_le_one`: the expected number of machine reactions fired from level `k`
  is at most one, so the total entry mass of every level is at most one;
* `Wt_ne_top`, `clockBalance`: for a live outer state `x`, the expected holding times
  `c ↦ Wt (k, (x, c))` are finite and satisfy the clock balance of `ClockOccupation`;
* `cone_eN`: entries lie in the cone `C_a` (induction on the level);
* `level_time_le`, `level_err_le`: the per-level bounds of Lemmas 2.3 and 2.4.
-/

namespace Ripple.sCRNUniversality.RegisterMachine.Clocked

open MeasureTheory ProbabilityTheory Preorder Stochastic Stochastic.MassAction
open Stochastic.ClockOccupation
open scoped ENNReal

variable {Reg Label : Type} [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label]
variable {L : ℕ} {M : RM Reg Label}

/-! ### Instructions, rates and sums over labels -/

omit [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label] in
theorem IncIdx.ext_q {p p' : IncIdx M} (h : p.1.1 = p'.1.1) : p = p' := by
  obtain ⟨⟨q, r, j⟩, hp⟩ := p
  obtain ⟨⟨q', r', j'⟩, hp'⟩ := p'
  simp only at h hp hp'
  subst h
  rw [hp] at hp'
  cases hp'
  rfl

omit [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label] in
theorem DecIdx.ext_q {d d' : DecIdx M} (h : d.1.1 = d'.1.1) : d = d' := by
  obtain ⟨⟨q, r, j, k⟩, hd⟩ := d
  obtain ⟨⟨q', r', j', k'⟩, hd'⟩ := d'
  simp only at h hd hd'
  subst h
  rw [hd] at hd'
  cases hd'
  rfl

theorem sum_idx {β : Type*} [AddCommMonoid β] (f : (net M L).I → β) :
    ∑ i, f i = (∑ p : IncIdx M, f (Sum.inl p)) + ((∑ d : DecIdx M, f (Sum.inr (Sum.inl d))) +
      ((∑ d : DecIdx M, f (Sum.inr (Sum.inr (Sum.inl d)))) +
        ((∑ j : Fin L, f (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) +
          ∑ j : Fin L, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))))) := by
  change ∑ i : Idx M L, f i = _
  simp only [Fintype.sum_sum_type]

theorem sum_idx' {β : Type*} [AddCommMonoid β] (f : Idx M L → β) :
    ∑ i, f i = (∑ p : IncIdx M, f (Sum.inl p)) + ((∑ d : DecIdx M, f (Sum.inr (Sum.inl d))) +
      ((∑ d : DecIdx M, f (Sum.inr (Sum.inr (Sum.inl d)))) +
        ((∑ j : Fin L, f (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) +
          ∑ j : Fin L, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))))) := by
  simp only [Fintype.sum_sum_type]

theorem sum_succ_eq {β : Type*} [AddCommMonoid β] (c : Fin (L + 1)) (f : ℕ → β) :
    (∑ j : Fin L, if c = j.succ then f j.val else 0) = if 0 < c.val then f (c.val - 1) else 0 := by
  have hcL := c.isLt
  split_ifs with hc
  · rw [Finset.sum_eq_single ⟨c.val - 1, by omega⟩]
    · rw [if_pos (Fin.ext (by simp only [Fin.val_succ]; omega))]
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      have := congrArg Fin.val h
      simp only [Fin.val_succ] at this
      exact Fin.ext (by simp only; omega)
    · simp
  · refine Finset.sum_eq_zero fun j _ => if_neg ?_
    intro h
    apply hc
    rw [h, Fin.val_succ]
    omega

theorem sum_castSucc_eq {β : Type*} [AddCommMonoid β] (c : Fin (L + 1)) (f : ℕ → β) :
    (∑ j : Fin L, if c = j.castSucc then f j.val else 0) =
      if c.val + 1 < L + 1 then f c.val else 0 := by
  have hcL := c.isLt
  split_ifs with hc
  · rw [Finset.sum_eq_single ⟨c.val, by omega⟩]
    · rw [if_pos (Fin.ext (by simp))]
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      exact Fin.ext (by simp only; omega)
    · simp
  · refine Finset.sum_eq_zero fun j _ => if_neg ?_
    intro h
    apply hc
    have := j.isLt
    rw [h, Fin.val_castSucc]
    omega

/-- Clock-independent machine rate `ρ(x)`: the `inc` and `dec1` propensities. -/
def rho (M : RM Reg Label) (x : Outer Reg Label) : ℕ :=
  (∑ p : IncIdx M, if p.1.1 = x.1 then 1 else 0) +
    ∑ d : DecIdx M, if d.1.1 = x.1 then x.2 d.1.2.1 else 0

/-- `κ(x)`: the `dec2` propensity at clock position `0`. -/
def kappa (M : RM Reg Label) (x : Outer Reg Label) : ℕ :=
  ∑ d : DecIdx M, if d.1.1 = x.1 then 1 else 0

/-- The machine has not halted at `x`. -/
def Live (M : RM Reg Label) (x : Outer Reg Label) : Prop := M.code x.1 ≠ .halt

theorem Btot_eq (a : ℕ) (x : Outer Reg Label) (c : Fin (L + 1)) :
    Btot M a (x, c) = rho M x + (if c = 0 then kappa M x else 0) +
      (if c.val + 1 < L + 1 then a else 0) + (if 0 < c.val then 1 else 0) := by
  have hup : (∑ j : Fin L, if j.castSucc = c then a else 0) =
      if c.val + 1 < L + 1 then a else 0 := by
    rw [← sum_castSucc_eq c (fun _ => a)]
    exact Finset.sum_congr rfl fun j _ => by simp only [eq_comm]
  have hdown : (∑ j : Fin L, if j.succ = c then 1 else 0) = if 0 < c.val then 1 else 0 := by
    rw [← sum_succ_eq c (fun _ => 1)]
    exact Finset.sum_congr rfl fun j _ => by simp only [eq_comm]
  have h2 : (∑ d : DecIdx M, if (0 : Fin (L + 1)) = c ∧ d.1.1 = x.1 then 1 else 0) =
      if c = 0 then kappa M x else 0 := by
    by_cases hc : c = 0
    · subst hc; simp [kappa]
    · rw [if_neg hc]
      exact Finset.sum_eq_zero fun d _ => if_neg fun h => hc h.1.symm
  unfold Btot rho
  rw [sum_idx']
  simp only [beta]
  rw [hup, hdown, h2]
  ring

theorem kappa_le_one (x : Outer Reg Label) : kappa M x ≤ 1 := by
  unfold kappa
  by_cases h : ∃ d : DecIdx M, d.1.1 = x.1
  · obtain ⟨d, hd⟩ := h
    rw [Finset.sum_eq_single d]
    · simp [hd]
    · intro d' _ hne; rw [if_neg]; intro h'; exact hne (DecIdx.ext_q (h'.trans hd.symm))
    · simp
  · push Not at h
    rw [Finset.sum_eq_zero fun d _ => if_neg (h d)]
    omega

theorem kappa_eq_one {x : Outer Reg Label} {r : Reg} {j k : Label}
    (h : M.code x.1 = .decJz r j k) : kappa M x = 1 := by
  unfold kappa
  obtain ⟨d, hd⟩ : ∃ d : DecIdx M, d.1.1 = x.1 := ⟨⟨(x.1, r, j, k), h⟩, rfl⟩
  rw [Finset.sum_eq_single d]
  · simp [hd]
  · intro d' _ hne; rw [if_neg]; intro h'; exact hne (DecIdx.ext_q (h'.trans hd.symm))
  · simp

theorem one_le_rho_of_inc {x : Outer Reg Label} {r : Reg} {j : Label}
    (h : M.code x.1 = .inc r j) : 1 ≤ rho M x := by
  unfold rho
  have : (if (⟨(x.1, r, j), h⟩ : IncIdx M).1.1 = x.1 then 1 else 0) ≤
      ∑ p : IncIdx M, if p.1.1 = x.1 then 1 else 0 :=
    Finset.single_le_sum (f := fun p : IncIdx M => if p.1.1 = x.1 then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [if_true] at this
  omega

theorem le_rho_of_dec (x : Outer Reg Label) (d : DecIdx M) (hd : d.1.1 = x.1) :
    x.2 d.1.2.1 ≤ rho M x := by
  unfold rho
  have : (if d.1.1 = x.1 then x.2 d.1.2.1 else 0) ≤
      ∑ d : DecIdx M, if d.1.1 = x.1 then x.2 d.1.2.1 else 0 :=
    Finset.single_le_sum (f := fun d : DecIdx M => if d.1.1 = x.1 then x.2 d.1.2.1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  rw [if_pos hd] at this
  omega

theorem kappa_eq_one_of_rho_eq_zero {x : Outer Reg Label} (hx : Live M x) (h : rho M x = 0) :
    kappa M x = 1 := by
  unfold Live at hx
  rcases hcode : M.code x.1 with ⟨r, j⟩ | ⟨r, j, k⟩ | _
  · have := one_le_rho_of_inc hcode; omega
  · exact kappa_eq_one hcode
  · exact absurd hcode hx

omit [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label] in
theorem live_of_inc (p : IncIdx M) (x : Outer Reg Label) (h : p.1.1 = x.1) : Live M x := by
  unfold Live; rw [← h, p.2]; simp

omit [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label] in
theorem live_of_dec (d : DecIdx M) (x : Outer Reg Label) (h : d.1.1 = x.1) : Live M x := by
  unfold Live; rw [← h, d.2]; simp

/-! ### Transition weights of single labels -/

variable (a : ℕ) (σ₀ : RState Reg Label L)

theorem trans_rm (k : ℕ) (σ : RState Reg Label L) (i : (net M L).I)
    (hi : rmOpt (M := M) (some i) = 1) (σ' : RState Reg Label L) :
    trans (M := M) a k σ (some i) (k + 1, σ') =
      if tgt M i σ = σ' then (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0 := by
  show (if (k + rmOpt (M := M) (some i), tgt M i σ) = (k + 1, σ') then
    (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0) = _
  rw [hi]
  by_cases h : tgt M i σ = σ'
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun he => h (congrArg Prod.snd he)), if_neg h]

theorem trans_rm_same (k : ℕ) (σ : RState Reg Label L) (i : (net M L).I)
    (hi : rmOpt (M := M) (some i) = 1) (σ' : RState Reg Label L) :
    trans (M := M) a k σ (some i) (k, σ') = 0 := by
  show (if (k + rmOpt (M := M) (some i), tgt M i σ) = (k, σ') then
    (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0) = _
  rw [hi, if_neg]
  intro he
  have := congrArg Prod.fst he
  simp at this

theorem trans_clock_succ (k : ℕ) (σ : RState Reg Label L) (i : (net M L).I)
    (hi : rmOpt (M := M) (some i) = 0) (σ' : RState Reg Label L) :
    trans (M := M) a k σ (some i) (k + 1, σ') = 0 := by
  show (if (k + rmOpt (M := M) (some i), tgt M i σ) = (k + 1, σ') then
    (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0) = _
  rw [hi, if_neg]
  intro he
  have := congrArg Prod.fst he
  simp at this

theorem trans_far (k k' : ℕ) (σ : RState Reg Label L) (o : Option (net M L).I)
    (σ' : RState Reg Label L) (h1 : k' ≠ k) (h2 : k' ≠ k + 1) :
    trans (M := M) a k σ o (k', σ') = 0 := by
  cases o with
  | none => rfl
  | some i =>
    show (if (k + rmOpt (M := M) (some i), tgt M i σ) = (k', σ') then
      (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0) = _
    rw [if_neg]
    intro he
    have h3 : k + rmOpt (M := M) (some i) = k' := congrArg Prod.fst he
    have := rmOpt_le_one (M := M) (L := L) (some i)
    omega

theorem trans_up (k : ℕ) (σ : RState Reg Label L) (j : Fin L) (ξ' : ℕ × RState Reg Label L) :
    trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) ξ' =
      if ξ' = (k, (σ.1, j.succ)) ∧ σ.2 = j.castSucc then
        (a : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0 := by
  show (if (k + rmOpt (M := M) (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))),
      (σ.1, j.succ)) = ξ' then
    ((if j.castSucc = σ.2 then a else 0 : ℕ) : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0) = _
  have hr : rmOpt (M := M) (L := L) (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) = 0 := rfl
  rw [hr, add_zero]
  by_cases h1 : (k, (σ.1, j.succ)) = ξ' <;> by_cases h2 : j.castSucc = σ.2
  · rw [if_pos h1, if_pos h2, if_pos ⟨h1.symm, h2.symm⟩]
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2.symm)]; simp
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]

theorem trans_down (k : ℕ) (σ : RState Reg Label L) (j : Fin L) (ξ' : ℕ × RState Reg Label L) :
    trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) ξ' =
      if ξ' = (k, (σ.1, j.castSucc)) ∧ σ.2 = j.succ then
        1 / (Btot M a σ : ℝ≥0∞) else 0 := by
  show (if (k + rmOpt (M := M) (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))),
      (σ.1, j.castSucc)) = ξ' then
    ((if j.succ = σ.2 then 1 else 0 : ℕ) : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0) = _
  have hr : rmOpt (M := M) (L := L) (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) = 0 := rfl
  rw [hr, add_zero]
  by_cases h1 : (k, (σ.1, j.castSucc)) = ξ' <;> by_cases h2 : j.succ = σ.2
  · rw [if_pos h1, if_pos h2, if_pos ⟨h1.symm, h2.symm⟩, Nat.cast_one]
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2.symm)]; simp
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.symm)]

/-! ### Holding times and entries -/

/-- Expected holding time at `ξ` (unit-rate time units). -/
noncomputable def Wt (ξ : ℕ × RState Reg Label L) : ℝ≥0∞ :=
  occ (M := M) a σ₀ ξ / (Btot M a ξ.2 : ℝ≥0∞)

/-- Entry mass of `(k, σ')`: the initial state at level `0`, machine reactions from level
`k - 1` otherwise. -/
noncomputable def eE : ℕ → RState Reg Label L → ℝ≥0∞
  | 0, σ' => if σ' = σ₀ then 1 else 0
  | k + 1, σ' => ∑' σ, ∑ o, occ (M := M) a σ₀ (k, σ) * trans (M := M) a k σ o (k + 1, σ')

/-- Holding times of one outer state, indexed by `ℕ` (zero beyond the clock). -/
noncomputable def wN (k : ℕ) (x : Outer Reg Label) (c : ℕ) : ℝ≥0∞ :=
  if h : c < L + 1 then Wt (M := M) a σ₀ (k, (x, ⟨c, h⟩)) else 0

/-- Entries of one outer state, indexed by `ℕ`. -/
noncomputable def eN (k : ℕ) (x : Outer Reg Label) (c : ℕ) : ℝ≥0∞ :=
  if h : c < L + 1 then eE (M := M) a σ₀ k (x, ⟨c, h⟩) else 0

theorem wN_val (k : ℕ) (x : Outer Reg Label) (c : Fin (L + 1)) :
    wN (M := M) a σ₀ k x c.val = Wt (M := M) a σ₀ (k, (x, c)) := by
  rw [wN, dif_pos c.isLt]

theorem eN_val (k : ℕ) (x : Outer Reg Label) (c : Fin (L + 1)) :
    eN (M := M) a σ₀ k x c.val = eE (M := M) a σ₀ k (x, c) := by
  rw [eN, dif_pos c.isLt]

theorem occ_mul_div (ξ : ℕ × RState Reg Label L) (b : ℕ) :
    occ (M := M) a σ₀ ξ * ((b : ℝ≥0∞) / (Btot M a ξ.2 : ℝ≥0∞)) =
      Wt (M := M) a σ₀ ξ * b := by
  unfold Wt
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem occ_eq_mul (ha : 1 ≤ a) (hL : 1 ≤ L) (ξ : ℕ × RState Reg Label L) :
    occ (M := M) a σ₀ ξ = (Btot M a ξ.2 : ℝ≥0∞) * Wt (M := M) a σ₀ ξ := by
  unfold Wt
  rw [mul_comm, ENNReal.div_mul_cancel]
  · exact_mod_cast (Btot_pos (M := M) ha hL ξ.2).ne'
  · exact ENNReal.natCast_ne_top _

/-- **Level split of the balance law**. -/
theorem occ_split (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (σ' : RState Reg Label L) :
    occ (M := M) a σ₀ (k, σ') = eE (M := M) a σ₀ k σ' +
      ∑' σ, ∑ o, occ (M := M) a σ₀ (k, σ) * trans (M := M) a k σ o (k, σ') := by
  rw [occ_balance ha hL σ₀ (k, σ'), ENNReal.tsum_prod']
  dsimp only
  cases k with
  | zero =>
    rw [tsum_eq_single 0]
    · congr 1
      simp only [eE, Prod.mk.injEq, true_and]
    · intro k hk
      refine ENNReal.tsum_eq_zero.mpr fun σ => Finset.sum_eq_zero fun o _ => ?_
      rw [trans_far a k 0 σ o σ' (by omega) (by omega), mul_zero]
  | succ k =>
    rw [tsum_eq_sum (s := {k, k + 1})]
    · rw [Finset.sum_pair (by omega), if_neg (by simp), zero_add]
      rfl
    · intro k' hk'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
      refine ENNReal.tsum_eq_zero.mpr fun σ => Finset.sum_eq_zero fun o _ => ?_
      rw [trans_far a k' (k + 1) σ o σ' (by omega) (by omega), mul_zero]

/-- **Clock inflow**: up from `c - 1` at rate `a`, down from `c + 1` at rate `1`. -/
theorem clock_part (k : ℕ) (x : Outer Reg Label) (c : Fin (L + 1)) :
    ∑' σ, ∑ o, occ (M := M) a σ₀ (k, σ) * trans (M := M) a k σ o (k, (x, c)) =
      (if 0 < c.val then (a : ℝ≥0∞) * wN (M := M) a σ₀ k x (c.val - 1) else 0) +
        (if c.val + 1 < L + 1 then wN (M := M) a σ₀ k x (c.val + 1) else 0) := by
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), Fintype.sum_option]
  have hnone : ∑' σ, occ (M := M) a σ₀ (k, σ) * trans (M := M) a k σ none (k, (x, c)) = 0 := by
    simp [trans]
  rw [hnone, zero_add, sum_idx]
  have hinc : ∀ p : IncIdx M, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inl p)) (k, (x, c)) = 0 := fun p => by
    simp [trans_rm_same a k _ (Sum.inl p) rfl]
  have hdec1 : ∀ d : DecIdx M, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inr (Sum.inl d))) (k, (x, c)) = 0 := fun d => by
    simp [trans_rm_same a k _ (Sum.inr (Sum.inl d)) rfl]
  have hdec2 : ∀ d : DecIdx M, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inl d)))) (k, (x, c)) = 0 := fun d => by
    simp [trans_rm_same a k _ (Sum.inr (Sum.inr (Sum.inl d))) rfl]
  have hup : ∀ j : Fin L, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) (k, (x, c)) =
        if c = j.succ then (a : ℝ≥0∞) * wN (M := M) a σ₀ k x j.val else 0 := by
    intro j
    rw [tsum_eq_single (x, j.castSucc)]
    · rw [trans_up]
      by_cases hj : c = j.succ
      · rw [if_pos ⟨by rw [hj], rfl⟩, if_pos hj, occ_mul_div]
        have : wN (M := M) a σ₀ k x j.val = Wt (M := M) a σ₀ (k, (x, j.castSucc)) :=
          wN_val (M := M) a σ₀ k x j.castSucc
        rw [this, mul_comm]
      · rw [if_neg (fun h => hj (congrArg (fun p => p.2.2) h.1)), if_neg hj, mul_zero]
    · intro σ hσ
      rw [trans_up, if_neg, mul_zero]
      rintro ⟨h1, h2⟩
      exact hσ (Prod.ext (congrArg (fun p => p.2.1) h1).symm h2)
  have hdown : ∀ j : Fin L, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) (k, (x, c)) =
        if c = j.castSucc then wN (M := M) a σ₀ k x (j.val + 1) else 0 := by
    intro j
    rw [tsum_eq_single (x, j.succ)]
    · rw [trans_down]
      by_cases hj : c = j.castSucc
      · rw [if_pos ⟨by rw [hj], rfl⟩, if_pos hj]
        have : wN (M := M) a σ₀ k x (j.val + 1) = Wt (M := M) a σ₀ (k, (x, j.succ)) :=
          wN_val (M := M) a σ₀ k x j.succ
        rw [this]
        unfold Wt
        rw [one_div, div_eq_mul_inv]
      · rw [if_neg (fun h => hj (congrArg (fun p => p.2.2) h.1)), if_neg hj, mul_zero]
    · intro σ hσ
      rw [trans_down, if_neg, mul_zero]
      rintro ⟨h1, h2⟩
      exact hσ (Prod.ext (congrArg (fun p => p.2.1) h1).symm h2)
  simp only [hinc, hdec1, hdec2, hup, hdown, Finset.sum_const_zero, zero_add]
  rw [sum_succ_eq c (fun m => (a : ℝ≥0∞) * wN (M := M) a σ₀ k x m),
    sum_castSucc_eq c (fun m => wN (M := M) a σ₀ k x (m + 1))]

/-! ### Exits and entries -/

/-- **At most one machine step leaves each level**: the expected number of machine reactions
fired at level `k` is at most `1`. -/
theorem exit_le_one (k : ℕ) :
    ∑' σ, ∑ o, occ (M := M) a σ₀ (k, σ) *
      (if rmOpt (M := M) o = 1 then
        massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) o else 0) ≤ 1 := by
  classical
  let F : ℕ × RState Reg Label L × Option (net M L).I → Set (Ω M L) := fun p =>
    if rmOpt (M := M) p.2.2 = 1 then E a σ₀ p.1 k p.2.1 ∩ {ω | ω (p.1 + 1) = p.2.2} else ∅
  have hmeas : ∀ p, MeasurableSet (F p) := by
    intro p
    simp only [F]
    split_ifs
    · exact (measurableSet_E a σ₀ _ _ _).inter (measurableSet_label _ _)
    · exact MeasurableSet.empty
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    intro p p' hne
    refine Set.disjoint_left.mpr ?_
    intro ω h h'
    simp only [F] at h h'
    split_ifs at h h' with h1 h2
    swap; · simp_all
    swap; · simp_all
    swap; · simp_all
    obtain ⟨⟨hK, hZ⟩, ho⟩ := h
    obtain ⟨⟨hK', hZ'⟩, ho'⟩ := h'
    simp only [Set.mem_setOf_eq] at ho ho'
    rcases lt_trichotomy p.1 p'.1 with hlt | heq | hgt
    · have h3 := K_mono ω (show p.1 + 1 ≤ p'.1 from hlt)
      rw [K_succ, hK, ho, h1] at h3
      omega
    · apply hne
      have hσ : p.2.1 = p'.2.1 := enc_injective a (hZ.symm.trans (heq ▸ hZ'))
      have hoo : p.2.2 = p'.2.2 := ho.symm.trans (heq ▸ ho')
      exact Prod.ext heq (Prod.ext hσ hoo)
    · have h3 := K_mono ω (show p'.1 + 1 ≤ p.1 from hgt)
      rw [K_succ, hK', ho', h2] at h3
      omega
  have hval : ∀ p, law M L a σ₀ (F p) = law M L a σ₀ (E a σ₀ p.1 k p.2.1) *
      (if rmOpt (M := M) p.2.2 = 1 then
        massActionPMF (net M L) (net_hasPositiveRates M L) (enc a p.2.1) p.2.2 else 0) := by
    intro p
    simp only [F]
    split_ifs
    · exact law_E_label a σ₀ p.1 k p.2.1 p.2.2
    · simp
  have hR : ∑' p : ℕ × RState Reg Label L × Option (net M L).I, law M L a σ₀ (F p) =
      ∑' n : ℕ, ∑' σ : RState Reg Label L, ∑' o : Option (net M L).I,
        law M L a σ₀ (F (n, σ, o)) := by
    rw [ENNReal.tsum_prod']
    exact tsum_congr fun n => ENNReal.tsum_prod'
  calc _ = ∑' σ : RState Reg Label L, ∑' o : Option (net M L).I, ∑' n : ℕ,
        law M L a σ₀ (F (n, σ, o)) := by
        refine tsum_congr fun σ => ?_
        rw [tsum_fintype]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [occ, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun n => (hval (n, σ, o)).symm
    _ = ∑' σ : RState Reg Label L, ∑' n : ℕ, ∑' o : Option (net M L).I,
        law M L a σ₀ (F (n, σ, o)) := tsum_congr fun σ => ENNReal.tsum_comm
    _ = ∑' n : ℕ, ∑' σ : RState Reg Label L, ∑' o : Option (net M L).I,
        law M L a σ₀ (F (n, σ, o)) := ENNReal.tsum_comm
    _ = ∑' p : ℕ × RState Reg Label L × Option (net M L).I, law M L a σ₀ (F p) := hR.symm
    _ = law M L a σ₀ (⋃ p, F p) := (measure_iUnion hdisj hmeas).symm
    _ ≤ 1 := prob_le_one

theorem tsum_trans_succ (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (σ : RState Reg Label L)
    (o : Option (net M L).I) :
    ∑' σ', trans (M := M) a k σ o (k + 1, σ') =
      if rmOpt (M := M) o = 1 then
        massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) o else 0 := by
  cases o with
  | none => simp [trans, rmOpt]
  | some i =>
    by_cases hi : rmOpt (M := M) (some i) = 1
    · rw [if_pos hi, pmf_enc_some ha hL, tsum_eq_single (tgt M i σ)]
      · rw [trans_rm a k σ i hi, if_pos rfl]
      · intro σ' hσ'
        rw [trans_rm a k σ i hi, if_neg (Ne.symm hσ')]
    · have h0 : rmOpt (M := M) (some i) = 0 := by
        have := rmOpt_le_one (M := M) (L := L) (some i); omega
      rw [if_neg hi]
      exact ENNReal.tsum_eq_zero.mpr fun σ' => trans_clock_succ a k σ i h0 σ'

/-- **Total entry mass of each level is at most one.** -/
theorem eE_total_le_one (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) :
    ∑' σ', eE (M := M) a σ₀ k σ' ≤ 1 := by
  cases k with
  | zero => simp [eE]
  | succ k =>
    simp only [eE]
    rw [ENNReal.tsum_comm]
    calc _ = ∑' σ, ∑ o, occ (M := M) a σ₀ (k, σ) * ∑' σ', trans (M := M) a k σ o (k + 1, σ') := by
          refine tsum_congr fun σ => ?_
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          exact Finset.sum_congr rfl fun o _ => ENNReal.tsum_mul_left
      _ = _ := by simp only [tsum_trans_succ (M := M) a ha hL]
      _ ≤ 1 := exit_le_one (M := M) a σ₀ k

theorem eE_le_one (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (σ : RState Reg Label L) :
    eE (M := M) a σ₀ k σ ≤ 1 :=
  (ENNReal.le_tsum σ).trans (eE_total_le_one (M := M) a σ₀ ha hL k)

theorem eN_ne_top (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (x : Outer Reg Label) (c : ℕ) :
    eN (M := M) a σ₀ k x c ≠ ∞ := by
  unfold eN
  split_ifs
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (eE_le_one (M := M) a σ₀ ha hL k _)
  · exact ENNReal.zero_ne_top

/-- One machine label at one reduced state carries holding time at most `1`. -/
theorem Wt_mul_beta_le_one (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (σ : RState Reg Label L)
    (i : (net M L).I) (hi : rmOpt (M := M) (some i) = 1) :
    Wt (M := M) a σ₀ (k, σ) * beta M a i σ ≤ 1 := by
  rw [← occ_mul_div]
  refine le_trans ?_ (exit_le_one (M := M) a σ₀ k)
  refine le_trans ?_ (ENNReal.le_tsum σ)
  refine le_trans ?_ (Finset.single_le_sum (f := fun o => occ (M := M) a σ₀ (k, σ) *
      (if rmOpt (M := M) o = 1 then
        massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) o else 0))
    (fun _ _ => zero_le) (Finset.mem_univ (some i)))
  simp only [if_pos hi, pmf_enc_some ha hL]
  exact le_rfl

/-! ### The clock balance of a live outer state -/

theorem balance_enn (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (x : Outer Reg Label) (c : Fin (L + 1)) :
    (Btot M a (x, c) : ℝ≥0∞) * Wt (M := M) a σ₀ (k, (x, c)) =
      eE (M := M) a σ₀ k (x, c) +
        (if 0 < c.val then (a : ℝ≥0∞) * wN (M := M) a σ₀ k x (c.val - 1) else 0) +
          (if c.val + 1 < L + 1 then wN (M := M) a σ₀ k x (c.val + 1) else 0) := by
  rw [← occ_eq_mul (M := M) a σ₀ ha hL (k, (x, c)), occ_split (M := M) a σ₀ ha hL k, clock_part, add_assoc]

theorem Wt_ne_top (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) {x : Outer Reg Label} (hx : Live M x) :
    ∀ c : ℕ, wN (M := M) a σ₀ k x c ≠ ∞ := by
  intro c
  induction c with
  | zero =>
    rw [show (0 : ℕ) = (0 : Fin (L + 1)).val from rfl, wN_val]
    unfold Live at hx
    rcases hcode : M.code x.1 with ⟨r, j⟩ | ⟨r, j, k'⟩ | _
    · have h := Wt_mul_beta_le_one (M := M) a σ₀ ha hL k (x, 0) (Sum.inl ⟨(x.1, r, j), hcode⟩) rfl
      have hb : beta M a (Sum.inl ⟨(x.1, r, j), hcode⟩) (x, (0 : Fin (L + 1))) = 1 := by
        simp [beta]
      rw [hb, Nat.cast_one, mul_one] at h
      exact ne_top_of_le_ne_top ENNReal.one_ne_top h
    · have h := Wt_mul_beta_le_one (M := M) a σ₀ ha hL k (x, 0)
        (Sum.inr (Sum.inr (Sum.inl ⟨(x.1, r, j, k'), hcode⟩))) rfl
      have hb : beta M a (Sum.inr (Sum.inr (Sum.inl ⟨(x.1, r, j, k'), hcode⟩)))
          (x, (0 : Fin (L + 1))) = 1 := by
        simp [beta]
      rw [hb, Nat.cast_one, mul_one] at h
      exact ne_top_of_le_ne_top ENNReal.one_ne_top h
    · exact absurd hcode hx
  | succ c ih =>
    by_cases hc : c + 1 < L + 1
    · have hcL : c < L + 1 := by omega
      have hb := balance_enn (M := M) a σ₀ ha hL k x (⟨c, hcL⟩ : Fin (L + 1))
      simp only [if_pos (show c + 1 < L + 1 from hc)] at hb
      have hle : wN (M := M) a σ₀ k x (c + 1) ≤
          (Btot M a (x, (⟨c, hcL⟩ : Fin (L + 1))) : ℝ≥0∞) *
            Wt (M := M) a σ₀ (k, (x, (⟨c, hcL⟩ : Fin (L + 1)))) := by
        rw [hb]; exact le_add_self
      refine ne_top_of_le_ne_top ?_ hle
      refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      have := ih
      rwa [wN, dif_pos hcL] at this
    · rw [wN, dif_neg hc]; exact ENNReal.zero_ne_top

/-- Real holding times and entries of one outer state. -/
noncomputable def wR (k : ℕ) (x : Outer Reg Label) (c : ℕ) : ℝ := (wN (M := M) a σ₀ k x c).toReal

noncomputable def eR (k : ℕ) (x : Outer Reg Label) (c : ℕ) : ℝ := (eN (M := M) a σ₀ k x c).toReal

theorem clockBalance (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) {x : Outer Reg Label} (hx : Live M x) :
    ClockBalance (L + 1) a (rho M x) (kappa M x) (wR (M := M) a σ₀ k x) (eR (M := M) a σ₀ k x) := by
  intro c hc
  have hb := balance_enn (M := M) a σ₀ ha hL k x ⟨c, hc⟩
  have hfin := Wt_ne_top (M := M) a σ₀ ha hL k hx
  have hBeq := Btot_eq (M := M) a x ⟨c, hc⟩
  simp only at hb hBeq
  rw [← wN_val (M := M) a σ₀ k x ⟨c, hc⟩, ← eN_val (M := M) a σ₀ k x ⟨c, hc⟩] at hb
  simp only at hb
  have hreal := congrArg ENNReal.toReal hb
  have hE := eN_ne_top (M := M) a σ₀ ha hL k x c
  have hA : (if 0 < c then (a : ℝ≥0∞) * wN (M := M) a σ₀ k x (c - 1) else 0) ≠ ∞ := by
    split_ifs
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hfin _)
    · exact ENNReal.zero_ne_top
  have hC : (if c + 1 < L + 1 then wN (M := M) a σ₀ k x (c + 1) else 0) ≠ ∞ := by
    split_ifs
    · exact hfin _
    · exact ENNReal.zero_ne_top
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hE, hA⟩) hC, ENNReal.toReal_add hE hA] at hreal
  have hA' : (if 0 < c then (a : ℝ≥0∞) * wN (M := M) a σ₀ k x (c - 1) else 0).toReal =
      if 0 < c then (a : ℝ) * (wN (M := M) a σ₀ k x (c - 1)).toReal else 0 := by
    split_ifs <;> simp [ENNReal.toReal_mul]
  have hC' : (if c + 1 < L + 1 then wN (M := M) a σ₀ k x (c + 1) else 0).toReal =
      if c + 1 < L + 1 then (wN (M := M) a σ₀ k x (c + 1)).toReal else 0 := by
    split_ifs <;> simp
  rw [hA', hC'] at hreal
  unfold wR eR rate
  rw [← hreal, hBeq]
  have hc0 : ((⟨c, hc⟩ : Fin (L + 1)) = 0) ↔ c = 0 := by simp [Fin.ext_iff]
  simp only [hc0]
  push_cast
  split_ifs <;> ring

/-! ### Entries lie in the cone -/

/-- The cone `C_a` for `ℝ≥0∞`-valued clock vectors. -/
def ConeE (L a : ℕ) (v : ℕ → ℝ≥0∞) : Prop :=
  ∀ c, c + 1 < L + 1 → (a : ℝ≥0∞) * v c ≤ v (c + 1)

theorem cone_eN_zero (hσ₀ : σ₀.2 = Fin.last L) (x : Outer Reg Label) :
    ConeE L a (eN (M := M) a σ₀ 0 x) := by
  intro c hc
  have h0 : eN (M := M) a σ₀ 0 x c = 0 := by
    rw [eN, dif_pos (by omega)]
    simp only [eE]
    rw [if_neg]
    intro h
    have := congrArg (fun σ : RState Reg Label L => σ.2.val) h
    simp only [hσ₀, Fin.val_last] at this
    omega
  rw [h0, mul_zero]
  exact zero_le

/-- Contribution of one machine label to the entries of level `k + 1`. -/
noncomputable def piece (k : ℕ) (i : (net M L).I) (σ' : RState Reg Label L) : ℝ≥0∞ :=
  ∑' σ, occ (M := M) a σ₀ (k, σ) * trans (M := M) a k σ (some i) (k + 1, σ')

theorem eE_succ_eq (k : ℕ) (σ' : RState Reg Label L) :
    eE (M := M) a σ₀ (k + 1) σ' =
      (∑ p : IncIdx M, piece (M := M) a σ₀ k (Sum.inl p) σ') +
        ((∑ d : DecIdx M, piece (M := M) a σ₀ k (Sum.inr (Sum.inl d)) σ') +
          ∑ d : DecIdx M, piece (M := M) a σ₀ k (Sum.inr (Sum.inr (Sum.inl d))) σ') := by
  simp only [eE]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), Fintype.sum_option]
  have hnone : ∑' σ, occ (M := M) a σ₀ (k, σ) * trans (M := M) a k σ none (k + 1, σ') = 0 := by
    simp [trans]
  rw [hnone, zero_add, sum_idx]
  have hup : ∀ j : Fin L, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) (k + 1, σ') = 0 :=
    fun j => by simp [trans_clock_succ a k _ (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) rfl]
  have hdown : ∀ j : Fin L, ∑' σ, occ (M := M) a σ₀ (k, σ) *
      trans (M := M) a k σ (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) (k + 1, σ') = 0 :=
    fun j => by simp [trans_clock_succ a k _ (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))) rfl]
  simp only [hup, hdown, Finset.sum_const_zero, add_zero]
  rfl

/-- A machine label that keeps the clock and whose propensity does not see the clock. -/
theorem piece_pres (k : ℕ) (i : (net M L).I) (hi : rmOpt (M := M) (some i) = 1)
    (hpres : ∀ y c, tgt M i (y, c) = ((tgt M i (y, 0)).1, c))
    (hβ : ∀ y c, beta M a i (y, c) = beta M a i (y, 0)) (x' : Outer Reg Label)
    (cf : Fin (L + 1)) :
    piece (M := M) a σ₀ k i (x', cf) = ∑' y, if (tgt M i (y, 0)).1 = x' then
      Wt (M := M) a σ₀ (k, (y, cf)) * beta M a i (y, 0) else 0 := by
  unfold piece
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun y => ?_
  rw [tsum_eq_single cf]
  · rw [trans_rm a k _ i hi, hpres y cf]
    by_cases h : (tgt M i (y, 0)).1 = x'
    · rw [if_pos (by rw [h]), if_pos h, occ_mul_div, hβ]
    · rw [if_neg (fun he => h (congrArg Prod.fst he)), if_neg h, mul_zero]
  · intro c hc
    rw [trans_rm a k _ i hi, hpres y c, if_neg (fun he => hc (congrArg Prod.snd he)), mul_zero]

theorem piece_cone (k : ℕ) (i : (net M L).I) (hi : rmOpt (M := M) (some i) = 1)
    (hpres : ∀ y c, tgt M i (y, c) = ((tgt M i (y, 0)).1, c))
    (hβ : ∀ y c, beta M a i (y, c) = beta M a i (y, 0))
    (hlive : ∀ y, beta M a i (y, 0) ≠ 0 → Live M y)
    (hw : ∀ y, Live M y → ConeE L a (wN (M := M) a σ₀ k y)) (x' : Outer Reg Label)
    (c : ℕ) (hc : c + 1 < L + 1) :
    (a : ℝ≥0∞) * piece (M := M) a σ₀ k i (x', ⟨c, by omega⟩) ≤
      piece (M := M) a σ₀ k i (x', ⟨c + 1, hc⟩) := by
  rw [piece_pres (M := M) a σ₀ k i hi hpres hβ, piece_pres (M := M) a σ₀ k i hi hpres hβ,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs
  · by_cases h0 : beta M a i (y, 0) = 0
    · simp [h0]
    · have hcone := hw y (hlive y h0) c hc
      rw [wN, dif_pos (by omega), wN, dif_pos hc] at hcone
      rw [← mul_assoc]
      gcongr
  · simp

theorem piece_dec2_zero (k : ℕ) (d : DecIdx M) (x' : Outer Reg Label) (c : ℕ) (hc : c < L) :
    piece (M := M) a σ₀ k (Sum.inr (Sum.inr (Sum.inl d))) (x', ⟨c, by omega⟩) = 0 := by
  unfold piece
  refine ENNReal.tsum_eq_zero.mpr fun σ => ?_
  rw [trans_rm a k σ _ rfl, if_neg, mul_zero]
  intro h
  have := congrArg (fun σ : RState Reg Label L => σ.2.val) h
  simp only [tgt, Fin.val_last] at this
  omega

theorem cone_eN_succ (k : ℕ) (hw : ∀ y, Live M y → ConeE L a (wN (M := M) a σ₀ k y))
    (x' : Outer Reg Label) : ConeE L a (eN (M := M) a σ₀ (k + 1) x') := by
  intro c hc
  rw [eN, dif_pos (by omega), eN, dif_pos hc, eE_succ_eq, eE_succ_eq]
  simp only [piece_dec2_zero (M := M) a σ₀ k _ x' c (by omega), Finset.sum_const_zero, add_zero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun p _ => ?_) (le_trans (Finset.sum_le_sum fun d _ => ?_)
    le_self_add)
  · exact piece_cone (M := M) a σ₀ k (Sum.inl p) rfl (fun y c => rfl) (fun y c => rfl)
      (fun y h => live_of_inc p y (by by_contra hne; exact h (by simp [beta, hne])))
      hw x' c hc
  · exact piece_cone (M := M) a σ₀ k (Sum.inr (Sum.inl d)) rfl (fun y c => rfl) (fun y c => rfl)
      (fun y h => live_of_dec d y (by by_contra hne; exact h (by simp [beta, hne])))
      hw x' c hc

theorem inCone_eR (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) (x : Outer Reg Label)
    (he : ConeE L a (eN (M := M) a σ₀ k x)) : InCone (L + 1) a (eR (M := M) a σ₀ k x) := by
  intro c hc
  have h := ENNReal.toReal_mono (eN_ne_top (M := M) a σ₀ ha hL k x (c + 1)) (he c hc)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h

theorem inCone_wR (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) {x : Outer Reg Label} (hx : Live M x)
    (he : ConeE L a (eN (M := M) a σ₀ k x)) : InCone (L + 1) a (wR (M := M) a σ₀ k x) :=
  (clockBalance (M := M) a σ₀ ha hL k hx).inCone (by omega) (by exact_mod_cast ha) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) ENNReal.toReal_nonneg (inCone_eR (M := M) a σ₀ ha hL k x he)

theorem cone_wN (ha : 1 ≤ a) (hL : 1 ≤ L) (k : ℕ) {x : Outer Reg Label} (hx : Live M x)
    (he : ConeE L a (eN (M := M) a σ₀ k x)) : ConeE L a (wN (M := M) a σ₀ k x) := by
  intro c hc
  have h := inCone_wR (M := M) a σ₀ ha hL k hx he c hc
  have hfin := Wt_ne_top (M := M) a σ₀ ha hL k hx
  unfold wR at h
  rw [← ENNReal.toReal_natCast, ← ENNReal.toReal_mul] at h
  exact (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hfin c))
    (hfin (c + 1))).mp h

/-- **Entries lie in the cone `C_a` at every level** (induction on the level). -/
theorem cone_eN (ha : 1 ≤ a) (hL : 1 ≤ L) (hσ₀ : σ₀.2 = Fin.last L) :
    ∀ k x, ConeE L a (eN (M := M) a σ₀ k x)
  | 0, x => cone_eN_zero (M := M) a σ₀ hσ₀ x
  | k + 1, x => cone_eN_succ (M := M) a σ₀ k
      (fun y hy => cone_wN (M := M) a σ₀ ha hL k hy (cone_eN ha hL hσ₀ k y)) x

/-! ### Per-level bounds (Lemmas 2.3 and 2.4) -/

theorem one_le_geomWeight (a : ℝ) (ha : 0 ≤ a) : 1 ≤ geomWeight a (L + 1) := by
  unfold geomWeight
  rw [Finset.sum_range_succ']
  have : 0 ≤ ∑ c ∈ Finset.range L, a ^ (c + 1) := Finset.sum_nonneg fun _ _ => by positivity
  simp only [pow_zero]
  linarith

theorem sum_Wt_eq (k : ℕ) (x : Outer Reg Label) :
    ∑ c : Fin (L + 1), Wt (M := M) a σ₀ (k, (x, c)) =
      ∑ m ∈ Finset.range (L + 1), wN (M := M) a σ₀ k x m := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => wN (M := M) a σ₀ k x m)]
  exact Finset.sum_congr rfl fun c _ => (wN_val (M := M) a σ₀ k x c).symm

theorem sum_eE_eq (k : ℕ) (x : Outer Reg Label) :
    ∑ c : Fin (L + 1), eE (M := M) a σ₀ k (x, c) =
      ∑ m ∈ Finset.range (L + 1), eN (M := M) a σ₀ k x m := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => eN (M := M) a σ₀ k x m)]
  exact Finset.sum_congr rfl fun c _ => (eN_val (M := M) a σ₀ k x c).symm

theorem level_bounds (ha2 : 2 ≤ a) (hL : 1 ≤ L) (hσ₀ : σ₀.2 = Fin.last L) (k : ℕ)
    {x : Outer Reg Label} (hx : Live M x) :
    ∑ c : Fin (L + 1), Wt (M := M) a σ₀ (k, (x, c)) ≤
        ENNReal.ofReal (2 * geomWeight a (L + 1)) * ∑ c : Fin (L + 1), eE (M := M) a σ₀ k (x, c) ∧
      (1 ≤ rho M x → Wt (M := M) a σ₀ (k, (x, 0)) * ENNReal.ofReal (geomWeight a (L + 1)) ≤
        ∑ c : Fin (L + 1), eE (M := M) a σ₀ k (x, c)) := by
  have ha : 1 ≤ a := by omega
  have hB := clockBalance (M := M) a σ₀ ha hL k hx
  have hcone := inCone_wR (M := M) a σ₀ ha hL k hx (cone_eN a σ₀ ha hL hσ₀ k x)
  have hfin := Wt_ne_top (M := M) a σ₀ ha hL k hx
  have hefin := eN_ne_top (M := M) a σ₀ ha hL k x
  have hw0 : 0 ≤ wR (M := M) a σ₀ k x 0 := ENNReal.toReal_nonneg
  have tick := ClockBalance.tick_le hB (by omega) hcone (Nat.cast_nonneg _) (Nat.cast_nonneg _) hw0
  set G := geomWeight (a : ℝ) (L + 1) with hG
  have hG1 : 1 ≤ G := one_le_geomWeight (a : ℝ) (Nat.cast_nonneg _)
  have hpw : psum (wR (M := M) a σ₀ k x) (L + 1) =
      (∑ m ∈ Finset.range (L + 1), wN (M := M) a σ₀ k x m).toReal := by
    unfold psum wR; rw [ENNReal.toReal_sum (fun m _ => hfin m)]
  have hpe : psum (eR (M := M) a σ₀ k x) (L + 1) =
      (∑ m ∈ Finset.range (L + 1), eN (M := M) a σ₀ k x m).toReal := by
    unfold psum eR; rw [ENNReal.toReal_sum (fun m _ => hefin m)]
  have hSW : ∑ c : Fin (L + 1), Wt (M := M) a σ₀ (k, (x, c)) =
      ENNReal.ofReal (psum (wR (M := M) a σ₀ k x) (L + 1)) := by
    rw [sum_Wt_eq, hpw, ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr fun m _ => hfin m)]
  have hSE : ∑ c : Fin (L + 1), eE (M := M) a σ₀ k (x, c) =
      ENNReal.ofReal (psum (eR (M := M) a σ₀ k x) (L + 1)) := by
    rw [sum_eE_eq, hpe, ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr fun m _ => hefin m)]
  have hpw0 : 0 ≤ psum (wR (M := M) a σ₀ k x) (L + 1) := by rw [hpw]; exact ENNReal.toReal_nonneg
  have hpe0 : 0 ≤ psum (eR (M := M) a σ₀ k x) (L + 1) := by rw [hpe]; exact ENNReal.toReal_nonneg
  refine ⟨?_, fun hρ => ?_⟩
  · have hreal : psum (wR (M := M) a σ₀ k x) (L + 1) ≤
        2 * G * psum (eR (M := M) a σ₀ k x) (L + 1) := by
      by_cases hρ : rho M x = 0
      · have hκ := kappa_eq_one_of_rho_eq_zero hx hρ
        have hB' : ClockBalance (L + 1) a 0 1 (wR (M := M) a σ₀ k x) (eR (M := M) a σ₀ k x) := by
          have := hB
          rw [hρ, hκ, Nat.cast_zero, Nat.cast_one] at this
          exact this
        have := ClockBalance.time_le_of_no_exit hB' (by omega) (by exact_mod_cast ha2)
          (fun _ => ENNReal.toReal_nonneg)
        linarith
      · have hρ1 : (1 : ℝ) ≤ rho M x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρ
        nlinarith [tick.2]
    rw [hSW, hSE, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hρ1 : (1 : ℝ) ≤ rho M x := by exact_mod_cast hρ
    have hreal : wR (M := M) a σ₀ k x 0 * G ≤ psum (eR (M := M) a σ₀ k x) (L + 1) := by
      nlinarith [tick.1, tick.2]
    rw [hSE, ← wN_val (M := M) a σ₀ k x 0]
    have : wN (M := M) a σ₀ k x (0 : Fin (L + 1)).val =
        ENNReal.ofReal (wR (M := M) a σ₀ k x 0) := by
      unfold wR; rw [ENNReal.ofReal_toReal (hfin 0)]; rfl
    rw [this, ← ENNReal.ofReal_mul hw0]
    exact ENNReal.ofReal_le_ofReal hreal

end Ripple.sCRNUniversality.RegisterMachine.Clocked

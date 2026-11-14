/-
  Ripple.LPP.NAPCriterion — (C1),(C2) ⇒ per-monomial splittability, hence Theorem 1 for every
  syntactic quartic protocol satisfying the criterion (the PP-to-NAP write-up, Theorem 1, (3)⇒(2)).

  (C1) `coef y (y³k) ≤ 0` and (C2) `coef k (y³k) + 2 coef y (y⁴) ≤ 0` for all distinct `y, k`.

  Proof shape. A positive demand at `(δ, α)` has a positive chain-rule term `coef j μ > 0` with
  `α_j > 0` and `(α − e_j) + μ = δ`. If `μ = j⁴` this contradicts conservation. Otherwise pick
  `i ≠ j` with `μ_i > 0`; the pair `β = α − e_j + e_i`, `γ = μ − e_i` splits `δ` with `β ≠ α`. It
  fails only if `γ = α`, i.e. `μ = α + e_i`; a second such `i'` gives a good pair, and if none
  exists then `α` is supported on `{i, j}` with `α_i ∈ {0,1,2}`: `α_i = 0` contradicts (C1),
  `α_i = 2` contradicts (C2) (through the full two-term demand), and `α_i = 1` is split by
  `{i³, j³}`.
-/

import Ripple.LPP.NAPDemand

namespace Ripple
namespace NAPTransport

open Finset

variable (n : ℕ)

/-! ### Multi-index constructors -/

/-- A multi-index from a bounded natural function of the right weight. -/
def MI.ofFun {m : ℕ} (g : Fin n → ℕ) (hb : ∀ k, g k ≤ m) (hw : ∑ k, g k = m) : MI n m :=
  ⟨fun k => ⟨g k, by have := hb k; omega⟩, by simpa using hw⟩

@[simp] theorem MI.ofFun_val {m : ℕ} (g : Fin n → ℕ) (hb : ∀ k, g k ≤ m) (hw : ∑ k, g k = m)
    (k : Fin n) : ((MI.ofFun n g hb hw).1 k : ℕ) = g k := rfl

theorem sum_ite_two {a b : ℕ} {y k : Fin n} (hyk : y ≠ k) :
    ∑ i, (if i = y then a else if i = k then b else 0) = a + b := by
  have : ∀ i, (if i = y then a else if i = k then b else 0)
      = (if i = y then a else 0) + (if i = k then b else 0) := by
    intro i
    by_cases h1 : i = y
    · subst h1; simp [hyk]
    · simp [h1]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]

/-- The pure power `y^m`. -/
def MI.pow (m : ℕ) (y : Fin n) : MI n m :=
  MI.ofFun n (fun i => if i = y then m else 0) (fun i => by dsimp only; split_ifs <;> omega)
    (by simp)

/-- The monomial `y^a k^b` of weight `a + b` (for `y ≠ k`). -/
def MI.two (a b : ℕ) (y k : Fin n) (hyk : y ≠ k) : MI n (a + b) :=
  MI.ofFun n (fun i => if i = y then a else if i = k then b else 0)
    (fun i => by dsimp only; split_ifs <;> omega) (sum_ite_two n hyk)

/-- Vacuity: `coef y (y⁴) ≤ 0` for every conservative syntactic quartic field. -/
theorem coef_pow_nonpos (f : QuarticPP n) (y : Fin n) : f.coef y (MI.pow n 4 y) ≤ 0 := by
  have hc := f.conservative (MI.pow n 4 y)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y)] at hc
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase y, f.coef j (MI.pow n 4 y) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjy : j ≠ y := (Finset.mem_erase.mp hj).1
    by_contra hneg
    rw [not_le] at hneg
    have := f.sign j _ hneg
    simp [MI.pow, hjy] at this
  linarith

/-! ### A positive chain-rule term -/

theorem demand_pos_term (f : QuarticPP n) (δ : Fin n → Fin (2 * 3 + 1)) (α : MI n 3)
    (h : 0 < demand n f δ α) :
    ∃ j μ, 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ ∧ 0 < f.coef j μ := by
  unfold demand at h
  have hmult := MI.mult_pos n 3 α
  have hsum : 0 < ∑ j, ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) := by
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonpos_of_nonneg_of_nonpos hmult.le hcon
    linarith
  have hj' : ∃ j, 0 < ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hsum (not_lt.mpr (Finset.sum_nonpos fun j _ => hcon j))
  obtain ⟨j, hj⟩ := hj'
  have hμ' : ∃ μ, 0 < (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hj (not_lt.mpr (Finset.sum_nonpos fun μ _ => hcon μ))
  obtain ⟨μ, hμ⟩ := hμ'
  split_ifs at hμ with hc
  · refine ⟨j, μ, hc.1, hc.2, ?_⟩
    have hαj : (0 : ℚ) < ((α.1 j : ℕ) : ℚ) := by exact_mod_cast hc.1
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonpos_of_nonneg_of_nonpos hαj.le hcon
    linarith
  · exact absurd hμ (lt_irrefl 0)

/-! ### The candidate split `β = α − e_j + e_i`, `γ = μ − e_i` -/

/-- `α − e_j + e_i` as a weight-3 multi-index (`i ≠ j`, `α_j > 0`). -/
def MI.shift (α : MI n 3) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ)) : MI n 3 :=
  MI.ofFun n (fun k => (α.1 k : ℕ) - (if k = j then 1 else 0) + (if k = i then 1 else 0))
    (fun k => by
      have h1 := MI.entry_le n α k
      have h2 := MI.two_entries_le n α hij
      by_cases hk : k = i
      · subst hk; simp only [hij, if_false, if_true]; omega
      · simp only [hk, if_false]; split_ifs <;> omega)
    (by
      have hle : ∀ k ∈ Finset.univ, (if k = j then 1 else 0) ≤ (α.1 k : ℕ) := by
        intro k _
        split_ifs with hk
        · subst hk; exact hαj
        · exact Nat.zero_le _
      rw [Finset.sum_add_distrib, Finset.sum_tsub_distrib Finset.univ hle, α.2,
        Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i]
      simp)

theorem MI.shift_ne (α : MI n 3) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ)) :
    MI.shift n α j i hij hαj ≠ α := by
  intro h
  have := congrArg (fun β : MI n 3 => (β.1 i : ℕ)) h
  simp only [MI.shift, MI.ofFun_val, hij, if_false, if_true] at this
  omega

theorem MI.add_shift_sub1 (α : MI n 3) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ))
    (μ : MI n 4) (hμi : 0 < (μ.1 i : ℕ)) (δ : Fin n → Fin (2 * 3 + 1))
    (hc : chainEq n α j μ δ) :
    MI.add n 3 (MI.shift n α j i hij hαj) (MI.sub1 n μ i hμi) = δ := by
  funext k
  apply Fin.ext
  simp only [MI.add, MI.shift, MI.sub1, MI.ofFun_val]
  have h := hc k
  by_cases hk : k = i
  · subst hk
    simp only [hij, if_false, if_true] at h ⊢
    omega
  · by_cases hkj : k = j
    · subst hkj
      simp only [hk, if_false, if_true] at h ⊢
      omega
    · simp only [hk, hkj, if_false] at h ⊢
      omega

theorem MI.sub1_inj (μ : MI n 4) (i i' : Fin n) (hi : 0 < (μ.1 i : ℕ)) (hi' : 0 < (μ.1 i' : ℕ))
    (h : MI.sub1 n μ i hi = MI.sub1 n μ i' hi') : i = i' := by
  by_contra hne
  have := congrArg (fun β : MI n 3 => (β.1 i : ℕ)) h
  simp only [MI.sub1, if_true, hne, if_false] at this
  omega

/-! ### The two-source evaluation of the demand -/

/-- Uniqueness of the chain-rule monomial `μ = δ − α + e_j`. -/
theorem chainEq_unique (α : MI n 3) (j : Fin n) (μ μ' : MI n 4) (δ : Fin n → Fin (2 * 3 + 1))
    (h : chainEq n α j μ δ) (h' : chainEq n α j μ' δ) : μ = μ' := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  have h1 := h k
  have h2 := h' k
  omega

/-- If `α` is supported on `S` and `m k` is the chain-rule monomial of source `k ∈ S`, the demand
is the sum over `S`. -/
theorem demand_eq_sum (f : QuarticPP n) (δ : Fin n → Fin (2 * 3 + 1)) (α : MI n 3)
    (S : Finset (Fin n)) (hS : ∀ k, 0 < (α.1 k : ℕ) → k ∈ S)
    (m : Fin n → MI n 4) (hm : ∀ k ∈ S, chainEq n α k (m k) δ) :
    demand n f δ α = MI.mult n 3 α * ∑ k ∈ S, ((α.1 k : ℕ) : ℚ) * f.coef k (m k) := by
  unfold demand
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hαk : 0 < (α.1 k : ℕ)
    · rw [Finset.sum_eq_single (m k)]
      · rw [if_pos ⟨hαk, hm k hk⟩]
      · intro μ _ hμ
        rw [if_neg]
        rintro ⟨_, hc⟩
        exact hμ (chainEq_unique n α k μ (m k) δ hc (hm k hk))
      · intro h; exact absurd (Finset.mem_univ _) h
    · have h0 : (α.1 k : ℕ) = 0 := by omega
      simp [h0]
  · intro k _ hk
    have h0 : (α.1 k : ℕ) = 0 := by
      by_contra hne
      exact hk (hS k (Nat.pos_of_ne_zero hne))
    simp [h0]

/-! ### The main lemma: (C1),(C2) ⇒ (h2) -/

/-- (C1),(C2) ⇒ per-monomial splittability of the demand table. -/
theorem demand_splittable_of_C1C2 (f : QuarticPP n)
    (hC1 : ∀ (y k : Fin n) (h : y ≠ k), f.coef y (MI.two n 3 1 y k h) ≤ 0)
    (hC2 : ∀ (y k : Fin n) (h : y ≠ k),
      f.coef k (MI.two n 3 1 y k h) + 2 * f.coef y (MI.pow n 4 y) ≤ 0)
    (δ : Fin n → Fin (2 * 3 + 1)) (α : MI n 3) (hpos : 0 < demand n f δ α) :
    ∃ β γ, MI.add n 3 β γ = δ ∧ β ≠ α ∧ γ ≠ α := by
  obtain ⟨j, μ, hαj, hc, hcoef⟩ := demand_pos_term n f δ α hpos
  by_cases hμ : ∀ i, i ≠ j → (μ.1 i : ℕ) = 0
  · -- μ = j⁴
    exfalso
    have hμj : (μ.1 j : ℕ) = 4 := by
      have hw := μ.2
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)] at hw
      have : ∑ i ∈ Finset.univ.erase j, (μ.1 i : ℕ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hμ i (Finset.mem_erase.mp hi).1
      omega
    have hμeq : μ = MI.pow n 4 j := by
      apply Subtype.ext
      funext k
      apply Fin.ext
      simp only [MI.pow, MI.ofFun_val]
      by_cases hk : k = j
      · subst hk; simp [hμj]
      · simp [hk, hμ k hk]
    rw [hμeq] at hcoef
    exact absurd hcoef (not_lt.mpr (coef_pow_nonpos n f j))
  · simp only [not_forall, Classical.not_imp] at hμ
    obtain ⟨i, hij, hμi0⟩ := hμ
    have hμi : 0 < (μ.1 i : ℕ) := Nat.pos_of_ne_zero hμi0
    by_cases hbad : MI.sub1 n μ i hμi = α
    · by_cases hi' : ∃ i', i' ≠ j ∧ i' ≠ i ∧ 0 < (μ.1 i' : ℕ)
      · obtain ⟨i', hi'j, hi'i, hμi'⟩ := hi'
        refine ⟨MI.shift n α j i' hi'j hαj, MI.sub1 n μ i' hμi',
          MI.add_shift_sub1 n α j i' hi'j hαj μ hμi' δ hc, MI.shift_ne n α j i' hi'j hαj, ?_⟩
        intro h
        exact hi'i (MI.sub1_inj n μ i' i hμi' hμi (h.trans hbad.symm))
      · -- supp μ ⊆ {i, j}, α = μ − e_i
        simp only [not_exists, not_and, not_lt] at hi'
        have hsupp : ∀ k, k ≠ i → k ≠ j → (μ.1 k : ℕ) = 0 := by
          intro k hki hkj
          have := hi' k hkj hki
          omega
        have hαval : ∀ k, (α.1 k : ℕ) = (μ.1 k : ℕ) - (if k = i then 1 else 0) := by
          intro k
          have := congrArg (fun β : MI n 3 => (β.1 k : ℕ)) hbad
          simp only [MI.sub1] at this
          omega
        have hαi : (α.1 i : ℕ) ≤ 2 := by
          have := MI.two_entries_le n α hij
          omega
        have hαsupp : ∀ k, k ≠ i → k ≠ j → (α.1 k : ℕ) = 0 := by
          intro k hki hkj
          rw [hαval k, hsupp k hki hkj]
          simp
        -- the weight of α: α_i + α_j = 3
        have hαw : (α.1 i : ℕ) + (α.1 j : ℕ) = 3 := by
          have hw := α.2
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)] at hw
          have : ∑ k ∈ (Finset.univ.erase i).erase j, (α.1 k : ℕ) = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            have h1 := (Finset.mem_erase.mp hk).1
            have h2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
            exact hαsupp k h2 h1
          omega
        -- the monomial μ in terms of α
        have hμval : ∀ k, (μ.1 k : ℕ) = (α.1 k : ℕ) + (if k = i then 1 else 0) := by
          intro k
          have h1 := hαval k
          by_cases hk : k = i
          · subst hk; simp only [if_true] at h1 ⊢; omega
          · simp only [hk, if_false] at h1 ⊢; omega
        have hji : j ≠ i := Ne.symm hij
        rcases Nat.lt_or_ge (α.1 i : ℕ) 1 with h0 | h1
        · -- α_i = 0: α = j³, μ = j³ i, contradiction with (C1)
          exfalso
          have hμeq : μ = MI.two n 3 1 j i hji := by
            apply Subtype.ext
            funext k
            apply Fin.ext
            simp only [MI.two, MI.ofFun_val]
            have := hμval k
            by_cases hkj : k = j
            · subst hkj; simp only [if_true, hji, if_false] at this ⊢; omega
            · by_cases hki : k = i
              · subst hki; simp only [hkj, if_false, if_true] at this ⊢; omega
              · simp only [hkj, hki, if_false] at this ⊢
                rw [this, hαsupp k hki hkj]
          rw [hμeq] at hcoef
          exact absurd hcoef (not_lt.mpr (hC1 j i hji))
        · rcases Nat.lt_or_ge (α.1 i : ℕ) 2 with h1' | h2
          · -- α_i = 1: α = i j², δ = i³ j³, split {i³, j³}
            have hαi1 : (α.1 i : ℕ) = 1 := by omega
            have hαj2 : (α.1 j : ℕ) = 2 := by omega
            refine ⟨MI.pow n 3 i, MI.pow n 3 j, ?_, ?_, ?_⟩
            · funext k
              apply Fin.ext
              simp only [MI.add, MI.pow, MI.ofFun_val]
              have hck := hc k
              have hμk := hμval k
              by_cases hki : k = i
              · subst hki; simp only [if_true, hij, if_false] at hck hμk ⊢; omega
              · by_cases hkj : k = j
                · subst hkj; simp only [hki, if_false, if_true] at hck hμk ⊢; omega
                · simp only [hki, hkj, if_false] at hck hμk ⊢
                  rw [hαsupp k hki hkj] at hck hμk
                  omega
            · intro h
              have := congrArg (fun β : MI n 3 => (β.1 j : ℕ)) h
              simp only [MI.pow, MI.ofFun_val, hji, if_false] at this
              omega
            · intro h
              have := congrArg (fun β : MI n 3 => (β.1 i : ℕ)) h
              simp only [MI.pow, MI.ofFun_val, hij, if_false] at this
              omega
          · -- α_i = 2: α = i² j, the full demand is ≤ 0 by (C2)
            exfalso
            have hαi2 : (α.1 i : ℕ) = 2 := by omega
            have hαj1 : (α.1 j : ℕ) = 1 := by omega
            -- chain-rule monomials of the two sources
            have hμeq : μ = MI.two n 3 1 i j hij := by
              apply Subtype.ext
              funext k
              apply Fin.ext
              simp only [MI.two, MI.ofFun_val]
              have := hμval k
              by_cases hki : k = i
              · subst hki; simp only [if_true] at this ⊢; omega
              · by_cases hkj : k = j
                · subst hkj; simp only [hki, if_false, if_true] at this ⊢; omega
                · simp only [hki, hkj, if_false] at this ⊢
                  rw [this, hαsupp k hki hkj]
            have hci : chainEq n α i (MI.pow n 4 i) δ := by
              intro k
              have hck := hc k
              have hμk := hμval k
              simp only [MI.pow, MI.ofFun_val]
              by_cases hki : k = i
              · subst hki; simp only [if_true, hij, if_false] at hck hμk ⊢; omega
              · by_cases hkj : k = j
                · subst hkj; simp only [hki, if_false, if_true] at hck hμk ⊢; omega
                · simp only [hki, hkj, if_false] at hck hμk ⊢
                  rw [hαsupp k hki hkj] at hck hμk ⊢
                  omega
            have hcj : chainEq n α j μ δ := hc
            have hdem := demand_eq_sum n f δ α {i, j}
              (fun k hk => by
                by_contra hkn
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkn
                have := hαsupp k hkn.1 hkn.2
                omega)
              (fun k => if k = i then MI.pow n 4 i else μ)
              (fun k hk => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hk
                rcases hk with rfl | rfl
                · simp only [if_true]; exact hci
                · simp only [hji, if_false]; exact hcj)
            rw [Finset.sum_pair hij] at hdem
            simp only [if_true, hji, if_false] at hdem
            rw [hdem, hαi2, hαj1, hμeq] at hpos
            have hm := MI.mult_pos n 3 α
            have hC := hC2 i j hij
            push_cast at hpos
            nlinarith
    · exact ⟨MI.shift n α j i hij hαj, MI.sub1 n μ i hμi,
        MI.add_shift_sub1 n α j i hij hαj μ hμi δ hc, MI.shift_ne n α j i hij hαj, hbad⟩

/-- **Theorem 1 (sufficiency), general form.** Every syntactic quartic protocol satisfying (C1),(C2)
has a non-negative non-autocatalytic weighted realisation of its cubed system. -/
theorem exists_nap_realizing_of_C1C2 (f : QuarticPP n)
    (hC1 : ∀ (y k : Fin n) (h : y ≠ k), f.coef y (MI.two n 3 1 y k h) ≤ 0)
    (hC2 : ∀ (y k : Fin n) (h : y ≠ k),
      f.coef k (MI.two n 3 1 y k h) + 2 * f.coef y (MI.pow n 4 y) ≤ 0) :
    ∃ w : WProtocol (MI n 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift n 3) w (demand n f) :=
  exists_nap_realizing_of_splittable n f (demand_splittable_of_C1C2 n f hC1 hC2)

end NAPTransport
end Ripple

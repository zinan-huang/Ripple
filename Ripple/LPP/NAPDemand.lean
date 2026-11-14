/-
  Ripple.LPP.NAPDemand — the demand table of a syntactic quartic protocol and Lemma 2 of
  the PP-to-NAP write-up.

  A `QuarticPP n` is a degree-4 field on `n` species given by its coefficient table
  `coef j μ` (coefficient of the monomial `x^μ`, `|μ| = 4`, in `ẋ_j`), conservative
  (`Σ_j coef j μ = 0`) and syntactic (`coef j μ < 0 → μ_j > 0`). Cubing it, the chain rule gives
  `v̇_α = mult α · Σ_j α_j x^{α − e_j} ẋ_j`, so the coefficient of `x^δ` (`|δ| = 6`) in `v̇_α` is
  `demand f δ α = mult α · Σ_j Σ_μ [α_j > 0 ∧ (α − e_j) + μ = δ] α_j · coef j μ`.

  Lemma 2 of the write-up, formalised:
  * `demand_sum_zero`   (h0): `Σ_α demand f δ α = 0` for every `δ`;
  * `demand_neg_half`   (h1): `demand f δ α < 0 → α` is a half of `δ`.
  Hence (`exists_nap_realizing_of_splittable`) for any quartic protocol whose demand table is
  per-monomial splittable (hypothesis (h2) = criterion (2) of Theorem 1) the cubed system has a
  non-autocatalytic realisation — the general Theorem 1 (sufficiency) with the pushforward computed
  from the field. The derivation of (h2) from (C1),(C2) is the classification of §2 and is not in
  this file.
-/

import Ripple.LPP.NAPTransport

namespace Ripple
namespace NAPTransport

open Finset

variable (n : ℕ)

/-- A syntactic quartic protocol field, as a coefficient table on weight-4 multi-indices. -/
structure QuarticPP where
  coef : Fin n → MI n 4 → ℚ
  conservative : ∀ μ, ∑ j, coef j μ = 0
  sign : ∀ j μ, coef j μ < 0 → 0 < (μ.1 j : ℕ)

/-- `(α − e_j) + μ = δ` as natural-number exponent vectors. -/
def chainEq (α : MI n 3) (j : Fin n) (μ : MI n 4) (δ : Fin n → Fin (2 * 3 + 1)) : Prop :=
  ∀ k, (α.1 k : ℕ) - (if k = j then 1 else 0) + (μ.1 k : ℕ) = (δ k : ℕ)

instance (α : MI n 3) (j : Fin n) (μ : MI n 4) (δ : Fin n → Fin (2 * 3 + 1)) :
    Decidable (chainEq n α j μ δ) := by unfold chainEq; infer_instance

/-- The demand table (coefficient of `x^δ` in `v̇_α`) of the cubed quartic protocol. -/
noncomputable def demand (f : QuarticPP n) (δ : Fin n → Fin (2 * 3 + 1)) (α : MI n 3) : ℚ :=
  MI.mult n 3 α * ∑ j, ∑ μ, if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
    then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0

/-! ### (h1): negative demands sit at halves -/

/-- An entry of a weight-`m` multi-index is at most `m`. -/
theorem MI.entry_le {m : ℕ} (μ : MI n m) (k : Fin n) : (μ.1 k : ℕ) ≤ m := by
  have h := Finset.single_le_sum (f := fun i => (μ.1 i : ℕ)) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ k)
  have h2 := μ.2
  simp only at h
  omega

/-- Two distinct entries of a weight-`m` multi-index sum to at most `m`. -/
theorem MI.two_entries_le {m : ℕ} (μ : MI n m) {j k : Fin n} (hjk : j ≠ k) :
    (μ.1 j : ℕ) + (μ.1 k : ℕ) ≤ m := by
  have hsum := μ.2
  have h1 := Finset.add_sum_erase Finset.univ (fun i => (μ.1 i : ℕ)) (Finset.mem_univ j)
  have h2 : (μ.1 k : ℕ) ≤ ∑ i ∈ Finset.univ.erase j, (μ.1 i : ℕ) :=
    Finset.single_le_sum (f := fun i => (μ.1 i : ℕ)) (fun i _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩)
  simp only at h1
  omega

/-- `μ − e_j` as a weight-3 multi-index, when `μ_j > 0`. -/
def MI.sub1 (μ : MI n 4) (j : Fin n) (hj : 0 < (μ.1 j : ℕ)) : MI n 3 :=
  ⟨fun k => ⟨(μ.1 k : ℕ) - (if k = j then 1 else 0), by
      by_cases hk : k = j
      · subst hk
        have := MI.entry_le n μ k
        simp only [if_true]
        omega
      · have := MI.two_entries_le n μ hk
        simp only [hk, if_false]
        omega⟩,
    by
      have hsum := μ.2
      have hle : ∀ k ∈ Finset.univ, (if k = j then 1 else 0) ≤ (μ.1 k : ℕ) := by
        intro k _
        split_ifs with hk
        · subst hk; exact hj
        · exact Nat.zero_le _
      simp only
      rw [Finset.sum_tsub_distrib Finset.univ hle, hsum, Finset.sum_ite_eq' Finset.univ j]
      simp⟩

theorem MI.add_sub1 (α : MI n 3) (j : Fin n) (μ : MI n 4) (hj : 0 < (μ.1 j : ℕ))
    (δ : Fin n → Fin (2 * 3 + 1)) (hα : 0 < (α.1 j : ℕ)) (hc : chainEq n α j μ δ) :
    MI.add n 3 α (MI.sub1 n μ j hj) = δ := by
  funext k
  apply Fin.ext
  simp only [MI.add, MI.sub1]
  have := hc k
  by_cases hk : k = j
  · subst hk
    simp only [if_true] at this ⊢
    omega
  · simp only [hk, if_false] at this ⊢
    omega

/-- (h1): a negative demand at `(δ, α)` forces `α` to be a half of `δ`. -/
theorem demand_neg_half (f : QuarticPP n) (δ : Fin n → Fin (2 * 3 + 1)) (α : MI n 3)
    (h : demand n f δ α < 0) : ∃ γ, MI.add n 3 α γ = δ := by
  unfold demand at h
  have hmult := MI.mult_pos n 3 α
  have hsum : ∑ j, ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonneg hmult.le hcon
    linarith
  have hj' : ∃ j, ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) < 0 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hsum (not_lt.mpr (Finset.sum_nonneg fun j _ => hcon j))
  obtain ⟨j, hj⟩ := hj'
  have hμ' : ∃ μ, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) < 0 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hj (not_lt.mpr (Finset.sum_nonneg fun μ _ => hcon μ))
  obtain ⟨μ, hμ⟩ := hμ'
  split_ifs at hμ with hc
  · have hcoef : f.coef j μ < 0 := by
      have hαj : (0 : ℚ) < ((α.1 j : ℕ) : ℚ) := by exact_mod_cast hc.1
      by_contra hcon
      rw [not_lt] at hcon
      have := mul_nonneg hαj.le hcon
      linarith
    have hμj := f.sign j μ hcoef
    exact ⟨MI.sub1 n μ j hμj, MI.add_sub1 n α j μ hμj δ hc.1 hc.2⟩
  · exact absurd hμ (lt_irrefl 0)

/-! ### (h0): conservation of the demand table -/

/-- The multinomial weight `6 / ∏ ν_k!` of a natural exponent vector. -/
noncomputable def W (ν : Fin n → ℕ) : ℚ := 6 / ∏ k, ((ν k).factorial : ℚ)

theorem MI.mult_eq_W (α : MI n 3) : MI.mult n 3 α = W n (fun k => (α.1 k : ℕ)) := by
  unfold MI.mult W
  norm_num [Nat.factorial]

/-- The derivative identity behind `Σ_α mult α · α_j x^{α−e_j} = 3 (Σ x)^2`:
`W(ν + e_j) · (ν_j + 1) = W(ν)`. -/
theorem W_succ_mul (ν : Fin n → ℕ) (j : Fin n) :
    W n (fun k => ν k + if k = j then 1 else 0) * ((ν j + 1 : ℕ) : ℚ) = W n ν := by
  unfold W
  have h1 : ∏ k, (((ν k + if k = j then 1 else 0)).factorial : ℚ)
      = ((ν j + 1).factorial : ℚ) * ∏ k ∈ Finset.univ.erase j, ((ν k).factorial : ℚ) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [this]
  have h2 : ∏ k, ((ν k).factorial : ℚ)
      = ((ν j).factorial : ℚ) * ∏ k ∈ Finset.univ.erase j, ((ν k).factorial : ℚ) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  rw [h1, h2, Nat.factorial_succ]
  have hp : (0 : ℚ) < ∏ k ∈ Finset.univ.erase j, ((ν k).factorial : ℚ) :=
    Finset.prod_pos fun k _ => by exact_mod_cast Nat.factorial_pos _
  have hf : (0 : ℚ) < ((ν j).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp

/-- Validity of `ν = δ − μ` as the exponent vector of a weight-2 monomial. -/
def validDiff (δ : Fin n → Fin (2 * 3 + 1)) (μ : MI n 4) : Prop :=
  (∀ k, (μ.1 k : ℕ) ≤ (δ k : ℕ)) ∧ ∑ k, ((δ k : ℕ) - (μ.1 k : ℕ)) = 2

instance (δ : Fin n → Fin (2 * 3 + 1)) (μ : MI n 4) : Decidable (validDiff n δ μ) := by
  unfold validDiff; infer_instance

/-- The chain-rule partner `α₀ = (δ − μ) + e_j` as a weight-3 multi-index. -/
def partner (δ : Fin n → Fin (2 * 3 + 1)) (μ : MI n 4) (j : Fin n) (hv : validDiff n δ μ) :
    MI n 3 :=
  ⟨fun k => ⟨(δ k : ℕ) - (μ.1 k : ℕ) + (if k = j then 1 else 0), by
      have hk : (δ k : ℕ) - (μ.1 k : ℕ) ≤ ∑ i, ((δ i : ℕ) - (μ.1 i : ℕ)) :=
        Finset.single_le_sum (f := fun i => (δ i : ℕ) - (μ.1 i : ℕ)) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ k)
      rw [hv.2] at hk
      split_ifs <;> omega⟩,
    by
      simp only
      rw [Finset.sum_add_distrib, hv.2, Finset.sum_ite_eq' Finset.univ j]
      simp⟩

theorem chainEq_iff_partner (δ : Fin n → Fin (2 * 3 + 1)) (μ : MI n 4) (j : Fin n)
    (hv : validDiff n δ μ) (α : MI n 3) :
    (0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ) ↔ α = partner n δ μ j hv := by
  constructor
  · rintro ⟨hj, hc⟩
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [partner]
    have h1 := hc k
    have h2 := hv.1 k
    by_cases hk : k = j
    · subst hk
      simp only [if_true] at h1 ⊢
      omega
    · simp only [hk, if_false] at h1 ⊢
      omega
  · intro h
    subst h
    constructor
    · simp [partner]
    · intro k
      simp only [partner]
      have h2 := hv.1 k
      by_cases hk : k = j
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        omega

theorem chainEq_validDiff (δ : Fin n → Fin (2 * 3 + 1)) (μ : MI n 4) (j : Fin n) (α : MI n 3)
    (hj : 0 < (α.1 j : ℕ)) (hc : chainEq n α j μ δ) : validDiff n δ μ := by
  constructor
  · intro k
    have := hc k
    split_ifs at this <;> omega
  · have hα := α.2
    have : ∀ k, (δ k : ℕ) - (μ.1 k : ℕ) = (α.1 k : ℕ) - (if k = j then 1 else 0) := by
      intro k
      have := hc k
      split_ifs at this ⊢ <;> omega
    simp only [this]
    have hle : ∀ k ∈ Finset.univ, (if k = j then 1 else 0) ≤ (α.1 k : ℕ) := by
      intro k _
      split_ifs with hk
      · subst hk; exact hj
      · exact Nat.zero_le _
    rw [Finset.sum_tsub_distrib Finset.univ hle, hα, Finset.sum_ite_eq' Finset.univ j]
    simp

/-- The inner chain-rule sum is independent of `j`: it equals `W(δ − μ)` when `δ − μ` is a valid
weight-2 vector, and `0` otherwise. -/
theorem sum_mult_chain (δ : Fin n → Fin (2 * 3 + 1)) (μ : MI n 4) (j : Fin n) :
    ∑ α : MI n 3, (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
        then MI.mult n 3 α * ((α.1 j : ℕ) : ℚ) else 0)
      = if validDiff n δ μ then W n (fun k => (δ k : ℕ) - (μ.1 k : ℕ)) else 0 := by
  by_cases hv : validDiff n δ μ
  · rw [if_pos hv]
    rw [Finset.sum_eq_single (partner n δ μ j hv)]
    · rw [if_pos ((chainEq_iff_partner n δ μ j hv _).mpr rfl)]
      rw [MI.mult_eq_W]
      have := W_succ_mul n (fun k => (δ k : ℕ) - (μ.1 k : ℕ)) j
      simp only [partner] at this ⊢
      (convert this using 2) <;> (try push_cast) <;> (try ring)
    · intro α _ hα
      rw [if_neg]
      intro h
      exact hα ((chainEq_iff_partner n δ μ j hv α).mp h)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro α _
    rw [if_neg]
    intro h
    exact hv (chainEq_validDiff n δ μ j α h.1 h.2)

/-- (h0): the demand table is conservative. -/
theorem demand_sum_zero (f : QuarticPP n) (δ : Fin n → Fin (2 * 3 + 1)) :
    ∑ α, demand n f δ α = 0 := by
  unfold demand
  have hterm : ∀ (α : MI n 3) (j : Fin n) (μ : MI n 4),
      MI.mult n 3 α * (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
        then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0)
      = (if 0 < (α.1 j : ℕ) ∧ chainEq n α j μ δ
        then MI.mult n 3 α * ((α.1 j : ℕ) : ℚ) else 0) * f.coef j μ := by
    intro α j μ
    split_ifs <;> ring
  simp only [Finset.mul_sum, hterm]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (MI n 3))) (t := (Finset.univ : Finset (MI n 4)))]
  simp only [← Finset.sum_mul, sum_mult_chain]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro μ _
  rw [← Finset.mul_sum, f.conservative μ, mul_zero]

/-! ### Theorem 1 (sufficiency) for a quartic protocol with splittable demand -/

/-- For a syntactic quartic protocol whose demand table is per-monomial splittable, the cubed
system has a non-negative non-autocatalytic weighted realisation. -/
theorem exists_nap_realizing_of_splittable (f : QuarticPP n)
    (h2 : ∀ δ α, 0 < demand n f δ α → ∃ β γ, MI.add n 3 β γ = δ ∧ β ≠ α ∧ γ ≠ α) :
    ∃ w : WProtocol (MI n 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift n 3) w (demand n f) :=
  exists_nap_realizing_veronese n 3 (demand n f) (demand_sum_zero n f) (demand_neg_half n f) h2

end NAPTransport
end Ripple

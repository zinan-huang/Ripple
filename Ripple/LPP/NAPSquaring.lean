/-
  Ripple.LPP.NAPSquaring — Theorem 3 of the PP-to-NAP write-up (§5): the r-trick and squaring.

  Part A (Theorem 1 for `m = 2`). A `CubicPP n` is a syntactic conservative degree-3 field
  (coefficient table on weight-3 indices). Squaring it, the coefficient of `x^δ` (`|δ| = 4`) in
  `v̇_α` (`|α| = 2`) is `demandSq f δ α = mult α · Σ_j Σ_μ [α_j > 0 ∧ (α − e_j) + μ = δ] α_j coef j μ`.
  * `demandSq_sum_zero` (h0), `demandSq_neg_half` (h1);
  * `demandSq_splittable_of_C1C2`: (C1) `[y²k] f_y ≤ 0` and (C2) `[y²k] f_k + [y³] f_y ≤ 0` for
    `y ≠ k` give per-monomial splittability (h2);
  * `C1_of_realizesSq`, `C2_of_realizesSq`: conversely, a non-negative NAP realisation forces (C1),
    (C2) (the monomial `y³k` splits only as `y² + yk`);
  * `exists_nap_realizing_sq_iff`: realisable ⟺ (C1) ∧ (C2).

  Part B (the r-trick). For a syntactic quadratic PP `g`, a shrunk set `J` and `λ`, the cubic field
  `r · g` on `n + 1` species has coefficient table `liftCoefR` (slack exponent `1`):
    `coef' 0 (r ⊕ μ) = (1 − λ) λ^{−μ(J)} Σ_{j∈J} g.coef j μ`,
    `coef' j.succ (r ⊕ μ) = [j ∈ J ? λ : 1] λ^{−μ(J)} g.coef j μ`.
  * `squaring_iff` (**Theorem 3**): its squared system has a non-negative NAP realisation iff
    `Σ_{j∈J} [y²] g_j ≤ 0` for every species `y`.
-/

import Ripple.LPP.NAPPipelineSet

namespace Ripple
namespace NAPTransport

open Finset

variable (n : ℕ)

/-! ## Part A: Theorem 1 for the squaring (`m = 2`) -/

/-- A syntactic cubic protocol field, as a coefficient table on weight-3 multi-indices. -/
structure CubicPP where
  coef : Fin n → MI n 3 → ℚ
  conservative : ∀ μ, ∑ j, coef j μ = 0
  sign : ∀ j μ, coef j μ < 0 → 0 < (μ.1 j : ℕ)

/-- `(α − e_j) + μ = δ` for `|α| = 2`, `|μ| = 3`. -/
def chainEqSq (α : MI n 2) (j : Fin n) (μ : MI n 3) (δ : Fin n → Fin (2 * 2 + 1)) : Prop :=
  ∀ k, (α.1 k : ℕ) - (if k = j then 1 else 0) + (μ.1 k : ℕ) = (δ k : ℕ)

instance (α : MI n 2) (j : Fin n) (μ : MI n 3) (δ : Fin n → Fin (2 * 2 + 1)) :
    Decidable (chainEqSq n α j μ δ) := by unfold chainEqSq; infer_instance

/-- The demand table of the squared cubic protocol. -/
noncomputable def demandSq (f : CubicPP n) (δ : Fin n → Fin (2 * 2 + 1)) (α : MI n 2) : ℚ :=
  MI.mult n 2 α * ∑ j, ∑ μ, if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
    then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0

/-- `μ − e_j` as a weight-2 multi-index, when `μ_j > 0`. -/
def MI.sub1Sq (μ : MI n 3) (j : Fin n) (hj : 0 < (μ.1 j : ℕ)) : MI n 2 :=
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

theorem MI.add_sub1Sq (α : MI n 2) (j : Fin n) (μ : MI n 3) (hj : 0 < (μ.1 j : ℕ))
    (δ : Fin n → Fin (2 * 2 + 1)) (hα : 0 < (α.1 j : ℕ)) (hc : chainEqSq n α j μ δ) :
    MI.add n 2 α (MI.sub1Sq n μ j hj) = δ := by
  funext k
  apply Fin.ext
  simp only [MI.add, MI.sub1Sq]
  have := hc k
  by_cases hk : k = j
  · subst hk
    simp only [if_true] at this ⊢
    omega
  · simp only [hk, if_false] at this ⊢
    omega

/-- (h1) for the squaring. -/
theorem demandSq_neg_half (f : CubicPP n) (δ : Fin n → Fin (2 * 2 + 1)) (α : MI n 2)
    (h : demandSq n f δ α < 0) : ∃ γ, MI.add n 2 α γ = δ := by
  unfold demandSq at h
  have hmult := MI.mult_pos n 2 α
  have hsum : ∑ j, ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonneg hmult.le hcon
    linarith
  have hj' : ∃ j, ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) < 0 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hsum (not_lt.mpr (Finset.sum_nonneg fun j _ => hcon j))
  obtain ⟨j, hj⟩ := hj'
  have hμ' : ∃ μ, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
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
    exact ⟨MI.sub1Sq n μ j hμj, MI.add_sub1Sq n α j μ hμj δ hc.1 hc.2⟩
  · exact absurd hμ (lt_irrefl 0)

/-- The multinomial weight `2 / ∏ ν_k!`. -/
noncomputable def WSq (ν : Fin n → ℕ) : ℚ := 2 / ∏ k, ((ν k).factorial : ℚ)

theorem MI.mult_eq_WSq (α : MI n 2) : MI.mult n 2 α = WSq n (fun k => (α.1 k : ℕ)) := by
  unfold MI.mult WSq
  norm_num [Nat.factorial]

theorem WSq_succ_mul (ν : Fin n → ℕ) (j : Fin n) :
    WSq n (fun k => ν k + if k = j then 1 else 0) * ((ν j + 1 : ℕ) : ℚ) = WSq n ν := by
  unfold WSq
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

/-- `δ − μ` is a weight-1 exponent vector. -/
def validDiffSq (δ : Fin n → Fin (2 * 2 + 1)) (μ : MI n 3) : Prop :=
  (∀ k, (μ.1 k : ℕ) ≤ (δ k : ℕ)) ∧ ∑ k, ((δ k : ℕ) - (μ.1 k : ℕ)) = 1

instance (δ : Fin n → Fin (2 * 2 + 1)) (μ : MI n 3) : Decidable (validDiffSq n δ μ) := by
  unfold validDiffSq; infer_instance

/-- The chain-rule partner `(δ − μ) + e_j` as a weight-2 multi-index. -/
def partnerSq (δ : Fin n → Fin (2 * 2 + 1)) (μ : MI n 3) (j : Fin n) (hv : validDiffSq n δ μ) :
    MI n 2 :=
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

theorem chainEqSq_iff_partner (δ : Fin n → Fin (2 * 2 + 1)) (μ : MI n 3) (j : Fin n)
    (hv : validDiffSq n δ μ) (α : MI n 2) :
    (0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ) ↔ α = partnerSq n δ μ j hv := by
  constructor
  · rintro ⟨hj, hc⟩
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [partnerSq]
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
    · simp [partnerSq]
    · intro k
      simp only [partnerSq]
      have h2 := hv.1 k
      by_cases hk : k = j
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        omega

theorem chainEqSq_validDiff (δ : Fin n → Fin (2 * 2 + 1)) (μ : MI n 3) (j : Fin n) (α : MI n 2)
    (hj : 0 < (α.1 j : ℕ)) (hc : chainEqSq n α j μ δ) : validDiffSq n δ μ := by
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

theorem sum_mult_chainSq (δ : Fin n → Fin (2 * 2 + 1)) (μ : MI n 3) (j : Fin n) :
    ∑ α : MI n 2, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
        then MI.mult n 2 α * ((α.1 j : ℕ) : ℚ) else 0)
      = if validDiffSq n δ μ then WSq n (fun k => (δ k : ℕ) - (μ.1 k : ℕ)) else 0 := by
  by_cases hv : validDiffSq n δ μ
  · rw [if_pos hv]
    rw [Finset.sum_eq_single (partnerSq n δ μ j hv)]
    · rw [if_pos ((chainEqSq_iff_partner n δ μ j hv _).mpr rfl)]
      rw [MI.mult_eq_WSq]
      have := WSq_succ_mul n (fun k => (δ k : ℕ) - (μ.1 k : ℕ)) j
      simp only [partnerSq] at this ⊢
      convert this using 2
    · intro α _ hα
      rw [if_neg]
      intro h
      exact hα ((chainEqSq_iff_partner n δ μ j hv α).mp h)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro α _
    rw [if_neg]
    intro h
    exact hv (chainEqSq_validDiff n δ μ j α h.1 h.2)

/-- (h0) for the squaring. -/
theorem demandSq_sum_zero (f : CubicPP n) (δ : Fin n → Fin (2 * 2 + 1)) :
    ∑ α, demandSq n f δ α = 0 := by
  unfold demandSq
  have hterm : ∀ (α : MI n 2) (j : Fin n) (μ : MI n 3),
      MI.mult n 2 α * (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
        then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0)
      = (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
        then MI.mult n 2 α * ((α.1 j : ℕ) : ℚ) else 0) * f.coef j μ := by
    intro α j μ
    split_ifs <;> ring
  simp only [Finset.mul_sum, hterm]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (MI n 2)))
    (t := (Finset.univ : Finset (MI n 3)))]
  simp only [← Finset.sum_mul, sum_mult_chainSq]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro μ _
  rw [← Finset.mul_sum, f.conservative μ, mul_zero]

/-! ### (C1),(C2) ⇒ (h2) for the squaring -/

theorem coefSq_pow_nonpos (f : CubicPP n) (y : Fin n) : f.coef y (MI.pow n 3 y) ≤ 0 := by
  have hc := f.conservative (MI.pow n 3 y)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y)] at hc
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase y, f.coef j (MI.pow n 3 y) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjy : j ≠ y := (Finset.mem_erase.mp hj).1
    by_contra hneg
    rw [not_le] at hneg
    have := f.sign j _ hneg
    simp [MI.pow, hjy] at this
  linarith

theorem demandSq_pos_term (f : CubicPP n) (δ : Fin n → Fin (2 * 2 + 1)) (α : MI n 2)
    (h : 0 < demandSq n f δ α) :
    ∃ j μ, 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ ∧ 0 < f.coef j μ := by
  unfold demandSq at h
  have hmult := MI.mult_pos n 2 α
  have hsum : 0 < ∑ j, ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) := by
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonpos_of_nonneg_of_nonpos hmult.le hcon
    linarith
  have hj' : ∃ j, 0 < ∑ μ, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
      then ((α.1 j : ℕ) : ℚ) * f.coef j μ else 0) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact absurd hsum (not_lt.mpr (Finset.sum_nonpos fun j _ => hcon j))
  obtain ⟨j, hj⟩ := hj'
  have hμ' : ∃ μ, 0 < (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ
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

/-- `α − e_j + e_i` as a weight-2 multi-index. -/
def MI.shiftSq (α : MI n 2) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ)) : MI n 2 :=
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

theorem MI.shiftSq_ne (α : MI n 2) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ)) :
    MI.shiftSq n α j i hij hαj ≠ α := by
  intro h
  have := congrArg (fun β : MI n 2 => (β.1 i : ℕ)) h
  simp only [MI.shiftSq, MI.ofFun_val, hij, if_false, if_true] at this
  omega

theorem MI.add_shiftSq_sub1Sq (α : MI n 2) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ))
    (μ : MI n 3) (hμi : 0 < (μ.1 i : ℕ)) (δ : Fin n → Fin (2 * 2 + 1))
    (hc : chainEqSq n α j μ δ) :
    MI.add n 2 (MI.shiftSq n α j i hij hαj) (MI.sub1Sq n μ i hμi) = δ := by
  funext k
  apply Fin.ext
  simp only [MI.add, MI.shiftSq, MI.sub1Sq, MI.ofFun_val]
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

theorem MI.sub1Sq_inj (μ : MI n 3) (i i' : Fin n) (hi : 0 < (μ.1 i : ℕ))
    (hi' : 0 < (μ.1 i' : ℕ)) (h : MI.sub1Sq n μ i hi = MI.sub1Sq n μ i' hi') : i = i' := by
  by_contra hne
  have := congrArg (fun β : MI n 2 => (β.1 i : ℕ)) h
  simp only [MI.sub1Sq, if_true, hne, if_false] at this
  omega

theorem chainEqSq_unique (α : MI n 2) (j : Fin n) (μ μ' : MI n 3) (δ : Fin n → Fin (2 * 2 + 1))
    (h : chainEqSq n α j μ δ) (h' : chainEqSq n α j μ' δ) : μ = μ' := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  have h1 := h k
  have h2 := h' k
  omega

theorem demandSq_eq_sum (f : CubicPP n) (δ : Fin n → Fin (2 * 2 + 1)) (α : MI n 2)
    (S : Finset (Fin n)) (hS : ∀ k, 0 < (α.1 k : ℕ) → k ∈ S)
    (m : Fin n → MI n 3) (hm : ∀ k ∈ S, chainEqSq n α k (m k) δ) :
    demandSq n f δ α = MI.mult n 2 α * ∑ k ∈ S, ((α.1 k : ℕ) : ℚ) * f.coef k (m k) := by
  unfold demandSq
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
        exact hμ (chainEqSq_unique n α k μ (m k) δ hc (hm k hk))
      · intro h; exact absurd (Finset.mem_univ _) h
    · have h0 : (α.1 k : ℕ) = 0 := by omega
      simp [h0]
  · intro k _ hk
    have h0 : (α.1 k : ℕ) = 0 := by
      by_contra hne
      exact hk (hS k (Nat.pos_of_ne_zero hne))
    simp [h0]

/-- The weight of a multi-index supported on `{y, k}`. -/
theorem MI.weight_pair {m : ℕ} (a : MI n m) {y k : Fin n} (h : y ≠ k)
    (hz : ∀ l, l ≠ y → l ≠ k → (a.1 l : ℕ) = 0) : (a.1 y : ℕ) + (a.1 k : ℕ) = m := by
  have hw := a.2
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ k⟩)] at hw
  have : ∑ l ∈ (Finset.univ.erase y).erase k, (a.1 l : ℕ) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    exact hz l (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1 (Finset.mem_erase.mp hl).1
  omega

/-- (C1),(C2) ⇒ per-monomial splittability of the squared demand table. -/
theorem demandSq_splittable_of_C1C2 (f : CubicPP n)
    (hC1 : ∀ (y k : Fin n) (h : y ≠ k), f.coef y (MI.two n 2 1 y k h) ≤ 0)
    (hC2 : ∀ (y k : Fin n) (h : y ≠ k),
      f.coef k (MI.two n 2 1 y k h) + f.coef y (MI.pow n 3 y) ≤ 0)
    (δ : Fin n → Fin (2 * 2 + 1)) (α : MI n 2) (hpos : 0 < demandSq n f δ α) :
    ∃ β γ, MI.add n 2 β γ = δ ∧ β ≠ α ∧ γ ≠ α := by
  obtain ⟨j, μ, hαj, hc, hcoef⟩ := demandSq_pos_term n f δ α hpos
  by_cases hμ : ∀ i, i ≠ j → (μ.1 i : ℕ) = 0
  · -- μ = j³
    exfalso
    have hμj : (μ.1 j : ℕ) = 3 := by
      have hw := μ.2
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)] at hw
      have : ∑ i ∈ Finset.univ.erase j, (μ.1 i : ℕ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hμ i (Finset.mem_erase.mp hi).1
      omega
    have hμeq : μ = MI.pow n 3 j := by
      apply Subtype.ext
      funext k
      apply Fin.ext
      simp only [MI.pow, MI.ofFun_val]
      by_cases hk : k = j
      · subst hk; simp [hμj]
      · simp [hk, hμ k hk]
    rw [hμeq] at hcoef
    exact absurd hcoef (not_lt.mpr (coefSq_pow_nonpos n f j))
  · simp only [not_forall] at hμ
    obtain ⟨i, hij, hμi0⟩ := hμ
    have hμi : 0 < (μ.1 i : ℕ) := Nat.pos_of_ne_zero hμi0
    by_cases hbad : MI.sub1Sq n μ i hμi = α
    · by_cases hi' : ∃ i', i' ≠ j ∧ i' ≠ i ∧ 0 < (μ.1 i' : ℕ)
      · obtain ⟨i', hi'j, hi'i, hμi'⟩ := hi'
        refine ⟨MI.shiftSq n α j i' hi'j hαj, MI.sub1Sq n μ i' hμi',
          MI.add_shiftSq_sub1Sq n α j i' hi'j hαj μ hμi' δ hc, MI.shiftSq_ne n α j i' hi'j hαj, ?_⟩
        intro h
        exact hi'i (MI.sub1Sq_inj n μ i' i hμi' hμi (h.trans hbad.symm))
      · simp only [not_exists, not_and, not_lt] at hi'
        have hsupp : ∀ k, k ≠ i → k ≠ j → (μ.1 k : ℕ) = 0 := by
          intro k hki hkj
          have := hi' k hkj hki
          omega
        have hαval : ∀ k, (α.1 k : ℕ) = (μ.1 k : ℕ) - (if k = i then 1 else 0) := by
          intro k
          have := congrArg (fun β : MI n 2 => (β.1 k : ℕ)) hbad
          simp only [MI.sub1Sq] at this
          omega
        have hαsupp : ∀ k, k ≠ i → k ≠ j → (α.1 k : ℕ) = 0 := by
          intro k hki hkj
          rw [hαval k, hsupp k hki hkj]
          simp
        have hαw : (α.1 i : ℕ) + (α.1 j : ℕ) = 2 := MI.weight_pair n α hij hαsupp
        have hμval : ∀ k, (μ.1 k : ℕ) = (α.1 k : ℕ) + (if k = i then 1 else 0) := by
          intro k
          have h1 := hαval k
          by_cases hk : k = i
          · subst hk; simp only [if_true] at h1 ⊢; omega
          · simp only [hk, if_false] at h1 ⊢; omega
        have hji : j ≠ i := Ne.symm hij
        rcases Nat.lt_or_ge (α.1 i : ℕ) 1 with h0 | h1
        · -- α_i = 0: α = j², μ = j² i, contradiction with (C1)
          exfalso
          have hμeq : μ = MI.two n 2 1 j i hji := by
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
        · -- α_i = 1 = α_j: α = ij, δ = i³ j, the full demand is ≤ 0 by (C2)
          exfalso
          have hαi1 : (α.1 i : ℕ) = 1 := by omega
          have hαj1 : (α.1 j : ℕ) = 1 := by omega
          have hμeq : μ = MI.two n 2 1 i j hij := by
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
          have hci : chainEqSq n α i (MI.pow n 3 i) δ := by
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
          have hdem := demandSq_eq_sum n f δ α {i, j}
            (fun k hk => by
              by_contra hkn
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkn
              have := hαsupp k hkn.1 hkn.2
              omega)
            (fun k => if k = i then MI.pow n 3 i else μ)
            (fun k hk => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl
              · simp only [if_true]; exact hci
              · simp only [hji, if_false]; exact hc)
          rw [Finset.sum_pair hij] at hdem
          simp only [if_true, hji, if_false] at hdem
          rw [hdem, hαi1, hαj1, hμeq] at hpos
          have hm := MI.mult_pos n 2 α
          have hC := hC2 i j hij
          push_cast at hpos
          nlinarith
    · exact ⟨MI.shiftSq n α j i hij hαj, MI.sub1Sq n μ i hμi,
        MI.add_shiftSq_sub1Sq n α j i hij hαj μ hμi δ hc, MI.shiftSq_ne n α j i hij hαj, hbad⟩

/-! ### Necessity: a NAP realisation forces (C1),(C2) -/

/-- The monomial `y³k = y² + yk`. -/
def deltaYK (y k : Fin n) (h : y ≠ k) : Fin n → Fin (2 * 2 + 1) :=
  MI.add n 2 (MI.pow n 2 y) (MI.two n 1 1 y k h)

theorem deltaYK_val (y k : Fin n) (h : y ≠ k) (l : Fin n) :
    (deltaYK n y k h l : ℕ) = (if l = y then 3 else if l = k then 1 else 0) := by
  simp only [deltaYK, MI.add, MI.pow, MI.two, MI.ofFun_val]
  by_cases hly : l = y
  · subst hly; simp
  · by_cases hlk : l = k
    · subst hlk; simp [hly]
    · simp [hly, hlk]

theorem MI.eq_of_vals {m : ℕ} (a b : MI n m) (h : ∀ l, (a.1 l : ℕ) = (b.1 l : ℕ)) : a = b :=
  Subtype.ext (funext fun l => Fin.ext (h l))

/-- Every pair of weight-2 halves of `y³k` contains `y²` and `yk`. -/
theorem halves_deltaYK (y k : Fin n) (h : y ≠ k) (a b : MI n 2)
    (hab : MI.add n 2 a b = deltaYK n y k h) :
    (a = MI.pow n 2 y ∧ b = MI.two n 1 1 y k h) ∨ (a = MI.two n 1 1 y k h ∧ b = MI.pow n 2 y) := by
  have hv : ∀ l, (a.1 l : ℕ) + (b.1 l : ℕ) = (if l = y then 3 else if l = k then 1 else 0) := by
    intro l
    rw [← deltaYK_val n y k h l, ← hab]
    rfl
  have haz : ∀ l, l ≠ y → l ≠ k → (a.1 l : ℕ) = 0 := fun l hly hlk => by
    have := hv l
    simp only [hly, hlk, if_false] at this
    omega
  have hbz : ∀ l, l ≠ y → l ≠ k → (b.1 l : ℕ) = 0 := fun l hly hlk => by
    have := hv l
    simp only [hly, hlk, if_false] at this
    omega
  have hwa := MI.weight_pair n a h haz
  have hwb := MI.weight_pair n b h hbz
  have hk := hv k
  simp only [Ne.symm h, if_false, if_true] at hk
  have hpow : ∀ c : MI n 2, (c.1 k : ℕ) = 0 → (∀ l, l ≠ y → l ≠ k → (c.1 l : ℕ) = 0) →
      c = MI.pow n 2 y := by
    intro c hck hcz
    have hw := MI.weight_pair n c h hcz
    apply MI.eq_of_vals
    intro l
    simp only [MI.pow, MI.ofFun_val]
    by_cases hly : l = y
    · subst hly; simp only [if_true]; omega
    · simp only [hly, if_false]
      by_cases hlk : l = k
      · subst hlk; exact hck
      · exact hcz l hly hlk
  have htwo : ∀ c : MI n 2, (c.1 k : ℕ) = 1 → (∀ l, l ≠ y → l ≠ k → (c.1 l : ℕ) = 0) →
      c = MI.two n 1 1 y k h := by
    intro c hck hcz
    have hw := MI.weight_pair n c h hcz
    apply MI.eq_of_vals
    intro l
    simp only [MI.two, MI.ofFun_val]
    by_cases hly : l = y
    · subst hly; simp only [if_true]; omega
    · simp only [hly, if_false]
      by_cases hlk : l = k
      · subst hlk; simp only [if_true]; exact hck
      · simp only [hlk, if_false]; exact hcz l hly hlk
  rcases Nat.lt_or_ge (a.1 k : ℕ) 1 with h0 | h1
  · left
    exact ⟨hpow a (by omega) haz, htwo b (by omega) hbz⟩
  · right
    exact ⟨htwo a (by omega) haz, hpow b (by omega) hbz⟩

theorem C1_of_realizesSq (f : CubicPP n) (w : WProtocol (MI n 2)) (hw : ∀ sh, 0 ≤ w sh)
    (hnap : w.IsNAP) (hr : Realizes (veroneseLift n 2) w (demandSq n f)) :
    ∀ (y k : Fin n) (h : y ≠ k), f.coef y (MI.two n 2 1 y k h) ≤ 0 := by
  intro y k h
  have hle := realizes_nonpos_of_unique_pair (veroneseLift n 2) w (demandSq n f) hw hnap hr
    (deltaYK n y k h) (MI.pow n 2 y) (fun sh hsh => by
      rcases halves_deltaYK n y k h sh.1 sh.2.1 hsh with hh | hh
      · exact Or.inl hh.1
      · exact Or.inr hh.2)
  have hch : chainEqSq n (MI.pow n 2 y) y (MI.two n 2 1 y k h) (deltaYK n y k h) := by
    intro l
    rw [deltaYK_val]
    simp only [MI.pow, MI.two, MI.ofFun_val]
    by_cases hly : l = y
    · subst hly; simp
    · by_cases hlk : l = k
      · subst hlk; simp [hly]
      · simp [hly, hlk]
  have hdem := demandSq_eq_sum n f (deltaYK n y k h) (MI.pow n 2 y) {y}
    (fun l hl => by
      simp only [Finset.mem_singleton]
      by_contra hne
      simp [MI.pow, hne] at hl)
    (fun _ => MI.two n 2 1 y k h) (fun l hl => by
      rw [Finset.mem_singleton] at hl
      subst hl
      exact hch)
  rw [Finset.sum_singleton] at hdem
  rw [hdem] at hle
  have hm := MI.mult_pos n 2 (MI.pow n 2 y)
  have hy2 : ((MI.pow n 2 y).1 y : ℕ) = 2 := by simp [MI.pow]
  rw [hy2] at hle
  push_cast at hle
  nlinarith

theorem C2_of_realizesSq (f : CubicPP n) (w : WProtocol (MI n 2)) (hw : ∀ sh, 0 ≤ w sh)
    (hnap : w.IsNAP) (hr : Realizes (veroneseLift n 2) w (demandSq n f)) :
    ∀ (y k : Fin n) (h : y ≠ k),
      f.coef k (MI.two n 2 1 y k h) + f.coef y (MI.pow n 3 y) ≤ 0 := by
  intro y k h
  have hle := realizes_nonpos_of_unique_pair (veroneseLift n 2) w (demandSq n f) hw hnap hr
    (deltaYK n y k h) (MI.two n 1 1 y k h) (fun sh hsh => by
      rcases halves_deltaYK n y k h sh.1 sh.2.1 hsh with hh | hh
      · exact Or.inr hh.2
      · exact Or.inl hh.1)
  have hchy : chainEqSq n (MI.two n 1 1 y k h) y (MI.pow n 3 y) (deltaYK n y k h) := by
    intro l
    rw [deltaYK_val]
    simp only [MI.pow, MI.two, MI.ofFun_val]
    by_cases hly : l = y
    · subst hly; simp
    · by_cases hlk : l = k
      · subst hlk; simp [hly]
      · simp [hly, hlk]
  have hchk : chainEqSq n (MI.two n 1 1 y k h) k (MI.two n 2 1 y k h) (deltaYK n y k h) := by
    intro l
    rw [deltaYK_val]
    simp only [MI.two, MI.ofFun_val]
    by_cases hly : l = y
    · subst hly; simp [h]
    · by_cases hlk : l = k
      · subst hlk; simp [hly]
      · simp [hly, hlk]
  have hdem := demandSq_eq_sum n f (deltaYK n y k h) (MI.two n 1 1 y k h) {y, k}
    (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hne
      simp only [not_or] at hne
      simp [MI.two, hne.1, hne.2] at hl)
    (fun l => if l = y then MI.pow n 3 y else MI.two n 2 1 y k h) (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · simp only [if_true]; exact hchy
      · simp only [Ne.symm h, if_false]; exact hchk)
  rw [Finset.sum_pair h] at hdem
  simp only [if_true, Ne.symm h, if_false] at hdem
  rw [hdem] at hle
  have hm := MI.mult_pos n 2 (MI.two n 1 1 y k h)
  have hy1 : ((MI.two n 1 1 y k h).1 y : ℕ) = 1 := by simp [MI.two]
  have hk1 : ((MI.two n 1 1 y k h).1 k : ℕ) = 1 := by simp [MI.two, Ne.symm h]
  rw [hy1, hk1] at hle
  push_cast at hle
  nlinarith

/-- **Theorem 1 for the squaring.** The squared system of a syntactic cubic protocol has a
non-negative non-autocatalytic weighted realisation iff (C1) and (C2) hold. -/
theorem exists_nap_realizing_sq_iff (f : CubicPP n) :
    (∃ w : WProtocol (MI n 2), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
        Realizes (veroneseLift n 2) w (demandSq n f)) ↔
      ((∀ (y k : Fin n) (h : y ≠ k), f.coef y (MI.two n 2 1 y k h) ≤ 0) ∧
        (∀ (y k : Fin n) (h : y ≠ k),
          f.coef k (MI.two n 2 1 y k h) + f.coef y (MI.pow n 3 y) ≤ 0)) := by
  constructor
  · rintro ⟨w, hw, hnap, hr⟩
    exact ⟨C1_of_realizesSq n f w hw hnap hr, C2_of_realizesSq n f w hw hnap hr⟩
  · rintro ⟨hC1, hC2⟩
    exact exists_nap_realizing_veronese n 2 (demandSq n f) (demandSq_sum_zero n f)
      (demandSq_neg_half n f) (demandSq_splittable_of_C1C2 n f hC1 hC2)

/-! ## Part B: the r-trick and Theorem 3 -/

/-- The tail of a weight-3 index on `n+1` species whose slack exponent is `1`. -/
def tail1 (μ' : MI (n + 1) 3) (h : (μ'.1 0 : ℕ) = 1) : MI n 2 :=
  MI.ofFun n (fun j => (μ'.1 j.succ : ℕ))
    (fun j => by
      have := MI.two_entries_le (n + 1) μ' (Fin.succ_ne_zero j)
      dsimp only
      omega)
    (by
      have hw := μ'.2
      rw [Fin.sum_univ_succ] at hw
      dsimp only
      omega)

theorem tail1_eq (μ' : MI (n + 1) 3) (h : (μ'.1 0 : ℕ) = 1) (μ : MI n 2)
    (hμ : ∀ j, (μ'.1 j.succ : ℕ) = (μ.1 j : ℕ)) : tail1 n μ' h = μ :=
  Subtype.ext (funext fun j => Fin.ext (hμ j))

/-- The coefficient table of `r · g` (slack trick with shrunk set `J`, then the r-trick). -/
noncomputable def liftCoefR (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (j' : Fin (n + 1))
    (μ' : MI (n + 1) 3) : ℚ :=
  if h : (μ'.1 0 : ℕ) = 1 then
    Fin.cases
      ((1 - lam) * lam⁻¹ ^ expIn n J (tail1 n μ' h) * ∑ j ∈ J, g.coef j (tail1 n μ' h))
      (fun j => (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J (tail1 n μ' h) *
        g.coef j (tail1 n μ' h)) j'
  else 0

theorem liftCoefR_sum (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (μ' : MI (n + 1) 3) :
    ∑ j', liftCoefR n g J lam j' μ' = 0 := by
  unfold liftCoefR
  by_cases h : (μ'.1 0 : ℕ) = 1
  · simp only [dif_pos h]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    set sc := lam⁻¹ ^ expIn n J (tail1 n μ' h)
    set μ := tail1 n μ' h
    have hsplit : ∀ j, (if j ∈ J then lam else 1) * sc * g.coef j μ
        = sc * g.coef j μ + (if j ∈ J then (lam - 1) * sc * g.coef j μ else 0) := by
      intro j
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_add_distrib, sum_ite_mem_univ, ← Finset.mul_sum,
      g.conservative μ, mul_zero, zero_add]
    ring
  · simp [dif_neg h]

theorem liftCoefR_sign (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam)
    (j' : Fin (n + 1)) (μ' : MI (n + 1) 3) (hneg : liftCoefR n g J lam j' μ' < 0) :
    0 < (μ'.1 j' : ℕ) := by
  unfold liftCoefR at hneg
  by_cases h : (μ'.1 0 : ℕ) = 1
  · simp only [dif_pos h] at hneg
    have hsc : 0 < lam⁻¹ ^ expIn n J (tail1 n μ' h) := pow_pos (inv_pos.mpr hlam) _
    induction j' using Fin.cases with
    | zero => omega
    | succ j =>
      simp only [Fin.cases_succ] at hneg
      have hfac : 0 < (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J (tail1 n μ' h) := by
        apply mul_pos _ hsc
        split_ifs <;> linarith
      have hg : g.coef j (tail1 n μ' h) < 0 := by
        by_contra hcon
        rw [not_lt] at hcon
        have := mul_nonneg hfac.le hcon
        linarith
      have := g.sign j _ hg
      simpa [tail1] using this
  · simp [dif_neg h] at hneg

/-- The cubic protocol `r · g` on `n + 1` species. -/
noncomputable def liftR1Set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam) :
    CubicPP (n + 1) where
  coef := liftCoefR n g J lam
  conservative := liftCoefR_sum n g J lam
  sign := liftCoefR_sign n g J lam hlam

theorem liftR1Set_coef (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam)
    (j' : Fin (n + 1)) (μ' : MI (n + 1) 3) :
    (liftR1Set n g J lam hlam).coef j' μ' = liftCoefR n g J lam j' μ' := rfl

theorem liftCoefR_eq_zero_of_slack (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (j' : Fin (n + 1)) (μ' : MI (n + 1) 3) (h : (μ'.1 0 : ℕ) ≠ 1) :
    liftCoefR n g J lam j' μ' = 0 := by
  unfold liftCoefR
  rw [dif_neg h]

/-- Vacuity for a quadratic protocol: `[y²] g_y ≤ 0`. -/
theorem quad_coef_pow_nonpos (g : QuadPP n) (y : Fin n) : g.coef y (MI.pow n 2 y) ≤ 0 := by
  have hc := g.conservative (MI.pow n 2 y)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y)] at hc
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase y, g.coef j (MI.pow n 2 y) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjy : j ≠ y := (Finset.mem_erase.mp hj).1
    by_contra hneg
    rw [not_le] at hneg
    have := g.sign j _ hneg
    simp [MI.pow, hjy] at this
  linarith

theorem slack_two_succ_zero (y : Fin n) (h : y.succ ≠ 0) :
    ((MI.two (n + 1) 2 1 y.succ 0 h).1 0 : ℕ) = 1 := by
  simp [MI.two, (Fin.succ_ne_zero y).symm]

theorem tail1_two_succ_zero (y : Fin n) (h : y.succ ≠ 0)
    (hs : ((MI.two (n + 1) 2 1 y.succ 0 h).1 0 : ℕ) = 1) :
    tail1 n (MI.two (n + 1) 2 1 y.succ 0 h) hs = MI.pow n 2 y := by
  apply tail1_eq
  intro j
  simp only [MI.two, MI.pow, MI.ofFun_val, Fin.succ_inj, Fin.succ_ne_zero, if_false]

theorem liftCoefR_two_succ_zero (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (y : Fin n)
    (h : y.succ ≠ 0) (j' : Fin (n + 1)) :
    liftCoefR n g J lam j' (MI.two (n + 1) 2 1 y.succ 0 h) =
      Fin.cases ((1 - lam) * lam⁻¹ ^ expIn n J (MI.pow n 2 y) * ∑ j ∈ J, g.coef j (MI.pow n 2 y))
        (fun j => (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J (MI.pow n 2 y) *
          g.coef j (MI.pow n 2 y)) j' := by
  unfold liftCoefR
  rw [dif_pos (slack_two_succ_zero n y h), tail1_two_succ_zero]

/-- The slack exponent of `y²k` is `1` only when `k` is the slack and `y` is not. -/
theorem slack_two_ne (y k : Fin (n + 1)) (h : y ≠ k) (hk : ¬ (k = 0 ∧ y ≠ 0)) :
    ((MI.two (n + 1) 2 1 y k h).1 0 : ℕ) ≠ 1 := by
  simp only [MI.two, MI.ofFun_val]
  by_cases hy : (0 : Fin (n + 1)) = y
  · rw [if_pos hy]; omega
  · rw [if_neg hy]
    by_cases hk0 : (0 : Fin (n + 1)) = k
    · exact absurd ⟨hk0.symm, fun hy0 => hy hy0.symm⟩ hk
    · rw [if_neg hk0]; omega

theorem slack_pow_ne (y : Fin (n + 1)) : ((MI.pow (n + 1) 3 y).1 0 : ℕ) ≠ 1 := by
  simp only [MI.pow, MI.ofFun_val]
  split_ifs <;> omega

/-- (C1) always holds for `r · g`. -/
theorem liftR1Set_C1 (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam) :
    ∀ (y k : Fin (n + 1)) (h : y ≠ k),
      (liftR1Set n g J lam hlam).coef y (MI.two (n + 1) 2 1 y k h) ≤ 0 := by
  intro y k h
  rw [liftR1Set_coef]
  by_cases hk : k = 0 ∧ y ≠ 0
  · obtain ⟨hk0, hy0⟩ := hk
    subst hk0
    obtain ⟨y', rfl⟩ := Fin.exists_succ_eq.mpr hy0
    rw [liftCoefR_two_succ_zero]
    simp only [Fin.cases_succ]
    have hsc : 0 < (if y' ∈ J then lam else 1) * lam⁻¹ ^ expIn n J (MI.pow n 2 y') := by
      apply mul_pos _ (pow_pos (inv_pos.mpr hlam) _)
      split_ifs <;> linarith
    exact mul_nonpos_of_nonneg_of_nonpos hsc.le (quad_coef_pow_nonpos n g y')
  · rw [liftCoefR_eq_zero_of_slack n g J lam y _ (slack_two_ne n y k h hk)]

/-- **Theorem 3 (the r-trick and squaring).** For a syntactic quadratic PP `g`, a shrunk set `J`
and rational `λ ∈ (0,1)`, the squared system of the cubic protocol `r · g` has a non-negative
non-autocatalytic weighted realisation iff `Σ_{j∈J} [y²] g_j ≤ 0` for every species `y`. -/
theorem squaring_iff (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    (∃ w : WProtocol (MI (n + 1) 2), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
        Realizes (veroneseLift (n + 1) 2) w (demandSq (n + 1) (liftR1Set n g J lam hlam0))) ↔
      ∀ y : Fin n, ∑ j ∈ J, g.coef j (MI.pow n 2 y) ≤ 0 := by
  rw [exists_nap_realizing_sq_iff]
  have hfac : ∀ y : Fin n, 0 < (1 - lam) * lam⁻¹ ^ expIn n J (MI.pow n 2 y) := fun y =>
    mul_pos (by linarith) (pow_pos (inv_pos.mpr hlam0) _)
  have hval : ∀ (y : Fin n) (h : y.succ ≠ 0),
      (liftR1Set n g J lam hlam0).coef 0 (MI.two (n + 1) 2 1 y.succ 0 h)
        + (liftR1Set n g J lam hlam0).coef y.succ (MI.pow (n + 1) 3 y.succ)
      = (1 - lam) * lam⁻¹ ^ expIn n J (MI.pow n 2 y) * ∑ j ∈ J, g.coef j (MI.pow n 2 y) := by
    intro y h
    rw [liftR1Set_coef, liftR1Set_coef, liftCoefR_two_succ_zero,
      liftCoefR_eq_zero_of_slack n g J lam _ _ (slack_pow_ne n _)]
    simp only [Fin.cases_zero, add_zero]
  constructor
  · rintro ⟨_, hC2⟩ y
    have := hC2 y.succ 0 (Fin.succ_ne_zero y)
    rw [hval] at this
    by_contra hcon
    rw [not_le] at hcon
    have := mul_pos (hfac y) hcon
    linarith
  · intro hJ
    refine ⟨liftR1Set_C1 n g J lam hlam0, fun y k h => ?_⟩
    by_cases hk : k = 0 ∧ y ≠ 0
    · obtain ⟨hk0, hy0⟩ := hk
      subst hk0
      obtain ⟨y', rfl⟩ := Fin.exists_succ_eq.mpr hy0
      rw [hval]
      exact mul_nonpos_of_nonneg_of_nonpos (hfac y').le (hJ y')
    · rw [liftR1Set_coef, liftR1Set_coef,
        liftCoefR_eq_zero_of_slack n g J lam k _ (slack_two_ne n y k h hk),
        liftCoefR_eq_zero_of_slack n g J lam y _ (slack_pow_ne n y)]
      norm_num

/-- **Theorem 3, realisation.** Under the squaring condition there is a non-negative
non-autocatalytic weighted protocol on the `C(n+2, 2)` weight-2 multi-indices of `n + 1` species
realising the squared system of `r · g`. -/
theorem exists_nap_realizing_squaring (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hJ : ∀ y : Fin n, ∑ j ∈ J, g.coef j (MI.pow n 2 y) ≤ 0) :
    ∃ w : WProtocol (MI (n + 1) 2), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 2) w (demandSq (n + 1) (liftR1Set n g J lam hlam0)) :=
  (squaring_iff n g J lam hlam0 hlam1).mpr hJ

/-! ### The r-trick field: `liftR1Set` is `r · g` -/

/-- Monomial of a weight-3 multi-index. -/
noncomputable def mono3 {m : ℕ} (x : Fin m → ℝ) (μ : MI m 3) : ℝ := ∏ k, x k ^ (μ.1 k : ℕ)

/-- The cubic field of a cubic coefficient table. -/
noncomputable def cubicFun {m : ℕ} (f : CubicPP m) (x : Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ μ, (f.coef j μ : ℝ) * mono3 x μ

/-- The weight-3 index `r ⊕ μ` on `n + 1` species. -/
def cons1 (μ : MI n 2) : MI (n + 1) 3 :=
  MI.ofFun (n + 1) (Fin.cases 1 (fun j => (μ.1 j : ℕ)))
    (fun k => by
      induction k using Fin.cases with
      | zero => simp
      | succ j =>
        have := MI.entry_le n μ j
        simp only [Fin.cases_succ]
        omega)
    (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      have := μ.2
      omega)

@[simp] theorem cons1_val_zero (μ : MI n 2) : ((cons1 n μ).1 0 : ℕ) = 1 := rfl

@[simp] theorem cons1_val_succ (μ : MI n 2) (j : Fin n) :
    ((cons1 n μ).1 j.succ : ℕ) = (μ.1 j : ℕ) := rfl

theorem cons1_tail1 (μ' : MI (n + 1) 3) (h : (μ'.1 0 : ℕ) = 1) : cons1 n (tail1 n μ' h) = μ' := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  induction k using Fin.cases with
  | zero => exact h.symm
  | succ j => rfl

theorem cons1_injective : Function.Injective (cons1 n) := by
  intro a b h
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun μ' : MI (n + 1) 3 => ((μ'.1 j.succ : ℕ))) h

theorem sum_slack_one (F : MI (n + 1) 3 → ℝ) (hF : ∀ μ', (μ'.1 0 : ℕ) ≠ 1 → F μ' = 0) :
    ∑ μ', F μ' = ∑ μ, F (cons1 n μ) := by
  rw [← Finset.sum_image (f := F) (s := Finset.univ) (g := cons1 n)
    (fun a _ b _ h => cons1_injective n h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro μ' _ hμ'
  apply hF
  intro h
  exact hμ' (Finset.mem_image.mpr ⟨tail1 n μ' h, Finset.mem_univ _, cons1_tail1 n μ' h⟩)

theorem mono3_cons1 (x : Fin (n + 1) → ℝ) (μ : MI n 2) :
    mono3 x (cons1 n μ) = x 0 * ∏ k, x k.succ ^ (μ.1 k : ℕ) := by
  unfold mono3
  rw [Fin.prod_univ_succ]
  simp only [cons1_val_zero, cons1_val_succ, pow_one]

theorem liftCoefR_cons1 (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (j' : Fin (n + 1))
    (μ : MI n 2) :
    liftCoefR n g J lam j' (cons1 n μ) =
      Fin.cases ((1 - lam) * lam⁻¹ ^ expIn n J μ * ∑ j ∈ J, g.coef j μ)
        (fun j => (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J μ * g.coef j μ) j' := by
  unfold liftCoefR
  rw [dif_pos (cons1_val_zero n μ), tail1_eq n _ _ μ (fun j => rfl)]

/-- **Evaluation identity of the r-trick.** The cubic field of `liftR1Set g J λ` is `x_0` times the
slack-trick field: `liftR1Set` is the coefficient table of `r · g`. -/
theorem cubicFun_liftR1Set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam)
    (x : Fin (n + 1) → ℝ) :
    cubicFun (liftR1Set n g J lam hlam) x = fun j' => x 0 * slackFieldSet n g J lam x j' := by
  funext j'
  unfold cubicFun
  rw [sum_slack_one n _ (fun μ' h => by
    rw [liftR1Set_coef, liftCoefR_eq_zero_of_slack n g J lam j' μ' h, Rat.cast_zero, zero_mul])]
  simp only [liftR1Set_coef, liftCoefR_cons1, mono3_cons1]
  refine Fin.cases ?_ (fun j => ?_) j'
  · simp only [Fin.cases_zero, slackFieldSet, quadFun, mono2_unshrinkSet]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => ?_
    ring
  · simp only [Fin.cases_succ, slackFieldSet, quadFun, mono2_unshrinkSet, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hj : j ∈ J
    · simp only [if_pos hj]
      push_cast
      ring
    · simp only [if_neg hj]
      push_cast
      ring

end NAPTransport
end Ripple

/-
  Ripple.LPP.NAPExchange — the exchange reactions of §6 of the PP-to-NAP write-up and Lemma 6.1.

  For every ordered quadruple `(β₁, γ₁, β₂, γ₂)` of weight-3 multi-indices with `β₁ + γ₁ = β₂ + γ₂`
  the exchange protocol `wE` contains the reaction `β₁ + γ₁ → β₂ + γ₂` with rate `1 / (mult β₁ mult γ₁)`,
  so that its flux on the Veronese image is `x^{β₁+γ₁}`; the reverse quadruple is in the list too, so
  `wE` is the reversible exchange network of the paper (same-pair quadruples are null reactions).

  * `coeffAt_wE`: every coefficient of the exchange field vanishes (swap involution), hence
    `balanceFun_wE_ver` (`E₁ = 0` on the image) and `realizes_add_wE` (`F + K E₁` realises what `F` does);
  * `wE_nonneg`, `wE_isNAP`: non-negative rates, non-autocatalytic;
  * `contentMat_mulVec_netR`: each exchange preserves the content `L_j(v) = Σ_α α_j v_α`;
  * `exchange_span` (**Lemma 6.1**): a vector orthogonal to all exchange vectors `e_{β₂}+e_{γ₂}−e_{β₁}−e_{γ₁}`
    is orthogonal to `S = ker L`; proved by showing that such a `y` is linear, `y_α = Σ_j α_j y_{3e_j}/3`
    (the difference `y_{α−e_b+e_a} − y_α` does not depend on `α`).
-/

import Ripple.LPP.NAPNormalStability

namespace Ripple
namespace NAPTransport

open Finset Matrix

variable (n : ℕ)

/-! ### The exchange protocol -/

/-- Ordered exchange quadruples: shapes `(β₁, γ₁, β₂, γ₂)` with `β₁ + γ₁ = β₂ + γ₂`. -/
abbrev ExIdx := {sh : Shape (MI n 3) // MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2}

/-- Swap reactants and products. -/
def exSwap (q : ExIdx n) : ExIdx n := ⟨(q.1.2.2.1, q.1.2.2.2, q.1.1, q.1.2.1), q.2.symm⟩

theorem exSwap_exSwap (q : ExIdx n) : exSwap n (exSwap n q) = q := rfl

/-- The swap as an equivalence. -/
def exSwapEquiv : ExIdx n ≃ ExIdx n := ⟨exSwap n, exSwap n, fun _ => rfl, fun _ => rfl⟩

/-- A function that changes sign under the swap sums to zero. -/
theorem sum_exSwap_neg {F : Type*} [Field F] [CharZero F] (g : ExIdx n → F)
    (hg : ∀ q, g (exSwap n q) = -g q) : ∑ q, g q = 0 := by
  have h1 : ∑ q, g (exSwap n q) = ∑ q, g q := Equiv.sum_comp (exSwapEquiv n) g
  have h2 : ∑ q, g (exSwap n q) = -∑ q, g q := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q _ => hg q
  have h3 : ∑ q, g q + ∑ q, g q = 0 := by
    have := h1.symm.trans h2
    calc ∑ q, g q + ∑ q, g q = ∑ q, g q + -∑ q, g q := by rw [← this]
      _ = 0 := add_neg_cancel _
  exact add_self_eq_zero.mp h3

/-- The exchange protocol at unit rate: `β₁ + γ₁ → β₂ + γ₂` with rate `1 / (mult β₁ mult γ₁)`
whenever `β₁ + γ₁ = β₂ + γ₂`. -/
noncomputable def wE : WProtocol (MI n 3) := fun sh =>
  if MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2
    then 1 / (MI.mult n 3 sh.1 * MI.mult n 3 sh.2.1) else 0

theorem wE_nonneg (sh : Shape (MI n 3)) : 0 ≤ wE n sh := by
  unfold wE
  split_ifs
  · have := MI.mult_pos n 3 sh.1
    have := MI.mult_pos n 3 sh.2.1
    positivity
  · exact le_rfl

/-! Cancellation facts for an exchange quadruple. -/

theorem ex_cancel_left {β₁ γ₁ β₂ γ₂ : MI n 3} (h : MI.add n 3 β₁ γ₁ = MI.add n 3 β₂ γ₂)
    (hβ : β₂ = β₁) : γ₂ = γ₁ := by
  subst hβ
  exact (MI.add_cancel n 3 β₂ γ₁ γ₂ h).symm

theorem ex_cancel_right {β₁ γ₁ β₂ γ₂ : MI n 3} (h : MI.add n 3 β₁ γ₁ = MI.add n 3 β₂ γ₂)
    (hγ : γ₂ = β₁) : β₂ = γ₁ := by
  subst hγ
  have : MI.add n 3 γ₂ γ₁ = MI.add n 3 γ₂ β₂ := by rw [h, MI.add_comm]
  exact (MI.add_cancel n 3 γ₂ γ₁ β₂ this).symm

theorem ex_cancel_left' {β₁ γ₁ β₂ γ₂ : MI n 3} (h : MI.add n 3 β₁ γ₁ = MI.add n 3 β₂ γ₂)
    (hβ : β₂ = γ₁) : γ₂ = β₁ := by
  subst hβ
  have : MI.add n 3 β₂ β₁ = MI.add n 3 β₂ γ₂ := by rw [← h, MI.add_comm]
  exact (MI.add_cancel n 3 β₂ β₁ γ₂ this).symm

theorem ex_cancel_right' {β₁ γ₁ β₂ γ₂ : MI n 3} (h : MI.add n 3 β₁ γ₁ = MI.add n 3 β₂ γ₂)
    (hγ : γ₂ = γ₁) : β₂ = β₁ := by
  subst hγ
  have : MI.add n 3 γ₂ β₁ = MI.add n 3 γ₂ β₂ := by rw [MI.add_comm, h, MI.add_comm]
  exact (MI.add_cancel n 3 γ₂ β₁ β₂ this).symm

/-- Exchange reactions are non-autocatalytic (reactants and products are disjoint unless the
reaction is null). -/
theorem wE_isNAP : (wE n).IsNAP := by
  intro sh hsh
  have hc : MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2 := by
    by_contra h
    simp [wE, h] at hsh
  refine ⟨?_, ?_⟩
  · show net sh sh.1 ≤ 0
    by_cases h1 : sh.2.2.1 = sh.1
    · have h2 : sh.2.2.2 = sh.2.1 := ex_cancel_left n hc h1
      simp only [net, h1, h2, if_true]
      split_ifs <;> norm_num
    · by_cases h2 : sh.2.2.2 = sh.1
      · have h3 : sh.2.2.1 = sh.2.1 := ex_cancel_right n hc h2
        simp only [net, h1, h2, h3, if_true, if_false]
        split_ifs <;> norm_num
      · simp only [net, h1, h2, if_true, if_false]
        split_ifs <;> norm_num
  · show net sh sh.2.1 ≤ 0
    by_cases h1 : sh.2.2.1 = sh.2.1
    · have h2 : sh.2.2.2 = sh.1 := ex_cancel_left' n hc h1
      simp only [net, h1, h2, if_true]
      split_ifs <;> norm_num
    · by_cases h2 : sh.2.2.2 = sh.2.1
      · have h3 : sh.2.2.1 = sh.1 := ex_cancel_right' n hc h2
        simp only [net, h1, h2, h3, if_true, if_false]
        split_ifs <;> norm_num
      · simp only [net, h1, h2, if_true, if_false]
        split_ifs <;> norm_num

/-! ### The exchange field vanishes on the image -/

theorem rat_cast_ite (p : Prop) [Decidable p] (a b : ℚ) :
    ((ite p a b : ℚ) : ℝ) = ite p (a : ℝ) (b : ℝ) := by
  split_ifs <;> rfl

/-- Every coefficient of the exchange field is zero. -/
theorem coeffAt_wE (δ : Fin n → Fin (2 * 3 + 1)) (α : MI n 3) :
    coeffAt (veroneseLift n 3) (wE n) δ α = 0 := by
  have hterm : ∀ sh : Shape (MI n 3), wE n sh * sel (veroneseLift n 3) δ α sh
      = if MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2
          then (if MI.add n 3 sh.1 sh.2.1 = δ then net sh α else 0) else 0 := by
    intro sh
    have hm1 := (MI.mult_pos n 3 sh.1).ne'
    have hm2 := (MI.mult_pos n 3 sh.2.1).ne'
    simp only [wE, sel, veroneseLift]
    split_ifs
    · rw [one_div, inv_mul_eq_div, mul_div_cancel_left₀ _ (mul_ne_zero hm1 hm2)]
    · simp
    · simp
    · simp
  calc coeffAt (veroneseLift n 3) (wE n) δ α
      = ∑ sh : Shape (MI n 3), (if MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2
          then (if MI.add n 3 sh.1 sh.2.1 = δ then net sh α else 0) else 0) :=
        Finset.sum_congr rfl fun sh _ => hterm sh
    _ = ∑ q : ExIdx n, (if MI.add n 3 q.1.1 q.1.2.1 = δ then net q.1 α else 0) := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype
          (p := fun sh : Shape (MI n 3) => MI.add n 3 sh.1 sh.2.1 = MI.add n 3 sh.2.2.1 sh.2.2.2)
          _ (by simp) _
    _ = 0 := by
        apply sum_exSwap_neg
        intro q
        simp only [exSwap]
        rw [show MI.add n 3 q.1.2.2.1 q.1.2.2.2 = MI.add n 3 q.1.1 q.1.2.1 from q.2.symm]
        split_ifs
        · simp only [net]
          ring
        · simp

/-- `E₁ = 0` on the Veronese image. -/
theorem balanceFun_wE_ver (x : Fin n → ℝ) : balanceFun n (wE n) (ver n x) = 0 := by
  funext α
  rw [balanceFun_ver_eq_sum]
  simp [coeffAt_wE]

theorem coeffAt_add_smul {V D : Type} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
    (L : LiftData V D) (w w' : WProtocol V) (c : ℚ) (δ : D) (α : V) :
    coeffAt L (w + c • w') δ α = coeffAt L w δ α + c * coeffAt L w' δ α := by
  simp only [coeffAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- Adding exchange reactions does not change the realised demand. -/
theorem realizes_add_wE (w : WProtocol (MI n 3)) (p : (Fin n → Fin (2 * 3 + 1)) → MI n 3 → ℚ)
    (K : ℚ) : Realizes (veroneseLift n 3) (w + K • wE n) p ↔ Realizes (veroneseLift n 3) w p := by
  unfold Realizes
  simp only [coeffAt_add_smul, coeffAt_wE, mul_zero, add_zero]

theorem add_wE_nonneg (w : WProtocol (MI n 3)) (hw : ∀ sh, 0 ≤ w sh) (K : ℚ) (hK : 0 ≤ K) :
    ∀ sh, 0 ≤ (w + K • wE n) sh := by
  intro sh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := wE_nonneg n sh
  have := hw sh
  positivity

theorem add_wE_isNAP (w : WProtocol (MI n 3)) (hw : ∀ sh, 0 ≤ w sh) (hnap : w.IsNAP) (K : ℚ)
    (hK : 0 ≤ K) : (w + K • wE n).IsNAP := by
  intro sh hsh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsh
  by_cases h : 0 < w sh
  · exact hnap sh h
  · have h0 : w sh = 0 := le_antisymm (not_lt.mp h) (hw sh)
    rw [h0, zero_add] at hsh
    have : 0 < wE n sh := by
      by_contra h'
      have h'' : wE n sh = 0 := le_antisymm (not_lt.mp h') (wE_nonneg n sh)
      rw [h'', mul_zero] at hsh
      exact lt_irrefl _ hsh
    exact wE_isNAP n sh this

/-- The balance field is linear in the protocol. -/
theorem balanceFun_add_smul (w w' : WProtocol (MI n 3)) (K : ℚ) (v : MI n 3 → ℝ) (α : MI n 3) :
    balanceFun n (w + K • w') v α = balanceFun n w v α + (K : ℝ) * balanceFun n w' v α := by
  simp only [balanceFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun sh _ => ?_
  ring

/-! ### Content preservation -/

/-- The net vector of a shape, real-valued. -/
def netR (sh : Shape (MI n 3)) : MI n 3 → ℝ := fun α => (net sh α : ℝ)

theorem netR_apply (sh : Shape (MI n 3)) (α : MI n 3) :
    netR n sh α = (if sh.2.2.1 = α then 1 else 0) + (if sh.2.2.2 = α then 1 else 0)
      - (if sh.1 = α then 1 else 0) - (if sh.2.1 = α then 1 else 0) := by
  simp only [netR, net, Rat.cast_sub, Rat.cast_add, rat_cast_ite, Rat.cast_one, Rat.cast_zero]

theorem dotProduct_netR (sh : Shape (MI n 3)) (y : MI n 3 → ℝ) :
    netR n sh ⬝ᵥ y = y sh.2.2.1 + y sh.2.2.2 - y sh.1 - y sh.2.1 := by
  simp only [dotProduct, netR_apply, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-- The content map `L_j(v) = Σ_α α_j v_α` as a matrix. -/
def contentMat : Matrix (Fin n) (MI n 3) ℝ := Matrix.of fun j α => ((α.1 j : ℕ) : ℝ)

theorem sum_entry_ite (β : MI n 3) (j : Fin n) :
    ∑ α : MI n 3, ((α.1 j : ℕ) : ℝ) * (if β = α then 1 else 0) = ((β.1 j : ℕ) : ℝ) := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Each exchange preserves the content. -/
theorem contentMat_mulVec_netR (q : ExIdx n) : contentMat n *ᵥ netR n q.1 = 0 := by
  funext j
  simp only [contentMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, netR_apply,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_entry_ite]
  have h := congrFun q.2 j
  simp only [MI.add, Fin.mk.injEq] at h
  have h' : ((q.1.1.1 j : ℕ) : ℝ) + ((q.1.2.1.1 j : ℕ) : ℝ)
      = ((q.1.2.2.1.1 j : ℕ) : ℝ) + ((q.1.2.2.2.1 j : ℕ) : ℝ) := by exact_mod_cast h
  linarith

/-! ### Lemma 6.1: the exchange vectors span `S = ker L` -/

section Span

variable {n}

/-- Entries of `MI.shift` (`α − e_j + e_i`) as reals. -/
theorem shift_entry_real (α : MI n 3) (j i : Fin n) (hij : i ≠ j) (hαj : 0 < (α.1 j : ℕ))
    (k : Fin n) :
    (((MI.shift n α j i hij hαj).1 k : ℕ) : ℝ)
      = ((α.1 k : ℕ) : ℝ) - (if k = j then 1 else 0) + (if k = i then 1 else 0) := by
  have h : ((MI.shift n α j i hij hαj).1 k : ℕ) + (if k = j then 1 else 0)
      = (α.1 k : ℕ) + (if k = i then 1 else 0) := by
    simp only [MI.shift, MI.ofFun_val]
    by_cases hk : k = j
    · subst hk
      simp only [if_true]
      split_ifs <;> omega
    · simp only [hk, if_false]
      split_ifs <;> omega
  have h' := congrArg (fun m : ℕ => (m : ℝ)) h
  push_cast at h'
  linarith

theorem shift_entry_self (α : MI n 3) (b a : Fin n) (hab : a ≠ b) (hα : 0 < (α.1 b : ℕ)) :
    ((MI.shift n α b a hab hα).1 a : ℕ) = (α.1 a : ℕ) + 1 := by
  simp [MI.shift, MI.ofFun_val, hab]

/-- The pair relation: `y_{β₂} + y_{γ₂} = y_{β₁} + y_{γ₁}` whenever `β₁ + γ₁ = β₂ + γ₂`. -/
def PairAdditive (y : MI n 3 → ℝ) : Prop :=
  ∀ β₁ γ₁ β₂ γ₂ : MI n 3, MI.add n 3 β₁ γ₁ = MI.add n 3 β₂ γ₂ → y β₂ + y γ₂ = y β₁ + y γ₁

theorem pairAdditive_of_orth (y : MI n 3 → ℝ) (hy : ∀ q : ExIdx n, netR n q.1 ⬝ᵥ y = 0) :
    PairAdditive y := by
  intro β₁ γ₁ β₂ γ₂ h
  have := hy ⟨(β₁, γ₁, β₂, γ₂), h⟩
  rw [dotProduct_netR] at this
  dsimp only at this
  linarith

/-- `{α − e_b + e_a, α'}` and `{α, α' − e_b + e_a}` have the same sum. -/
theorem add_shift_eq (α α' : MI n 3) (b a : Fin n) (hab : a ≠ b) (hα : 0 < (α.1 b : ℕ))
    (hα' : 0 < (α'.1 b : ℕ)) :
    MI.add n 3 (MI.shift n α b a hab hα) α' = MI.add n 3 α (MI.shift n α' b a hab hα') := by
  funext k
  apply Fin.ext
  simp only [MI.add, MI.shift, MI.ofFun_val]
  by_cases hk : k = b
  · subst hk
    simp only [if_true]
    split_ifs <;> omega
  · simp only [hk, if_false]
    split_ifs <;> omega

/-- The move difference `y_{α−e_b+e_a} − y_α` does not depend on `α`. -/
theorem shift_diff_const (y : MI n 3 → ℝ) (hy : PairAdditive y) (α α' : MI n 3) (b a : Fin n)
    (hab : a ≠ b) (hα : 0 < (α.1 b : ℕ)) (hα' : 0 < (α'.1 b : ℕ)) :
    y (MI.shift n α b a hab hα) - y α = y (MI.shift n α' b a hab hα') - y α' := by
  have := hy _ _ _ _ (add_shift_eq α α' b a hab hα hα')
  linarith

theorem pow_entry (m : ℕ) (a k : Fin n) : ((MI.pow n m a).1 k : ℕ) = if k = a then m else 0 := rfl

/-- The move difference equals `(y_{3e_a} − y_{3e_b}) / 3` (chain `3b → 2b+a → b+2a → 3a`). -/
theorem shift_diff_eq (y : MI n 3 → ℝ) (hy : PairAdditive y) (b a : Fin n) (hab : a ≠ b)
    (α : MI n 3) (hα : 0 < (α.1 b : ℕ)) :
    y (MI.shift n α b a hab hα) - y α = (y (MI.pow n 3 a) - y (MI.pow n 3 b)) / 3 := by
  have h0 : 0 < ((MI.pow n 3 b).1 b : ℕ) := by simp [pow_entry]
  have h1 : 0 < ((MI.shift n (MI.pow n 3 b) b a hab h0).1 b : ℕ) := by
    simp [MI.shift, MI.ofFun_val, pow_entry, Ne.symm hab]
  have h2 : 0 < ((MI.shift n (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab h1).1 b : ℕ) := by
    simp [MI.shift, MI.ofFun_val, pow_entry, Ne.symm hab]
  have h3 : MI.shift n (MI.shift n (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab h1) b a hab h2
      = MI.pow n 3 a := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [MI.shift, MI.pow, MI.ofFun_val]
    by_cases hk : k = a
    · simp [hk, hab]
    · by_cases hk' : k = b
      · simp [hk', Ne.symm hab]
      · simp [hk, hk']
  have e1 := shift_diff_const y hy α (MI.pow n 3 b) b a hab hα h0
  have e2 := shift_diff_const y hy α (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab hα h1
  have e3 := shift_diff_const y hy α
    (MI.shift n (MI.shift n (MI.pow n 3 b) b a hab h0) b a hab h1) b a hab hα h2
  rw [h3] at e3
  linarith

/-- The linear part `Σ_j α_j y_{3e_j} / 3`. -/
noncomputable def linPart (y : MI n 3 → ℝ) (α : MI n 3) : ℝ := ∑ j, ((α.1 j : ℕ) : ℝ) * (y (MI.pow n 3 j) / 3)

theorem linPart_shift (y : MI n 3 → ℝ) (α : MI n 3) (b a : Fin n) (hab : a ≠ b)
    (hα : 0 < (α.1 b : ℕ)) :
    linPart y (MI.shift n α b a hab hα)
      = linPart y α + (y (MI.pow n 3 a) - y (MI.pow n 3 b)) / 3 := by
  unfold linPart
  simp only [shift_entry_real, sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem linPart_pow (y : MI n 3 → ℝ) (a : Fin n) : linPart y (MI.pow n 3 a) = y (MI.pow n 3 a) := by
  unfold linPart
  have : ∀ j : Fin n, (((MI.pow n 3 a).1 j : ℕ) : ℝ) * (y (MI.pow n 3 j) / 3)
      = if j = a then y (MI.pow n 3 j) else 0 := by
    intro j
    rw [pow_entry]
    split_ifs
    · push_cast
      ring
    · simp
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A pair-additive function is linear in the multi-index. -/
theorem linear_of_pairAdditive (y : MI n 3 → ℝ) (hy : PairAdditive y) (α : MI n 3) :
    y α = linPart y α := by
  have hne : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := α.2
    simp [Finset.univ_eq_empty] at this
  obtain ⟨a⟩ := hne
  have hz_shift : ∀ (β : MI n 3) (b : Fin n) (hab : a ≠ b) (hβ : 0 < (β.1 b : ℕ)),
      y (MI.shift n β b a hab hβ) - linPart y (MI.shift n β b a hab hβ) = y β - linPart y β := by
    intro β b hab hβ
    have := shift_diff_eq y hy b a hab β hβ
    rw [linPart_shift]
    linarith
  have key : ∀ k : ℕ, ∀ β : MI n 3, (β.1 a : ℕ) + k = 3 → y β - linPart y β = 0 := by
    intro k
    induction k with
    | zero =>
      intro β hβ
      have hβa : β = MI.pow n 3 a := by
        apply Subtype.ext
        funext j
        apply Fin.ext
        rw [pow_entry]
        by_cases hj : j = a
        · rw [if_pos hj, hj]
          omega
        · rw [if_neg hj]
          have := MI.two_entries_le n β hj
          omega
      rw [hβa, linPart_pow, sub_self]
    | succ k ih =>
      intro β hβ
      have hex : ∃ b, b ≠ a ∧ 0 < (β.1 b : ℕ) := by
        by_contra h
        push Not at h
        have hsum := β.2
        rw [Finset.sum_eq_single a] at hsum
        · omega
        · intro j _ hj
          have := h j hj
          omega
        · intro h'
          exact absurd (Finset.mem_univ a) h'
      obtain ⟨b, hba, hβb⟩ := hex
      have hab : a ≠ b := Ne.symm hba
      have hnext : ((MI.shift n β b a hab hβb).1 a : ℕ) + k = 3 := by
        rw [shift_entry_self]
        omega
      have := ih (MI.shift n β b a hab hβb) hnext
      rw [← hz_shift β b hab hβb]
      exact this
  have := key (3 - (α.1 a : ℕ)) α (by have := MI.entry_le n α a; omega)
  linarith

/-- **Lemma 6.1.** A vector orthogonal to every exchange vector is orthogonal to `ker L`. -/
theorem exchange_span (y : MI n 3 → ℝ) (hy : ∀ q : ExIdx n, netR n q.1 ⬝ᵥ y = 0)
    (s : MI n 3 → ℝ) (hs : contentMat n *ᵥ s = 0) : y ⬝ᵥ s = 0 := by
  have hlin := linear_of_pairAdditive y (pairAdditive_of_orth y hy)
  simp only [dotProduct]
  calc ∑ α, y α * s α
      = ∑ α, (∑ j, ((α.1 j : ℕ) : ℝ) * (y (MI.pow n 3 j) / 3)) * s α := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hlin α]
        rfl
    _ = ∑ j, (y (MI.pow n 3 j) / 3) * ∑ α, ((α.1 j : ℕ) : ℝ) * s α := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
        ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have := congrFun hs j
        simp only [contentMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
        rw [this, mul_zero]

end Span

end NAPTransport
end Ripple

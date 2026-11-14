/-
  Ripple.LPP.NAPSquaringConj — Proposition 4.2 of the PP-to-NAP write-up for the degree-2 Veronese
  lift (squaring), the template being `NAPConjugacy` and `NAPLipschitz` (degree 3).

  * `balanceFunSq w v α = Σ_sh w · v_{r1} v_{r2} · net α` on weight-2 indices;
  * `verSq x α = mult α ∏ x_k^{α_k}`, `pushSq f x α = mult α Σ_j α_j x^{α − e_j} (cubicFun f x)_j`;
  * `balanceFunSq_verSq`: a realisation of `demandSq f` satisfies `balanceFunSq w (verSq x) = pushSq f x`;
  * `verSq_hasDerivWithinAt`: chain rule along a trajectory of `cubicFun f`;
  * `balanceFunSq_lipschitzOnWith` (explicit constant), `lifted_solution_uniqueSq`;
  * `sum_verSq_eq` (`Σ_α verSq x α = (Σ x)²`), `sum_weight_verSq` (`Σ_α α_j verSq x α = 2 x_j Σ x`),
    `readoutSq_verSq` (readout weights `(1/2) Σ_j c_j α_j`).
-/

import Ripple.LPP.NAPSquaringCF24

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

/-- Balance field of a weighted protocol on weight-2 indices. -/
noncomputable def balanceFunSq (w : WProtocol (MI n 2)) (v : MI n 2 → ℝ) (α : MI n 2) : ℝ :=
  ∑ sh, (w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)

/-- The degree-2 Veronese map with multinomial normalisation. -/
noncomputable def verSq (x : Fin n → ℝ) (α : MI n 2) : ℝ :=
  (MI.mult n 2 α : ℝ) * ∏ k, x k ^ (α.1 k : ℕ)

/-- Monomial of a degree-4 exponent vector. -/
noncomputable def monoD4 (x : Fin n → ℝ) (δ : Fin n → Fin (2 * 2 + 1)) : ℝ :=
  ∏ k, x k ^ (δ k : ℕ)

/-- `x^{α − e_j}` for a weight-2 index. -/
noncomputable def monoSubSq (x : Fin n → ℝ) (α : MI n 2) (j : Fin n) : ℝ :=
  ∏ k, x k ^ ((α.1 k : ℕ) - if k = j then 1 else 0)

/-- The pushforward `P_α(x) = mult α Σ_j α_j x^{α−e_j} f_j(x)` of a cubic field. -/
noncomputable def pushSq (f : CubicPP n) (x : Fin n → ℝ) (α : MI n 2) : ℝ :=
  (MI.mult n 2 α : ℝ) * ∑ j, ((α.1 j : ℕ) : ℝ) * monoSubSq n x α j * cubicFun f x j

theorem verSq_mul_verSq (x : Fin n → ℝ) (β γ : MI n 2) :
    verSq n x β * verSq n x γ
      = (MI.mult n 2 β : ℝ) * (MI.mult n 2 γ : ℝ) * monoD4 n x (MI.add n 2 β γ) := by
  unfold verSq monoD4
  have : ∏ k, x k ^ ((MI.add n 2 β γ k : ℕ))
      = (∏ k, x k ^ (β.1 k : ℕ)) * ∏ k, x k ^ (γ.1 k : ℕ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    simp only [MI.add]
    rw [pow_add]
  rw [this]
  ring

theorem balanceFunSq_verSq_eq_sum (w : WProtocol (MI n 2)) (x : Fin n → ℝ) (α : MI n 2) :
    balanceFunSq n w (verSq n x) α
      = ∑ δ, (coeffAt (veroneseLift n 2) w δ α : ℝ) * monoD4 n x δ := by
  unfold balanceFunSq coeffAt sel
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sh _
  have hcast : ∀ δ : Fin n → Fin (2 * 2 + 1),
      ((if (veroneseLift n 2).pair sh.1 sh.2.1 = δ then
          (veroneseLift n 2).mult sh.1 * (veroneseLift n 2).mult sh.2.1 * net sh α else 0 : ℚ) : ℝ)
      = if (veroneseLift n 2).pair sh.1 sh.2.1 = δ then
          ((veroneseLift n 2).mult sh.1 : ℝ) * ((veroneseLift n 2).mult sh.2.1 : ℝ) * (net sh α : ℝ)
        else 0 := by
    intro δ
    split_ifs <;> push_cast <;> ring
  simp only [hcast, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ ((veroneseLift n 2).pair sh.1 sh.2.1)]
  simp only [Finset.mem_univ, if_true]
  have := verSq_mul_verSq n x sh.1 sh.2.1
  show (w sh : ℝ) * verSq n x sh.1 * verSq n x sh.2.1 * (net sh α : ℝ) = _
  rw [mul_assoc ((w sh : ℝ)), this]
  simp only [veroneseLift]
  ring

/-- The degree-4 exponent vector `(α − e_j) + μ`. -/
def chainDeltaSq (α : MI n 2) (j : Fin n) (μ : MI n 3) : Fin n → Fin (2 * 2 + 1) :=
  fun k => ⟨min ((α.1 k : ℕ) - (if k = j then 1 else 0) + (μ.1 k : ℕ)) 4, by omega⟩

theorem chainEqSq_chainDeltaSq (α : MI n 2) (j : Fin n) (μ : MI n 3) (hαj : 0 < (α.1 j : ℕ)) :
    chainEqSq n α j μ (chainDeltaSq n α j μ) := by
  intro k
  simp only [chainDeltaSq]
  have h2 := MI.entry_le n μ k
  by_cases hk : k = j
  · subst hk
    have h1 := MI.entry_le n α k
    simp only [if_true]
    omega
  · have h1 := MI.two_entries_le n α hk
    simp only [hk, if_false]
    omega

theorem chainEqSq_eq_chainDeltaSq (α : MI n 2) (j : Fin n) (μ : MI n 3)
    (δ : Fin n → Fin (2 * 2 + 1)) (h : chainEqSq n α j μ δ) : δ = chainDeltaSq n α j μ := by
  funext k
  apply Fin.ext
  have := h k
  simp only [chainDeltaSq]
  omega

theorem chainDeltaSq_val (α : MI n 2) (j : Fin n) (μ : MI n 3) (hαj : 0 < (α.1 j : ℕ))
    (k : Fin n) :
    (chainDeltaSq n α j μ k : ℕ) = (α.1 k : ℕ) - (if k = j then 1 else 0) + (μ.1 k : ℕ) := by
  have := chainEqSq_chainDeltaSq n α j μ hαj k
  omega

theorem monoD4_chainDeltaSq (x : Fin n → ℝ) (α : MI n 2) (j : Fin n) (μ : MI n 3)
    (hαj : 0 < (α.1 j : ℕ)) :
    monoD4 n x (chainDeltaSq n α j μ) = monoSubSq n x α j * mono3 x μ := by
  unfold monoD4 monoSubSq mono3
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [chainDeltaSq_val n α j μ hαj k, pow_add]

theorem sum_delta_collapseSq (x : Fin n → ℝ) (α : MI n 2) (j : Fin n) (μ : MI n 3) (c : ℝ) :
    ∑ δ, (if 0 < (α.1 j : ℕ) ∧ chainEqSq n α j μ δ then c else 0) * monoD4 n x δ
      = if 0 < (α.1 j : ℕ) then c * (monoSubSq n x α j * mono3 x μ) else 0 := by
  by_cases hαj : 0 < (α.1 j : ℕ)
  · rw [if_pos hαj]
    rw [Finset.sum_eq_single_of_mem (chainDeltaSq n α j μ) (Finset.mem_univ _)]
    · rw [if_pos ⟨hαj, chainEqSq_chainDeltaSq n α j μ hαj⟩, monoD4_chainDeltaSq n x α j μ hαj]
    · intro δ _ hδ
      rw [if_neg, zero_mul]
      rintro ⟨_, hc⟩
      exact hδ (chainEqSq_eq_chainDeltaSq n α j μ δ hc)
  · simp [hαj]

theorem demandSq_sum_eq_pushSq (f : CubicPP n) (x : Fin n → ℝ) (α : MI n 2) :
    ∑ δ, (demandSq n f δ α : ℝ) * monoD4 n x δ = pushSq n f x α := by
  unfold demandSq pushSq cubicFun
  have hcast : ∀ (p : Prop) [Decidable p] (a b : ℚ),
      ((ite p a b : ℚ) : ℝ) = ite p (a : ℝ) (b : ℝ) := by
    intro p _ a b
    split_ifs <;> rfl
  simp only [Rat.cast_mul, Rat.cast_sum, Finset.mul_sum, Finset.sum_mul, mul_ite, mul_zero, hcast,
    Rat.cast_zero, Rat.cast_natCast]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_delta_collapseSq]
  by_cases hαj : 0 < (α.1 j : ℕ)
  · rw [if_pos hαj]
    ring
  · have h0 : (α.1 j : ℕ) = 0 := by omega
    rw [if_neg hαj]
    simp [h0]

/-- **Lemma 2 for the squaring (polynomial form).** -/
theorem balanceFunSq_verSq (f : CubicPP n) (w : WProtocol (MI n 2))
    (hr : Realizes (veroneseLift n 2) w (demandSq n f)) (x : Fin n → ℝ) (α : MI n 2) :
    balanceFunSq n w (verSq n x) α = pushSq n f x α := by
  rw [balanceFunSq_verSq_eq_sum, ← demandSq_sum_eq_pushSq]
  apply Finset.sum_congr rfl
  intro δ _
  rw [hr δ α]

theorem monoSubSq_eq (x : Fin n → ℝ) (α : MI n 2) (j : Fin n) :
    (∏ k ∈ Finset.univ.erase j, x k ^ (α.1 k : ℕ)) * x j ^ ((α.1 j : ℕ) - 1)
      = monoSubSq n x α j := by
  unfold monoSubSq
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => x k ^ ((α.1 k : ℕ) - if k = j then 1 else 0)) (Finset.mem_univ j)]
  simp only [if_true]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [this]

/-- Along `z' = cubicFun f z`, `verSq (z t) α` has derivative `pushSq f (z t) α`. -/
theorem verSq_hasDerivWithinAt (f : CubicPP n) {z : ℝ → Fin n → ℝ} {s : Set ℝ} {t : ℝ}
    (hz : HasDerivWithinAt z (cubicFun f (z t)) s t) (α : MI n 2) :
    HasDerivWithinAt (fun u => verSq n (z u) α) (pushSq n f (z t) α) s t := by
  have hk : ∀ k, HasDerivWithinAt (fun u => z u k) (cubicFun f (z t) k) s t :=
    fun k => hasDerivWithinAt_pi.mp hz k
  have hpow : ∀ k ∈ Finset.univ, HasDerivWithinAt (fun u => z u k ^ (α.1 k : ℕ))
      ((((α.1 k : ℕ) : ℕ) : ℝ) * z t k ^ ((α.1 k : ℕ) - 1) * cubicFun f (z t) k) s t :=
    fun k _ => (hk k).pow _
  have hprod := HasDerivWithinAt.finsetProd hpow
  have hmul := hprod.const_mul (MI.mult n 2 α : ℝ)
  unfold verSq pushSq
  convert hmul using 1
  all_goals first
    | (rw [Finset.mul_sum, Finset.mul_sum]
       refine Finset.sum_congr rfl fun j _ => ?_
       rw [smul_eq_mul, ← monoSubSq_eq n (z t) α j]
       ring)
    | (funext u; simp [Finset.prod_apply])

/-- `‖verSq x‖ ≤ 2` on the unit ball of the sup norm. -/
theorem verSq_norm_le (x : Fin n → ℝ) (hx : ‖x‖ ≤ 1) : ‖fun α => verSq n x α‖ ≤ 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro α
  unfold verSq
  rw [Real.norm_eq_abs, abs_mul]
  have hm : |(MI.mult n 2 α : ℝ)| ≤ 2 := by
    unfold MI.mult
    have hp : (1 : ℚ) ≤ ∏ k, ((α.1 k : ℕ).factorial : ℚ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.succ_le_of_lt (Finset.prod_pos fun k _ => Nat.factorial_pos _)
    have h2 : (0 : ℚ) ≤ ((Nat.factorial 2 : ℕ) : ℚ) / ∏ k, ((α.1 k : ℕ).factorial : ℚ) := by
      positivity
    have : ((Nat.factorial 2 : ℕ) : ℚ) / ∏ k, ((α.1 k : ℕ).factorial : ℚ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      norm_num [Nat.factorial]
      nlinarith
    rw [abs_of_nonneg (by exact_mod_cast h2)]
    exact_mod_cast this
  have hpr : |∏ k, x k ^ (α.1 k : ℕ)| ≤ 1 := by
    rw [abs_prod]
    apply Finset.prod_le_one
    · intro k _; exact abs_nonneg _
    · intro k _
      rw [abs_pow]
      apply pow_le_one₀ (abs_nonneg _)
      have := norm_le_pi_norm x k
      rw [Real.norm_eq_abs] at this
      linarith
  calc |(MI.mult n 2 α : ℝ)| * |∏ k, x k ^ (α.1 k : ℕ)| ≤ 2 * 1 :=
        mul_le_mul hm hpr (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

/-! ### Lipschitz bound and uniqueness -/

/-- Explicit Lipschitz constant of `balanceFunSq w` on the closed ball of radius `R`. -/
noncomputable def balanceLipSq (w : WProtocol (MI n 2)) (R : ℝ) : ℝ :=
  2 * R * ∑ sh, ∑ α, |(w sh : ℝ)| * |(net sh α : ℝ)|

theorem balanceFunSq_lipschitzOnWith (w : WProtocol (MI n 2)) (R : ℝ) :
    LipschitzOnWith (Real.toNNReal (balanceLipSq n w R)) (balanceFunSq n w)
      (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv v' hv'
  rw [Metric.mem_closedBall, dist_zero_right] at hv hv'
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hv
  have hK : 0 ≤ balanceLipSq n w R := by
    unfold balanceLipSq
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg fun sh _ => Finset.sum_nonneg fun α _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [Real.coe_toNNReal _ hK]
  have hd : 0 ≤ dist v v' := dist_nonneg
  have hcv : ∀ a, |v a| ≤ R := fun a => by
    have := norm_le_pi_norm v a
    rw [Real.norm_eq_abs] at this
    linarith
  have hcv' : ∀ a, |v' a| ≤ R := fun a => by
    have := norm_le_pi_norm v' a
    rw [Real.norm_eq_abs] at this
    linarith
  have hdc : ∀ a, |v a - v' a| ≤ dist v v' := fun a => by
    have := dist_le_pi_dist v v' a
    rwa [Real.dist_eq] at this
  rw [dist_pi_le_iff (mul_nonneg hK hd)]
  intro α
  rw [Real.dist_eq]
  unfold balanceFunSq
  rw [← Finset.sum_sub_distrib]
  calc |∑ sh, ((w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)
          - (w sh : ℝ) * v' sh.1 * v' sh.2.1 * (net sh α : ℝ))|
      ≤ ∑ sh, |(w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)
          - (w sh : ℝ) * v' sh.1 * v' sh.2.1 * (net sh α : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ sh, |(w sh : ℝ)| * |(net sh α : ℝ)| * (2 * R * dist v v') := by
        apply Finset.sum_le_sum
        intro sh _
        have e : (w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)
            - (w sh : ℝ) * v' sh.1 * v' sh.2.1 * (net sh α : ℝ)
            = ((w sh : ℝ) * (net sh α : ℝ)) * (v sh.1 * v sh.2.1 - v' sh.1 * v' sh.2.1) := by
          ring
        rw [e, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_mul_sub_mul_le (hcv _) (hcv' _) (hdc _) (hdc _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ ∑ sh, (∑ α', |(w sh : ℝ)| * |(net sh α' : ℝ)|) * (2 * R * dist v v') := by
        apply Finset.sum_le_sum
        intro sh _
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Finset.single_le_sum (f := fun α' => |(w sh : ℝ)| * |(net sh α' : ℝ)|)
          (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ α)
    _ = balanceLipSq n w R * dist v v' := by
        unfold balanceLipSq
        rw [← Finset.sum_mul]
        ring

/-- **Proposition 4.2 for the squaring.** Let `w` realise `demandSq f` and `z` solve the cubic
field on `[0,T]` in the unit ball. Every solution `u` of `balanceFunSq w` on `[0,T]` with
`u 0 = verSq (z 0)` equals `verSq ∘ z` on `[0,T]`. -/
theorem lifted_solution_uniqueSq (f : CubicPP n) (w : WProtocol (MI n 2))
    (hr : Realizes (veroneseLift n 2) w (demandSq n f))
    {T : ℝ} {z : ℝ → Fin n → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt z (cubicFun f (z t)) (Icc 0 T) t)
    (hzb : ∀ t ∈ Icc (0 : ℝ) T, ‖z t‖ ≤ 1)
    {u : ℝ → MI n 2 → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFunSq n w (u t)) (Icc 0 T) t)
    (hu0 : u 0 = fun α => verSq n (z 0) α) :
    EqOn u (fun t α => verSq n (z t) α) (Icc 0 T) := by
  rcases lt_or_ge 0 T with hT | hT
  · have hcont : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hlip := balanceFunSq_lipschitzOnWith n w (max M 2)
    have h_hv : ∀ t ∈ Ico (0 : ℝ) T,
        LipschitzOnWith (Real.toNNReal (balanceLipSq n w (max M 2)))
          ((fun _ : ℝ => balanceFunSq n w) t)
          ((fun _ : ℝ => Metric.closedBall (0 : MI n 2 → ℝ) (max M 2)) t) := fun _ _ => hlip
    have hverd : ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun t α => verSq n (z t) α) (balanceFunSq n w (verSq n (z t)))
          (Icc 0 T) t := by
      intro t ht
      rw [hasDerivWithinAt_pi]
      intro α
      have := verSq_hasDerivWithinAt n f (hz t ht) α
      rw [← balanceFunSq_verSq n f w hr] at this
      exact this
    exact ODE_solution_unique_of_mem_Icc_right h_hv
      (fun t ht => (hu t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Icc_to_Ici' ht (hu t ⟨ht.1, ht.2.le⟩))
      (fun t ht => by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact le_trans (hM t ⟨ht.1, ht.2.le⟩) (le_max_left _ _))
      (fun t ht => (hverd t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Icc_to_Ici' ht (hverd t ⟨ht.1, ht.2.le⟩))
      (fun t ht => by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact le_trans (verSq_norm_le n (z t) (hzb t ⟨ht.1, ht.2.le⟩)) (le_max_right _ _))
      hu0
  · intro t ht
    have : t = 0 := le_antisymm (le_trans ht.2 hT) ht.1
    subst this
    exact hu0

/-! ### Multinomial identities and the readout for the squaring -/

/-- `Σ_α verSq x α = (Σ_k x_k)²`. -/
theorem sum_verSq_eq {m : ℕ} (x : Fin m → ℝ) : ∑ α, verSq m x α = (∑ k, x k) ^ 2 := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  symm
  refine Finset.sum_bij
    (fun k hk => (⟨fun i => ⟨k i, by
        have hs : ∑ j, k j = 2 := (Finset.mem_piAntidiag.mp hk).1
        have := Finset.single_le_sum (f := k) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega⟩, by
        have hs := (Finset.mem_piAntidiag.mp hk).1
        simpa using hs⟩ : MI m 2)) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_univ _
  · intro k₁ _ k₂ _ h
    funext i
    have := congrArg (fun α : MI m 2 => ((α.1 i : ℕ))) h
    simpa using this
  · intro α _
    refine ⟨fun i => (α.1 i : ℕ), ?_, ?_⟩
    · rw [Finset.mem_piAntidiag]
      exact ⟨by simpa using α.2, fun i _ => Finset.mem_univ i⟩
    · apply Subtype.ext
      funext i
      apply Fin.ext
      rfl
  · intro k hk
    have hs := (Finset.mem_piAntidiag.mp hk).1
    unfold verSq MI.mult
    simp only
    congr 1
    have hspec := Nat.multinomial_spec Finset.univ k
    rw [hs] at hspec
    have hne : (∏ i, ((k i).factorial : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    rw [eq_div_iff hne, mul_comm]
    exact_mod_cast hspec

theorem verSq_scaleAt {m : ℕ} (j : Fin m) (s : ℝ) (x : Fin m → ℝ) (α : MI m 2) :
    verSq m (scaleAt j s x) α = s ^ (α.1 j : ℕ) * verSq m x α := by
  unfold verSq scaleAt
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [prod_ite_pow j s (fun k => (α.1 k : ℕ))]
  ring

/-- **Reconstruction identity (squaring).** `Σ_α α_j verSq x α = 2 x_j (Σ_k x_k)`. -/
theorem sum_weight_verSq {m : ℕ} (x : Fin m → ℝ) (j : Fin m) :
    ∑ α, ((α.1 j : ℕ) : ℝ) * verSq m x α = 2 * x j * ∑ k, x k := by
  have h1 : HasDerivAt (fun s : ℝ => ∑ α, s ^ (α.1 j : ℕ) * verSq m x α)
      (∑ α, ((α.1 j : ℕ) : ℝ) * (1 : ℝ) ^ ((α.1 j : ℕ) - 1) * verSq m x α) 1 :=
    HasDerivAt.fun_sum fun α _ => (hasDerivAt_pow (α.1 j : ℕ) (1 : ℝ)).mul_const (verSq m x α)
  have hlin : HasDerivAt (fun s : ℝ => ∑ k, scaleAt j s x k) (x j) 1 := by
    have : HasDerivAt (fun s : ℝ => ∑ k, scaleAt j s x k)
        (∑ k, (if k = j then (1 : ℝ) else 0) * x k) 1 := by
      apply HasDerivAt.fun_sum
      intro k _
      unfold scaleAt
      by_cases hk : k = j
      · simp only [if_pos hk]
        exact (hasDerivAt_id (1 : ℝ)).mul_const (x k)
      · simp only [if_neg hk]
        exact (hasDerivAt_const (1 : ℝ) (1 * x k)).congr_deriv (by ring)
    simpa [ite_mul, Finset.sum_ite_eq'] using this
  have h2 := hlin.pow 2
  have heq : (fun s : ℝ => ∑ α, s ^ (α.1 j : ℕ) * verSq m x α)
      = fun s => (∑ k, scaleAt j s x k) ^ 2 := by
    funext s
    rw [← sum_verSq_eq]
    simp only [verSq_scaleAt]
  rw [heq] at h1
  have hu := h1.unique h2
  have hs1' : ∑ k, scaleAt j 1 x k = ∑ k, x k := by
    simp [scaleAt]
  simp only [one_pow, mul_one] at hu
  rw [hu, hs1']
  push_cast
  ring

/-- Readout weights of the squared protocol: `w_α = (1/2) Σ_j c_j α_j`. -/
noncomputable def readWSq {m : ℕ} (c : Fin m → ℝ) (α : MI m 2) : ℝ :=
  (1 / 2) * ∑ j, c j * ((α.1 j : ℕ) : ℝ)

theorem readWSq_mem {m : ℕ} (c : Fin m → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (α : MI m 2) : 0 ≤ readWSq c α ∧ readWSq c α ≤ 1 := by
  unfold readWSq
  have hsum : ∑ j, ((α.1 j : ℕ) : ℝ) = 2 := by exact_mod_cast α.2
  constructor
  · exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hc0 j) (by positivity))
  · have : ∑ j, c j * ((α.1 j : ℕ) : ℝ) ≤ ∑ j, ((α.1 j : ℕ) : ℝ) :=
      Finset.sum_le_sum fun j _ => by
        have : (0 : ℝ) ≤ ((α.1 j : ℕ) : ℝ) := by positivity
        nlinarith [hc1 j]
    rw [hsum] at this
    linarith

/-- On the degree-2 Veronese image the readout `Σ_α readWSq c α v_α` is `(Σ_j c_j z_j)(Σ_k z_k)`. -/
theorem readoutSq_verSq {m : ℕ} (c : Fin m → ℝ) (z : Fin m → ℝ) :
    ∑ α, readWSq c α * verSq m z α = (∑ j, c j * z j) * ∑ k, z k := by
  have h : ∀ α, readWSq c α * verSq m z α
      = ∑ j, (1 / 2 * c j) * (((α.1 j : ℕ) : ℝ) * verSq m z α) := by
    intro α
    unfold readWSq
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, sum_weight_verSq]
  ring

end NAPTransport
end Ripple

/-
  Ripple.LPP.NAPPipelineODE — the ODE half of Theorem 2 of the PP-to-NAP write-up
  (the pipeline preserves the computation), composing `NAPPipeline`, `NAPTimeChange`,
  `NAPConjugacy` and `NAPLipschitz`.

  * `quadFun g x j = Σ_μ g.coef j μ x^μ` is the quadratic field of a syntactic 2-PP `g`;
  * `slackMap j₀ λ x = (r, x')` with `r = (1 − λ) x_{j₀}`, `x'_{j₀} = λ x_{j₀}`, `x'_j = x_j` (Step 1);
  * `slackField j₀ λ` is the slack-trick field `g` of Step 1 (substitute `x_{j₀} = u/λ`);
  * `fieldFun_liftR2`: the quartic field of `liftR2 g j₀ λ` is `x_0² · slackField` (Step 2, the
    evaluation identity behind the r²-trick), and `slackField (slackMap x) = slackMap (quadFun x)`;
  * `coord_pos`: along a PP trajectory in the simplex, a species with positive initial value stays
    positive (`x_j(t) ≥ x_j(0) e^{−Ct}`);
  * `sum_ver_eq` (multinomial theorem) and `sum_weight_ver`: `Σ_α α_j ver x α = 3 x_j (Σ x)²`;
    `readout_ver`: the NAP readout `Σ_α readW c α · v_α` equals `(Σ_j c_j z_j)(Σ z)²` on `v = ver z`;
  * `pipeline_ode` (**Theorem 2, ODE half**) and `pp_to_nap_ode` (with the realisation of
    `exists_nap_realizing_pipeline`).
-/

import Ripple.LPP.NAPLipschitz
import Ripple.LPP.NAPPipeline
import Ripple.LPP.NAPTimeChange
import Mathlib.Data.Nat.Choose.Multinomial

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

/-! ### The quadratic field and the slack trick -/

/-- Monomial of a weight-2 multi-index. -/
noncomputable def mono2 (x : Fin n → ℝ) (μ : MI n 2) : ℝ := ∏ k, x k ^ (μ.1 k : ℕ)

/-- The quadratic field of a syntactic 2-PP coefficient table. -/
noncomputable def quadFun (g : QuadPP n) (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ μ, (g.coef j μ : ℝ) * mono2 n x μ

/-- Step 1 of the pipeline: slot `0` is the slack `r = (1 − λ) x_{j₀}`, slot `j.succ` is `x_j`,
except `u = λ x_{j₀}` in slot `j₀.succ`. -/
noncomputable def slackMap (j₀ : Fin n) (lam : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases ((1 - lam) * x j₀) (fun j => (if j = j₀ then lam else 1) * x j)

@[simp] theorem slackMap_zero (j₀ : Fin n) (lam : ℝ) (x : Fin n → ℝ) :
    slackMap n j₀ lam x 0 = (1 - lam) * x j₀ := rfl

@[simp] theorem slackMap_succ (j₀ : Fin n) (lam : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    slackMap n j₀ lam x j.succ = (if j = j₀ then lam else 1) * x j := rfl

/-- The substitution `ι`: back from slots `1..n` to the original species (`x_{j₀} = u/λ`). -/
noncomputable def unshrink (j₀ : Fin n) (lam : ℝ) (x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun j => (if j = j₀ then lam⁻¹ else 1) * x j.succ

/-- The slack-trick field `g` of Step 1 on `n + 1` species (it does not involve slot `0`). -/
noncomputable def slackField (g : QuadPP n) (j₀ : Fin n) (lam : ℝ) (x : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.cases ((1 - lam) * quadFun n g (unshrink n j₀ lam x) j₀)
    (fun j => (if j = j₀ then lam else 1) * quadFun n g (unshrink n j₀ lam x) j)

theorem unshrink_slackMap (j₀ : Fin n) {lam : ℝ} (hlam : lam ≠ 0) (x : Fin n → ℝ) :
    unshrink n j₀ lam (slackMap n j₀ lam x) = x := by
  funext j
  simp only [unshrink, slackMap_succ]
  by_cases hj : j = j₀
  · rw [if_pos hj, if_pos hj, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  · rw [if_neg hj, if_neg hj, one_mul, one_mul]

/-- On the image of `slackMap`, the slack-trick field is the pushforward of the PP field. -/
theorem slackField_slackMap (g : QuadPP n) (j₀ : Fin n) {lam : ℝ} (hlam : lam ≠ 0)
    (x : Fin n → ℝ) :
    slackField n g j₀ lam (slackMap n j₀ lam x) = slackMap n j₀ lam (quadFun n g x) := by
  funext j'
  refine Fin.cases ?_ (fun j => ?_) j'
  · simp only [slackField, Fin.cases_zero, slackMap_zero, unshrink_slackMap n j₀ hlam]
  · simp only [slackField, Fin.cases_succ, slackMap_succ, unshrink_slackMap n j₀ hlam]

/-! ### The evaluation identity of the r²-trick -/

/-- The weight-4 index `r² ⊕ μ` on `n + 1` species. -/
def cons2 (μ : MI n 2) : MI (n + 1) 4 :=
  MI.ofFun (n + 1) (Fin.cases 2 (fun j => (μ.1 j : ℕ)))
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

@[simp] theorem cons2_val_zero (μ : MI n 2) : ((cons2 n μ).1 0 : ℕ) = 2 := rfl

@[simp] theorem cons2_val_succ (μ : MI n 2) (j : Fin n) :
    ((cons2 n μ).1 j.succ : ℕ) = (μ.1 j : ℕ) := rfl

theorem tail_cons2 (μ : MI n 2) (h : ((cons2 n μ).1 0 : ℕ) = 2) : tail n (cons2 n μ) h = μ :=
  Subtype.ext (funext fun _ => Fin.ext rfl)

theorem cons2_tail (μ' : MI (n + 1) 4) (h : (μ'.1 0 : ℕ) = 2) : cons2 n (tail n μ' h) = μ' := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  induction k using Fin.cases with
  | zero => exact h.symm
  | succ j => rfl

theorem cons2_injective : Function.Injective (cons2 n) := by
  intro a b h
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun μ' : MI (n + 1) 4 => ((μ'.1 j.succ : ℕ))) h

/-- A sum over weight-4 indices supported on slack exponent `2` is a sum over weight-2 indices. -/
theorem sum_slack_two (F : MI (n + 1) 4 → ℝ) (hF : ∀ μ', (μ'.1 0 : ℕ) ≠ 2 → F μ' = 0) :
    ∑ μ', F μ' = ∑ μ, F (cons2 n μ) := by
  rw [← Finset.sum_image (f := F) (s := Finset.univ) (g := cons2 n)
    (fun a _ b _ h => cons2_injective n h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro μ' _ hμ'
  apply hF
  intro h
  exact hμ' (Finset.mem_image.mpr ⟨tail n μ' h, Finset.mem_univ _, cons2_tail n μ' h⟩)

theorem mono4_cons2 (x : Fin (n + 1) → ℝ) (μ : MI n 2) :
    mono4 (n + 1) x (cons2 n μ) = x 0 ^ 2 * ∏ k, x k.succ ^ (μ.1 k : ℕ) := by
  unfold mono4
  rw [Fin.prod_univ_succ]
  simp only [cons2_val_zero, cons2_val_succ]

theorem prod_ite_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (c : ℝ) (e : ι → ℕ) :
    ∏ k, (if k = j then c else 1) ^ e k = c ^ e j := by
  rw [Finset.prod_congr rfl (fun k _ => show (if k = j then c else 1) ^ e k
      = if k = j then c ^ e k else 1 by split_ifs <;> simp),
    Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]

theorem mono2_unshrink (j₀ : Fin n) (lam : ℝ) (x : Fin (n + 1) → ℝ) (μ : MI n 2) :
    mono2 n (unshrink n j₀ lam x) μ = lam⁻¹ ^ (μ.1 j₀ : ℕ) * ∏ k, x k.succ ^ (μ.1 k : ℕ) := by
  unfold mono2 unshrink
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [prod_ite_pow j₀ lam⁻¹ (fun k => (μ.1 k : ℕ))]

theorem liftCoef_cons2 (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (j' : Fin (n + 1)) (μ : MI n 2) :
    liftCoef n g j₀ lam j' (cons2 n μ) =
      Fin.cases ((1 - lam) * lam⁻¹ ^ (μ.1 j₀ : ℕ) * g.coef j₀ μ)
        (fun j => (if j = j₀ then lam else 1) * lam⁻¹ ^ (μ.1 j₀ : ℕ) * g.coef j μ) j' := by
  unfold liftCoef
  rw [dif_pos (cons2_val_zero n μ), tail_cons2]

theorem liftR2_coef (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam) (j' : Fin (n + 1))
    (μ' : MI (n + 1) 4) : (liftR2 n g j₀ lam hlam).coef j' μ' = liftCoef n g j₀ lam j' μ' := rfl

/-- **Evaluation identity (Step 2).** The quartic field of the lifted protocol `liftR2 g j₀ λ`
is `x_0²` times the slack-trick field. -/
theorem fieldFun_liftR2 (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam)
    (x : Fin (n + 1) → ℝ) :
    fieldFun (n + 1) (liftR2 n g j₀ lam hlam) x = fun j' => x 0 ^ 2 * slackField n g j₀ lam x j' := by
  funext j'
  unfold fieldFun
  rw [sum_slack_two n _ (fun μ' h => by
    rw [liftR2_coef, liftCoef_eq_zero_of_slack n g j₀ lam j' μ' h, Rat.cast_zero, zero_mul])]
  simp only [liftR2_coef, liftCoef_cons2, mono4_cons2]
  refine Fin.cases ?_ (fun j => ?_) j'
  · simp only [Fin.cases_zero, slackField, quadFun, mono2_unshrink, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  · simp only [Fin.cases_succ, slackField, quadFun, mono2_unshrink, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hj : j = j₀
    · simp only [if_pos hj]
      push_cast
      ring
    · simp only [if_neg hj]
      push_cast
      ring

/-- Composite form: on the image of `slackMap`, the lifted quartic field is
`((1 − λ) x_{j₀})² · slackMap (quadFun x)`. -/
theorem fieldFun_liftR2_slackMap (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam : 0 < lam)
    (x : Fin n → ℝ) :
    fieldFun (n + 1) (liftR2 n g j₀ lam hlam) (slackMap n j₀ lam x)
      = ((1 - (lam : ℝ)) * x j₀) ^ 2 • slackMap n j₀ lam (quadFun n g x) := by
  rw [fieldFun_liftR2, slackField_slackMap n g j₀ (by exact_mod_cast hlam.ne') x]
  funext j'
  simp only [slackMap_zero, Pi.smul_apply, smul_eq_mul]

/-! ### Calculus along the slack map -/

theorem slackMap_hasDerivWithinAt {x : ℝ → Fin n → ℝ} {x' : Fin n → ℝ} {s : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' s t) (j₀ : Fin n) (lam : ℝ) :
    HasDerivWithinAt (fun t => slackMap n j₀ lam (x t)) (slackMap n j₀ lam x') s t := by
  rw [hasDerivWithinAt_pi]
  intro j'
  have hk : ∀ k, HasDerivWithinAt (fun t => x t k) (x' k) s t := fun k => hasDerivWithinAt_pi.mp hx k
  induction j' using Fin.cases with
  | zero => simpa only [slackMap_zero] using (hk j₀).const_mul (1 - lam)
  | succ j => simpa only [slackMap_succ] using (hk j).const_mul (if j = j₀ then lam else 1)

theorem continuous_slackMap (j₀ : Fin n) (lam : ℝ) : Continuous (slackMap n j₀ lam) := by
  apply continuous_pi
  intro j'
  induction j' using Fin.cases with
  | zero => simpa only [slackMap_zero] using continuous_const.mul (continuous_apply j₀)
  | succ j => simpa only [slackMap_succ] using continuous_const.mul (continuous_apply j)

theorem sum_liftReadout_aux (j₀ : Fin n) (lam : ℝ) (c x : Fin n → ℝ) :
    c j₀ * ((1 - lam) * x j₀) + ∑ j, c j * ((if j = j₀ then lam else 1) * x j)
      = ∑ j, c j * x j := by
  have hsplit : ∀ j, c j * ((if j = j₀ then lam else 1) * x j)
      = c j * x j + (if j = j₀ then (lam - 1) * (c j * x j) else 0) := by
    intro j
    split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j₀, Finset.mem_univ,
    if_true]
  ring

theorem sum_slackMap (j₀ : Fin n) (lam : ℝ) (x : Fin n → ℝ) :
    ∑ j', slackMap n j₀ lam x j' = ∑ j, x j := by
  rw [Fin.sum_univ_succ]
  simp only [slackMap_zero, slackMap_succ]
  have := sum_liftReadout_aux n j₀ lam (fun _ => 1) x
  simp only [one_mul] at this
  exact this

theorem slackMap_norm_le (j₀ : Fin n) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (x : Fin n → ℝ)
    (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1) : ‖slackMap n j₀ lam x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j'
  rw [Real.norm_eq_abs]
  induction j' using Fin.cases with
  | zero =>
    rw [slackMap_zero, abs_of_nonneg (mul_nonneg (by linarith) (hx0 j₀))]
    exact mul_le_one₀ (by linarith) (hx0 j₀) (hx1 j₀)
  | succ j =>
    rw [slackMap_succ]
    have hc0 : 0 ≤ (if j = j₀ then lam else 1) := by split_ifs <;> linarith
    have hc1 : (if j = j₀ then lam else 1) ≤ 1 := by split_ifs <;> linarith
    rw [abs_of_nonneg (mul_nonneg hc0 (hx0 j))]
    exact mul_le_one₀ hc1 (hx0 j) (hx1 j)

/-! ### Positivity of the shrunk species -/

theorem mono2_le (x : Fin n → ℝ) (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1) (μ : MI n 2)
    (j : Fin n) (hj : 0 < (μ.1 j : ℕ)) : mono2 n x μ ≤ x j := by
  unfold mono2
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have h1 : ∏ k ∈ Finset.univ.erase j, x k ^ (μ.1 k : ℕ) ≤ 1 :=
    Finset.prod_le_one (fun k _ => pow_nonneg (hx0 k) _) (fun k _ => pow_le_one₀ (hx0 k) (hx1 k))
  have h2 : x j ^ (μ.1 j : ℕ) ≤ x j := pow_le_of_le_one (hx0 j) (hx1 j) (by omega)
  have h3 : 0 ≤ x j ^ (μ.1 j : ℕ) := pow_nonneg (hx0 j) _
  calc x j ^ (μ.1 j : ℕ) * ∏ k ∈ Finset.univ.erase j, x k ^ (μ.1 k : ℕ)
      ≤ x j ^ (μ.1 j : ℕ) * 1 := mul_le_mul_of_nonneg_left h1 h3
    _ ≤ x j := by rw [mul_one]; exact h2

/-- The sign condition gives `g_j(x) ≥ −C x_j` on the unit cube, `C = Σ_μ |g.coef j μ|`. -/
theorem quadFun_ge (g : QuadPP n) (x : Fin n → ℝ) (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1)
    (j : Fin n) : -(∑ μ, |(g.coef j μ : ℝ)|) * x j ≤ quadFun n g x j := by
  unfold quadFun
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro μ _
  have hm0 : 0 ≤ mono2 n x μ := Finset.prod_nonneg fun k _ => pow_nonneg (hx0 k) _
  by_cases hc : 0 ≤ g.coef j μ
  · have h1 : 0 ≤ (g.coef j μ : ℝ) * mono2 n x μ := mul_nonneg (by exact_mod_cast hc) hm0
    have h2 : 0 ≤ |(g.coef j μ : ℝ)| * x j := mul_nonneg (abs_nonneg _) (hx0 j)
    linarith
  · rw [not_le] at hc
    have hle := mono2_le n x hx0 hx1 μ j (g.sign j μ hc)
    have hcr : (g.coef j μ : ℝ) < 0 := by exact_mod_cast hc
    rw [abs_of_neg hcr]
    nlinarith

/-- **Positivity.** Along a trajectory of a syntactic 2-PP in the unit cube, a species with
positive initial value stays positive: `x_j(t) e^{Ct} ≥ x_j(0)`. -/
theorem coord_pos (g : QuadPP n) {x : ℝ → Fin n → ℝ} (j : Fin n)
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t)
    (hx0 : ∀ t, 0 ≤ t → ∀ k, 0 ≤ x t k) (hx1 : ∀ t, 0 ≤ t → ∀ k, x t k ≤ 1)
    (hpos : 0 < x 0 j) {t : ℝ} (ht : 0 ≤ t) : 0 < x t j := by
  set C : ℝ := ∑ μ, |(g.coef j μ : ℝ)| with hC
  have he : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => Real.exp (C * s) * x s j)
      (Real.exp (C * s) * C * x s j + Real.exp (C * s) * quadFun n g (x s) j) (Ici 0) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => Real.exp (C * s)) (Real.exp (C * s) * C) s := by
      have := ((hasDerivAt_id s).const_mul C).exp
      simpa only [id, mul_one] using this
    exact h1.hasDerivWithinAt.mul (hasDerivWithinAt_pi.mp (hx s hs) j)
  have hmono : MonotoneOn (fun s => Real.exp (C * s) * x s j) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun s hs => (he s hs).continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs ⊢
      exact (he s (le_of_lt hs)).mono Ioi_subset_Ici_self
    · intro s hs
      rw [interior_Ici] at hs
      have hq := quadFun_ge n g (x s) (hx0 s hs.le) (hx1 s hs.le) j
      have hE := Real.exp_pos (C * s)
      have : 0 ≤ C * x s j + quadFun n g (x s) j := by linarith
      nlinarith [mul_nonneg hE.le this]
  have h := hmono (Set.self_mem_Ici) (show t ∈ Set.Ici 0 from ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul] at h
  by_contra hneg
  rw [not_lt] at hneg
  have hE := Real.exp_pos (C * t)
  nlinarith

/-! ### The multinomial theorem for `ver` and the readout -/

/-- **Multinomial theorem.** `Σ_α ver x α = (Σ_k x_k)³`. -/
theorem sum_ver_eq {m : ℕ} (x : Fin m → ℝ) : ∑ α, ver m x α = (∑ k, x k) ^ 3 := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  symm
  refine Finset.sum_bij
    (fun k hk => (⟨fun i => ⟨k i, by
        have hs : ∑ j, k j = 3 := (Finset.mem_piAntidiag.mp hk).1
        have := Finset.single_le_sum (f := k) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega⟩, by
        have hs := (Finset.mem_piAntidiag.mp hk).1
        simpa using hs⟩ : MI m 3)) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_univ _
  · intro k₁ _ k₂ _ h
    funext i
    have := congrArg (fun α : MI m 3 => ((α.1 i : ℕ))) h
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
    unfold ver MI.mult
    simp only
    congr 1
    have hspec := Nat.multinomial_spec Finset.univ k
    rw [hs] at hspec
    have hne : (∏ i, ((k i).factorial : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    rw [eq_div_iff hne, mul_comm]
    exact_mod_cast hspec

/-- Scaling of one coordinate. -/
noncomputable def scaleAt {m : ℕ} (j : Fin m) (s : ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun k => (if k = j then s else 1) * x k

theorem ver_scaleAt {m : ℕ} (j : Fin m) (s : ℝ) (x : Fin m → ℝ) (α : MI m 3) :
    ver m (scaleAt j s x) α = s ^ (α.1 j : ℕ) * ver m x α := by
  unfold ver scaleAt
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [prod_ite_pow j s (fun k => (α.1 k : ℕ))]
  ring

/-- **Reconstruction identity.** `Σ_α α_j ver x α = 3 x_j (Σ_k x_k)²`. -/
theorem sum_weight_ver {m : ℕ} (x : Fin m → ℝ) (j : Fin m) :
    ∑ α, ((α.1 j : ℕ) : ℝ) * ver m x α = 3 * x j * (∑ k, x k) ^ 2 := by
  have h1 : HasDerivAt (fun s : ℝ => ∑ α, s ^ (α.1 j : ℕ) * ver m x α)
      (∑ α, ((α.1 j : ℕ) : ℝ) * (1 : ℝ) ^ ((α.1 j : ℕ) - 1) * ver m x α) 1 :=
    HasDerivAt.fun_sum fun α _ => (hasDerivAt_pow (α.1 j : ℕ) (1 : ℝ)).mul_const (ver m x α)
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
  have h2 := hlin.pow 3
  have heq : (fun s : ℝ => ∑ α, s ^ (α.1 j : ℕ) * ver m x α)
      = fun s => (∑ k, scaleAt j s x k) ^ 3 := by
    funext s
    rw [← sum_ver_eq]
    simp only [ver_scaleAt]
  rw [heq] at h1
  have hu := h1.unique h2
  have hs1 : (fun k => scaleAt j 1 x k) = x := by
    funext k
    simp [scaleAt]
  have hs1' : ∑ k, scaleAt j 1 x k = ∑ k, x k := by
    simp [scaleAt]
  simp only [one_pow, mul_one] at hu
  rw [hu, hs1']
  push_cast
  ring

/-- Readout weights of the cubed protocol: `w_α = (1/3) Σ_j c_j α_j`. -/
noncomputable def readW {m : ℕ} (c : Fin m → ℝ) (α : MI m 3) : ℝ :=
  (1 / 3) * ∑ j, c j * ((α.1 j : ℕ) : ℝ)

theorem readW_mem {m : ℕ} (c : Fin m → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (α : MI m 3) : 0 ≤ readW c α ∧ readW c α ≤ 1 := by
  unfold readW
  have hsum : ∑ j, ((α.1 j : ℕ) : ℝ) = 3 := by exact_mod_cast α.2
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => mul_nonneg (hc0 j) (by positivity))
  · have : ∑ j, c j * ((α.1 j : ℕ) : ℝ) ≤ ∑ j, ((α.1 j : ℕ) : ℝ) :=
      Finset.sum_le_sum fun j _ => by
        have : (0 : ℝ) ≤ ((α.1 j : ℕ) : ℝ) := by positivity
        nlinarith [hc1 j]
    rw [hsum] at this
    linarith

/-- On the Veronese image the linear readout `Σ_α readW c α v_α` is `(Σ_j c_j z_j)(Σ_k z_k)²`. -/
theorem readout_ver {m : ℕ} (c : Fin m → ℝ) (z : Fin m → ℝ) :
    ∑ α, readW c α * ver m z α = (∑ j, c j * z j) * (∑ k, z k) ^ 2 := by
  unfold readW
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h := sum_weight_ver z j
  calc ∑ α, 1 / 3 * (c j * ((α.1 j : ℕ) : ℝ)) * ver m z α
      = (1 / 3 * c j) * ∑ α, ((α.1 j : ℕ) : ℝ) * ver m z α := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun α _ => by ring
    _ = c j * z j * (∑ k, z k) ^ 2 := by rw [h]; ring

/-- Lifted readout coefficients: the slack carries the weight of the shrunk species `j₀`. -/
def liftReadout (j₀ : Fin n) (c : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases (c j₀) c

theorem liftReadout_slackMap (j₀ : Fin n) (lam : ℝ) (c x : Fin n → ℝ) :
    ∑ j', liftReadout n j₀ c j' * slackMap n j₀ lam x j' = ∑ j, c j * x j := by
  rw [Fin.sum_univ_succ]
  simp only [liftReadout, Fin.cases_zero, Fin.cases_succ, slackMap_zero, slackMap_succ]
  exact sum_liftReadout_aux n j₀ lam c x

/-! ### The clock of the pipeline -/

/-- The slack curve `y(s) = slackMap (x (max s 0))` (continuous on `ℝ`). -/
noncomputable def slackCurve (j₀ : Fin n) (lam : ℝ) (x : ℝ → Fin n → ℝ) (s : ℝ) : Fin (n + 1) → ℝ :=
  slackMap n j₀ lam (x (max s 0))

/-- The slack coordinate. -/
def slackCoord (v : Fin (n + 1) → ℝ) : ℝ := v 0

theorem slackData_of_simplex (g : QuadPP n) (j₀ : Fin n) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t)
    (hxs : ∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1)
    (hx0 : 0 < x 0 j₀) :
    NAPTimeChange.SlackData (slackCurve n j₀ lam x) (slackCoord n) := by
  have hle : ∀ t, 0 ≤ t → ∀ j, x t j ≤ 1 := fun t ht j => by
    rw [← (hxs t ht).2]
    exact Finset.single_le_sum (fun k _ => (hxs t ht).1 k) (Finset.mem_univ j)
  have hpos : ∀ t, 0 ≤ t → 0 < x t j₀ := fun t ht =>
    coord_pos n g j₀ hx (fun s hs => (hxs s hs).1) hle hx0 ht
  have hxc : ContinuousOn x (Ici 0) := fun t ht => (hx t ht).continuousWithinAt
  refine ⟨?_, continuous_apply 0, ?_, ?_⟩
  · exact (continuous_slackMap n j₀ lam).comp
      (hxc.comp_continuous (continuous_id.max continuous_const) (fun s => le_max_right s 0))
  · intro t ht
    simp only [slackCoord, slackCurve, slackMap_zero, max_eq_left ht]
    exact mul_pos (by linarith) (hpos t ht)
  · intro t ht
    simp only [slackCoord, slackCurve, slackMap_zero, max_eq_left ht]
    exact mul_le_one₀ (by linarith) ((hxs t ht).1 j₀) (hle t ht j₀)

/-! ### Theorem 2, ODE half -/

/-- **Theorem 2 (PP ⇒ NAP), ODE half.** Let `g` be a syntactic quadratic PP on `n` species,
`j₀` a species, `λ ∈ (0,1)` rational, and `w` any weighted protocol realising the demand table of
the lifted quartic protocol `liftR2 g j₀ λ` (e.g. the non-autocatalytic one of
`exists_nap_realizing_pipeline`). Let `x` solve `ẋ = g(x)` on `[0,∞)` inside the simplex with
`x_{j₀}(0) > 0`. Then there is a clock `τ`, explicitly the inverse of
`σ ↦ ∫₀^σ ((1 − λ) x_{j₀}(s))⁻²`, with `τ 0 = 0`, `τ` strictly increasing, `τ → ∞`,
`τ' = ((1 − λ) x_{j₀}(τ))²`, such that
* `v(t) = ver (slackMap (x (τ t)))` solves the cubed protocol `v̇ = balanceFun w v` on `[0,∞)`;
* it is the only solution from `ver (slackMap (x 0))` on every `[0,T]`;
* for every linear readout `c`, the cubed readout `Σ_α readW (liftReadout c) α · v_α(t)` equals
  `Σ_j c_j x_j(τ t)`, so every readout limit of the PP is a readout limit of the cubed protocol. -/
theorem pipeline_ode (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (w : WProtocol (MI (n + 1) 3))
    (hr : Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2 n g j₀ lam hlam0)))
    {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t)
    (hxs : ∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1)
    (hx0 : 0 < x 0 j₀) :
    ∃ τ : ℝ → ℝ,
      (∀ σ, 0 ≤ σ → τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * x s j₀)⁻¹ ^ 2) = σ) ∧
      τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
      (∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ (((1 - (lam : ℝ)) * x (τ t) j₀) ^ 2) t) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ver (n + 1) (slackMap n j₀ lam (x (τ s))))
          (balanceFun (n + 1) w (ver (n + 1) (slackMap n j₀ lam (x (τ t))))) (Ici 0) t) ∧
      (∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 → ℝ),
          (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFun (n + 1) w (u t)) (Icc 0 T) t) →
          u 0 = ver (n + 1) (slackMap n j₀ lam (x 0)) →
          EqOn u (fun t => ver (n + 1) (slackMap n j₀ lam (x (τ t)))) (Icc 0 T)) ∧
      (∀ (c : Fin n → ℝ) (t : ℝ), 0 ≤ t →
          ∑ α, readW (liftReadout n j₀ c) α * ver (n + 1) (slackMap n j₀ lam (x (τ t))) α
            = ∑ j, c j * x (τ t) j) ∧
      (∀ (c : Fin n → ℝ) (ν : ℝ), Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
          Tendsto (fun t => ∑ α, readW (liftReadout n j₀ c) α *
            ver (n + 1) (slackMap n j₀ lam (x (τ t))) α) atTop (𝓝 ν)) := by
  have hl0 : (0 : ℝ) < lam := by exact_mod_cast hlam0
  have hl1 : (lam : ℝ) < 1 := by exact_mod_cast hlam1
  have hle : ∀ t, 0 ≤ t → ∀ j, x t j ≤ 1 := fun t ht j => by
    rw [← (hxs t ht).2]
    exact Finset.single_le_sum (fun k _ => (hxs t ht).1 k) (Finset.mem_univ j)
  have hS := slackData_of_simplex n g j₀ hl0 hl1 hx hxs hx0
  set τ := NAPTimeChange.tau hS with hτdef
  have hτn : ∀ t, 0 ≤ t → 0 ≤ τ t := fun t ht => NAPTimeChange.tau_nonneg hS ht
  -- the curve z = slackMap ∘ x ∘ τ solves the lifted quartic field on [0, ∞)
  have hz : ∀ t, 0 ≤ t → HasDerivWithinAt (fun s => slackMap n j₀ lam (x (τ s)))
      (fieldFun (n + 1) (liftR2 n g j₀ lam hlam0) (slackMap n j₀ lam (x (τ t)))) (Ici 0) t := by
    intro t ht
    have hy : HasDerivWithinAt (slackCurve n j₀ lam x)
        (slackMap n j₀ lam (quadFun n g (x (τ t)))) (Ici 0) (τ t) := by
      have h := slackMap_hasDerivWithinAt n (hx (τ t) (hτn t ht)) j₀ lam
      refine h.congr_of_mem (fun s hs => ?_) (hτn t ht)
      simp only [slackCurve, max_eq_left (show (0 : ℝ) ≤ s from hs)]
    have hc := HasDerivWithinAt.scomp t hy (NAPTimeChange.tau_hasDerivAt hS ht).hasDerivWithinAt
      (fun s hs => hτn s hs)
    have heq : EqOn (fun s => slackMap n j₀ lam (x (τ s))) (slackCurve n j₀ lam x ∘ τ) (Ici 0) :=
      fun s hs => by
        simp only [Function.comp, slackCurve, max_eq_left (hτn s hs)]
    refine (hc.congr_of_mem heq ht).congr_deriv ?_
    rw [fieldFun_liftR2_slackMap]
    simp only [slackCoord, slackCurve, slackMap_zero, ← hτdef, max_eq_left (hτn t ht)]
  have hzb : ∀ t, 0 ≤ t → ‖slackMap n j₀ lam (x (τ t))‖ ≤ 1 := fun t ht =>
    slackMap_norm_le n j₀ hl0 hl1 _ (hxs _ (hτn t ht)).1 (hle _ (hτn t ht))
  have hτ0 : τ 0 = 0 := NAPTimeChange.tau_zero hS
  refine ⟨τ, ?_, hτ0, NAPTimeChange.tau_strictMono hS, NAPTimeChange.tau_tendsto_atTop hS,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the clock is the inverse of the explicit integral
    intro σ hσ
    have hT : NAPTimeChange.Tfun (slackCurve n j₀ lam x) (slackCoord n) σ
        = ∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * x s j₀)⁻¹ ^ 2 := by
      unfold NAPTimeChange.Tfun NAPTimeChange.phi
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hσ] at hs
      simp only [slackCoord, slackCurve, slackMap_zero, max_eq_left hs.1]
    rw [← hT]
    exact NAPTimeChange.tau_Tfun hS σ
  · intro t ht
    refine ⟨hτn t ht, ?_⟩
    have := NAPTimeChange.tau_hasDerivAt hS ht
    rw [← hτdef] at this
    simpa only [slackCoord, slackCurve, slackMap_zero, max_eq_left (hτn t ht)] using this
  · intro t ht
    rw [hasDerivWithinAt_pi]
    intro α
    have := ver_hasDerivWithinAt (n + 1) (liftR2 n g j₀ lam hlam0) (hz t ht) α
    rw [← balanceFun_ver (n + 1) _ w hr] at this
    exact this
  · intro T u hu hu0
    have hzT : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => slackMap n j₀ lam (x (τ s)))
        (fieldFun (n + 1) (liftR2 n g j₀ lam hlam0) (slackMap n j₀ lam (x (τ t)))) (Icc 0 T) t :=
      fun t ht => (hz t ht.1).mono Icc_subset_Ici_self
    have hu0' : u 0 = fun α => ver (n + 1) (slackMap n j₀ lam (x (τ 0))) α := by
      rw [hu0, hτ0]
    exact lifted_solution_unique (n + 1) (liftR2 n g j₀ lam hlam0) w hr hzT
      (fun t ht => hzb t ht.1) hu hu0'
  · intro c t ht
    rw [readout_ver, sum_slackMap, (hxs _ (hτn t ht)).2, one_pow, mul_one,
      liftReadout_slackMap]
  · intro c ν hc
    have hlim := hc.comp (NAPTimeChange.tau_tendsto_atTop hS)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Function.comp]
    rw [readout_ver, sum_slackMap, (hxs _ (hτn t ht)).2, one_pow, mul_one,
      liftReadout_slackMap]

/-- **Theorem 2 (PP ⇒ NAP), with the realisation.** For every syntactic quadratic PP `g`, species
`j₀` and rational `λ ∈ (0,1)` there is a non-negative non-autocatalytic weighted protocol `w` on the
weight-3 multi-indices of `n + 1` species realising the cubed lifted field, and for every PP
trajectory in the simplex with `x_{j₀}(0) > 0` the conclusions of `pipeline_ode` hold for `w`. -/
theorem pp_to_nap_ode (g : QuadPP n) (j₀ : Fin n) (lam : ℚ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2 n g j₀ lam hlam0)) ∧
      ∀ {x : ℝ → Fin n → ℝ},
        (∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t) →
        (∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1) →
        0 < x 0 j₀ →
        ∃ τ : ℝ → ℝ,
          (∀ σ, 0 ≤ σ → τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * x s j₀)⁻¹ ^ 2) = σ) ∧
          τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
          (∀ t, 0 ≤ t → 0 ≤ τ t ∧ HasDerivAt τ (((1 - (lam : ℝ)) * x (τ t) j₀) ^ 2) t) ∧
          (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ver (n + 1) (slackMap n j₀ lam (x (τ s))))
              (balanceFun (n + 1) w (ver (n + 1) (slackMap n j₀ lam (x (τ t))))) (Ici 0) t) ∧
          (∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 → ℝ),
              (∀ t ∈ Icc (0 : ℝ) T,
                HasDerivWithinAt u (balanceFun (n + 1) w (u t)) (Icc 0 T) t) →
              u 0 = ver (n + 1) (slackMap n j₀ lam (x 0)) →
              EqOn u (fun t => ver (n + 1) (slackMap n j₀ lam (x (τ t)))) (Icc 0 T)) ∧
          (∀ (c : Fin n → ℝ) (t : ℝ), 0 ≤ t →
              ∑ α, readW (liftReadout n j₀ c) α * ver (n + 1) (slackMap n j₀ lam (x (τ t))) α
                = ∑ j, c j * x (τ t) j) ∧
          (∀ (c : Fin n → ℝ) (ν : ℝ), Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α, readW (liftReadout n j₀ c) α *
                ver (n + 1) (slackMap n j₀ lam (x (τ t))) α) atTop (𝓝 ν)) := by
  obtain ⟨w, hw0, hwN, hwr⟩ := exists_nap_realizing_pipeline n g j₀ lam hlam0
  exact ⟨w, hw0, hwN, hwr, fun hx hxs hx0 => pipeline_ode n g j₀ lam hlam0 hlam1 w hwr hx hxs hx0⟩

end NAPTransport
end Ripple

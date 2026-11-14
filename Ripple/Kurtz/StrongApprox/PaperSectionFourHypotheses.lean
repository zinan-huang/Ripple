import Ripple.Kurtz.StrongApprox.RateLimitBound
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate hypotheses for the diffusion approximation

The coordinate norm in this module is the sup norm;
`paperNorm` is the Euclidean norm in the printed hypotheses.

The differentiability input below consists only of first and second derivatives
along coordinate lines. Continuity of the second derivatives is not assumed.
A finite-coordinate mean value argument supplies the full derivative.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace Ripple.Kurtz.StrongApprox.PaperSectionFourHypotheses

variable {d : ℕ}

/-- Euclidean norm of a vector represented in the sup-norm state space. -/
def paperNorm (x : Fin d → ℝ) : ℝ := Real.sqrt (∑ j, (x j) ^ 2)

theorem paperNorm_nonneg (x : Fin d → ℝ) : 0 ≤ paperNorm x := Real.sqrt_nonneg _

/-- The explicit square-root sum is the usual Euclidean-space norm. -/
theorem paperNorm_eq_euclidean (x : Fin d → ℝ) :
    paperNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [paperNorm, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

theorem paperNorm_sq (x : Fin d → ℝ) : paperNorm x ^ 2 = ∑ j, (x j) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (x j))

theorem paperNorm_pos {x : Fin d → ℝ} (hx : x ≠ 0) : 0 < paperNorm x := by
  have hsome : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := hsome
  apply Real.sqrt_pos.2
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hj)
    (Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j))

theorem paperNorm_sq_le (x : Fin d → ℝ) : paperNorm x ^ 2 ≤ (d : ℝ) * ‖x‖ ^ 2 := by
  rw [paperNorm_sq]
  calc
    ∑ j, (x j) ^ 2 ≤ ∑ _j : Fin d, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := norm_le_pi_norm x j
      rw [Real.norm_eq_abs] at h
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x j)) (norm_nonneg x)).2 h
    _ = (d : ℝ) * ‖x‖ ^ 2 := by simp

/-- The coefficient after converting a Euclidean state distance to the sup norm. -/
def channelSqrtConstant (M : ℝ) (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (M * (d : ℝ)) / paperNorm v

/-- Each nonzero channel inherits a scalar Lipschitz estimate. The dimension
factor is exactly `sqrt d`: `sqrt (M*d) / |v_l|₂`. -/
theorem sqrt_rate_sub_le {ι : Type*} [Fintype ι]
    {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hsum : ∀ x y, ∑ l, paperNorm (v l) ^ 2 *
      (Real.sqrt (f l x) - Real.sqrt (f l y)) ^ 2 ≤ M * paperNorm (x - y) ^ 2)
    (l : ι) (hl : v l ≠ 0) (x y : Fin d → ℝ) :
    |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ channelSqrtConstant M (v l) * ‖x - y‖ := by
  have hv := paperNorm_pos hl
  have hterm : paperNorm (v l) ^ 2 *
      (Real.sqrt (f l x) - Real.sqrt (f l y)) ^ 2 ≤
      M * (d : ℝ) * ‖x - y‖ ^ 2 := by
    calc
      _ ≤ ∑ k, paperNorm (v k) ^ 2 *
          (Real.sqrt (f k x) - Real.sqrt (f k y)) ^ 2 :=
        Finset.single_le_sum (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.mem_univ l)
      _ ≤ M * paperNorm (x - y) ^ 2 := hsum x y
      _ ≤ M * ((d : ℝ) * ‖x - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (paperNorm_sq_le (x - y)) hM
      _ = M * (d : ℝ) * ‖x - y‖ ^ 2 := by ring
  have hroot : Real.sqrt (M * (d : ℝ)) ^ 2 = M * (d : ℝ) :=
    Real.sq_sqrt (mul_nonneg hM (Nat.cast_nonneg d))
  have hmul : paperNorm (v l) * |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤
      Real.sqrt (M * (d : ℝ)) * ‖x - y‖ := by
    have ha := mul_nonneg hv.le (abs_nonneg (Real.sqrt (f l x) - Real.sqrt (f l y)))
    have hb := mul_nonneg (Real.sqrt_nonneg (M * (d : ℝ))) (norm_nonneg (x - y))
    apply (sq_le_sq₀ ha hb).1
    simpa only [mul_pow, sq_abs, hroot] using hterm
  unfold channelSqrtConstant
  have hdiv : |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤
      (Real.sqrt (M * (d : ℝ)) * ‖x - y‖) / paperNorm (v l) :=
    (le_div_iff₀ hv).2 (by simpa only [mul_comm] using hmul)
  simpa only [div_mul_eq_mul_div] using hdiv

/-- Masking a zero jump preserves every finite sum of scalar multiples of the
jump directions. This applies to drift, chain increments, and stochastic terms. -/
theorem sum_smul_mask {ι E : Type*} [Fintype ι] [DecidableEq E]
    [AddCommMonoid E] [Module ℝ E] (v : ι → E) (c : ι → ℝ) :
    (∑ l, (if v l = 0 then 0 else c l) • v l) = ∑ l, c l • v l := by
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : v l = 0 <;> simp [hl]

/-- Scalar coefficient of a zero jump is replaced by zero. -/
def maskZeroRate {ι : Type*} (v : ι → Fin d → ℝ)
    (f : ι → (Fin d → ℝ) → ℝ) (l : ι) (x : Fin d → ℝ) : ℝ := by
  classical
  exact if v l = 0 then 0 else f l x

/-- The zero direction receives scalar Lipschitz constant zero. -/
def maskedChannelSqrtConstant (M : ℝ) (v : Fin d → ℝ) : ℝ := by
  classical
  exact if v = 0 then 0 else channelSqrtConstant M v

/-- Sign, upper bounds, and approximation errors survive zero-direction
masking. The same mask is applied to the finite-scale and limiting rates. -/
theorem maskZeroRate_bounds {ι : Type*} {v : ι → Fin d → ℝ}
    {f : ι → (Fin d → ℝ) → ℝ} {eps : ι → ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hf : ∀ l x, 0 ≤ f l x)
    (hb : ∀ l x, f l x ≤ eps l) :
    (∀ l x, 0 ≤ maskZeroRate v f l x) ∧
    (∀ l x, maskZeroRate v f l x ≤ eps l) := by
  constructor
  · intro l x
    unfold maskZeroRate
    split_ifs
    · exact le_rfl
    · exact hf l x
  · intro l x
    unfold maskZeroRate
    split_ifs
    · exact heps l
    · exact hb l x

theorem maskZeroRate_approximation {ι : Type*} {v : ι → Fin d → ℝ}
    {f g : ι → (Fin d → ℝ) → ℝ} {C : ι → ℝ}
    (hC : ∀ l, 0 ≤ C l) (hfg : ∀ l x, |f l x - g l x| ≤ C l) :
    ∀ l x, |maskZeroRate v f l x - maskZeroRate v g l x| ≤ C l := by
  intro l x
  unfold maskZeroRate
  split_ifs
  · simpa using hC l
  · exact hfg l x

/-- Masking makes the per-channel square-root assumption available at all
indices, including the zero jump, where its Lipschitz constant is zero. -/
theorem sqrt_maskZeroRate_sub_le {ι : Type*} [Fintype ι]
    {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hsum : ∀ x y, ∑ l, paperNorm (v l) ^ 2 *
      (Real.sqrt (f l x) - Real.sqrt (f l y)) ^ 2 ≤ M * paperNorm (x - y) ^ 2)
    (l : ι) (x y : Fin d → ℝ) :
    |Real.sqrt (maskZeroRate v f l x) - Real.sqrt (maskZeroRate v f l y)| ≤
      maskedChannelSqrtConstant M (v l) * ‖x - y‖ := by
  classical
  by_cases hl : v l = 0
  · simp [maskZeroRate, maskedChannelSqrtConstant, hl]
  · simpa [maskZeroRate, maskedChannelSqrtConstant, hl] using
      sqrt_rate_sub_le hM hsum l hl x y

theorem channelSqrtConstant_nonneg (M : ℝ) (v : Fin d → ℝ) :
    0 ≤ channelSqrtConstant M v :=
  div_nonneg (Real.sqrt_nonneg _) (paperNorm_nonneg _)

/-- The scalar coefficient hypotheses consumed by the strong SDE theorem,
after the harmless zero-direction masking. -/
theorem lipschitzWith_sqrt_maskZeroRate {ι : Type*} [Fintype ι]
    {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hsum : ∀ x y, ∑ l, paperNorm (v l) ^ 2 *
      (Real.sqrt (f l x) - Real.sqrt (f l y)) ^ 2 ≤ M * paperNorm (x - y) ^ 2)
    (l : ι) :
    LipschitzWith (maskedChannelSqrtConstant M (v l)).toNNReal
      (fun x => Real.sqrt (maskZeroRate v f l x)) := by
  classical
  have hc : 0 ≤ maskedChannelSqrtConstant M (v l) := by
    by_cases hl : v l = 0
    · simp [maskedChannelSqrtConstant, hl]
    · simpa [maskedChannelSqrtConstant, hl] using channelSqrtConstant_nonneg M (v l)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ hc, Real.dist_eq, dist_eq_norm]
  exact sqrt_maskZeroRate_sub_le hM hsum l x y

/-- Arbitrary channel outputs may be changed on zero directions. No property
of the scalar output construction is needed in the zero branch. -/
theorem sum_smul_congr_of_nonzero {ι E : Type*} [Fintype ι]
    [AddCommMonoid E] [Module ℝ E] (v : ι → E) (c c' : ι → ℝ)
    (hc : ∀ l, v l ≠ 0 → c l = c' l) :
    (∑ l, c l • v l) = ∑ l, c' l • v l := by
  classical
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : v l = 0
  · simp [hl]
  · rw [hc l hl]

/-- Clock integrals, scalar stochastic integrals, or Poisson outputs are all
covered by `J`: their contribution is unchanged after zero-direction masking. -/
theorem sum_output_maskZeroRate {ι : Type*} [Fintype ι]
    (v : ι → Fin d → ℝ) (f : ι → (Fin d → ℝ) → ℝ)
    (J : ι → ((Fin d → ℝ) → ℝ) → ℝ) :
    (∑ l, J l (maskZeroRate v f l) • v l) = ∑ l, J l (f l) • v l := by
  apply sum_smul_congr_of_nonzero
  intro l hl
  congr 1
  funext x
  simp [maskZeroRate, hl]

/-- The actual drift used in the project is unchanged by the mask. -/
theorem tcDrift_maskZeroRate {ι : Type*} [Fintype ι]
    (v : ι → Fin d → ℝ) (f : ι → (Fin d → ℝ) → ℝ) :
    tcDrift (maskZeroRate v f) v = tcDrift f v := by
  classical
  funext x
  exact sum_output_maskZeroRate v f (fun _ g => g x)

/-- Bounded nonnegative rates convert square-root Lipschitz bounds to rate
Lipschitz bounds with the factor `2 sqrt ε`. -/
theorem rate_sub_le_of_sqrt {f : (Fin d → ℝ) → ℝ} {eps L : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ eps)
    (hsqrt : ∀ x y, |Real.sqrt (f x) - Real.sqrt (f y)| ≤ L * ‖x - y‖)
    (x y : Fin d → ℝ) :
    |f x - f y| ≤ (2 * Real.sqrt eps * L) * ‖x - y‖ := by
  have hx := Real.sq_sqrt (hf x)
  have hy := Real.sq_sqrt (hf y)
  have hsum : |Real.sqrt (f x) + Real.sqrt (f y)| ≤ 2 * Real.sqrt eps := by
    rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith [Real.sqrt_le_sqrt (hbound x), Real.sqrt_le_sqrt (hbound y)]
  calc
    |f x - f y| = |(Real.sqrt (f x) - Real.sqrt (f y)) *
        (Real.sqrt (f x) + Real.sqrt (f y))| := by congr 1; nlinarith
    _ = |Real.sqrt (f x) - Real.sqrt (f y)| *
        |Real.sqrt (f x) + Real.sqrt (f y)| := abs_mul _ _
    _ ≤ |Real.sqrt (f x) - Real.sqrt (f y)| * (2 * Real.sqrt eps) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ (L * ‖x - y‖) * (2 * Real.sqrt eps) :=
      mul_le_mul_of_nonneg_right (hsqrt x y) (by positivity)
    _ = (2 * Real.sqrt eps * L) * ‖x - y‖ := by ring

/-- A common rate Lipschitz constant exists for finitely many bounded rates.
The zero-`eps` branch is treated directly, so division never requires an
artificial positive lower bound on the rates. -/
theorem common_rate_lipschitz {ι : Type*} [Fintype ι]
    {f : ι → (Fin d → ℝ) → ℝ} {eps L : ι → ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hL : ∀ l, 0 ≤ L l)
    (hf : ∀ l x, 0 ≤ f l x) (hb : ∀ l x, f l x ≤ eps l)
    (hsqrt : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ L l * ‖x - y‖) :
    0 ≤ (∑ l, 2 * L l / Real.sqrt (eps l)) ∧
    ∀ l x y, |f l x - f l y| ≤
      eps l * (∑ k, 2 * L k / Real.sqrt (eps k)) * ‖x - y‖ := by
  have hterm : ∀ l, 0 ≤ 2 * L l / Real.sqrt (eps l) := fun l =>
    div_nonneg (mul_nonneg (by norm_num) (hL l)) (Real.sqrt_nonneg _)
  refine ⟨Finset.sum_nonneg (fun l _ => hterm l), fun l x y => ?_⟩
  by_cases hz : eps l = 0
  · have hx : f l x = 0 := le_antisymm (by simpa [hz] using hb l x) (hf l x)
    have hy : f l y = 0 := le_antisymm (by simpa [hz] using hb l y) (hf l y)
    simp [hx, hy, hz]
  · have hpos : 0 < Real.sqrt (eps l) := Real.sqrt_pos.2 (lt_of_le_of_ne (heps l) (Ne.symm hz))
    have hlocal := rate_sub_le_of_sqrt (hf l) (hb l) (hsqrt l) x y
    have hscale : 2 * Real.sqrt (eps l) * L l =
        eps l * (2 * L l / Real.sqrt (eps l)) := by
      rw [← mul_div_assoc]
      apply (eq_div_iff hpos.ne').2
      calc
        (2 * Real.sqrt (eps l) * L l) * Real.sqrt (eps l) =
            2 * L l * Real.sqrt (eps l) ^ 2 := by ring
        _ = eps l * (2 * L l) := by rw [Real.sq_sqrt (heps l)]; ring
    rw [hscale] at hlocal
    exact hlocal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ l)) (heps l))
      (norm_nonneg (x - y)))

/-- The paper's all-scale approximation already yields both limiting bounds. -/
theorem limiting_rate_bounds {ι State : Type*} {f : ι → State → ℝ}
    {fN : ℕ → ι → State → ℝ} {eps : ι → ℝ} {Gamma : ℝ}
    (hfN : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (hbound : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hpert : ∀ N, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ)) :
    (∀ l x, 0 ≤ f l x) ∧ (∀ l x, f l x ≤ eps l) :=
  ⟨rate_limit_nonneg hfN hpert, rate_limit_le hbound hpert⟩

/-! ## Coordinate mean value estimates -/

private def mix (s : Finset (Fin d)) (x y : Fin d → ℝ) : Fin d → ℝ :=
  fun j => if j ∈ s then y j else x j

private theorem mix_insert (s : Finset (Fin d)) (x y : Fin d → ℝ) (i : Fin d) :
    mix (insert i s) x y = Function.update (mix s x y) i (y i) := by
  funext j
  by_cases h : j = i
  · subst j; simp [mix]
  · simp [mix, h]

private theorem mix_empty (x y : Fin d → ℝ) : mix ∅ x y = x := by
  funext j
  simp [mix]

private theorem mix_univ (x y : Fin d → ℝ) : mix Finset.univ x y = y := by
  funext j
  simp [mix]

private theorem norm_update_mix_sub_le (s : Finset (Fin d)) (x y : Fin d → ℝ)
    (i : Fin d) {t r : ℝ} (hr : 0 ≤ r) (hxy : ‖y - x‖ ≤ r)
    (ht : t ∈ uIcc (x i) (y i)) :
    ‖Function.update (mix s x y) i t - x‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun j => ?_
  have hj : |y j - x j| ≤ r :=
    (show |y j - x j| ≤ ‖y - x‖ by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - x) j).trans hxy
  by_cases hji : j = i
  · subst j
    simp only [Pi.sub_apply, Function.update_self, Real.norm_eq_abs]
    have hlo : x i - r ≤ min (x i) (y i) := by
      apply le_min <;> linarith [(abs_le.mp hj).1]
    have hhi : max (x i) (y i) ≤ x i + r := by
      apply max_le <;> linarith [(abs_le.mp hj).2]
    exact abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · by_cases hjs : j ∈ s <;> simp [Function.update_of_ne hji, mix, hjs,
      Real.norm_eq_abs, hj, hr]

/-- A coordinate-line mean value estimate on a sup-norm ball. Neither total
differentiability nor continuity of the coordinate derivative field is assumed. -/
theorem coordinate_mean_value {H : (Fin d → ℝ) → ℝ}
    {A : (Fin d → ℝ) → Fin d → ℝ} {B r : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hA : ∀ z j, HasDerivAt (fun t => H (Function.update z j t)) (A z j) (z j))
    (x y : Fin d → ℝ) (hxy : ‖y - x‖ ≤ r)
    (hbound : ∀ z, ‖z - x‖ ≤ r → ∀ j, |A z j| ≤ B) :
    |H y - H x| ≤ (d : ℝ) * B * ‖y - x‖ := by
  have hstep : ∀ (s : Finset (Fin d)) (i : Fin d), i ∉ s →
      |H (mix (insert i s) x y) - H (mix s x y)| ≤ B * |y i - x i| := by
    intro s i hi
    let z := mix s x y
    have hzi : z i = x i := by simp [z, mix, hi]
    have hd : ∀ t ∈ uIcc (x i) (y i),
        HasDerivWithinAt (fun t => H (Function.update z i t))
          (A (Function.update z i t) i) (uIcc (x i) (y i)) t := by
      intro t _
      simpa only [Function.update_self, Function.update_idem] using
        (hA (Function.update z i t) i).hasDerivWithinAt
    have hb : ∀ t ∈ uIcc (x i) (y i), ‖A (Function.update z i t) i‖ ≤ B := by
      intro t ht
      rw [Real.norm_eq_abs]
      exact hbound _ (norm_update_mix_sub_le s x y i hr hxy ht) i
    have hm := (convex_uIcc (x i) (y i)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hd hb (left_mem_uIcc) (right_mem_uIcc)
    have hz : Function.update z i (x i) = z := by rw [← hzi]; exact Function.update_eq_self i z
    rw [mix_insert]
    change |H (Function.update z i (y i)) - H z| ≤ B * |y i - x i|
    simpa only [hz, Real.norm_eq_abs] using hm
  have htel : ∀ s : Finset (Fin d),
      |H (mix s x y) - H x| ≤ B * ∑ j ∈ s, |y j - x j| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [mix_empty]
    | @insert i s hi ih =>
      have ht := abs_add_le (H (mix (insert i s) x y) - H (mix s x y))
        (H (mix s x y) - H x)
      have heq : H (mix (insert i s) x y) - H x =
          (H (mix (insert i s) x y) - H (mix s x y)) +
            (H (mix s x y) - H x) := by ring
      rw [heq]
      calc
        _ ≤ _ := ht
        _ ≤ B * |y i - x i| + B * ∑ j ∈ s, |y j - x j| :=
          add_le_add (hstep s i hi) ih
        _ = B * ∑ j ∈ insert i s, |y j - x j| := by rw [Finset.sum_insert hi]; ring
  have hsum : (∑ j : Fin d, |y j - x j|) ≤ (d : ℝ) * ‖y - x‖ := by
    calc
      _ ≤ ∑ _j : Fin d, ‖y - x‖ := Finset.sum_le_sum fun j _ => by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - x) j
      _ = _ := by simp
  have hu := htel Finset.univ
  rw [mix_univ] at hu
  refine hu.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hsum hB]

/-- Global form of the coordinate mean value estimate. -/
theorem coordinate_global_bound {H : (Fin d → ℝ) → ℝ}
    {A : (Fin d → ℝ) → Fin d → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hA : ∀ z j, HasDerivAt (fun t => H (Function.update z j t)) (A z j) (z j))
    (hbound : ∀ z j, |A z j| ≤ B) (x y : Fin d → ℝ) :
    |H y - H x| ≤ (d : ℝ) * B * ‖y - x‖ :=
  coordinate_mean_value hB (norm_nonneg _) hA x y le_rfl (fun z _ j => hbound z j)

/-- A row of a derivative matrix as a continuous linear functional. -/
def row (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j, a j • ContinuousLinearMap.proj j

@[simp] theorem row_apply (a z : Fin d → ℝ) : row a z = ∑ j, a j * z j := by
  simp [row]

@[simp] theorem row_single (a : Fin d → ℝ) (j : Fin d) :
    row a (Pi.single j 1) = a j := by simp [row_apply, Pi.single_apply]

/-- Scalar coordinate-line derivatives with a Lipschitz coefficient field
produce the full derivative. This proves the regularity conversion rather than
assuming total differentiability as an additional premise. -/
theorem hasFDerivAt_row {H : (Fin d → ℝ) → ℝ}
    {A : (Fin d → ℝ) → Fin d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ z j, HasDerivAt (fun t => H (Function.update z j t)) (A z j) (z j))
    (hLip : ∀ x y j, |A y j - A x j| ≤ K * ‖y - x‖) (x : Fin d → ℝ) :
    HasFDerivAt H (row (A x)) x := by
  have herr : ∀ y, |H y - H x - row (A x) (y - x)| ≤
      ((d : ℝ) * K * ‖y - x‖) * ‖y - x‖ := by
    intro y
    let R : (Fin d → ℝ) → ℝ := fun z => H z - row (A x) z
    have hR : ∀ z j, HasDerivAt (fun t => R (Function.update z j t))
        (A z j - A x j) (z j) := by
      intro z j
      have hd : HasDerivAt (fun t => row (A x) (Function.update z j t)) (A x j) (z j) := by
        have h0 := (row (A x)).hasFDerivAt.comp_hasDerivAt (z j) (hasDerivAt_update z j (z j))
        simpa only [Function.comp_def, row_single] using h0
      exact (hA z j).sub hd
    have hm := coordinate_mean_value (mul_nonneg hK (norm_nonneg (y - x)))
      (norm_nonneg (y - x)) hR x y le_rfl (fun z hz j =>
        (hLip x z j).trans (mul_le_mul_of_nonneg_left hz hK))
    have heq : R y - R x = H y - H x - row (A x) (y - x) := by
      simp only [R, map_sub]
      ring
    rw [heq] at hm
    simpa only [mul_assoc] using hm
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  have hden : 0 < (d : ℝ) * K + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds x (div_pos heps hden)] with y hy
  have hsmall : (d : ℝ) * K * ‖y - x‖ ≤ eps := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hm := (lt_div_iff₀ hden).1 hy
    nlinarith [norm_nonneg (y - x)]
  simpa only [Real.norm_eq_abs] using
    (herr y).trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg (y - x)))

/-- The Jacobian assembled from the first coordinate partials. -/
def jacobian (A : (Fin d → ℝ) → Fin d → Fin d → ℝ) (x : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => row (A x i))

@[simp] theorem jacobian_apply (A : (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (x z : Fin d → ℝ) (i : Fin d) : jacobian A x z i = ∑ j, A x i j * z j := by
  simp [jacobian]

/-- Matrix entries bounded by `B` give the sup-operator norm bound `d B`. -/
theorem norm_matrix_le {L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}
    {a : Fin d → Fin d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ z i, L z i = ∑ j, a i j * z j) (ha : ∀ i j, |a i j| ≤ B) :
    ‖L‖ ≤ (d : ℝ) * B := by
  apply L.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg d) hB)
  intro z
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [hL, Real.norm_eq_abs]
  calc
    |∑ j, a i j * z j| ≤ ∑ j, |a i j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, B * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (ha i j) (by simpa [Real.norm_eq_abs] using norm_le_pi_norm z j)
        (abs_nonneg _) hB
    _ = ((d : ℝ) * B) * ‖z‖ := by simp; ring

/-- Paper-form first and second partial hypotheses. `A x i j` is `∂_j F_i(x)`;
`B x i j k` is `∂_k ∂_j F_i(x)`. These are derivatives along coordinate lines,
with no full differentiability, derivative-norm bound, or continuity premise. -/
structure BoundedCoordinatePartials (F : (Fin d → ℝ) → Fin d → ℝ)
    (firstBound secondBound : ℝ) where
  first : (Fin d → ℝ) → Fin d → Fin d → ℝ
  second : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ
  first_nonneg : 0 ≤ firstBound
  second_nonneg : 0 ≤ secondBound
  has_first : ∀ x i j, HasDerivAt (fun t => F (Function.update x j t) i)
    (first x i j) (x j)
  has_second : ∀ x i j k, HasDerivAt (fun t => first (Function.update x k t) i j)
    (second x i j k) (x k)
  first_bound : ∀ x i j, |first x i j| ≤ firstBound
  second_bound : ∀ x i j k, |second x i j k| ≤ secondBound

namespace BoundedCoordinatePartials

variable {F : (Fin d → ℝ) → Fin d → ℝ} {firstBound secondBound : ℝ}
    (h : BoundedCoordinatePartials F firstBound secondBound)

theorem first_sub_le (x y : Fin d → ℝ) (i j : Fin d) :
    |h.first y i j - h.first x i j| ≤ (d : ℝ) * secondBound * ‖y - x‖ :=
  coordinate_global_bound (H := fun z => h.first z i j) (A := fun z k => h.second z i j k)
    h.second_nonneg (fun z k => h.has_second z i j k)
    (fun z k => h.second_bound z i j k) x y

/-- The precise derivative premise consumed by the Section 4 remainder bound. -/
theorem hasFDerivAt (x : Fin d → ℝ) : HasFDerivAt F (jacobian h.first x) x := by
  change HasFDerivAt (fun z i => F z i)
    (ContinuousLinearMap.pi (fun i => row (h.first x i))) x
  rw [hasFDerivAt_pi]
  intro i
  exact hasFDerivAt_row (mul_nonneg (Nat.cast_nonneg d) h.second_nonneg)
    (fun z j => h.has_first z i j) (fun x y j => h.first_sub_le x y i j) x

/-- The first operator bound has dimension factor `d`. -/
theorem norm_jacobian_le (x : Fin d → ℝ) : ‖jacobian h.first x‖ ≤ (d : ℝ) * firstBound :=
  norm_matrix_le h.first_nonneg (jacobian_apply h.first x) (h.first_bound x)

/-- Bounded second partials give the derivative Lipschitz premise with factor
`d²`, entirely in the sup norm used by the Section 4 estimates. -/
theorem norm_jacobian_sub_le (x y : Fin d → ℝ) :
    ‖jacobian h.first y - jacobian h.first x‖ ≤
      ((d : ℝ) ^ 2 * secondBound) * ‖y - x‖ := by
  have hm := norm_matrix_le (L := jacobian h.first y - jacobian h.first x)
    (a := fun i j => h.first y i j - h.first x i j)
    (B := (d : ℝ) * secondBound * ‖y - x‖)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) h.second_nonneg) (norm_nonneg _))
    (fun z i => by simp [jacobian_apply, Finset.sum_sub_distrib, sub_mul])
    (fun i j => h.first_sub_le x y i j)
  convert hm using 1 <;> ring

/-- All internal derivative premises are produced from the printed coordinate
bounds; the map can be instantiated by the actual finite-channel drift. -/
theorem sectionFour_derivative_hypotheses :
    (∀ x, HasFDerivAt F (jacobian h.first x) x) ∧
    (∀ x, ‖jacobian h.first x‖ ≤ (d : ℝ) * firstBound) ∧
    (0 ≤ (d : ℝ) ^ 2 * secondBound) ∧
    (∀ x y, ‖jacobian h.first y - jacobian h.first x‖ ≤
      ((d : ℝ) ^ 2 * secondBound) * ‖y - x‖) :=
  ⟨h.hasFDerivAt, h.norm_jacobian_le, mul_nonneg (sq_nonneg _) h.second_nonneg,
    h.norm_jacobian_sub_le⟩

end BoundedCoordinatePartials
end Ripple.Kurtz.StrongApprox.PaperSectionFourHypotheses

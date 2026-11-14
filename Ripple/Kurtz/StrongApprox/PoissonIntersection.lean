/-
  Ripple.Kurtz.StrongApprox.PoissonIntersection — the Poisson intersection (PI)

  Direct proof, with one sign change in `λ`.

  For `k ≥ 1`, `λ > 0`, with `a(λ) = sgn(k−λ)√(2 I_k(λ))`:
    `P(Pois(λ) ≤ k−1) ≤ Φ(a(λ)) ≤ P(Pois(λ) ≤ k)`.
  Both halves are `Δ ≤ 0` for a difference whose derivative is `w·σ` with `w > 0` and `{σ < 0}`
  an initial segment (monotone `r`, antitone `s` from `PoissonSignedRoot`), and which tends to
  `0` at `0⁺` and at `+∞` (`le_zero_of_sign_change`).
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.GaussianCdf
import Ripple.Kurtz.StrongApprox.NormalTail
import Ripple.Kurtz.StrongApprox.SignChange
import Ripple.Kurtz.StrongApprox.PoissonCdfDeriv
import Ripple.Kurtz.StrongApprox.PoissonSignedRoot

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter Topology

local notation "μ₀" => gaussianReal 0 1

/-! ### The standard normal cdf is an antiderivative of its density -/

theorem gaussian_real_Ioc_eq (x y : ℝ) :
    (μ₀).real (Ioc x y) = ∫ t in Ioc x y, gaussianPDFReal 0 1 t := by
  have hμ : μ₀ (Ioc x y) = ENNReal.ofReal (∫ t in Ioc x y, gaussianPDFReal 0 1 t) :=
    gaussianReal_apply_eq_integral 0 one_ne_zero _
  have hint_nonneg : 0 ≤ ∫ t in Ioc x y, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => gaussianPDFReal_nonneg 0 1 t
  rw [measureReal_def, hμ, ENNReal.toReal_ofReal hint_nonneg]

theorem stdNormalCdf_eq_integral (c y : ℝ) :
    stdNormalCdf y = stdNormalCdf c + ∫ x in c..y, gaussianPDFReal 0 1 x := by
  rcases le_total c y with hcy | hyc
  · rw [intervalIntegral.integral_of_le hcy, ← gaussian_real_Ioc_eq, ← stdNormalCdf_sub hcy]
    ring
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hyc,
      ← gaussian_real_Ioc_eq, ← stdNormalCdf_sub hyc]
    ring

theorem hasDerivAt_stdNormalCdf (x : ℝ) :
    HasDerivAt stdNormalCdf (gaussianPDFReal 0 1 x) x := by
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    simp only [gaussianPDFReal_def]; fun_prop
  have h := (intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 x) (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).const_add
    (stdNormalCdf 0)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  exact stdNormalCdf_eq_integral 0 y

/-! ### Algebraic identities along the signed root -/

theorem gaussianPDFReal_poisSignedRoot (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    gaussianPDFReal 0 1 (poisSignedRoot k l) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(poisRate k l)) := by
  rw [gaussianPDFReal_zero_one, poisSignedRoot_sq k hk hl]
  have : -(2 * poisRate k l) / 2 = -(poisRate k l) := by ring
  rw [this]

/-- `e^{−I_k(λ)} = e^{−λ} e^{k} λ^k / k^k`. -/
theorem exp_neg_poisRate (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    Real.exp (-(poisRate k l)) = Real.exp (-l) * Real.exp k * l ^ k / (k : ℝ) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : Real.exp ((k : ℝ) * Real.log l) = l ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hl]
  have h2 : Real.exp ((k : ℝ) * Real.log k) = (k : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hkR]
  have : -(poisRate k l) = -l + k + (k * Real.log l) - (k * Real.log k) := by
    unfold poisRate; ring
  rw [this, Real.exp_sub, Real.exp_add, Real.exp_add, h1, h2]

/-- Constant `A = k^k e^{−k} / (k−1)!` with `k = j+1`. -/
noncomputable def poisConstA (j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) ^ (j + 1) * Real.exp (-((j + 1 : ℕ) : ℝ)) / (j.factorial : ℝ)

/-- Constant `B = k^k e^{−k} / k!` with `k = j+1`. -/
noncomputable def poisConstB (j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) ^ (j + 1) * Real.exp (-((j + 1 : ℕ) : ℝ)) / ((j + 1).factorial : ℝ)

theorem poisConstA_pos (j : ℕ) : 0 < poisConstA j := by unfold poisConstA; positivity
theorem poisConstB_pos (j : ℕ) : 0 < poisConstB j := by unfold poisConstB; positivity

theorem poisTerm_eq_constA (j : ℕ) {l : ℝ} (hl : 0 < l) :
    poisTerm j l = poisConstA j * Real.exp (-(poisRate (j + 1) l)) / l := by
  rw [exp_neg_poisRate (j + 1) (Nat.succ_pos j) hl]
  unfold poisTerm poisConstA
  have hkR : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hl' : l ≠ 0 := hl.ne'
  simp only [Real.exp_neg]
  field_simp <;> ring

theorem poisTerm_succ_eq_constB (j : ℕ) {l : ℝ} (hl : 0 < l) :
    poisTerm (j + 1) l = poisConstB j * Real.exp (-(poisRate (j + 1) l)) := by
  rw [exp_neg_poisRate (j + 1) (Nat.succ_pos j) hl]
  unfold poisTerm poisConstB
  have hkR : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  simp only [Real.exp_neg]
  field_simp <;> ring

/-! ### Derivative of `Φ ∘ a` -/

theorem hasDerivAt_stdNormalCdf_poisSignedRoot (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l)
    (hne : l ≠ k) :
    HasDerivAt (fun x => stdNormalCdf (poisSignedRoot k x))
      (-((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(poisRate k l)) * rPois k l / l)) l := by
  have h := (hasDerivAt_stdNormalCdf (poisSignedRoot k l)).comp l
    (hasDerivAt_poisSignedRoot k hk hl hne)
  refine h.congr_deriv ?_
  rw [gaussianPDFReal_poisSignedRoot k hk hl, rPois_of_ne k hne]
  have hI : 0 < poisRate k l := poisRate_pos_of_ne k hk hl hne
  have hs : 0 < Real.sqrt (2 * poisRate k l) := Real.sqrt_pos.mpr (by positivity)
  field_simp <;> ring

theorem continuousOn_stdNormalCdf_poisSignedRoot (k : ℕ) (hk : 0 < k) :
    ContinuousOn (fun x => stdNormalCdf (poisSignedRoot k x)) (Ioi 0) :=
  stdNormalCdf_continuous.comp_continuousOn (continuousOn_poisSignedRoot k hk)

/-! ### Limits -/

theorem poisCdf_zero (j : ℕ) : poisCdf (j + 1) 0 = 1 := by
  unfold poisCdf
  rw [Finset.sum_range_succ']
  simp [poisTerm]

theorem tendsto_sqrt_atTop : Tendsto Real.sqrt atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => Real.sqrt_le_sqrt h)
    (fun b => ⟨b ^ 2, by rw [Real.sqrt_sq_eq_abs]; exact le_abs_self b⟩)

theorem tendsto_poisSignedRoot_nhdsGT_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (poisSignedRoot k) (𝓝[>] 0) atTop := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h : Tendsto (fun l => Real.sqrt (2 * poisRate k l)) (𝓝[>] 0) atTop :=
    tendsto_sqrt_atTop.comp ((tendsto_poisRate_nhdsGT_zero k hk).const_mul_atTop two_pos)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hkR] with l hl
  exact (poisSignedRoot_of_lt k hl.2).symm

theorem tendsto_poisSignedRoot_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (poisSignedRoot k) atTop atBot := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h : Tendsto (fun l => -Real.sqrt (2 * poisRate k l)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_sqrt_atTop.comp ((tendsto_poisRate_atTop k hk).const_mul_atTop two_pos))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (k : ℝ)] with l hl
  exact (poisSignedRoot_of_gt k hl).symm

theorem tendsto_stdNormalCdf_poisSignedRoot_nhdsGT_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun x => stdNormalCdf (poisSignedRoot k x)) (𝓝[>] 0) (𝓝 1) := by
  have htop : Tendsto stdNormalCdf atTop (𝓝 1) := tendsto_cdf_atTop μ₀
  exact htop.comp (tendsto_poisSignedRoot_nhdsGT_zero k hk)

theorem tendsto_stdNormalCdf_poisSignedRoot_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun x => stdNormalCdf (poisSignedRoot k x)) atTop (𝓝 0) := by
  have hbot : Tendsto stdNormalCdf atBot (𝓝 0) := tendsto_cdf_atBot μ₀
  exact hbot.comp (tendsto_poisSignedRoot_atTop k hk)

theorem tendsto_poisCdf_nhdsGT_zero (j : ℕ) : Tendsto (poisCdf (j + 1)) (𝓝[>] 0) (𝓝 1) := by
  have h := (hasDerivAt_poisCdf j 0).continuousAt.tendsto
  rw [poisCdf_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_poisTerm_atTop (i : ℕ) : Tendsto (poisTerm i) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).div_const (i.factorial : ℝ)
  rw [zero_div] at h
  refine h.congr fun l => ?_
  unfold poisTerm; ring

theorem tendsto_poisCdf_atTop (j : ℕ) : Tendsto (poisCdf j) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range j) (fun i _ => tendsto_poisTerm_atTop i)
  simpa [poisCdf] using h

/-! ### The two halves of (PI) -/

/-- Lower half: `P(Pois(λ) ≤ k−1) ≤ Φ(a(λ))`. -/
theorem poisCdf_le_stdNormalCdf_poisSignedRoot (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    poisCdf k l ≤ stdNormalCdf (poisSignedRoot k l) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkR : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hc1 : ContinuousOn (poisCdf (j + 1)) (Ioi 0) :=
    fun x _ => (hasDerivAt_poisCdf j x).continuousAt.continuousWithinAt
  have key : ∀ x, 0 < x → poisCdf (j + 1) x - stdNormalCdf (poisSignedRoot (j + 1) x) ≤ 0 := by
    refine le_zero_of_sign_change
      (Δ := fun x => poisCdf (j + 1) x - stdNormalCdf (poisSignedRoot (j + 1) x))
      (k := ((j + 1 : ℕ) : ℝ))
      (σ := fun x => rPois (j + 1) x / Real.sqrt (2 * Real.pi) - poisConstA j)
      (w := fun x => Real.exp (-(poisRate (j + 1) x)) / x) hkR ?_ ?_ ?_ ?_ ?_ ?_
    · exact hc1.sub (continuousOn_stdNormalCdf_poisSignedRoot (j + 1) hk)
    · intro x hx hne
      have h := (hasDerivAt_poisCdf j x).sub
        (hasDerivAt_stdNormalCdf_poisSignedRoot (j + 1) hk hx hne)
      refine h.congr_deriv ?_
      beta_reduce
      rw [poisTerm_eq_constA j hx]
      have hx' : x ≠ 0 := hx.ne'
      field_simp
      ring
    · intro x hx
      beta_reduce
      positivity
    · intro x y hx hxy hy
      beta_reduce at hy ⊢
      have hm := rPois_mono (j + 1) hk hx hxy.le
      have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
      have : rPois (j + 1) x / Real.sqrt (2 * Real.pi) ≤ rPois (j + 1) y / Real.sqrt (2 * Real.pi) := by
        gcongr
      linarith
    · have := (tendsto_poisCdf_nhdsGT_zero j).sub
        (tendsto_stdNormalCdf_poisSignedRoot_nhdsGT_zero (j + 1) hk)
      simpa using this
    · have := (tendsto_poisCdf_atTop (j + 1)).sub
        (tendsto_stdNormalCdf_poisSignedRoot_atTop (j + 1) hk)
      simpa using this
  linarith [key l hl]

/-- Upper half: `Φ(a(λ)) ≤ P(Pois(λ) ≤ k)`. -/
theorem stdNormalCdf_poisSignedRoot_le_poisCdf (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    stdNormalCdf (poisSignedRoot k l) ≤ poisCdf (k + 1) l := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkR : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hc2 : ContinuousOn (poisCdf (j + 1 + 1)) (Ioi 0) :=
    fun x _ => (hasDerivAt_poisCdf (j + 1) x).continuousAt.continuousWithinAt
  have key : ∀ x, 0 < x →
      stdNormalCdf (poisSignedRoot (j + 1) x) - poisCdf (j + 1 + 1) x ≤ 0 := by
    refine le_zero_of_sign_change
      (Δ := fun x => stdNormalCdf (poisSignedRoot (j + 1) x) - poisCdf (j + 1 + 1) x)
      (k := ((j + 1 : ℕ) : ℝ))
      (σ := fun x => poisConstB j - sPois (j + 1) x / Real.sqrt (2 * Real.pi))
      (w := fun x => Real.exp (-(poisRate (j + 1) x))) hkR ?_ ?_ ?_ ?_ ?_ ?_
    · exact (continuousOn_stdNormalCdf_poisSignedRoot (j + 1) hk).sub hc2
    · intro x hx hne
      have h := (hasDerivAt_stdNormalCdf_poisSignedRoot (j + 1) hk hx hne).sub
        (hasDerivAt_poisCdf (j + 1) x)
      refine h.congr_deriv ?_
      beta_reduce
      rw [poisTerm_succ_eq_constB j hx, sPois_of_ne (j + 1) hne, rPois_of_ne (j + 1) hne]
      have hx' : x ≠ 0 := hx.ne'
      have hI : 0 < poisRate (j + 1) x := poisRate_pos_of_ne (j + 1) hk hx hne
      have hs : 0 < Real.sqrt (2 * poisRate (j + 1) x) := Real.sqrt_pos.mpr (by positivity)
      field_simp
      ring
    · intro x hx
      beta_reduce
      positivity
    · intro x y hx hxy hy
      beta_reduce at hy ⊢
      have hm := sPois_anti (j + 1) hk hx hxy.le
      have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
      have : sPois (j + 1) y / Real.sqrt (2 * Real.pi) ≤ sPois (j + 1) x / Real.sqrt (2 * Real.pi) := by
        gcongr
      linarith
    · have := (tendsto_stdNormalCdf_poisSignedRoot_nhdsGT_zero (j + 1) hk).sub
        (tendsto_poisCdf_nhdsGT_zero (j + 1))
      simpa using this
    · have := (tendsto_stdNormalCdf_poisSignedRoot_atTop (j + 1) hk).sub
        (tendsto_poisCdf_atTop (j + 1 + 1))
      simpa using this
  linarith [key l hl]

/-- **(PI)**: for `k ≥ 1` and `λ > 0`,
`P(Pois(λ) ≤ k−1) ≤ Φ(sgn(k−λ)√(2 I_k(λ))) ≤ P(Pois(λ) ≤ k)`. -/
theorem poisson_intersection (k : ℕ) (hk : 0 < k) {l : ℝ} (hl : 0 < l) :
    poisCdf k l ≤ stdNormalCdf (poisSignedRoot k l) ∧
      stdNormalCdf (poisSignedRoot k l) ≤ poisCdf (k + 1) l :=
  ⟨poisCdf_le_stdNormalCdf_poisSignedRoot k hk hl, stdNormalCdf_poisSignedRoot_le_poisCdf k hk hl⟩

end Ripple.Kurtz.StrongApprox

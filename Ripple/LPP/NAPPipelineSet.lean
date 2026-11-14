/-
  Ripple.LPP.NAPPipelineSet — the pipeline of the PP-to-NAP write-up §4 with a shrunk *set*
  `J₀` (Step 1 as in the paper), alongside the single-species versions of `NAPPipeline`,
  `NAPPipelineODE`, `NAPPipelineInit`.

  Slot `0` is the slack `r = (1 − λ) Σ_{j ∈ J₀} x_j`, slot `j.succ` is `λ x_j` for `j ∈ J₀` and
  `x_j` otherwise. The lifted quartic coefficient table is
    `coef' 0      (r² ⊕ μ) = (1 − λ) λ^{−μ(J₀)} Σ_{j ∈ J₀} g.coef j μ`,
    `coef' j.succ (r² ⊕ μ) = [j ∈ J₀ ? λ : 1] λ^{−μ(J₀)} g.coef j μ`,
  `0` off slack exponent `2`, where `μ(J₀) = Σ_{j ∈ J₀} μ_j`.

  * `liftR2Set`, `liftR2Set_C1`, `liftR2Set_C2`, `exists_nap_realizing_pipeline_set`;
  * `fieldFun_liftR2Set` (evaluation identity), `slackFieldSet_slackMapSet`;
  * `pipeline_ode_set` and `pp_to_nap_ode_of_init_set` (**Theorem 2, ODE half, shrunk set**);
    the readout coefficients must be constant (`= c₀`) on `J₀`, as in the paper.
-/

import Ripple.LPP.NAPPipelineInit

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

theorem sum_ite_mem_univ {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (J : Finset ι) (f : ι → M) : ∑ j, (if j ∈ J then f j else 0) = ∑ j ∈ J, f j := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem prod_ite_mem_univ {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (J : Finset ι) (f : ι → M) : ∏ j, (if j ∈ J then f j else 1) = ∏ j ∈ J, f j := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem prod_ite_mem_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Finset ι) (c : ℝ)
    (e : ι → ℕ) : ∏ k, (if k ∈ J then c else 1) ^ e k = c ^ ∑ k ∈ J, e k := by
  rw [Finset.prod_congr rfl (fun k _ => show (if k ∈ J then c else 1) ^ e k
      = if k ∈ J then c ^ e k else 1 by split_ifs <;> simp),
    prod_ite_mem_univ, Finset.prod_pow_eq_pow_sum]

/-! ### Coefficient level -/

/-- The total exponent of a weight-2 index on the shrunk set. -/
def expIn (J : Finset (Fin n)) (μ : MI n 2) : ℕ := ∑ j ∈ J, (μ.1 j : ℕ)

/-- The lifted coefficient table for a shrunk set `J`. -/
noncomputable def liftCoefSet (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (j' : Fin (n + 1))
    (μ' : MI (n + 1) 4) : ℚ :=
  if h : (μ'.1 0 : ℕ) = 2 then
    Fin.cases
      ((1 - lam) * lam⁻¹ ^ expIn n J (tail n μ' h) * ∑ j ∈ J, g.coef j (tail n μ' h))
      (fun j => (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J (tail n μ' h) *
        g.coef j (tail n μ' h)) j'
  else 0

theorem liftCoefSet_sum (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (μ' : MI (n + 1) 4) :
    ∑ j', liftCoefSet n g J lam j' μ' = 0 := by
  unfold liftCoefSet
  by_cases h : (μ'.1 0 : ℕ) = 2
  · simp only [dif_pos h]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    set sc := lam⁻¹ ^ expIn n J (tail n μ' h)
    set μ := tail n μ' h
    have hsplit : ∀ j, (if j ∈ J then lam else 1) * sc * g.coef j μ
        = sc * g.coef j μ + (if j ∈ J then (lam - 1) * sc * g.coef j μ else 0) := by
      intro j
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_add_distrib, sum_ite_mem_univ, ← Finset.mul_sum,
      g.conservative μ, mul_zero, zero_add]
    ring
  · simp [dif_neg h]

theorem liftCoefSet_sign (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam)
    (j' : Fin (n + 1)) (μ' : MI (n + 1) 4) (hneg : liftCoefSet n g J lam j' μ' < 0) :
    0 < (μ'.1 j' : ℕ) := by
  unfold liftCoefSet at hneg
  by_cases h : (μ'.1 0 : ℕ) = 2
  · simp only [dif_pos h] at hneg
    have hsc : 0 < lam⁻¹ ^ expIn n J (tail n μ' h) := pow_pos (inv_pos.mpr hlam) _
    induction j' using Fin.cases with
    | zero => omega
    | succ j =>
      simp only [Fin.cases_succ] at hneg
      have hfac : 0 < (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J (tail n μ' h) := by
        apply mul_pos _ hsc
        split_ifs <;> linarith
      have hg : g.coef j (tail n μ' h) < 0 := by
        by_contra hcon
        rw [not_lt] at hcon
        have := mul_nonneg hfac.le hcon
        linarith
      have := g.sign j _ hg
      simpa [tail] using this
  · simp [dif_neg h] at hneg

/-- The lifted quartic protocol for a shrunk set `J`. -/
noncomputable def liftR2Set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam) :
    QuarticPP (n + 1) where
  coef := liftCoefSet n g J lam
  conservative := liftCoefSet_sum n g J lam
  sign := liftCoefSet_sign n g J lam hlam

theorem liftR2Set_coef (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam)
    (j' : Fin (n + 1)) (μ' : MI (n + 1) 4) :
    (liftR2Set n g J lam hlam).coef j' μ' = liftCoefSet n g J lam j' μ' := rfl

theorem liftCoefSet_eq_zero_of_slack (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (j' : Fin (n + 1)) (μ' : MI (n + 1) 4) (h : (μ'.1 0 : ℕ) ≠ 2) :
    liftCoefSet n g J lam j' μ' = 0 := by
  unfold liftCoefSet
  rw [dif_neg h]

theorem liftR2Set_C1 (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam) :
    ∀ (y k : Fin (n + 1)) (h : y ≠ k),
      (liftR2Set n g J lam hlam).coef y (MI.two (n + 1) 3 1 y k h) ≤ 0 := by
  intro y k h
  rw [liftR2Set_coef, liftCoefSet_eq_zero_of_slack n g J lam y _ (two_slack_ne n y k h)]

theorem liftR2Set_C2 (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam) :
    ∀ (y k : Fin (n + 1)) (h : y ≠ k),
      (liftR2Set n g J lam hlam).coef k (MI.two (n + 1) 3 1 y k h)
        + 2 * (liftR2Set n g J lam hlam).coef y (MI.pow (n + 1) 4 y) ≤ 0 := by
  intro y k h
  rw [liftR2Set_coef, liftR2Set_coef,
    liftCoefSet_eq_zero_of_slack n g J lam k _ (two_slack_ne n y k h),
    liftCoefSet_eq_zero_of_slack n g J lam y _ (pow_slack_ne n y)]
  norm_num

/-- **Theorem 2, combinatorial half, shrunk set.** -/
theorem exists_nap_realizing_pipeline_set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (hlam : 0 < lam) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2Set n g J lam hlam)) :=
  exists_nap_realizing_of_C1C2 (n + 1) (liftR2Set n g J lam hlam)
    (liftR2Set_C1 n g J lam hlam) (liftR2Set_C2 n g J lam hlam)

/-! ### Evaluation identity -/

/-- Step 1 with a shrunk set. -/
noncomputable def slackMapSet (J : Finset (Fin n)) (lam : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases ((1 - lam) * ∑ j ∈ J, x j) (fun j => (if j ∈ J then lam else 1) * x j)

@[simp] theorem slackMapSet_zero (J : Finset (Fin n)) (lam : ℝ) (x : Fin n → ℝ) :
    slackMapSet n J lam x 0 = (1 - lam) * ∑ j ∈ J, x j := rfl

@[simp] theorem slackMapSet_succ (J : Finset (Fin n)) (lam : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    slackMapSet n J lam x j.succ = (if j ∈ J then lam else 1) * x j := rfl

/-- The substitution `x_j = u_j/λ` for `j ∈ J`. -/
noncomputable def unshrinkSet (J : Finset (Fin n)) (lam : ℝ) (x : Fin (n + 1) → ℝ) :
    Fin n → ℝ :=
  fun j => (if j ∈ J then lam⁻¹ else 1) * x j.succ

/-- The slack-trick field of Step 1 with a shrunk set. -/
noncomputable def slackFieldSet (g : QuadPP n) (J : Finset (Fin n)) (lam : ℝ)
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases ((1 - lam) * ∑ j ∈ J, quadFun n g (unshrinkSet n J lam x) j)
    (fun j => (if j ∈ J then lam else 1) * quadFun n g (unshrinkSet n J lam x) j)

theorem unshrinkSet_slackMapSet (J : Finset (Fin n)) {lam : ℝ} (hlam : lam ≠ 0)
    (x : Fin n → ℝ) : unshrinkSet n J lam (slackMapSet n J lam x) = x := by
  funext j
  simp only [unshrinkSet, slackMapSet_succ]
  by_cases hj : j ∈ J
  · rw [if_pos hj, if_pos hj, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  · rw [if_neg hj, if_neg hj, one_mul, one_mul]

theorem slackFieldSet_slackMapSet (g : QuadPP n) (J : Finset (Fin n)) {lam : ℝ} (hlam : lam ≠ 0)
    (x : Fin n → ℝ) :
    slackFieldSet n g J lam (slackMapSet n J lam x) = slackMapSet n J lam (quadFun n g x) := by
  funext j'
  refine Fin.cases ?_ (fun j => ?_) j'
  · simp only [slackFieldSet, Fin.cases_zero, slackMapSet_zero, unshrinkSet_slackMapSet n J hlam]
  · simp only [slackFieldSet, Fin.cases_succ, slackMapSet_succ, unshrinkSet_slackMapSet n J hlam]

theorem mono2_unshrinkSet (J : Finset (Fin n)) (lam : ℝ) (x : Fin (n + 1) → ℝ) (μ : MI n 2) :
    mono2 n (unshrinkSet n J lam x) μ
      = lam⁻¹ ^ expIn n J μ * ∏ k, x k.succ ^ (μ.1 k : ℕ) := by
  unfold mono2 unshrinkSet expIn
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [prod_ite_mem_pow J lam⁻¹ (fun k => (μ.1 k : ℕ))]

theorem liftCoefSet_cons2 (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (j' : Fin (n + 1))
    (μ : MI n 2) :
    liftCoefSet n g J lam j' (cons2 n μ) =
      Fin.cases ((1 - lam) * lam⁻¹ ^ expIn n J μ * ∑ j ∈ J, g.coef j μ)
        (fun j => (if j ∈ J then lam else 1) * lam⁻¹ ^ expIn n J μ * g.coef j μ) j' := by
  unfold liftCoefSet
  rw [dif_pos (cons2_val_zero n μ), tail_cons2]

/-- **Evaluation identity (Step 2), shrunk set.** -/
theorem fieldFun_liftR2Set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam : 0 < lam)
    (x : Fin (n + 1) → ℝ) :
    fieldFun (n + 1) (liftR2Set n g J lam hlam) x
      = fun j' => x 0 ^ 2 * slackFieldSet n g J lam x j' := by
  funext j'
  unfold fieldFun
  rw [sum_slack_two n _ (fun μ' h => by
    rw [liftR2Set_coef, liftCoefSet_eq_zero_of_slack n g J lam j' μ' h, Rat.cast_zero, zero_mul])]
  simp only [liftR2Set_coef, liftCoefSet_cons2, mono4_cons2]
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

theorem fieldFun_liftR2Set_slackMapSet (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (hlam : 0 < lam) (x : Fin n → ℝ) :
    fieldFun (n + 1) (liftR2Set n g J lam hlam) (slackMapSet n J lam x)
      = ((1 - (lam : ℝ)) * ∑ j ∈ J, x j) ^ 2 • slackMapSet n J lam (quadFun n g x) := by
  rw [fieldFun_liftR2Set, slackFieldSet_slackMapSet n g J (by exact_mod_cast hlam.ne') x]
  funext j'
  simp only [slackMapSet_zero, Pi.smul_apply, smul_eq_mul]

/-! ### Calculus and readout along the slack map -/

theorem slackMapSet_hasDerivWithinAt {x : ℝ → Fin n → ℝ} {x' : Fin n → ℝ} {s : Set ℝ} {t : ℝ}
    (hx : HasDerivWithinAt x x' s t) (J : Finset (Fin n)) (lam : ℝ) :
    HasDerivWithinAt (fun t => slackMapSet n J lam (x t)) (slackMapSet n J lam x') s t := by
  rw [hasDerivWithinAt_pi]
  intro j'
  have hk : ∀ k, HasDerivWithinAt (fun t => x t k) (x' k) s t :=
    fun k => hasDerivWithinAt_pi.mp hx k
  induction j' using Fin.cases with
  | zero =>
    simpa only [slackMapSet_zero] using
      (HasDerivWithinAt.fun_sum (u := J) (fun k _ => hk k)).const_mul (1 - lam)
  | succ j => simpa only [slackMapSet_succ] using (hk j).const_mul (if j ∈ J then lam else 1)

theorem continuous_slackMapSet (J : Finset (Fin n)) (lam : ℝ) :
    Continuous (slackMapSet n J lam) := by
  apply continuous_pi
  intro j'
  induction j' using Fin.cases with
  | zero =>
    simpa only [slackMapSet_zero] using
      continuous_const.mul (continuous_finsetSum J fun k _ => continuous_apply k)
  | succ j => simpa only [slackMapSet_succ] using continuous_const.mul (continuous_apply j)

theorem readout_set_aux (J : Finset (Fin n)) (lam : ℝ) (c x : Fin n → ℝ) (c0 : ℝ)
    (hc : ∀ j ∈ J, c j = c0) :
    c0 * ((1 - lam) * ∑ j ∈ J, x j) + ∑ j, c j * ((if j ∈ J then lam else 1) * x j)
      = ∑ j, c j * x j := by
  have hsplit : ∀ j, c j * ((if j ∈ J then lam else 1) * x j)
      = c j * x j + (if j ∈ J then (lam - 1) * (c j * x j) else 0) := by
    intro j
    split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib, sum_ite_mem_univ]
  have h2 : ∑ j ∈ J, (lam - 1) * (c j * x j) = (lam - 1) * c0 * ∑ j ∈ J, x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by rw [hc j hj]; ring
  rw [h2]
  ring

/-- Lifted readout: the slack carries the common readout weight `c₀` of the shrunk set. -/
def liftReadoutSet (c0 : ℝ) (c : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases c0 c

theorem liftReadoutSet_slackMapSet (J : Finset (Fin n)) (lam : ℝ) (c x : Fin n → ℝ) (c0 : ℝ)
    (hc : ∀ j ∈ J, c j = c0) :
    ∑ j', liftReadoutSet n c0 c j' * slackMapSet n J lam x j' = ∑ j, c j * x j := by
  rw [Fin.sum_univ_succ]
  simp only [liftReadoutSet, Fin.cases_zero, Fin.cases_succ, slackMapSet_zero, slackMapSet_succ]
  exact readout_set_aux n J lam c x c0 hc

theorem sum_slackMapSet (J : Finset (Fin n)) (lam : ℝ) (x : Fin n → ℝ) :
    ∑ j', slackMapSet n J lam x j' = ∑ j, x j := by
  have := liftReadoutSet_slackMapSet n J lam (fun _ => 1) x 1 (fun _ _ => rfl)
  have h1 : ∀ j', liftReadoutSet n 1 (fun _ => 1) j' = 1 := fun j' => by
    induction j' using Fin.cases with
    | zero => rfl
    | succ j => rfl
  simpa only [h1, one_mul] using this

theorem slackMapSet_norm_le (J : Finset (Fin n)) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (x : Fin n → ℝ) (hx0 : ∀ k, 0 ≤ x k) (hxs : ∑ k, x k = 1) : ‖slackMapSet n J lam x‖ ≤ 1 := by
  have hx1 : ∀ k, x k ≤ 1 := fun k => by
    rw [← hxs]
    exact Finset.single_le_sum (fun i _ => hx0 i) (Finset.mem_univ k)
  have hJ0 : 0 ≤ ∑ j ∈ J, x j := Finset.sum_nonneg fun j _ => hx0 j
  have hJ1 : ∑ j ∈ J, x j ≤ 1 := by
    rw [← hxs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) fun i _ _ => hx0 i
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j'
  rw [Real.norm_eq_abs]
  induction j' using Fin.cases with
  | zero =>
    rw [slackMapSet_zero, abs_of_nonneg (mul_nonneg (by linarith) hJ0)]
    exact mul_le_one₀ (by linarith) hJ0 hJ1
  | succ j =>
    rw [slackMapSet_succ]
    have hc0 : 0 ≤ (if j ∈ J then lam else 1) := by split_ifs <;> linarith
    have hc1 : (if j ∈ J then lam else 1) ≤ 1 := by split_ifs <;> linarith
    rw [abs_of_nonneg (mul_nonneg hc0 (hx0 j))]
    exact mul_le_one₀ hc1 (hx0 j) (hx1 j)

/-! ### The clock with a shrunk set -/

/-- The slack curve `y(s) = slackMapSet (x (max s 0))`. -/
noncomputable def slackCurveSet (J : Finset (Fin n)) (lam : ℝ) (x : ℝ → Fin n → ℝ) (s : ℝ) :
    Fin (n + 1) → ℝ :=
  slackMapSet n J lam (x (max s 0))

theorem slackData_of_simplex_set (g : QuadPP n) (J : Finset (Fin n)) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t)
    (hxs : ∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1)
    (hx0 : 0 < ∑ j ∈ J, x 0 j) :
    NAPTimeChange.SlackData (slackCurveSet n J lam x) (slackCoord n) := by
  have hle : ∀ t, 0 ≤ t → ∀ j, x t j ≤ 1 := fun t ht j => by
    rw [← (hxs t ht).2]
    exact Finset.single_le_sum (fun k _ => (hxs t ht).1 k) (Finset.mem_univ j)
  obtain ⟨j₁, hj₁J, hj₁⟩ : ∃ j ∈ J, 0 < x 0 j := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have := Finset.sum_nonpos hcon
    linarith
  have hpos : ∀ t, 0 ≤ t → 0 < x t j₁ := fun t ht =>
    coord_pos n g j₁ hx (fun s hs => (hxs s hs).1) hle hj₁ ht
  have hJ1 : ∀ t, 0 ≤ t → ∑ j ∈ J, x t j ≤ 1 := fun t ht => by
    rw [← (hxs t ht).2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      fun i _ _ => (hxs t ht).1 i
  have hxc : ContinuousOn x (Ici 0) := fun t ht => (hx t ht).continuousWithinAt
  refine ⟨?_, continuous_apply 0, ?_, ?_⟩
  · exact (continuous_slackMapSet n J lam).comp
      (hxc.comp_continuous (continuous_id.max continuous_const) (fun s => le_max_right s 0))
  · intro t ht
    simp only [slackCoord, slackCurveSet, slackMapSet_zero, max_eq_left ht]
    have : x t j₁ ≤ ∑ j ∈ J, x t j :=
      Finset.single_le_sum (fun k _ => (hxs t ht).1 k) hj₁J
    exact mul_pos (by linarith) (lt_of_lt_of_le (hpos t ht) this)
  · intro t ht
    simp only [slackCoord, slackCurveSet, slackMapSet_zero, max_eq_left ht]
    exact mul_le_one₀ (by linarith) (Finset.sum_nonneg fun j _ => (hxs t ht).1 j) (hJ1 t ht)

/-! ### Theorem 2, ODE half, with a shrunk set -/

/-- **Theorem 2, ODE half, shrunk set `J`.** As `pipeline_ode`, with `r = (1 − λ) Σ_{j∈J} x_j`,
`Σ_{j∈J} x_j(0) > 0`, and readouts `c` constant (`= c₀`) on `J`. -/
theorem pipeline_ode_set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (w : WProtocol (MI (n + 1) 3))
    (hr : Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2Set n g J lam hlam0)))
    {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (quadFun n g (x t)) (Ici 0) t)
    (hxs : ∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1)
    (hx0 : 0 < ∑ j ∈ J, x 0 j) :
    ∃ τ : ℝ → ℝ,
      (∀ σ, 0 ≤ σ →
        τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹ ^ 2) = σ) ∧
      τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
      (∀ t, 0 ≤ t → 0 ≤ τ t ∧
        HasDerivAt τ (((1 - (lam : ℝ)) * ∑ j ∈ J, x (τ t) j) ^ 2) t) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ver (n + 1) (slackMapSet n J lam (x (τ s))))
          (balanceFun (n + 1) w (ver (n + 1) (slackMapSet n J lam (x (τ t))))) (Ici 0) t) ∧
      (∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 → ℝ),
          (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFun (n + 1) w (u t)) (Icc 0 T) t) →
          u 0 = ver (n + 1) (slackMapSet n J lam (x 0)) →
          EqOn u (fun t => ver (n + 1) (slackMapSet n J lam (x (τ t)))) (Icc 0 T)) ∧
      (∀ (c : Fin n → ℝ) (c0 : ℝ), (∀ j ∈ J, c j = c0) → ∀ t, 0 ≤ t →
          ∑ α, readW (liftReadoutSet n c0 c) α * ver (n + 1) (slackMapSet n J lam (x (τ t))) α
            = ∑ j, c j * x (τ t) j) ∧
      (∀ (c : Fin n → ℝ) (c0 ν : ℝ), (∀ j ∈ J, c j = c0) →
          Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
          Tendsto (fun t => ∑ α, readW (liftReadoutSet n c0 c) α *
            ver (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 ν)) := by
  have hl0 : (0 : ℝ) < lam := by exact_mod_cast hlam0
  have hl1 : (lam : ℝ) < 1 := by exact_mod_cast hlam1
  have hS := slackData_of_simplex_set n g J hl0 hl1 hx hxs hx0
  set τ := NAPTimeChange.tau hS with hτdef
  have hτn : ∀ t, 0 ≤ t → 0 ≤ τ t := fun t ht => NAPTimeChange.tau_nonneg hS ht
  have hz : ∀ t, 0 ≤ t → HasDerivWithinAt (fun s => slackMapSet n J lam (x (τ s)))
      (fieldFun (n + 1) (liftR2Set n g J lam hlam0) (slackMapSet n J lam (x (τ t)))) (Ici 0) t := by
    intro t ht
    have hy : HasDerivWithinAt (slackCurveSet n J lam x)
        (slackMapSet n J lam (quadFun n g (x (τ t)))) (Ici 0) (τ t) := by
      have h := slackMapSet_hasDerivWithinAt n (hx (τ t) (hτn t ht)) J lam
      refine h.congr_of_mem (fun s hs => ?_) (hτn t ht)
      simp only [slackCurveSet, max_eq_left (show (0 : ℝ) ≤ s from hs)]
    have hc := HasDerivWithinAt.scomp t hy (NAPTimeChange.tau_hasDerivAt hS ht).hasDerivWithinAt
      (fun s hs => hτn s hs)
    have heq : EqOn (fun s => slackMapSet n J lam (x (τ s))) (slackCurveSet n J lam x ∘ τ)
        (Ici 0) := fun s hs => by
      simp only [Function.comp, slackCurveSet, max_eq_left (hτn s hs)]
    refine (hc.congr_of_mem heq ht).congr_deriv ?_
    rw [fieldFun_liftR2Set_slackMapSet]
    simp only [slackCoord, slackCurveSet, slackMapSet_zero, ← hτdef, max_eq_left (hτn t ht)]
  have hzb : ∀ t, 0 ≤ t → ‖slackMapSet n J lam (x (τ t))‖ ≤ 1 := fun t ht =>
    slackMapSet_norm_le n J hl0 hl1 _ (hxs _ (hτn t ht)).1 (hxs _ (hτn t ht)).2
  have hτ0 : τ 0 = 0 := NAPTimeChange.tau_zero hS
  refine ⟨τ, ?_, hτ0, NAPTimeChange.tau_strictMono hS, NAPTimeChange.tau_tendsto_atTop hS,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have hT : NAPTimeChange.Tfun (slackCurveSet n J lam x) (slackCoord n) σ
        = ∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹ ^ 2 := by
      unfold NAPTimeChange.Tfun NAPTimeChange.phi
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hσ] at hs
      simp only [slackCoord, slackCurveSet, slackMapSet_zero, max_eq_left hs.1]
    rw [← hT]
    exact NAPTimeChange.tau_Tfun hS σ
  · intro t ht
    refine ⟨hτn t ht, ?_⟩
    have := NAPTimeChange.tau_hasDerivAt hS ht
    rw [← hτdef] at this
    simpa only [slackCoord, slackCurveSet, slackMapSet_zero, max_eq_left (hτn t ht)] using this
  · intro t ht
    rw [hasDerivWithinAt_pi]
    intro α
    have := ver_hasDerivWithinAt (n + 1) (liftR2Set n g J lam hlam0) (hz t ht) α
    rw [← balanceFun_ver (n + 1) _ w hr] at this
    exact this
  · intro T u hu hu0
    have hzT : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => slackMapSet n J lam (x (τ s)))
        (fieldFun (n + 1) (liftR2Set n g J lam hlam0) (slackMapSet n J lam (x (τ t))))
        (Icc 0 T) t :=
      fun t ht => (hz t ht.1).mono Icc_subset_Ici_self
    have hu0' : u 0 = fun α => ver (n + 1) (slackMapSet n J lam (x (τ 0))) α := by
      rw [hu0, hτ0]
    exact lifted_solution_unique (n + 1) (liftR2Set n g J lam hlam0) w hr hzT
      (fun t ht => hzb t ht.1) hu hu0'
  · intro c c0 hc t ht
    rw [readout_ver, sum_slackMapSet, (hxs _ (hτn t ht)).2, one_pow, mul_one,
      liftReadoutSet_slackMapSet n J lam c _ c0 hc]
  · intro c c0 ν hc hcν
    have hlim := hcν.comp (NAPTimeChange.tau_tendsto_atTop hS)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Function.comp]
    rw [readout_ver, sum_slackMapSet, (hxs _ (hτn t ht)).2, one_pow, mul_one,
      liftReadoutSet_slackMapSet n J lam c _ c0 hc]

/-- **Theorem 2 (PP ⇒ NAP), ODE half, from an initial point, shrunk set `J`.** For every
syntactic quadratic PP `g`, shrunk set `J` and rational `λ ∈ (0,1)` there is a non-negative
non-autocatalytic `w` realising the cubed lifted field such that for every simplex point `x0` with
`Σ_{j∈J} x0_j > 0`: the PP has a unique solution `x` on `[0,∞)` from `x0`, staying in the simplex;
the explicit clock `τ` (inverse of `σ ↦ ∫₀^σ ((1−λ) Σ_J x_j)⁻²`) makes `ver (slackMapSet (x ∘ τ))`
the unique solution of the cubed protocol from `ver (slackMapSet x0)`; readouts constant on `J`
transfer exactly and in the limit; and if `Σ_J x_j → m > 0` the clock and exponential readout
rates transfer with factor `θ ((1−λ)m)²`, `θ ∈ (0,1)`. -/
theorem pp_to_nap_ode_of_init_set (g : QuadPP n) (J : Finset (Fin n)) (lam : ℚ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : WProtocol (MI (n + 1) 3), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧
      Realizes (veroneseLift (n + 1) 3) w (demand (n + 1) (liftR2Set n g J lam hlam0)) ∧
      ∀ x0 : Fin n → ℝ, (∀ j, 0 ≤ x0 j) → ∑ j, x0 j = 1 → 0 < ∑ j ∈ J, x0 j →
      ∃ x : ℝ → Fin n → ℝ, x 0 = x0 ∧
        (∀ t, 0 ≤ t → HasDerivAt x (quadFun n g (x t)) t) ∧
        (∀ x' : ℝ → Fin n → ℝ, x' 0 = x0 →
          (∀ t, 0 ≤ t → HasDerivAt x' (quadFun n g (x' t)) t) → ∀ t, 0 ≤ t → x' t = x t) ∧
        (∀ t, 0 ≤ t → (∀ j, 0 ≤ x t j) ∧ ∑ j, x t j = 1) ∧
        ∃ τ : ℝ → ℝ,
          (∀ σ, 0 ≤ σ →
            τ (∫ s in (0 : ℝ)..σ, ((1 - (lam : ℝ)) * ∑ j ∈ J, x s j)⁻¹ ^ 2) = σ) ∧
          τ 0 = 0 ∧ StrictMono τ ∧ Tendsto τ atTop atTop ∧
          (∀ t, 0 ≤ t → 0 ≤ τ t ∧
            HasDerivAt τ (((1 - (lam : ℝ)) * ∑ j ∈ J, x (τ t) j) ^ 2) t) ∧
          (∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ver (n + 1) (slackMapSet n J lam (x (τ s))))
              (balanceFun (n + 1) w (ver (n + 1) (slackMapSet n J lam (x (τ t))))) (Ici 0) t) ∧
          (∀ (T : ℝ) (u : ℝ → MI (n + 1) 3 → ℝ),
              (∀ t ∈ Icc (0 : ℝ) T,
                HasDerivWithinAt u (balanceFun (n + 1) w (u t)) (Icc 0 T) t) →
              u 0 = ver (n + 1) (slackMapSet n J lam x0) →
              EqOn u (fun t => ver (n + 1) (slackMapSet n J lam (x (τ t)))) (Icc 0 T)) ∧
          (∀ (c : Fin n → ℝ) (c0 : ℝ), (∀ j ∈ J, c j = c0) → ∀ t, 0 ≤ t →
              ∑ α, readW (liftReadoutSet n c0 c) α *
                ver (n + 1) (slackMapSet n J lam (x (τ t))) α = ∑ j, c j * x (τ t) j) ∧
          (∀ (c : Fin n → ℝ) (c0 ν : ℝ), (∀ j ∈ J, c j = c0) →
              Tendsto (fun t => ∑ j, c j * x t j) atTop (𝓝 ν) →
              Tendsto (fun t => ∑ α, readW (liftReadoutSet n c0 c) α *
                ver (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 ν)) ∧
          (∀ m : ℝ, 0 < m → Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C ≤ τ t) ∧
          (∀ (c : Fin n → ℝ) (c0 ν A κ m : ℝ), (∀ j ∈ J, c j = c0) → 0 ≤ κ → 0 < m →
              Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
              (∀ s, 0 ≤ s → |∑ j, c j * x s j - ν| ≤ A * Real.exp (-κ * s)) →
              ∀ θ : ℝ, 0 < θ → θ < 1 →
              ∃ C, ∀ t, 0 ≤ t →
                |∑ α, readW (liftReadoutSet n c0 c) α *
                    ver (n + 1) (slackMapSet n J lam (x (τ t))) α - ν|
                  ≤ C * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t)) := by
  obtain ⟨w, hw0, hwN, hwr⟩ := exists_nap_realizing_pipeline_set n g J lam hlam0
  refine ⟨w, hw0, hwN, hwr, fun x0 hx0n hx0s hx0p => ?_⟩
  obtain ⟨x, hxi, hx, _, hxs⟩ := quad_global_solution n g x0 hx0n hx0s
  have hxp : 0 < ∑ j ∈ J, x 0 j := by rw [hxi]; exact hx0p
  obtain ⟨τ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    pipeline_ode_set n g J lam hlam0 hlam1 w hwr (fun t ht => (hx t ht).hasDerivWithinAt) hxs hxp
  have hl1 : (0 : ℝ) < 1 - (lam : ℝ) := by
    have : (lam : ℝ) < 1 := by exact_mod_cast hlam1
    linarith
  have hrate : ∀ m : ℝ, 0 < m → Tendsto (fun s => ∑ j ∈ J, x s j) atTop (𝓝 m) →
      ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ C, ∀ t, 0 ≤ t → θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C ≤ τ t :=
    fun m hm hxm θ hθ0 hθ1 =>
      clock_rate (ρ := fun s => (1 - (lam : ℝ)) * ∑ j ∈ J, x s j) (mul_pos hl1 hm) h5 h4
        (hxm.const_mul _) hθ0 hθ1
  refine ⟨x, hxi, hx, fun x' hx'0 hx' t ht => ?_, hxs, τ, h1, h2, h3, h4, h5, h6,
    fun T u hu hu0 => h7 T u hu (by rw [hxi]; exact hu0), h8, h9, hrate, ?_⟩
  · exact quad_solution_unique n g hx hx' (by rw [hxi]; exact hx0n) (by rw [hxi]; exact hx0s)
      (by rw [hx'0, hxi]) t ht
  · intro c c0 ν A κ m hc hκ hm hxm hA θ hθ0 hθ1
    obtain ⟨C0, hC0⟩ := hrate m hm hxm θ hθ0 hθ1
    have hA0 : 0 ≤ A := by
      have := hA 0 le_rfl
      simp only [mul_zero, Real.exp_zero, mul_one] at this
      exact le_trans (abs_nonneg _) this
    refine ⟨A * Real.exp (κ * C0), fun t ht => ?_⟩
    rw [h8 c c0 hc t ht]
    have hτt := hC0 t ht
    calc |∑ j, c j * x (τ t) j - ν| ≤ A * Real.exp (-κ * τ t) := hA (τ t) (h5 t ht).1
      _ ≤ A * Real.exp (-κ * (θ * ((1 - (lam : ℝ)) * m) ^ 2 * t - C0)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hτt hκ
          linarith
      _ = A * Real.exp (κ * C0) * Real.exp (-(θ * κ * ((1 - (lam : ℝ)) * m) ^ 2) * t) := by
          rw [mul_assoc A (Real.exp (κ * C0)), ← Real.exp_add]
          congr 2
          ring

end NAPTransport
end Ripple

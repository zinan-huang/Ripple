import Ripple.LPP.CF24Example

/-!
# CF'24 from interior initial conditions: the second basin

Reference: `ref/pp_to_nap_v5 (1).pdf` (CF'24 worked example) and OPEN_PROBLEMS.md §6.3.
Paper proof: `docs/audit/CF24-INTERIOR.md`.

The vertex `(z_00, z_01, z_11) = (0, 0, 1)` of the simplex is a **hyperbolic sink** of the
CF'24 field (eigenvalues `−2, −1`), so it has a nonempty open basin of interior initial
conditions on which the readout `z_11 + z_01/2` tends to `1`, not to `(3 − √5)/6`.  This
refutes the conjectured basin-entry predicate `Cf24SaddleExcludedBasinEntry`
(`cf24_saddleExcludedBasinEntry_false`): removing the stable manifold of the interior
saddle is not enough.

Method.  The linear function `Φ(x) = 16 z_00 + z_01` (`cornerWeight`) satisfies, on the
simplex with `z_00, z_01 ≥ 0`,

  `Φ̇ = −16 z_00 − z_01 + 121 z_00 z_01 − 14 z_00² + z_01² ≤ −Φ/8`  whenever `Φ ≤ 1/10`

(`cornerWeightDeriv_le`).  Hence `{Φ ≤ 1/10}` is forward invariant and `Φ` decays like
`Φ(0)·exp(−t/8)` along the trajectory (`cf24_cornerWeight_exp_bound`), so `z_00, z_01 → 0`,
`z_11 → 1`, the readout tends to `1` (`cf24_corner_readout_tendsto_one`), the trajectory does
not tend to the saddle, and the Lyapunov function `lyapunov` of `CF24Example` stays above the
sharp threshold `(13 − 4√5)²/784` for all time (`cf24_corner_lyapunov_ge_sharp`).

The true global statement (every interior trajectory tends to `fixedPoint`, to `(0,0,1)` or
to `saddlePoint`; proof on paper by Poincaré–Bendixson with the Dulac function `z_00^{-4/3}`)
is not formalized here: it needs ω-limit sets and the Poincaré–Bendixson theorem.
-/

namespace Ripple
namespace CF24

open scoped Topology

/-! ## The corner weight `Φ = 16 z_00 + z_01` and its Lie derivative -/

/-- The corner weight `Φ(x) = 16 z_00 + z_01`, a linear trapping function for the sink
`(0, 0, 1)`. -/
noncomputable def cornerWeight (x : Fin 3 → ℝ) : ℝ := 16 * x 0 + x 1

/-- Lie derivative of `cornerWeight` along `field`. -/
noncomputable def cornerWeightDeriv (x : Fin 3 → ℝ) : ℝ := 16 * field x 0 + field x 1

/-- On the simplex, `Φ̇ = −16a − b + 121ab − 14a² + b²` with `a = z_00`, `b = z_01`. -/
theorem cornerWeightDeriv_eq (x : Fin 3 → ℝ) (hs : x 0 + x 1 + x 2 = 1) :
    cornerWeightDeriv x
      = -16 * x 0 - x 1 + 121 * x 0 * x 1 - 14 * x 0 ^ 2 + x 1 ^ 2 := by
  have hc : x 2 = 1 - x 0 - x 1 := by linarith
  simp only [cornerWeightDeriv, field]
  rw [hc]
  ring

/-- Strict decrease on the corner: if `z_00, z_01 ≥ 0` lie on the simplex and
`Φ ≤ 1/10`, then `Φ̇ ≤ −Φ/8`.
Certificate: `Φ̇ + Φ/8 = −121a(1/10 − b) − (19/10)a − b(1/10 − b) − (31/40)b − 14a²`. -/
theorem cornerWeightDeriv_le (x : Fin 3 → ℝ) (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1)
    (hs : x 0 + x 1 + x 2 = 1) (hΦ : cornerWeight x ≤ 1 / 10) :
    cornerWeightDeriv x ≤ -(1 / 8) * cornerWeight x := by
  rw [cornerWeightDeriv_eq x hs]
  unfold cornerWeight at *
  have hb : x 1 ≤ 1 / 10 := by linarith
  have hb' : 0 ≤ 1 / 10 - x 1 := by linarith
  nlinarith [mul_nonneg h0 hb', mul_nonneg h1 hb', sq_nonneg (x 0)]

/-! ## Trajectory facts (wrappers around `cf24_global_solution`) -/

/-- The trajectory solves `ẋ = field x` at every `t ≥ 0`. -/
theorem cf24_traj_hasDerivAt (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (cf24_global_solution x0 h_nn h_simplex).trajectory
      (field ((cf24_global_solution x0 h_nn h_simplex).trajectory t)) t :=
  (cf24_global_solution x0 h_nn h_simplex).is_solution t ht

/-- The trajectory starts at `x0`. -/
theorem cf24_traj_zero (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) :
    (cf24_global_solution x0 h_nn h_simplex).trajectory 0 = x0 :=
  (cf24_global_solution x0 h_nn h_simplex).init_cond

/-- Coordinates stay non-negative. -/
theorem cf24_traj_nonneg (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    0 ≤ (cf24_global_solution x0 h_nn h_simplex).trajectory t i :=
  pivp_solution_nonneg (P := cf24PIVP x0)
    cf24_isCRNImplementable field_locally_lipschitz
    (by intro j; simpa [cf24PIVP] using h_nn j)
    (cf24_global_solution x0 h_nn h_simplex) t ht i

/-- Coordinates sum to one. -/
theorem cf24_traj_sum_eq_one (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) {t : ℝ} (ht : 0 ≤ t) :
    (cf24_global_solution x0 h_nn h_simplex).trajectory t 0
      + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1
      + (cf24_global_solution x0 h_nn h_simplex).trajectory t 2 = 1 := by
  have h_cons' : ∀ x, ∑ i, (cf24PIVP x0).field x i = 0 := fun x => field_conservative x
  have h_init' : ∑ i, (cf24PIVP x0).init i = 1 := by simpa [cf24PIVP] using h_simplex
  have hSum := conservative_trajectory_simplex (cf24_global_solution x0 h_nn h_simplex)
    h_cons' h_init' ht
  simpa [Fin.sum_univ_three] using hSum

/-- `Φ` along the trajectory is differentiable with derivative `cornerWeightDeriv`. -/
theorem cf24_cornerWeight_hasDerivAt (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
      (cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory t)) t := by
  have h := hasDerivAt_pi.mp (cf24_traj_hasDerivAt x0 h_nn h_simplex ht)
  exact ((h 0).const_mul 16).add (h 1)

/-! ## Forward invariance of `{Φ ≤ Φ(x0)}` and exponential decay -/

/-- **Forward invariance of the corner.**  If `z_00(0) > 0` and `Φ(x0) ≤ 1/10`, then
`Φ(x(t)) ≤ Φ(x0)` for all `t ≥ 0`. -/
theorem cf24_cornerWeight_le_init (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    ∀ t, 0 ≤ t →
      cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory t)
        ≤ cornerWeight x0 := by
  intro T hT
  have hΦ0 : 0 < cornerWeight x0 := by
    unfold cornerWeight; linarith [h_nn 1]
  have hcont : ContinuousOn
      (fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
      (Set.Icc 0 T) :=
    fun s hs => (cf24_cornerWeight_hasDerivAt x0 h_nn h_simplex hs.1).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
        (cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
        (Set.Ici s) s :=
    fun s hs => (cf24_cornerWeight_hasDerivAt x0 h_nn h_simplex hs.1).hasDerivWithinAt
  have hinit : cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory 0)
      ≤ cornerWeight x0 :=
    le_of_eq (by rw [cf24_traj_zero])
  refine image_le_of_deriv_right_lt_deriv_boundary
    (f := fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
    (f' := fun s => cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
    (B := fun _ => cornerWeight x0) (B' := fun _ => 0)
    hcont hderiv hinit (fun _ => hasDerivAt_const _ _) ?_ ⟨hT, le_refl T⟩
  intro s hs heq
  have heq' : cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s)
      = cornerWeight x0 := heq
  show cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s) < 0
  have hle := cornerWeightDeriv_le _ (cf24_traj_nonneg x0 h_nn h_simplex hs.1 0)
    (cf24_traj_nonneg x0 h_nn h_simplex hs.1 1) (cf24_traj_sum_eq_one x0 h_nn h_simplex hs.1)
    (by rw [heq']; exact hΦ)
  rw [heq'] at hle
  linarith

/-- **Exponential decay of the corner weight.**  If `z_00(0) > 0` and `Φ(x0) ≤ 1/10`, then
`Φ(x(t)) ≤ Φ(x0)·exp(−t/8)` for all `t ≥ 0`. -/
theorem cf24_cornerWeight_exp_bound (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    ∀ t, 0 ≤ t →
      cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory t)
        ≤ cornerWeight x0 * Real.exp (-(1 / 8) * t) := by
  intro T hT
  have hle := cf24_cornerWeight_le_init x0 h_nn h_simplex h0 hΦ
  have hcont : ContinuousOn
      (fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
      (Set.Icc 0 T) :=
    fun s hs => (cf24_cornerWeight_hasDerivAt x0 h_nn h_simplex hs.1).continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
        (cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
        (Set.Ici s) s :=
    fun s hs => (cf24_cornerWeight_hasDerivAt x0 h_nn h_simplex hs.1).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) T,
      cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s)
        ≤ -(1 / 8) * cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s) :=
    fun s hs => cornerWeightDeriv_le _ (cf24_traj_nonneg x0 h_nn h_simplex hs.1 0)
      (cf24_traj_nonneg x0 h_nn h_simplex hs.1 1) (cf24_traj_sum_eq_one x0 h_nn h_simplex hs.1)
      ((hle s hs.1).trans hΦ)
  have key := scalar_exponential_decay
    (V := fun s => cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
    (V' := fun s => cornerWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
    (α := 1 / 8) (T := T) (by norm_num) hT hcont hderiv hbound T ⟨hT, le_refl T⟩
  have key' : cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory T)
      ≤ cornerWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory 0)
          * Real.exp (-(1 / 8) * T) := key
  rwa [cf24_traj_zero] at key'

/-! ## Consequences: convergence to `(0, 0, 1)`, readout `→ 1`, no saddle, no basin entry -/

/-- A non-negative function below `C·exp(−t/8)` on `[0, ∞)` tends to `0`. -/
theorem tendsto_zero_of_le_exp_eighth {g : ℝ → ℝ} {C : ℝ}
    (hg0 : ∀ t, 0 ≤ t → 0 ≤ g t)
    (hg : ∀ t, 0 ≤ t → g t ≤ C * Real.exp (-(1 / 8) * t)) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have h_exp : Filter.Tendsto (fun t : ℝ => Real.exp (-(1 / 8) * t))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -(1 / 8) * t) Filter.atTop Filter.atBot :=
      (Filter.tendsto_const_mul_atBot_of_neg (by norm_num : -(1 / 8 : ℝ) < 0)).mpr
        Filter.tendsto_id
    exact Real.tendsto_exp_atBot.comp h1
  have h_rhs : Filter.Tendsto (fun t : ℝ => C * Real.exp (-(1 / 8) * t))
      Filter.atTop (nhds 0) := by
    simpa using h_exp.const_mul C
  refine squeeze_zero' ?_ ?_ h_rhs
  · exact Filter.eventually_atTop.mpr ⟨0, fun t ht => hg0 t ht⟩
  · exact Filter.eventually_atTop.mpr ⟨0, fun t ht => hg t ht⟩

/-- `z_00(t) → 0` from the corner. -/
theorem cf24_corner_coord_zero_tendsto (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    Filter.Tendsto (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 0)
      Filter.atTop (nhds 0) := by
  refine tendsto_zero_of_le_exp_eighth (C := cornerWeight x0)
    (fun t ht => cf24_traj_nonneg x0 h_nn h_simplex ht 0) ?_
  intro t ht
  have h := cf24_cornerWeight_exp_bound x0 h_nn h_simplex h0 hΦ t ht
  have ha := cf24_traj_nonneg x0 h_nn h_simplex ht 0
  have hb := cf24_traj_nonneg x0 h_nn h_simplex ht 1
  have h' : 16 * (cf24_global_solution x0 h_nn h_simplex).trajectory t 0
      + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1
      ≤ cornerWeight x0 * Real.exp (-(1 / 8) * t) := h
  have key : (cf24_global_solution x0 h_nn h_simplex).trajectory t 0
      ≤ cornerWeight x0 * Real.exp (-(1 / 8) * t) := by linarith
  exact key

/-- `z_01(t) → 0` from the corner. -/
theorem cf24_corner_coord_one_tendsto (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    Filter.Tendsto (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 1)
      Filter.atTop (nhds 0) := by
  refine tendsto_zero_of_le_exp_eighth (C := cornerWeight x0)
    (fun t ht => cf24_traj_nonneg x0 h_nn h_simplex ht 1) ?_
  intro t ht
  have h := cf24_cornerWeight_exp_bound x0 h_nn h_simplex h0 hΦ t ht
  have ha := cf24_traj_nonneg x0 h_nn h_simplex ht 0
  have h' : 16 * (cf24_global_solution x0 h_nn h_simplex).trajectory t 0
      + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1
      ≤ cornerWeight x0 * Real.exp (-(1 / 8) * t) := h
  have key : (cf24_global_solution x0 h_nn h_simplex).trajectory t 1
      ≤ cornerWeight x0 * Real.exp (-(1 / 8) * t) := by linarith
  exact key

/-- `z_11(t) → 1` from the corner. -/
theorem cf24_corner_coord_two_tendsto (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    Filter.Tendsto (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2)
      Filter.atTop (nhds 1) := by
  have ha := cf24_corner_coord_zero_tendsto x0 h_nn h_simplex h0 hΦ
  have hb := cf24_corner_coord_one_tendsto x0 h_nn h_simplex h0 hΦ
  have h : Filter.Tendsto
      (fun t => 1 - (cf24_global_solution x0 h_nn h_simplex).trajectory t 0
        - (cf24_global_solution x0 h_nn h_simplex).trajectory t 1)
      Filter.atTop (nhds (1 - 0 - 0)) :=
    (tendsto_const_nhds.sub ha).sub hb
  rw [show (1 : ℝ) - 0 - 0 = 1 by norm_num] at h
  refine h.congr' (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop (0 : ℝ)) ?_)
  intro t ht
  have := cf24_traj_sum_eq_one x0 h_nn h_simplex (Set.mem_Ici.mp ht)
  show (1 : ℝ) - _ - _ = _
  linarith

/-- The sink `(z_00, z_01, z_11) = (0, 0, 1)`. -/
noncomputable def cornerVertex : Fin 3 → ℝ := ![0, 0, 1]

/-- From the corner the whole trajectory tends to `(0, 0, 1)`. -/
theorem cf24_corner_tendsto_vertex (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    Filter.Tendsto (cf24_global_solution x0 h_nn h_simplex).trajectory
      Filter.atTop (nhds cornerVertex) := by
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa [cornerVertex] using cf24_corner_coord_zero_tendsto x0 h_nn h_simplex h0 hΦ
  · simpa [cornerVertex] using cf24_corner_coord_one_tendsto x0 h_nn h_simplex h0 hΦ
  · simpa [cornerVertex] using cf24_corner_coord_two_tendsto x0 h_nn h_simplex h0 hΦ

/-- **Readout from the corner tends to `1`**, not to `(3 − √5)/6`: an open set of interior
initial conditions (`z_00 > 0`, `16 z_00 + z_01 ≤ 1/10`) on which the protocol computes the
wrong number. -/
theorem cf24_corner_readout_tendsto_one (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
        + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds 1) := by
  have h := (cf24_corner_coord_two_tendsto x0 h_nn h_simplex h0 hΦ).add
    ((cf24_corner_coord_one_tendsto x0 h_nn h_simplex h0 hΦ).div_const 2)
  simpa using h

/-- The corner readout limit `1` differs from `readoutLimit = (3 − √5)/6`. -/
theorem readoutLimit_lt_one : readoutLimit < 1 := by
  unfold readoutLimit
  linarith [Real.sqrt_nonneg 5]

/-- From the corner the readout does **not** tend to `(3 − √5)/6`. -/
theorem cf24_corner_readout_not_tendsto_readoutLimit (x0 : Fin 3 → ℝ)
    (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0)
    (hΦ : cornerWeight x0 ≤ 1 / 10) :
    ¬ Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
        + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  intro h
  have := tendsto_nhds_unique h (cf24_corner_readout_tendsto_one x0 h_nn h_simplex h0 hΦ)
  linarith [readoutLimit_lt_one]

/-- From the corner the trajectory does not tend to the saddle (`z_01 → 0 ≠ 2/9`). -/
theorem cf24_corner_not_tendsto_saddle (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    ¬ Filter.Tendsto (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
        Filter.atTop (nhds saddlePoint) := by
  intro h
  have h1 : Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 1)
      Filter.atTop (nhds (saddlePoint 1)) :=
    ((continuous_apply (1 : Fin 3)).tendsto saddlePoint).comp h
  have := tendsto_nhds_unique h1 (cf24_corner_coord_one_tendsto x0 h_nn h_simplex h0 hΦ)
  simp only [saddlePoint] at this
  norm_num at this

/-- From the corner the Lyapunov function of `CF24Example` never drops below the sharp
threshold `(13 − 4√5)²/784`: `z_11(t) ≥ 9/10` while `z_11* < 7/18`. -/
theorem cf24_corner_lyapunov_ge_sharp (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) (h0 : 0 < x0 0) (hΦ : cornerWeight x0 ≤ 1 / 10) :
    ∀ t, 0 ≤ t →
      (13 - 4 * Real.sqrt 5) ^ 2 / 784
        ≤ lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t) := by
  intro t ht
  have hΦt := (cf24_cornerWeight_le_init x0 h_nn h_simplex h0 hΦ t ht).trans hΦ
  have ha := cf24_traj_nonneg x0 h_nn h_simplex ht 0
  have hb := cf24_traj_nonneg x0 h_nn h_simplex ht 1
  have hsum := cf24_traj_sum_eq_one x0 h_nn h_simplex ht
  have hc : 9 / 10 ≤ (cf24_global_solution x0 h_nn h_simplex).trajectory t 2 := by
    unfold cornerWeight at hΦt; linarith
  have hs5 := Real.sqrt_nonneg 5
  have hs5_le : Real.sqrt 5 ≤ 7 / 3 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 3), Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have hfp : fixedPoint 2 = (7 - 3 * Real.sqrt 5) / 18 := by simp only [fixedPoint]
  have hcc : 1 / 2 ≤ (cf24_global_solution x0 h_nn h_simplex).trajectory t 2 - fixedPoint 2 := by
    rw [hfp]; linarith
  have hsq : 1 / 4 ≤ ((cf24_global_solution x0 h_nn h_simplex).trajectory t 2 - fixedPoint 2) ^ 2 := by
    nlinarith [hcc]
  have hu : (13 - 4 * Real.sqrt 5) ^ 2 ≤ 14 ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  unfold lyapunov
  linarith [sq_nonneg ((cf24_global_solution x0 h_nn h_simplex).trajectory t 1 - fixedPoint 1)]

/-! ## The explicit counterexample `(1/200, 1/200, 99/100)` -/

/-- An interior initial condition in the corner: `Φ = 17/200 ≤ 1/10`. -/
noncomputable def cornerInit : Fin 3 → ℝ
  | ⟨0, _⟩ => 1 / 200
  | ⟨1, _⟩ => 1 / 200
  | ⟨2, _⟩ => 99 / 100

theorem cornerInit_zero_eq : cornerInit 0 = 1 / 200 := rfl

theorem cornerInit_one_eq : cornerInit 1 = 1 / 200 := rfl

theorem cornerInit_two_eq : cornerInit 2 = 99 / 100 := rfl

theorem cornerInit_nonneg : ∀ i, 0 ≤ cornerInit i := by
  intro i
  fin_cases i
  · rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, cornerInit_zero_eq]; norm_num
  · rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, cornerInit_one_eq]; norm_num
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, cornerInit_two_eq]; norm_num

theorem cornerInit_simplex : ∑ i, cornerInit i = 1 := by
  rw [Fin.sum_univ_three, cornerInit_zero_eq, cornerInit_one_eq, cornerInit_two_eq]; norm_num

theorem cornerInit_zero_pos : 0 < cornerInit 0 := by rw [cornerInit_zero_eq]; norm_num

theorem cornerInit_one_pos : 0 < cornerInit 1 := by rw [cornerInit_one_eq]; norm_num

theorem cornerInit_two_pos : 0 < cornerInit 2 := by rw [cornerInit_two_eq]; norm_num

theorem cornerInit_cornerWeight_le : cornerWeight cornerInit ≤ 1 / 10 := by
  rw [cornerWeight, cornerInit_zero_eq, cornerInit_one_eq]; norm_num

/-- **`Cf24SaddleExcludedBasinEntry` is false.**  The interior point `(1/200, 1/200, 99/100)`
lies in the basin of the sink `(0, 0, 1)`: its trajectory does not tend to the saddle, yet
the Lyapunov function never drops below the sharp threshold.  Removing the saddle's stable
manifold does not repair `Cf24BasinEntry`; the simplex interior splits into two open basins
(see `cf24_corner_readout_tendsto_one`). -/
theorem cf24_saddleExcludedBasinEntry_false : ¬ Cf24SaddleExcludedBasinEntry := by
  intro h
  obtain ⟨t₀, ht₀, -, hlt⟩ := h cornerInit cornerInit_nonneg cornerInit_simplex
    cornerInit_zero_pos cornerInit_one_pos cornerInit_two_pos
    (cf24_corner_not_tendsto_saddle cornerInit cornerInit_nonneg cornerInit_simplex
      cornerInit_zero_pos cornerInit_cornerWeight_le)
  have hge := cf24_corner_lyapunov_ge_sharp cornerInit cornerInit_nonneg cornerInit_simplex
    cornerInit_zero_pos cornerInit_cornerWeight_le t₀ ht₀
  linarith

end CF24
end Ripple

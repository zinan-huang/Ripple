import Ripple.LPP.CF24Example

/-!
# CF'24 readout from the canonical initial condition

Reference: `ref/pp_to_nap_v5 (1).pdf` (PP to NAP via the cubing construction, CF'24 worked
example), §1–§2 and §10: the CF'24 population protocol on the simplex
`z_00 + z_01 + z_11 = 1`, started at the canonical initial condition
`(z_00, z_01, z_11) = (1, 0, 0)`, has readout `z_11 + z_01/2 → (3 − √5)/6`; the λ-trick,
the r²-trick and the 20-variable NAP keep this limit.

This file proves that claim for the canonical initial condition, with no hypothesis.

Method.  On the part of the simplex where the Lyapunov function
`V = (z_01 − z_01*)² + (z_11 − z_11*)²` lies between `1/48` and `V(1, 0, 0)`, the derivative
of `V` along the field is at most `−1/20` (`lyapunovDeriv_le_of_annulus`; a polynomial
inequality, proved from a degree-3 certificate found by linear programming).  The trajectory
from `(1, 0, 0)` therefore stays below the barrier `V(1,0,0) − t/40` and enters the sharp
basin `V < (13 − 4√5)²/784` of `cf24_readout_tendsto_from_sharp_lyapunov_init`
(`cf24_canonical_basin_entry`).  Proof on paper: `docs/audit/FIX1-CF24.md`.
-/

namespace Ripple
namespace CF24

open scoped Topology

/-- The canonical initial condition `(z_00, z_01, z_11) = (1, 0, 0)` of the CF'24 protocol. -/
noncomputable def canonicalInit : Fin 3 → ℝ := ![1, 0, 0]

theorem canonicalInit_nonneg : ∀ i, 0 ≤ canonicalInit i := by
  intro i
  fin_cases i <;> simp [canonicalInit]

theorem canonicalInit_simplex : ∑ i, canonicalInit i = 1 := by
  simp [canonicalInit, Fin.sum_univ_three]

theorem canonicalInit_zero_pos : 0 < canonicalInit 0 := by
  simp [canonicalInit]

private lemma sqrt5_lo : (223606 / 100000 : ℝ) ≤ Real.sqrt 5 := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  nlinarith

private lemma sqrt5_hi : Real.sqrt 5 ≤ 223607 / 100000 := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  nlinarith

/-- The rational core inequality on the annulus (coordinates `u = z_01 − z_01*`,
`v = z_11 − z_11*`).  Certificate: a nonnegative combination of the products below. -/
private lemma annulus_poly (u v : ℝ) (h1 : -(2 / 9) ≤ u) (h2 : -(1623 / 100000) ≤ v)
    (h3 : u + v ≤ 7617 / 10000) (hq0 : 1 / 48 ≤ u ^ 2 + v ^ 2)
    (hq1 : u ^ 2 + v ^ 2 ≤ 4965 / 100000) :
    -1527 / 100 * u ^ 2 + 22435 / 1000 * u * v - 2086 / 100 * v ^ 2
        + 2 / 10000 * (u ^ 2 + v ^ 2)
        + 20 * u ^ 3 - 12 * u ^ 2 * v + 28 * v ^ 3 ≤ -1 / 20 := by
  have l0 : 0 ≤ u + 2 / 9 := by linarith
  have l1 : 0 ≤ v + 1623 / 100000 := by linarith
  have l2 : 0 ≤ 7617 / 10000 - u - v := by linarith
  have q0 : 0 ≤ u ^ 2 + v ^ 2 - 1 / 48 := by linarith
  have q1 : 0 ≤ 4965 / 100000 - (u ^ 2 + v ^ 2) := by linarith
  nlinarith [mul_nonneg l0 q1, mul_nonneg l1 q1, mul_nonneg l2 q0,
    mul_nonneg (mul_nonneg l1 l2) l2, mul_nonneg (mul_nonneg l2 l2) l2,
    sq_nonneg u,
    mul_nonneg l1 (sq_nonneg (u - v / 4)), mul_nonneg l1 (sq_nonneg (u - v / 2)),
    mul_nonneg l2 (sq_nonneg (u - 5 * v / 4)), mul_nonneg l2 (sq_nonneg (u - 3 * v / 2))]

/-- The quadratic part of `V̇`, with its `√5` coefficients replaced by rational bounds. -/
private lemma lyapunovQuad_le_rat (u v : ℝ) :
    lyapunovQuad u v ≤
      -1527 / 100 * u ^ 2 + 22435 / 1000 * u * v - 2086 / 100 * v ^ 2
        + 2 / 10000 * (u ^ 2 + v ^ 2) := by
  have hlo := sqrt5_lo
  have hhi := sqrt5_hi
  have a : 0 ≤ 223607 / 100000 - Real.sqrt 5 := by linarith
  have b : 0 ≤ Real.sqrt 5 - 223606 / 100000 := by linarith
  unfold lyapunovQuad
  nlinarith [mul_nonneg a (sq_nonneg u), mul_nonneg b (sq_nonneg v),
    mul_nonneg a (sq_nonneg (u + v)), mul_nonneg b (sq_nonneg (u + v)),
    mul_nonneg a (sq_nonneg (u - v)), mul_nonneg b (sq_nonneg (u - v)),
    sq_nonneg u, sq_nonneg v, sq_nonneg (u + v), sq_nonneg (u - v)]

private lemma fixedPoint_one : fixedPoint 1 = 2 / 9 := by
  first
  | rfl
  | simp [fixedPoint]

private lemma fixedPoint_two : fixedPoint 2 = (7 - 3 * Real.sqrt 5) / 18 := by
  first
  | rfl
  | simp [fixedPoint]

theorem lyapunov_canonicalInit :
    lyapunov canonicalInit = (fixedPoint 1) ^ 2 + (fixedPoint 2) ^ 2 := by
  simp [lyapunov, canonicalInit]

theorem lyapunov_canonicalInit_le : lyapunov canonicalInit ≤ 4965 / 100000 := by
  rw [lyapunov_canonicalInit, fixedPoint_one, fixedPoint_two]
  have h5 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [sqrt5_lo]

theorem lyapunov_canonicalInit_ge : (2 / 9) ^ 2 ≤ lyapunov canonicalInit := by
  rw [lyapunov_canonicalInit, fixedPoint_one]
  nlinarith [sq_nonneg (fixedPoint 2)]

/-- **The annulus bound.**  On the simplex, where `1/48 ≤ V ≤ V(1,0,0)`, the derivative of the
Lyapunov function along the CF'24 field is at most `−1/20`. -/
theorem lyapunovDeriv_le_of_annulus (x : Fin 3 → ℝ) (hnn : ∀ i, 0 ≤ x i)
    (hs : x 0 + x 1 + x 2 = 1) (hlo : 1 / 48 ≤ lyapunov x)
    (hhi : lyapunov x ≤ lyapunov canonicalInit) :
    lyapunovDeriv x ≤ -1 / 20 := by
  have s_lo := sqrt5_lo
  have s_hi := sqrt5_hi
  have hb := fixedPoint_one
  have hc := fixedPoint_two
  have hV0 := lyapunov_canonicalInit_le
  have hVx : lyapunov x = (x 1 - fixedPoint 1) ^ 2 + (x 2 - fixedPoint 2) ^ 2 := rfl
  rw [lyapunovDeriv_on_simplex x hs]
  have h1 : -(2 / 9) ≤ x 1 - fixedPoint 1 := by linarith [hnn 1]
  have h2 : -(1623 / 100000) ≤ x 2 - fixedPoint 2 := by linarith [hnn 2]
  have h3 : (x 1 - fixedPoint 1) + (x 2 - fixedPoint 2) ≤ 7617 / 10000 := by
    linarith [hnn 0]
  have hq0 : 1 / 48 ≤ (x 1 - fixedPoint 1) ^ 2 + (x 2 - fixedPoint 2) ^ 2 := by
    rw [← hVx]; exact hlo
  have hq1 : (x 1 - fixedPoint 1) ^ 2 + (x 2 - fixedPoint 2) ^ 2 ≤ 4965 / 100000 := by
    rw [← hVx]; exact hhi.trans hV0
  have hQ := lyapunovQuad_le_rat (x 1 - fixedPoint 1) (x 2 - fixedPoint 2)
  have hP := annulus_poly (x 1 - fixedPoint 1) (x 2 - fixedPoint 2) h1 h2 h3 hq0 hq1
  linarith

/-- The sharp basin threshold exceeds `1/48`. -/
theorem one_div_48_lt_sharp : (1 : ℝ) / 48 < (13 - 4 * Real.sqrt 5) ^ 2 / 784 := by
  have h : (405 / 100 : ℝ) ≤ 13 - 4 * Real.sqrt 5 := by linarith [sqrt5_hi]
  nlinarith [h]

/-- The global CF'24 trajectory from the canonical initial condition. -/
noncomputable abbrev canonicalSolution : PIVP.Solution (cf24PIVP canonicalInit) :=
  cf24_global_solution canonicalInit canonicalInit_nonneg canonicalInit_simplex

/-- **Basin entry from `(1, 0, 0)`.**  The canonical trajectory reaches the sharp basin. -/
theorem cf24_canonical_basin_entry :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      0 < lyapunov (canonicalSolution.trajectory t₀) ∧
      lyapunov (canonicalSolution.trajectory t₀) < (13 - 4 * Real.sqrt 5) ^ 2 / 784 := by
  set sol := canonicalSolution with hsol
  set V0 : ℝ := lyapunov canonicalInit with hV0_def
  have hV0_ge : (2 / 9) ^ 2 ≤ V0 := lyapunov_canonicalInit_ge
  set T : ℝ := 40 * (V0 - 1 / 48) with hT_def
  have hT_nn : 0 ≤ T := by rw [hT_def]; nlinarith [hV0_ge]
  have hly_cont : Continuous lyapunov := by
    unfold lyapunov
    exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
      |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
  have hsolD : ∀ t, 0 ≤ t →
      HasDerivAt sol.trajectory (field (sol.trajectory t)) t :=
    fun t ht => sol.is_solution t ht
  have hnn_traj : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i := by
    intro t ht i
    exact pivp_solution_nonneg (P := cf24PIVP canonicalInit)
      cf24_isCRNImplementable field_locally_lipschitz
      (by intro j; simpa [cf24PIVP] using canonicalInit_nonneg j)
      sol t ht i
  have hsimp_traj : ∀ t, 0 ≤ t →
      sol.trajectory t 0 + sol.trajectory t 1 + sol.trajectory t 2 = 1 := by
    intro t ht
    have hPi : ∑ i, sol.trajectory t i = 1 :=
      conservative_trajectory_simplex sol field_conservative
        (by simpa [cf24PIVP] using canonicalInit_simplex) ht
    simpa [Fin.sum_univ_three] using hPi
  have hg0 : lyapunov (sol.trajectory 0) = V0 := by
    rw [sol.init_cond]; rfl
  have hgc : ContinuousOn (fun t => lyapunov (sol.trajectory t)) (Set.Icc 0 T) := by
    intro t ht
    exact (hly_cont.continuousAt.comp (hsolD t ht.1).continuousAt).continuousWithinAt
  have hgD : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => lyapunov (sol.trajectory s))
        (lyapunovDeriv (sol.trajectory t)) (Set.Ici t) t := by
    intro t ht
    have h := hsolD t ht.1
    have h1 : HasDerivWithinAt (fun s => sol.trajectory s 1)
        (field (sol.trajectory t) 1) (Set.Ici t) t :=
      (hasDerivAt_pi.mp h 1).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun s => sol.trajectory s 2)
        (field (sol.trajectory t) 2) (Set.Ici t) t :=
      (hasDerivAt_pi.mp h 2).hasDerivWithinAt
    exact lyapunov_hasDerivWithinAt h1 h2
  have hBc : ContinuousOn (fun t : ℝ => V0 - t / 40) (Set.Icc 0 T) := by
    exact (continuous_const.sub (continuous_id.div_const 40)).continuousOn
  have hBD : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun t : ℝ => V0 - t / 40) (-(1 / 40)) (Set.Ici t) t := by
    intro t _
    exact (((hasDerivAt_id' t).div_const 40).const_sub V0).hasDerivWithinAt
  have hbarrier : ∀ ⦃t⦄, t ∈ Set.Icc (0 : ℝ) T →
      lyapunov (sol.trajectory t) ≤ V0 - t / 40 := by
    refine image_le_of_deriv_right_lt_deriv_boundary'
      (f := fun t => lyapunov (sol.trajectory t))
      (f' := fun t => lyapunovDeriv (sol.trajectory t))
      (B := fun t : ℝ => V0 - t / 40) (B' := fun _ => -(1 / 40))
      hgc hgD (by show lyapunov (sol.trajectory 0) ≤ V0 - 0 / 40; rw [hg0]; simp) hBc hBD ?_
    intro t ht heq0
    have heq : lyapunov (sol.trajectory t) = V0 - t / 40 := heq0
    have hlo : 1 / 48 ≤ lyapunov (sol.trajectory t) := by
      rw [heq]
      have : t < T := ht.2
      rw [hT_def] at this
      linarith
    have hhi : lyapunov (sol.trajectory t) ≤ lyapunov canonicalInit := by
      rw [heq]; linarith [ht.1]
    have := lyapunovDeriv_le_of_annulus (sol.trajectory t) (hnn_traj t ht.1)
      (hsimp_traj t ht.1) hlo hhi
    show lyapunovDeriv (sol.trajectory t) < -(1 / 40)
    linarith
  have hgT : lyapunov (sol.trajectory T) ≤ 1 / 48 := by
    have := hbarrier ⟨hT_nn, le_rfl⟩
    rw [hT_def] at this ⊢
    linarith
  have hsharp := one_div_48_lt_sharp
  by_cases hpos : 0 < lyapunov (sol.trajectory T)
  · exact ⟨T, hT_nn, hpos, lt_of_le_of_lt hgT hsharp⟩
  · -- `V(T) = 0`: take a time where `V = 1/96` (intermediate value theorem).
    have hzero : lyapunov (sol.trajectory T) ≤ 1 / 96 := by
      linarith [lyapunov_nonneg (sol.trajectory T), not_lt.mp hpos]
    have hmem : (1 / 96 : ℝ) ∈ Set.Icc (lyapunov (sol.trajectory T))
        (lyapunov (sol.trajectory 0)) := by
      refine ⟨hzero, ?_⟩
      rw [hg0]; nlinarith [hV0_ge]
    obtain ⟨t₀, ht₀, hval0⟩ := intermediate_value_Icc' hT_nn hgc hmem
    have hval : lyapunov (sol.trajectory t₀) = 1 / 96 := hval0
    refine ⟨t₀, ht₀.1, ?_, ?_⟩
    · rw [hval]; norm_num
    · rw [hval]; linarith [hsharp]

/-- Readout convergence from any simplex initial condition whose trajectory has entered the
sharp basin at some time `t₀`.  (Same proof as
`cf24_step5_readout_of_cornerExcludedBasinEntry`, with the entry time given.) -/
theorem cf24_readout_of_sharp_entry
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (t₀ : ℝ) (ht₀_nn : 0 ≤ t₀)
    (hV_pos : 0 < lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀))
    (hV_sharp : lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀)
      < (13 - 4 * Real.sqrt 5) ^ 2 / 784) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set y : ℝ → Fin 3 → ℝ := fun t => sol.trajectory (t + t₀) with hy_def
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x := fun _ => rfl
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => y s) (field (y t)) t := by
    intro t ht
    have hsol_is := sol.is_solution (t + t₀) (by linarith)
    have hcomp : HasDerivAt (fun s => sol.trajectory (s + t₀))
        ((cf24PIVP x0).field (sol.trajectory (t + t₀))) t :=
      hsol_is.comp_add_const t t₀
    simpa [hy_def, hsol_field_eq] using hcomp
  have hx_deriv_b : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => y s 1) (field (y t) 1) (Set.Ici t) t := by
    intro t ht
    exact (hasDerivAt_pi.mp (hy_deriv t ht) 1).hasDerivWithinAt
  have hx_deriv_c : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => y s 2) (field (y t) 2) (Set.Ici t) t := by
    intro t ht
    exact (hasDerivAt_pi.mp (hy_deriv t ht) 2).hasDerivWithinAt
  have hV0_pos : 0 < lyapunov (y 0) := by
    change 0 < lyapunov (sol.trajectory (0 + t₀))
    rw [zero_add]; exact hV_pos
  have hV0_sharp : lyapunov (y 0) < (13 - 4 * Real.sqrt 5) ^ 2 / 784 := by
    change lyapunov (sol.trajectory (0 + t₀)) < (13 - 4 * Real.sqrt 5) ^ 2 / 784
    rw [zero_add]; exact hV_sharp
  have hx_simplex : ∀ t ∈ Set.Ici (0 : ℝ), y t 0 + y t 1 + y t 2 = 1 := by
    intro t ht
    have ht_nn : 0 ≤ t := ht
    have hPi : ∑ i, sol.trajectory (t + t₀) i = 1 :=
      conservative_trajectory_simplex sol field_conservative
        (by simpa [cf24PIVP] using h_simplex) (by linarith)
    simpa [Fin.sum_univ_three, hy_def] using hPi
  have hV_cont : ContinuousOn (fun t => lyapunov (y t)) (Set.Ici 0) := by
    intro t ht
    have hy_cont : ContinuousAt (fun s => y s) t := (hy_deriv t ht).continuousAt
    have hly_cont : Continuous lyapunov := by
      unfold lyapunov
      exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
        |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
    exact (hly_cont.continuousAt.comp hy_cont).continuousWithinAt
  have h_shifted :
      Filter.Tendsto (fun t => y t 2 + y t 1 / 2) Filter.atTop (nhds readoutLimit) :=
    cf24_readout_tendsto_from_sharp_lyapunov_init (x := y)
      hV0_pos hV0_sharp hV_cont hx_deriv_b hx_deriv_c hx_simplex
  have h_shift_back : Filter.Tendsto (fun t : ℝ => t - t₀) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ (-t₀) Filter.tendsto_id
  have h_eq :
      (fun t => sol.trajectory t 2 + sol.trajectory t 1 / 2) =
        (fun t => y t 2 + y t 1 / 2) ∘ (fun t => t - t₀) := by
    funext t
    simp [hy_def, sub_add_cancel]
  rw [h_eq]
  exact h_shifted.comp h_shift_back

/-- **CF'24 readout, canonical initial condition** (paper §1, §4: `z_11 + z_01/2 → (3 − √5)/6`
from `(1, 0, 0)`). -/
theorem cf24_readout_canonical :
    Filter.Tendsto
      (fun t => canonicalSolution.trajectory t 2 + canonicalSolution.trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  obtain ⟨t₀, ht₀, hpos, hsharp⟩ := cf24_canonical_basin_entry
  exact cf24_readout_of_sharp_entry canonicalInit canonicalInit_nonneg canonicalInit_simplex
    t₀ ht₀ hpos hsharp

/-- **λ-trick (paper §2, §5, Proposition 11.4), canonical initial condition.** -/
theorem cf24_lambda_readout_canonical :
    Filter.Tendsto
      (fun t => cf24LambdaEmbed (canonicalSolution.trajectory t) 3
        + cf24LambdaEmbed (canonicalSolution.trajectory t) 2 / 2)
      Filter.atTop (nhds readoutLimit) :=
  cf24Lambda_readout_tendsto cf24_readout_canonical

/-- **r²-trick (paper §6, Proposition 11.5), canonical initial condition.**  The time change
`τ = cf24_tau …` turns the λ-trick orbit into a solution of the r²-trick field, and the
readout keeps its limit. -/
theorem cf24_r2_readout_canonical :
    ∃ τ : ℝ → ℝ,
      τ 0 = 0 ∧
      (∀ s, 0 ≤ s → 0 ≤ τ s) ∧
      Filter.Tendsto τ Filter.atTop Filter.atTop ∧
      (∀ s, 0 ≤ s → HasDerivWithinAt
        (fun s' => cf24LambdaEmbed (canonicalSolution.trajectory (τ s')))
        (r2Field (cf24LambdaEmbed (canonicalSolution.trajectory (τ s)))) (Set.Ici 0) s) ∧
      Filter.Tendsto
        (fun s => cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 3
          + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 2 / 2)
        Filter.atTop (nhds readoutLimit) := by
  refine ⟨cf24_tau canonicalInit canonicalInit_nonneg canonicalInit_simplex
      canonicalInit_zero_pos,
    cf24_tau_zero canonicalInit_nonneg canonicalInit_simplex canonicalInit_zero_pos,
    cf24_tau_nonneg canonicalInit_nonneg canonicalInit_simplex canonicalInit_zero_pos,
    cf24_tau_tendsto_atTop canonicalInit_nonneg canonicalInit_simplex canonicalInit_zero_pos,
    ?_, ?_⟩
  · intro s hs
    rcases lt_or_eq_of_le hs with hs_pos | hs_eq
    · exact (cf24_r2_reparam_hasDerivAt canonicalInit_nonneg canonicalInit_simplex
        canonicalInit_zero_pos hs_pos).hasDerivWithinAt
    · rw [← hs_eq]
      exact cf24_r2_reparam_hasDerivWithinAt_zero canonicalInit_nonneg canonicalInit_simplex
        canonicalInit_zero_pos
  · exact cf24_lambda_readout_canonical.comp
      (cf24_tau_tendsto_atTop canonicalInit_nonneg canonicalInit_simplex
        canonicalInit_zero_pos)

/-- The λ-trick image of the canonical initial condition: `(r, u, z_01, z_11) = (1/2, 1/2, 0, 0)`
(paper §5). -/
theorem cf24LambdaEmbed_canonicalInit :
    cf24LambdaEmbed canonicalInit 0 = 1 / 2 ∧ cf24LambdaEmbed canonicalInit 1 = 1 / 2 ∧
      cf24LambdaEmbed canonicalInit 2 = 0 ∧ cf24LambdaEmbed canonicalInit 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change canonicalInit 0 / 2 = 1 / 2
    simp [canonicalInit]
  · change canonicalInit 0 / 2 = 1 / 2
    simp [canonicalInit]
  · change canonicalInit 1 = 0
    simp [canonicalInit]
  · change canonicalInit 2 = 0
    simp [canonicalInit]

/-- **NAP-20 system (paper §7–§10, Theorem 11.2), canonical initial condition.**  With the
r²-trick time change `τ`, the cubed lift `w(s) = (cubedLift i (λ-embed (x (τ s))))ᵢ` of the
canonical trajectory starts at the cubed lift of `(1/2, 1/2, 0, 0)`, solves the 20-variable NAP
system `ẇ = napField w` for `s > 0`, and its linear readout `Σ readoutCoeff i · w i` tends to
`(3 − √5)/6`. -/
theorem cf24_nap20_readout_canonical :
    ∃ τ : ℝ → ℝ,
      τ 0 = 0 ∧
      Filter.Tendsto τ Filter.atTop Filter.atTop ∧
      (fun i => cubedLift i (cf24LambdaEmbed (canonicalSolution.trajectory (τ 0)))) =
        (fun i => cubedLift i (cf24LambdaEmbed canonicalInit)) ∧
      (∀ s, 0 < s → HasDerivAt
        (fun s' => fun i => cubedLift i (cf24LambdaEmbed (canonicalSolution.trajectory (τ s'))))
        (napField (fun i => cubedLift i (cf24LambdaEmbed (canonicalSolution.trajectory (τ s)))))
        s) ∧
      Filter.Tendsto
        (fun s => ∑ i, readoutCoeff i * cubedLift i
          (cf24LambdaEmbed (canonicalSolution.trajectory (τ s))))
        Filter.atTop (nhds readoutLimit) := by
  set τ := cf24_tau canonicalInit canonicalInit_nonneg canonicalInit_simplex
    canonicalInit_zero_pos with hτ_def
  have hτ0 : τ 0 = 0 :=
    cf24_tau_zero canonicalInit_nonneg canonicalInit_simplex canonicalInit_zero_pos
  have hτ_nn : ∀ s, 0 ≤ s → 0 ≤ τ s :=
    cf24_tau_nonneg canonicalInit_nonneg canonicalInit_simplex canonicalInit_zero_pos
  have hτ_atTop : Filter.Tendsto τ Filter.atTop Filter.atTop :=
    cf24_tau_tendsto_atTop canonicalInit_nonneg canonicalInit_simplex canonicalInit_zero_pos
  have h_readout : Filter.Tendsto
      (fun s => cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 3
        + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 2 / 2)
      Filter.atTop (nhds readoutLimit) :=
    cf24_lambda_readout_canonical.comp hτ_atTop
  refine ⟨τ, hτ0, hτ_atTop, ?_, ?_, ?_⟩
  · rw [hτ0, canonicalSolution.init_cond]
    rfl
  · intro s hs
    have hz := cf24_r2_reparam_hasDerivAt canonicalInit_nonneg canonicalInit_simplex
      canonicalInit_zero_pos hs
    exact hasDerivAt_pi.mpr (fun i => cubedLift_hasDerivAt hz i)
  have h_eq : ∀ s, 0 ≤ s →
      (∑ i, readoutCoeff i * cubedLift i
          (cf24LambdaEmbed (canonicalSolution.trajectory (τ s))))
        = cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 3
          + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 2 / 2 := by
    intro s hs
    have hτs : 0 ≤ τ s := hτ_nn s hs
    have hPi : ∑ i, canonicalSolution.trajectory (τ s) i = 1 :=
      conservative_trajectory_simplex canonicalSolution field_conservative
        (by simpa [cf24PIVP] using canonicalInit_simplex) hτs
    have h3 : canonicalSolution.trajectory (τ s) 0
             + canonicalSolution.trajectory (τ s) 1
             + canonicalSolution.trajectory (τ s) 2 = 1 := by
      simpa [Fin.sum_univ_three] using hPi
    have hsum :
        cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 0
          + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 1
          + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 2
          + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 3 = 1 := by
      have hA := cf24LambdaEmbed_sum (canonicalSolution.trajectory (τ s))
      simp [Fin.sum_univ_four] at hA
      linarith [h3]
    exact readout_eq_z11_plus_half_z01 _ hsum
  have hEv :
      (fun s => ∑ i, readoutCoeff i * cubedLift i
          (cf24LambdaEmbed (canonicalSolution.trajectory (τ s))))
        =ᶠ[Filter.atTop]
      (fun s => cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 3
        + cf24LambdaEmbed (canonicalSolution.trajectory (τ s)) 2 / 2) := by
    refine Filter.eventually_atTop.mpr ⟨0, ?_⟩
    intro s hs; exact h_eq s hs
  exact h_readout.congr' hEv.symm

end CF24
end Ripple

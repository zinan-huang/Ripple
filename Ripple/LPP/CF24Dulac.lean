import Ripple.LPP.CF24Interior

/-!
# CF'24: elementary ingredients of the global (Poincaré–Bendixson) argument

Paper proof: `docs/audit/CF24-INTERIOR.md`, §4–§6.  The trichotomy "every interior trajectory tends to
`fixedPoint`, to `(0,0,1)` or to `saddlePoint`" is proved on paper by Poincaré–Bendixson.
Its two elementary, non-topological ingredients are formalized here:

* **Dulac function** (§5).  On the planar reduction `(a, b) = (z_00, z_01)` of `field`
  (`reducedFieldA`, `reducedFieldB`), the weight `B(a) = a^{-4/3}` (`dulacWeight`) satisfies
  `∂_a(B·F_a) + ∂_b(B·F_b) = B·(−1/3 − b − 23a) < 0` on `{a > 0, b ≥ 0}` (`cf24_dulac`).
  By the Bendixson–Dulac criterion (Green's theorem; not in Mathlib) this excludes periodic
  orbits and homoclinic loops in the open simplex.
* **The source `(0,1,0)` repels** (§4).  The sublevel sets `{z_00 + z_11 ≤ η}`, `η ≤ 1/10`, are
  never re-entered: `z_00 + z_11 ≥ η` is preserved (`cf24_source_repelling`).  Hence the
  source is not an ω-limit point of any other orbit.

What remains for the trichotomy is planar topology: ω-limit sets, the Poincaré–Bendixson
theorem and Green's theorem on Jordan domains.
-/

namespace Ripple
namespace CF24

open scoped Topology

/-! ## Planar reduction -/

/-- `a`-component of the reduced field: `a' = a(9b − 2)`. -/
noncomputable def reducedFieldA (a b : ℝ) : ℝ := a * (9 * b - 2)

/-- `b`-component of the reduced field: `b' = 16a − b − 14a² − 23ab + b²`. -/
noncomputable def reducedFieldB (a b : ℝ) : ℝ :=
  16 * a - b - 14 * a ^ 2 - 23 * a * b + b ^ 2

/-- On the simplex, `field x 0 = reducedFieldA (x 0) (x 1)`. -/
theorem field_zero_reduced (x : Fin 3 → ℝ) (hs : x 0 + x 1 + x 2 = 1) :
    field x 0 = reducedFieldA (x 0) (x 1) := by
  have hc : x 2 = 1 - x 0 - x 1 := by linarith
  simp only [field, reducedFieldA]
  rw [hc]; ring

/-- On the simplex, `field x 1 = reducedFieldB (x 0) (x 1)`. -/
theorem field_one_reduced (x : Fin 3 → ℝ) (hs : x 0 + x 1 + x 2 = 1) :
    field x 1 = reducedFieldB (x 0) (x 1) := by
  have hc : x 2 = 1 - x 0 - x 1 := by linarith
  simp only [field, reducedFieldB]
  rw [hc]; ring

/-! ## Dulac function `a^{-4/3}` -/

/-- The Dulac weight `B(a) = a^{-4/3}`. -/
noncomputable def dulacWeight (a : ℝ) : ℝ := a ^ (-(4 : ℝ) / 3)

theorem dulacWeight_pos {a : ℝ} (ha : 0 < a) : 0 < dulacWeight a :=
  Real.rpow_pos_of_pos ha _

/-- `∂_a (B(a)·F_a(a, b)) = B(a)·(−3b + 2/3)` for `a > 0`. -/
theorem hasDerivAt_dulac_fieldA (b : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun a' => dulacWeight a' * reducedFieldA a' b)
      (dulacWeight a * (-3 * b + 2 / 3)) a := by
  have hw : HasDerivAt (fun a' : ℝ => a' ^ (-(4 : ℝ) / 3))
      (-(4 : ℝ) / 3 * a ^ (-(4 : ℝ) / 3 - 1)) a :=
    Real.hasDerivAt_rpow_const (Or.inl ha.ne')
  have hf : HasDerivAt (fun a' : ℝ => a' * (9 * b - 2)) (1 * (9 * b - 2)) a :=
    (hasDerivAt_id a).mul_const _
  refine (hw.mul hf).congr_deriv ?_
  have hane : a ≠ 0 := ha.ne'
  unfold dulacWeight
  rw [Real.rpow_sub_one hane]
  have hcancel : a ^ (-(4 : ℝ) / 3) / a * a = a ^ (-(4 : ℝ) / 3) := div_mul_cancel₀ _ hane
  linear_combination (-(4 : ℝ) / 3 * (9 * b - 2)) * hcancel

/-- `∂_b (B(a)·F_b(a, b)) = B(a)·(−1 − 23a + 2b)`. -/
theorem hasDerivAt_dulac_fieldB (a b : ℝ) :
    HasDerivAt (fun b' => dulacWeight a * reducedFieldB a b')
      (dulacWeight a * (-1 - 23 * a + 2 * b)) b := by
  have h1 : HasDerivAt (fun b' : ℝ => b') 1 b := hasDerivAt_id b
  have h2 : HasDerivAt (fun b' : ℝ => b' ^ 2) (2 * b) b := by
    simpa using hasDerivAt_pow 2 b
  have h3 : HasDerivAt (fun b' : ℝ => 16 * a - b' - 14 * a ^ 2 - 23 * a * b' + b' ^ 2)
      (0 - 1 - 0 - 23 * a * 1 + 2 * b) b :=
    ((((hasDerivAt_const b (16 * a)).sub h1).sub (hasDerivAt_const b (14 * a ^ 2))).sub
      (h1.const_mul (23 * a))).add h2
  refine (h3.const_mul (dulacWeight a)).congr_deriv ?_
  ring

/-- The Dulac divergence identity `∂_a(B F_a) + ∂_b(B F_b) = B·(−1/3 − b − 23a)`. -/
theorem dulac_divergence_eq (a b : ℝ) :
    dulacWeight a * (-3 * b + 2 / 3) + dulacWeight a * (-1 - 23 * a + 2 * b)
      = dulacWeight a * (-(1 / 3) - b - 23 * a) := by
  ring

/-- The Dulac divergence is strictly negative on `{a > 0, b ≥ 0}`. -/
theorem dulac_divergence_neg {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    dulacWeight a * (-(1 / 3) - b - 23 * a) < 0 :=
  mul_neg_of_pos_of_neg (dulacWeight_pos ha) (by linarith)

/-- **Dulac criterion data for the CF'24 planar reduction.**  At every point with `a > 0`,
`b ≥ 0` the weighted field `B·F` has partial derivatives whose sum (its divergence) is
strictly negative. -/
theorem cf24_dulac {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ Da Db : ℝ,
      HasDerivAt (fun a' => dulacWeight a' * reducedFieldA a' b) Da a ∧
      HasDerivAt (fun b' => dulacWeight a * reducedFieldB a b') Db b ∧
      Da + Db < 0 :=
  ⟨_, _, hasDerivAt_dulac_fieldA b ha, hasDerivAt_dulac_fieldB a b, by
    rw [dulac_divergence_eq]; exact dulac_divergence_neg ha hb⟩

/-! ## The source `(0, 1, 0)` repels -/

/-- Distance-like function to the source: `s(x) = z_00 + z_11 = 1 − z_01`. -/
noncomputable def sourceWeight (x : Fin 3 → ℝ) : ℝ := x 0 + x 2

/-- Lie derivative of `sourceWeight` along `field`. -/
noncomputable def sourceWeightDeriv (x : Fin 3 → ℝ) : ℝ := field x 0 + field x 2

/-- On the simplex, with `a = z_00`, `s = z_00 + z_11`:
`ṡ = s + 7a + 14a² − 23as − s²`. -/
theorem sourceWeightDeriv_eq (x : Fin 3 → ℝ) (hs : x 0 + x 1 + x 2 = 1) :
    sourceWeightDeriv x
      = sourceWeight x + 7 * x 0 + 14 * x 0 ^ 2 - 23 * x 0 * sourceWeight x
        - sourceWeight x ^ 2 := by
  have hb : x 1 = 1 - x 0 - x 2 := by linarith
  simp only [sourceWeightDeriv, sourceWeight, field]
  rw [hb]; ring

/-- Near the source, `ṡ ≥ (9/10)s`: if `z_00, z_11 ≥ 0` and `s ≤ 1/10` then `ṡ ≥ (9/10)·s`. -/
theorem sourceWeightDeriv_ge (x : Fin 3 → ℝ) (h0 : 0 ≤ x 0) (h2 : 0 ≤ x 2)
    (hs : x 0 + x 1 + x 2 = 1) (hsmall : sourceWeight x ≤ 1 / 10) :
    (9 / 10) * sourceWeight x ≤ sourceWeightDeriv x := by
  rw [sourceWeightDeriv_eq x hs]
  unfold sourceWeight at *
  have ha : x 0 ≤ 1 / 10 := by linarith
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr ha), mul_nonneg h2 (sub_nonneg.mpr hsmall),
    mul_nonneg h0 (sub_nonneg.mpr hsmall), sq_nonneg (x 0)]

/-- `s` along the trajectory is differentiable with derivative `sourceWeightDeriv`. -/
theorem cf24_sourceWeight_hasDerivAt (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
      (sourceWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory t)) t := by
  have h := hasDerivAt_pi.mp (cf24_traj_hasDerivAt x0 h_nn h_simplex ht)
  exact (h 0).add (h 2)

/-- **The source repels.**  For `0 < η ≤ 1/10`: if `z_00(0) + z_11(0) ≥ η` then
`z_00(t) + z_11(t) ≥ η` for all `t ≥ 0`.  Consequently the sublevel set `{s < η}`, a
neighbourhood of the source `(0, 1, 0)`, is never entered from outside, and the source is not
an ω-limit point of any trajectory other than itself. -/
theorem cf24_source_repelling (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i)
    (h_simplex : ∑ i, x0 i = 1) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 10)
    (hs0 : η ≤ sourceWeight x0) :
    ∀ t, 0 ≤ t →
      η ≤ sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory t) := by
  intro T hT
  have hcont : ContinuousOn
      (fun s => -sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
      (Set.Icc 0 T) :=
    fun s hs => (cf24_sourceWeight_hasDerivAt x0 h_nn h_simplex hs.1).neg.continuousAt.continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun s => -sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
        (-sourceWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
        (Set.Ici s) s :=
    fun s hs => (cf24_sourceWeight_hasDerivAt x0 h_nn h_simplex hs.1).neg.hasDerivWithinAt
  have hinit : -sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory 0) ≤ -η := by
    rw [cf24_traj_zero]; linarith
  suffices hT' : -sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory T) ≤ -η by
    linarith
  refine image_le_of_deriv_right_lt_deriv_boundary
    (f := fun s => -sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
    (f' := fun s => -sourceWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s))
    (B := fun _ => -η) (B' := fun _ => 0)
    hcont hderiv hinit (fun _ => hasDerivAt_const _ _) ?_ ⟨hT, le_refl T⟩
  intro s hs heq
  have heq' : -sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s) = -η := heq
  show -sourceWeightDeriv ((cf24_global_solution x0 h_nn h_simplex).trajectory s) < 0
  have hsw : sourceWeight ((cf24_global_solution x0 h_nn h_simplex).trajectory s) = η := by
    linarith
  have hge := sourceWeightDeriv_ge _ (cf24_traj_nonneg x0 h_nn h_simplex hs.1 0)
    (cf24_traj_nonneg x0 h_nn h_simplex hs.1 2) (cf24_traj_sum_eq_one x0 h_nn h_simplex hs.1)
    (by rw [hsw]; exact hη')
  rw [hsw] at hge
  linarith

end CF24
end Ripple

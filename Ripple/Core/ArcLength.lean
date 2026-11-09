/-
  Ripple.Core.ArcLength — trajectory length of a ℚ-PIVP ([BAC] §2.3, §4.1, §4.2)

  The Bournez–Graça–Pouly resource `L(t) = ∫₀ᵗ ‖p(y(u))‖ du` (sup norm), and the two facts of
  [BAC] §4 that use it:
  - Lemma 4.1 (one-sided bound): on a bounded trajectory, `L(t) ≤ v_max t`
    (`PolyPIVP.arcLength_le_of_bounded`). The converse `L(t) ≥ v_min t` fails for convergent
    systems ([BAC] p. 9) and is not stated.
  - Lemma 4.3 (state bound from arc length): `|yᵢ(t) − yᵢ(0)| ≤ L(t)`
    (`PolyPIVP.abs_sub_init_le_arcLength`).

  Numbering of [BAC]: the DNA 32 version, as in `docs/refactor/BC.md` (journal-draft labels in
  `docs/papers/BAC-journal.md` and in the header of `Ripple.Core.SurrogateCompilation`).
-/

import Ripple.Core.BoundedTime
import Mathlib.Topology.Algebra.MvPolynomial

namespace Ripple

open MeasureTheory

variable {d : ℕ}

namespace PolyPIVP

/-- The evaluated polynomial vector field is continuous. -/
theorem continuous_evalField (P : PolyPIVP d) : Continuous P.evalField := by
  refine continuous_pi fun i => ?_
  show Continuous fun x => (P.field i).eval₂ (Rat.castHom ℝ) x
  convert MvPolynomial.continuous_eval (p := MvPolynomial.map (Rat.castHom ℝ) (P.field i))
    using 1
  ext x
  exact MvPolynomial.eval₂_eq_eval_map (Rat.castHom ℝ) x (P.field i)

/-- Trajectory (arc) length `L(t) = ∫₀ᵗ ‖p(y(u))‖ du` ([BAC] §2.3, Bournez–Graça–Pouly),
with the sup norm of `Fin d → ℝ`. -/
noncomputable def arcLength (P : PolyPIVP d) (y : ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ‖P.evalField (y u)‖

/-- A solution is continuous at every `t ≥ 0`. -/
theorem solution_continuousAt (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP) {t : ℝ}
    (ht : 0 ≤ t) : ContinuousAt sol.trajectory t :=
  (sol.is_solution t ht).continuousAt

/-- The speed `‖p(y(u))‖` is continuous on `[0, t]`. -/
theorem speed_continuousOn (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP) (a b : ℝ)
    (ha : 0 ≤ a) : ContinuousOn (fun u => ‖P.evalField (sol.trajectory u)‖) (Set.Icc a b) :=
  fun u hu => ((P.continuous_evalField.continuousAt.comp
    (P.solution_continuousAt sol (ha.trans hu.1))).norm).continuousWithinAt

theorem arcLength_nonneg (P : PolyPIVP d) (y : ℝ → Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ P.arcLength y t :=
  intervalIntegral.integral_nonneg ht fun _ _ => norm_nonneg _

/-- The arc length is nondecreasing on `[0, ∞)`. -/
theorem arcLength_mono (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP) {t₁ t₂ : ℝ}
    (h₀ : 0 ≤ t₁) (h : t₁ ≤ t₂) :
    P.arcLength sol.trajectory t₁ ≤ P.arcLength sol.trajectory t₂ := by
  have hi1 : IntervalIntegrable (fun u => ‖P.evalField (sol.trajectory u)‖) volume 0 t₁ :=
    (P.speed_continuousOn sol 0 t₁ le_rfl).intervalIntegrable_of_Icc h₀
  have hi2 : IntervalIntegrable (fun u => ‖P.evalField (sol.trajectory u)‖) volume t₁ t₂ :=
    (P.speed_continuousOn sol t₁ t₂ h₀).intervalIntegrable_of_Icc h
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hnn : 0 ≤ ∫ u in t₁..t₂, ‖P.evalField (sol.trajectory u)‖ :=
    intervalIntegral.integral_nonneg h fun _ _ => norm_nonneg _
  unfold arcLength
  linarith

/-- [BAC] Prop 2.2 (journal draft `prop:bc-implies-bd`, bounded concentrations imply bounded
derivatives): for a ℚ-polynomial field `F` and a bound `M` there is a constant `C`, depending
only on `F` and `M`, such that every solution of `y' = F(y)` with `‖y(t)‖ ≤ M` on `[0, ∞)` has
`‖y'(t)‖ ≤ C` there (sup norm). -/
theorem exists_norm_deriv_le_of_norm_le (F : Fin d → MvPolynomial (Fin d) ℚ) (M : ℝ) :
    ∃ C : ℝ, ∀ y : ℝ → Fin d → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt y (fun i => (F i).eval₂ (Rat.castHom ℝ) (y t)) t) →
      (∀ t, 0 ≤ t → ‖y t‖ ≤ M) → ∀ t, 0 ≤ t → ‖deriv y t‖ ≤ C := by
  have hcont : Continuous fun x : Fin d → ℝ => fun i => (F i).eval₂ (Rat.castHom ℝ) x := by
    refine continuous_pi fun i => ?_
    convert MvPolynomial.continuous_eval (p := MvPolynomial.map (Rat.castHom ℝ) (F i)) using 1
    ext x
    exact MvPolynomial.eval₂_eq_eval_map (Rat.castHom ℝ) x (F i)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin d → ℝ) M).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C, fun y hy hb t ht => ?_⟩
  rw [(hy t ht).deriv]
  exact hC _ (mem_closedBall_zero_iff.mpr (hb t ht))

/-- [BAC] Prop 2.2 for a solution of a bounded `PolyPIVP` (`PIVP.IsBounded`). -/
theorem exists_norm_deriv_le_of_bounded (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hbd : P.toPIVP.IsBounded sol.trajectory) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖deriv sol.trajectory t‖ ≤ C := by
  obtain ⟨M, _, hb⟩ := hbd
  obtain ⟨C, hC⟩ := exists_norm_deriv_le_of_norm_le P.field M
  exact ⟨C, hC sol.trajectory sol.is_solution hb⟩

/-- The arc length is continuous on `[0, b]`. -/
theorem arcLength_continuousOn (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP) {b : ℝ}
    (hb : 0 ≤ b) : ContinuousOn (P.arcLength sol.trajectory) (Set.Icc 0 b) := by
  have h : IntegrableOn (fun u => ‖P.evalField (sol.trajectory u)‖) (Set.Icc 0 b) :=
    (P.speed_continuousOn sol 0 b le_rfl).integrableOn_Icc
  rw [← Set.uIcc_of_le hb] at h ⊢
  exact intervalIntegral.continuousOn_primitive_interval h

@[simp] theorem arcLength_zero (P : PolyPIVP d) (y : ℝ → Fin d → ℝ) :
    P.arcLength y 0 = 0 :=
  intervalIntegral.integral_same

/-- [BAC] Lemma 4.3: every coordinate moves at most the arc length,
`|yᵢ(t) − yᵢ(0)| ≤ L(t)`. -/
theorem abs_sub_init_le_arcLength (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    |sol.trajectory t i - (P.init i : ℝ)| ≤ P.arcLength sol.trajectory t := by
  have hderiv : ∀ u ∈ Set.uIcc 0 t,
      HasDerivAt (fun u => sol.trajectory u i) (P.evalField (sol.trajectory u) i) u := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact hasDerivAt_pi.mp (sol.is_solution u hu.1) i
  have hci : ContinuousOn (fun u => P.evalField (sol.trajectory u) i) (Set.Icc 0 t) :=
    fun u hu => ((continuous_apply i).continuousAt.comp
      (P.continuous_evalField.continuousAt.comp
        (P.solution_continuousAt sol hu.1))).continuousWithinAt
  have hint : IntervalIntegrable (fun u => P.evalField (sol.trajectory u) i) volume 0 t :=
    hci.intervalIntegrable_of_Icc ht
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h0 : sol.trajectory 0 i = (P.init i : ℝ) := by
    have := congrFun sol.init_cond i
    simpa using this
  rw [← h0, ← hftc]
  calc |∫ u in (0 : ℝ)..t, P.evalField (sol.trajectory u) i|
      ≤ ∫ u in (0 : ℝ)..t, |P.evalField (sol.trajectory u) i| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ u in (0 : ℝ)..t, ‖P.evalField (sol.trajectory u)‖ := by
        refine intervalIntegral.integral_mono_on ht ?_ ?_ ?_
        · exact (hci.abs).intervalIntegrable_of_Icc ht
        · exact (P.speed_continuousOn sol 0 t le_rfl).intervalIntegrable_of_Icc ht
        · intro u _
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (P.evalField (sol.trajectory u)) i

/-- [BAC] Lemma 4.1 (one-sided bound): on a trajectory bounded on `[0, ∞)`, the arc length
grows at most linearly, `L(t) ≤ v_max t`. -/
theorem arcLength_le_of_bounded (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hbd : P.toPIVP.IsBounded sol.trajectory) :
    ∃ v : ℝ, 0 ≤ v ∧ ∀ t, 0 ≤ t → P.arcLength sol.trajectory t ≤ v * t := by
  obtain ⟨M, _, hb⟩ := hbd
  obtain ⟨v, hv⟩ := (isCompact_closedBall (0 : Fin d → ℝ) M).exists_bound_of_continuousOn
    P.continuous_evalField.continuousOn
  refine ⟨max v 0, le_max_right _ _, fun t ht => ?_⟩
  have hle : P.arcLength sol.trajectory t ≤ ∫ _u in (0 : ℝ)..t, max v 0 := by
    refine intervalIntegral.integral_mono_on ht
      ((P.speed_continuousOn sol 0 t le_rfl).intervalIntegrable_of_Icc ht)
      intervalIntegrable_const fun u hu => ?_
    have hmem : sol.trajectory u ∈ Metric.closedBall (0 : Fin d → ℝ) M := by
      rw [mem_closedBall_zero_iff]; exact hb u hu.1
    exact (hv _ hmem).trans (le_max_left _ _)
  simpa [mul_comm] using hle

end PolyPIVP

end Ripple

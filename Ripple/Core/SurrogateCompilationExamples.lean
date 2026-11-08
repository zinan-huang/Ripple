/-
  Ripple.Core.SurrogateCompilationExamples — non-vacuity of bounded surrogate compilation

  The roots `bounded_compilation` ([BAC] Thm 3.3) and `bounded_compilation_polyTime`
  ([BAC] Thm 4.6) are applied to genuinely unbounded inputs. Their conclusions
  (`IsCRNComputable (π/2)`, `IsPolyTimeComputable 1 3`) follow from earlier results as well, so
  the evidence here is in the types: each input satisfies the hypotheses on a solution that is
  not bounded, and the compiled certificate is pinned to `jointSurrogateCompile`
  (BC.md §3.6, review P2).

  - `arctanSys`: `t' = 1, u' = -2 t u², x' = u`, `(t, u, x)(0) = (0, 1, 0)`, solution
    `(t, 1/(1+t²), arctan t)`; the clock `t` is unbounded and `x → π/2` (degree 3, `N = 4`).
  - `gaussianSys`: `t' = 1, x' = 2 t (1 - x)`, `(t, x)(0) = (0, 0)`, solution `(t, 1 - e^{-t²})`;
    the clock `t` is unbounded, `x → 1` with modulus `√r`, and the speed is at most 1, so
    `L(t) ≤ t` (degree 2, `N = 2`, `k = 1`).
  - `tanSys`: `u' = 1 + u², t' = 1`, `(u, t)(0) = (0, 0)`, solution `(tan t, t)` on `[0, π/2)`;
    `u` blows up at `π/2` and the output `t → π/2`. It instantiates
    `bounded_compilation_of_blowup_certified` ([BAC] Prop 3.2, `T* < ∞`) and
    `isCRNComputable_blowupTime_certified` ([BAC] Thm 3.4; the compiled system keeps no original
    coordinate, review P1).

  Numbering of [BAC]: the DNA 32 version, as in `docs/refactor/BC.md` (journal-draft labels in
  `docs/papers/BAC-journal.md` and in the header of `Ripple.Core.SurrogateCompilation`).
-/

import Ripple.Core.SurrogateCompilationBlowup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace Ripple

open MvPolynomial Filter

/-! ## The arctan clock -/

/-- `t' = 1, u' = -2 t u², x' = u`, `(t, u, x)(0) = (0, 1, 0)`, output `x`. -/
noncomputable def arctanSys : PolyPIVP 3 where
  field := ![1, C (-2) * X 0 * X 1 ^ 2, X 1]
  init := ![0, 1, 0]
  output := 2

/-- The solution `(t, 1/(1+t²), arctan t)`. -/
noncomputable def arctanTraj (t : ℝ) : Fin 3 → ℝ := ![t, 1 / (1 + t ^ 2), Real.arctan t]

theorem arctanSys_totalDegree : ∀ i, (arctanSys.field i).totalDegree ≤ 4 := by
  intro i
  fin_cases i
  · simp [arctanSys]
  · show (C (-2) * X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 4
    calc (C (-2) * X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) ℚ).totalDegree
        ≤ (C (-2) * X 0 : MvPolynomial (Fin 3) ℚ).totalDegree +
            (X 1 ^ 2 : MvPolynomial (Fin 3) ℚ).totalDegree := totalDegree_mul _ _
      _ ≤ ((C (-2) : MvPolynomial (Fin 3) ℚ).totalDegree +
            (X 0 : MvPolynomial (Fin 3) ℚ).totalDegree) +
            2 * (X 1 : MvPolynomial (Fin 3) ℚ).totalDegree := by
          gcongr
          · exact totalDegree_mul _ _
          · exact totalDegree_pow _ _
      _ ≤ 4 := by simp [totalDegree_C, totalDegree_X]
  · show (X 1 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 4
    simp [totalDegree_X]

theorem arctanTraj_hasDerivAt (t : ℝ) :
    HasDerivAt arctanTraj (arctanSys.evalField (arctanTraj t)) t := by
  have h1pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · have : (fun s => arctanTraj s 0) = fun s => s := by funext s; simp [arctanTraj]
    show HasDerivAt (fun s => arctanTraj s 0) _ t
    rw [this]
    convert hasDerivAt_id t using 1
    simp [arctanSys, PolyPIVP.evalField]
  · have : (fun s => arctanTraj s 1) = fun s => 1 / (1 + s ^ 2) := by
      funext s; simp [arctanTraj]
    show HasDerivAt (fun s => arctanTraj s 1) _ t
    rw [this]
    have hd := (((hasDerivAt_id t).pow 2).const_add 1).inv (ne_of_gt h1pos)
    convert (hd.const_mul 1) using 1
    simp [arctanSys, PolyPIVP.evalField, arctanTraj]
    field_simp
  · have : (fun s => arctanTraj s 2) = Real.arctan := by funext s; simp [arctanTraj]
    show HasDerivAt (fun s => arctanTraj s 2) _ t
    rw [this]
    convert Real.hasDerivAt_arctan t using 1
    simp [arctanSys, PolyPIVP.evalField, arctanTraj]

/-- The solution of `arctanSys` on `[0, ∞)`. -/
noncomputable def arctanSol : PIVP.Solution arctanSys.toPIVP where
  trajectory := arctanTraj
  init_cond := by
    funext i
    fin_cases i <;> simp [arctanTraj, arctanSys, PolyPIVP.toPIVP]
  is_solution := fun t _ => arctanTraj_hasDerivAt t

/-- The hypotheses of `bounded_compilation` hold for `arctanSys` on a solution that is not
bounded (its clock `t` diverges): the output tends to `π/2`, and the degree bound `4` holds. -/
theorem arctanSys_instance :
    (∀ i, (arctanSys.field i).totalDegree ≤ 4) ∧
    ∃ sol : PIVP.Solution arctanSys.toPIVP,
      arctanSys.toPIVP.Computes sol (Real.pi / 2) ∧
      ¬ arctanSys.toPIVP.IsBounded sol.trajectory := by
  refine ⟨arctanSys_totalDegree, arctanSol, ?_, ?_⟩
  · show Tendsto (fun t => arctanTraj t 2) atTop (nhds (Real.pi / 2))
    have : (fun t => arctanTraj t 2) = Real.arctan := by funext s; simp [arctanTraj]
    rw [this]
    exact Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  · rintro ⟨M, hM, hb⟩
    have h := hb (M + 1) (by linarith)
    have h0 : |arctanTraj (M + 1) 0| ≤ ‖arctanTraj (M + 1)‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (arctanTraj (M + 1)) 0
    have : arctanTraj (M + 1) 0 = M + 1 := by simp [arctanTraj]
    rw [this, abs_of_pos (by linarith)] at h0
    have : arctanSol.trajectory = arctanTraj := rfl
    rw [this] at h
    linarith

/-- The compiled bounded certificate for `π/2`, pinned to the joint construction
(`bounded_compilation_certified`, [BAC] Thm 3.3). -/
theorem arctanSys_compiled :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 3 4) (Real.pi / 2),
      btc.pivp = arctanSys.jointSurrogateCompile 4 := by
  obtain ⟨hdeg, sol, hlim, -⟩ := arctanSys_instance
  exact bounded_compilation_certified arctanSys ⟨2, rfl⟩ hdeg sol hlim

/-! ## The gaussian clock: a polynomial-length unbounded input -/

/-- `t' = 1, x' = 2 t (1 - x)`, `(t, x)(0) = (0, 0)`, output `x`. -/
noncomputable def gaussianSys : PolyPIVP 2 where
  field := ![1, C 2 * X 0 * (1 - X 1)]
  init := ![0, 0]
  output := 1

/-- The solution `(t, 1 - e^{-t²})`. -/
noncomputable def gaussianTraj (t : ℝ) : Fin 2 → ℝ := ![t, 1 - Real.exp (-t ^ 2)]

theorem gaussianSys_totalDegree : ∀ i, (gaussianSys.field i).totalDegree ≤ 2 := by
  intro i
  fin_cases i
  · simp [gaussianSys]
  · show (C 2 * X 0 * (1 - X 1) : MvPolynomial (Fin 2) ℚ).totalDegree ≤ 2
    calc (C 2 * X 0 * (1 - X 1) : MvPolynomial (Fin 2) ℚ).totalDegree
        ≤ (C 2 * X 0 : MvPolynomial (Fin 2) ℚ).totalDegree +
            (1 - X 1 : MvPolynomial (Fin 2) ℚ).totalDegree := totalDegree_mul _ _
      _ ≤ ((C 2 : MvPolynomial (Fin 2) ℚ).totalDegree +
            (X 0 : MvPolynomial (Fin 2) ℚ).totalDegree) +
            max (1 : MvPolynomial (Fin 2) ℚ).totalDegree
              (X 1 : MvPolynomial (Fin 2) ℚ).totalDegree := by
          gcongr
          · exact totalDegree_mul _ _
          · exact totalDegree_sub _ _
      _ ≤ 2 := by simp [totalDegree_C, totalDegree_X]

theorem gaussianSys_evalField (y : Fin 2 → ℝ) :
    gaussianSys.evalField y = ![1, 2 * y 0 * (1 - y 1)] := by
  funext i
  fin_cases i <;> simp [gaussianSys, PolyPIVP.evalField]

theorem gaussianTraj_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianTraj (gaussianSys.evalField (gaussianTraj t)) t := by
  rw [gaussianSys_evalField]
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · have : (fun s => gaussianTraj s 0) = fun s => s := by funext s; simp [gaussianTraj]
    show HasDerivAt (fun s => gaussianTraj s 0) _ t
    rw [this]
    simpa using hasDerivAt_id t
  · have : (fun s => gaussianTraj s 1) = fun s => 1 - Real.exp (-s ^ 2) := by
      funext s; simp [gaussianTraj]
    show HasDerivAt (fun s => gaussianTraj s 1) _ t
    rw [this]
    have hd := (((hasDerivAt_id t).pow 2).neg.exp).const_sub 1
    convert hd using 1
    simp [gaussianTraj]
    ring

/-- The solution of `gaussianSys` on `[0, ∞)`. -/
noncomputable def gaussianSol : PIVP.Solution gaussianSys.toPIVP where
  trajectory := gaussianTraj
  init_cond := by
    funext i
    fin_cases i <;> simp [gaussianTraj, gaussianSys, PolyPIVP.toPIVP]
  is_solution := fun t _ => gaussianTraj_hasDerivAt t

/-- The speed of the gaussian system is at most `1`: `2 |t| e^{-t²} ≤ 1`. -/
theorem gaussianSys_speed_le_one (t : ℝ) :
    ‖gaussianSys.evalField (gaussianTraj t)‖ ≤ 1 := by
  rw [gaussianSys_evalField]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  fin_cases i
  · simp
  · simp only [gaussianTraj]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs]
    have he : 0 < Real.exp (t ^ 2) := Real.exp_pos _
    have hexp : 1 + t ^ 2 ≤ Real.exp (t ^ 2) := by
      have := Real.add_one_le_exp (t ^ 2); linarith
    have hval : 2 * t * (1 - (1 - Real.exp (-t ^ 2))) = 2 * t / Real.exp (t ^ 2) := by
      rw [Real.exp_neg]; field_simp; ring
    rw [hval]
    change |2 * t / Real.exp (t ^ 2)| ≤ 1
    rw [abs_div, abs_of_pos he, div_le_one he, abs_mul]
    have h2t : 2 * |t| ≤ 1 + t ^ 2 := by
      have := sq_nonneg (|t| - 1)
      have habs : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith
    simpa using h2t.trans hexp

/-- The hypotheses of `bounded_compilation_polyTime` hold for `gaussianSys` (`k = 1`, `C = 1`,
`N = 2`) on a solution that is not bounded: modulus `√r`, arc length `L(t) ≤ t`. -/
theorem gaussianSys_instance :
    (∀ i, (gaussianSys.field i).totalDegree ≤ 2) ∧
    ∃ (sol : PIVP.Solution gaussianSys.toPIVP) (μ : TimeModulus),
      (∀ r : ℕ, ∀ t : ℝ, t > μ r →
        |sol.trajectory t gaussianSys.output - 1| < Real.exp (-(r : ℝ))) ∧
      (∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ 1 * ((r : ℝ) + 1) ^ 1) ∧
      (∀ r : ℕ, gaussianSys.arcLength sol.trajectory (μ r) ≤ 1 * ((r : ℝ) + 1) ^ 1) ∧
      ¬ gaussianSys.toPIVP.IsBounded sol.trajectory := by
  have hsqrt : ∀ r : ℕ, Real.sqrt r ≤ (r : ℝ) + 1 := by
    intro r
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have := Nat.cast_nonneg (α := ℝ) r; nlinarith
  refine ⟨gaussianSys_totalDegree, gaussianSol, fun r => Real.sqrt r, ?_, ?_, ?_, ?_⟩
  · intro r t ht
    have ht0 : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
    have hr : (r : ℝ) < t ^ 2 := (Real.sqrt_lt' ht0).mp ht
    show |gaussianTraj t 1 - 1| < _
    simp only [gaussianTraj, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show 1 - Real.exp (-t ^ 2) - 1 = -Real.exp (-t ^ 2) by ring, abs_neg,
      abs_of_pos (Real.exp_pos _), Real.exp_lt_exp]
    linarith
  · intro r
    exact ⟨Real.sqrt_nonneg _, by simpa using hsqrt r⟩
  · intro r
    have hle : gaussianSys.arcLength gaussianSol.trajectory (Real.sqrt r) ≤
        ∫ _u in (0 : ℝ)..(Real.sqrt r), (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
        ((gaussianSys.speed_continuousOn gaussianSol 0 _ le_rfl).intervalIntegrable_of_Icc
          (Real.sqrt_nonneg _)) intervalIntegrable_const fun u _ => ?_
      exact gaussianSys_speed_le_one u
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hle
    simpa using hle.trans (hsqrt r)
  · rintro ⟨M, hM, hb⟩
    have h := hb (M + 1) (by linarith)
    have h0 : |gaussianTraj (M + 1) 0| ≤ ‖gaussianTraj (M + 1)‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (gaussianTraj (M + 1)) 0
    have : gaussianTraj (M + 1) 0 = M + 1 := by simp [gaussianTraj]
    rw [this, abs_of_pos (by linarith)] at h0
    have : gaussianSol.trajectory = gaussianTraj := rfl
    rw [this] at h
    linarith

/-- The compiled bounded certificate for `1` with cubic time modulus, pinned to the joint
construction (`bounded_compilation_polyTime_certified`, [BAC] Thm 4.5 with `k = 1`, `N = 2`). -/
theorem gaussianSys_compiled :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 2 2) 1,
      btc.pivp = gaussianSys.jointSurrogateCompile 2 ∧
      ∃ C' : ℝ, 0 < C' ∧ ∀ r : ℕ, btc.modulus r ≤ C' * ((r : ℝ) + 1) ^ 3 := by
  obtain ⟨hdeg, sol, μ, hconv, hμ, hL, -⟩ := gaussianSys_instance
  obtain ⟨btc, hbtc, hmod, -⟩ :=
    bounded_compilation_polyTime_certified gaussianSys sol μ 1 1 hconv hμ hL
      (N := 2) ⟨1, rfl⟩ hdeg
  exact ⟨btc, hbtc, hmod⟩

/-! ## The tangent pole: a finite blow-up -/

/-- `u' = 1 + u², t' = 1`, `(u, t)(0) = (0, 0)`, output `t`. -/
noncomputable def tanSys : PolyPIVP 2 where
  field := ![1 + X 0 ^ 2, 1]
  init := ![0, 0]
  output := 1

/-- The solution `(tan t, t)` on `[0, π/2)`. -/
noncomputable def tanTraj (t : ℝ) : Fin 2 → ℝ := ![Real.tan t, t]

theorem tanSys_totalDegree : ∀ i, (tanSys.field i).totalDegree ≤ 2 := by
  intro i
  fin_cases i
  · show (1 + X 0 ^ 2 : MvPolynomial (Fin 2) ℚ).totalDegree ≤ 2
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
  · simp [tanSys]

theorem tanTraj_hasDerivAt (t : ℝ) (ht : t ∈ Set.Ico 0 (Real.pi / 2)) :
    HasDerivAt tanTraj (tanSys.evalField (tanTraj t)) t := by
  have hc : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
  have key : 1 / Real.cos t ^ 2 = 1 + Real.tan t ^ 2 := by
    rw [← Real.inv_one_add_tan_sq hc.ne', one_div, inv_inv]
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · have : (fun s => tanTraj s 0) = Real.tan := by funext s; simp [tanTraj]
    show HasDerivAt (fun s => tanTraj s 0) _ t
    rw [this]
    convert Real.hasDerivAt_tan hc.ne' using 1
    rw [key]
    simp [tanSys, PolyPIVP.evalField, tanTraj]
  · have : (fun s => tanTraj s 1) = fun s => s := by funext s; simp [tanTraj]
    show HasDerivAt (fun s => tanTraj s 1) _ t
    rw [this]
    convert hasDerivAt_id t using 1
    simp [tanSys, PolyPIVP.evalField]

/-- The hypotheses of `bounded_compilation_of_blowup_certified` and
`isCRNComputable_blowupTime_certified` hold for `tanSys` with `T = π/2`: the solution is
unbounded on `[0, π/2)` and the output tends to `π/2`. -/
theorem tanSys_instance :
    (∀ i, (tanSys.field i).totalDegree ≤ 2) ∧
    tanTraj 0 = (fun i => (tanSys.init i : ℝ)) ∧
    (∀ t ∈ Set.Ico 0 (Real.pi / 2), HasDerivAt tanTraj (tanSys.evalField (tanTraj t)) t) ∧
    ¬ BddAbove ((fun t => ‖tanTraj t‖) '' Set.Ico 0 (Real.pi / 2)) ∧
    Tendsto (fun t => tanTraj t tanSys.output)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (Real.pi / 2)) := by
  refine ⟨tanSys_totalDegree, ?_, tanTraj_hasDerivAt, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [tanTraj, tanSys]
  · rintro ⟨K, hK⟩
    have hT : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
    have hev : ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        x ∈ Set.Ioo 0 (Real.pi / 2) := Ioo_mem_nhdsLT hT
    obtain ⟨t, htK, ht⟩ :=
      ((Real.tendsto_tan_pi_div_two.eventually (eventually_gt_atTop K)).and hev).exists
    have h1 : ‖tanTraj t‖ ≤ K := hK ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
    have h0 : |tanTraj t 0| ≤ ‖tanTraj t‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (tanTraj t) 0
    have h2 : tanTraj t 0 = Real.tan t := by simp [tanTraj]
    rw [h2] at h0
    have := le_abs_self (Real.tan t)
    linarith
  · have : (fun t => tanTraj t tanSys.output) = fun t => t := by
      funext s; simp [tanTraj, tanSys]
    rw [this]
    exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- [BAC] Prop 3.2 at a finite blow-up: the bounded certificate for `π/2` from the output
limit, pinned to `jointSurrogateCompile 2`. -/
theorem tanSys_compiled_limit :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 2 2) (Real.pi / 2),
      btc.pivp = tanSys.jointSurrogateCompile 2 := by
  obtain ⟨hdeg, h0, hy, hunb, hlim⟩ := tanSys_instance
  exact bounded_compilation_of_blowup_certified tanSys ⟨1, rfl⟩ hdeg tanTraj h0 hy hunb hlim

/-- [BAC] Thm 3.4: the bounded certificate for the blow-up time `π/2`, pinned to
`jointClockCompile 2` (output the clock `s`, no original coordinate kept). -/
theorem tanSys_compiled_blowupTime :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 2 2) (Real.pi / 2),
      btc.pivp = tanSys.jointClockCompile 2 := by
  obtain ⟨hdeg, h0, hy, hunb, -⟩ := tanSys_instance
  exact isCRNComputable_blowupTime_certified tanSys ⟨1, rfl⟩ hdeg tanTraj h0 hy hunb

end Ripple

/-
  Ripple.Core.BGPPolyLength — the Bournez–Graça–Pouly poly-length definition and
  [BAC] Thm 4.6 from it

  [BAC] = Chen and Huang, *Bounded Analog Complexity*, journal draft (repository `Bounded`,
  branch `BAC-Journal`). Labels: §2.3 `subsec:bgp` (the definition [BGP, Def 2.3], sup norm,
  normalization `L(t) ≥ t`), Thm 4.6 `thm:poly-equiv` (from BGP poly length to bounded poly time).
  [BGP] = Bournez, Graça, Pouly, *Polynomial time corresponds to solutions of polynomial ordinary
  differential equations of polynomial length*, J. ACM 64 (2017).

  Main results:
  - `IsBGPPolyLengthComputable α`: [BGP, Def 2.3] for a real number (`n = 0`, `m = 1`), as
    recalled in [BAC] §2.3.
  - `bgpPolyLength_modulus`: the first step of the proof of [BAC] Thm 4.6: the BGP condition
    gives a time modulus `μ` with `μ(r) ≤ ω(r)` and `L(μ(r)) = ω(r)` for a polynomial `ω` of the
    degree of `Ω`.
  - `bounded_polyTime_of_bgpPolyLength` ([BAC] Thm 4.6 for real numbers, exponent pinned) and
    `isPolyTimeComputable_of_isBGPPolyLengthComputable` (the class statement).
-/

import Ripple.Core.Compilation

namespace Ripple

open MeasureTheory

variable {d : ℕ}

/-- [BAC] §2.3 (journal draft `subsec:bgp`) = [BGP, Def 2.3] for a real number (`n = 0`,
`m = 1`): `α` is *poly-length-computable* if there are a PIVP `y' = p(y)`, `y(0) = q ∈ ℚ^d`
with `p ∈ ℚ[y]^d` (a `PolyPIVP`) whose solution exists on `[0, ∞)`, and a polynomial `Ω`
(real coefficients; with `n = 0` it depends on the precision `μ` only), such that for all
`t, μ ≥ 0`
- `L(t) ≥ Ω(μ) ⇒ |y_o(t) − α| ≤ e^{−μ}`, and
- `L(t) ≥ t` (the normalization: the length grows at least linearly with time),
where `L(t) = ∫₀ᵗ ‖p(y(u))‖ du` is the trajectory length in the sup norm
(`PolyPIVP.arcLength`). The output coordinate is the designated `P.output` (BGP's `y₁` after a
renaming of the coordinates). A polynomial ODE has at most one solution, so the existential
over `sol` is the solution of [BGP]. -/
def IsBGPPolyLengthComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ P : PolyPIVP d, ∃ sol : PIVP.Solution P.toPIVP, ∃ Ω : Polynomial ℝ,
    (∀ t μ : ℝ, 0 ≤ t → 0 ≤ μ → Ω.eval μ ≤ P.arcLength sol.trajectory t →
      |sol.trajectory t P.output - α| ≤ Real.exp (-μ)) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ P.arcLength sol.trajectory t)

/-- `Ω⁺(x) = Σᵢ |cᵢ| xⁱ`, the polynomial with the absolute values of the coefficients of `Ω`. -/
noncomputable def absCoeffEval (Ω : Polynomial ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Ω.natDegree + 1), |Ω.coeff i| * x ^ i

theorem absCoeffEval_nonneg (Ω : Polynomial ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ absCoeffEval Ω x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (pow_nonneg hx i)

theorem eval_le_absCoeffEval (Ω : Polynomial ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Ω.eval x ≤ absCoeffEval Ω x := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hx i)

/-- `Ω⁺(x) ≤ (Σᵢ |cᵢ|) x^{deg Ω}` for `x ≥ 1`. -/
theorem absCoeffEval_le (Ω : Polynomial ℝ) {x : ℝ} (hx : 1 ≤ x) :
    absCoeffEval Ω x ≤ (∑ i ∈ Finset.range (Ω.natDegree + 1), |Ω.coeff i|) * x ^ Ω.natDegree := by
  rw [absCoeffEval, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact pow_le_pow_right₀ hx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- First step of the proof of [BAC] Thm 4.6 (journal draft `thm:poly-equiv`), for a real
number. From the BGP condition with polynomial `Ω`, let `ω(r) = Ω⁺(r + 1)`. There is a time
modulus `μ` for `α` (`|y_o(t) − α| < e^{−r}` for `t > μ(r)`) with `0 ≤ μ(r)`,
`L(μ(r)) = ω(r)`, and hence `μ(r) ≤ L(μ(r)) = ω(r)` by the normalization. The paper takes
`μ(r) = inf {t ≥ 0 : L(t) ≥ ω(r)}`; any `t₀ ∈ [0, ω(r)]` with `L(t₀) = ω(r)` (intermediate
value theorem) serves. -/
theorem bgpPolyLength_modulus {α : ℝ} (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (Ω : Polynomial ℝ)
    (hconv : ∀ t μ : ℝ, 0 ≤ t → 0 ≤ μ → Ω.eval μ ≤ P.arcLength sol.trajectory t →
      |sol.trajectory t P.output - α| ≤ Real.exp (-μ))
    (hnorm : ∀ t : ℝ, 0 ≤ t → t ≤ P.arcLength sol.trajectory t) :
    ∃ μ : TimeModulus,
      (∀ r : ℕ, ∀ t : ℝ, t > μ r → |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ))) ∧
      (∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ absCoeffEval Ω ((r : ℝ) + 1)) ∧
      (∀ r : ℕ, P.arcLength sol.trajectory (μ r) = absCoeffEval Ω ((r : ℝ) + 1)) := by
  have hex : ∀ r : ℕ, ∃ t₀ ∈ Set.Icc (0 : ℝ) (absCoeffEval Ω ((r : ℝ) + 1)),
      P.arcLength sol.trajectory t₀ = absCoeffEval Ω ((r : ℝ) + 1) := by
    intro r
    have hω := absCoeffEval_nonneg Ω (x := (r : ℝ) + 1) (by positivity)
    have hivt := intermediate_value_Icc hω (P.arcLength_continuousOn sol hω)
    have hmem : absCoeffEval Ω ((r : ℝ) + 1) ∈
        Set.Icc (P.arcLength sol.trajectory 0)
          (P.arcLength sol.trajectory (absCoeffEval Ω ((r : ℝ) + 1))) :=
      ⟨by rw [PolyPIVP.arcLength_zero]; exact hω, hnorm _ hω⟩
    exact hivt hmem
  choose μ hμI hμL using hex
  refine ⟨μ, fun r t ht => ?_, fun r => ⟨(hμI r).1, (hμI r).2⟩, hμL⟩
  have h0 : 0 ≤ μ r := (hμI r).1
  have ht0 : 0 ≤ t := h0.trans ht.le
  have hL : Ω.eval ((r : ℝ) + 1) ≤ P.arcLength sol.trajectory t :=
    calc Ω.eval ((r : ℝ) + 1) ≤ absCoeffEval Ω ((r : ℝ) + 1) :=
          eval_le_absCoeffEval Ω (by positivity)
      _ = P.arcLength sol.trajectory (μ r) := (hμL r).symm
      _ ≤ P.arcLength sol.trajectory t := P.arcLength_mono sol h0 ht.le
  calc |sol.trajectory t P.output - α| ≤ Real.exp (-((r : ℝ) + 1)) :=
        hconv t _ ht0 (by positivity) hL
    _ < Real.exp (-(r : ℝ)) := Real.exp_lt_exp.mpr (by linarith)

/-- [BAC] Thm 4.6 (journal draft `thm:poly-equiv`) for a real number, from the BGP definition
itself: if `α` is computed by a ℚ-PIVP in the sense of [BGP, Def 2.3] with polynomial `Ω`
(`L(t) ≥ Ω(μ) ⇒ |y_o(t) − α| ≤ e^{−μ}` and `L(t) ≥ t`), then for every even `N` at least the
degree of the field, `α` is computed by a bounded ℚ-PIVP (the joint surrogate compilation) in
polynomial time, with time modulus `O((r+1)^{deg Ω · (N+1)})`. Polynomial physical time is not
a hypothesis: it follows from the normalization (`bgpPolyLength_modulus`). -/
theorem bounded_polyTime_of_bgpPolyLength {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (Ω : Polynomial ℝ)
    (hconv : ∀ t μ : ℝ, 0 ≤ t → 0 ≤ μ → Ω.eval μ ≤ P.arcLength sol.trajectory t →
      |sol.trajectory t P.output - α| ≤ Real.exp (-μ))
    (hnorm : ∀ t : ℝ, 0 ≤ t → t ≤ P.arcLength sol.trajectory t)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    IsPolyTimeComputable α (Ω.natDegree * (N + 1)) := by
  obtain ⟨μ, hmod, hμ, hL⟩ := bgpPolyLength_modulus P sol Ω hconv hnorm
  set C := ∑ i ∈ Finset.range (Ω.natDegree + 1), |Ω.coeff i|
  have hω : ∀ r : ℕ, absCoeffEval Ω ((r : ℝ) + 1) ≤ C * ((r : ℝ) + 1) ^ Ω.natDegree :=
    fun r => absCoeffEval_le Ω (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  exact bounded_compilation_polyTime P sol μ Ω.natDegree C hmod
    (fun r => ⟨(hμ r).1, (hμ r).2.trans (hω r)⟩)
    (fun r => (hL r).le.trans (hω r)) hN hdeg

/-- [BAC] Thm 4.6 (journal draft `thm:poly-equiv`), real numbers, as an inclusion of classes:
a real number poly-length-computable in the sense of [BGP, Def 2.3] is computable by a bounded
ℚ-PIVP in polynomial time. -/
theorem isPolyTimeComputable_of_isBGPPolyLengthComputable {α : ℝ}
    (h : IsBGPPolyLengthComputable α) : ∃ n : ℕ, IsPolyTimeComputable α n := by
  obtain ⟨d, P, sol, Ω, hconv, hnorm⟩ := h
  have hdeg : ∀ i, (P.field i).totalDegree ≤
      2 * Finset.univ.sup fun j => (P.field j).totalDegree :=
    fun i => (Finset.le_sup (f := fun j => (P.field j).totalDegree) (Finset.mem_univ i)).trans
      (Nat.le_mul_of_pos_left _ two_pos)
  exact ⟨_, bounded_polyTime_of_bgpPolyLength P sol Ω hconv hnorm (even_two_mul _) hdeg⟩

/-! ## Non-vacuity: a system satisfying the BGP definition -/

/-- `x' = −x`, `x(0) = 1` with a clock `s' = 1`, `s(0) = 0`; output `x → 0`. The clock makes the
sup-norm speed `max(|x|, 1) = 1`, so `L(t) = t` and the normalization holds with equality. -/
noncomputable def expDecaySys : PolyPIVP 2 where
  field := ![-MvPolynomial.X 0, 1]
  init := ![1, 0]
  output := 0

/-- The explicit solution `(e^{−t}, t)`. -/
noncomputable def expDecaySol : PIVP.Solution expDecaySys.toPIVP where
  trajectory t := ![Real.exp (-t), t]
  init_cond := by
    funext i
    fin_cases i <;> simp [expDecaySys, PolyPIVP.toPIVP]
  is_solution t _ := by
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · have h := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
      convert h using 1
      simp [expDecaySys, PolyPIVP.toPIVP, PolyPIVP.evalField]
    · convert hasDerivAt_id t using 1
      · simp [expDecaySys, PolyPIVP.toPIVP, PolyPIVP.evalField]

theorem expDecaySys_evalField (u : ℝ) :
    expDecaySys.evalField (expDecaySol.trajectory u) = ![-Real.exp (-u), 1] := by
  funext i
  fin_cases i <;> simp [expDecaySys, expDecaySol, PolyPIVP.evalField]

/-- `L(t) = t` for `t ≥ 0`. -/
theorem expDecaySys_arcLength {t : ℝ} (ht : 0 ≤ t) :
    expDecaySys.arcLength expDecaySol.trajectory t = t := by
  have h : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      ‖expDecaySys.evalField (expDecaySol.trajectory u)‖ = (1 : ℝ) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    rw [expDecaySys_evalField]
    have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_) ?_
    · fin_cases i
      · simp [abs_of_pos (Real.exp_pos _), he]
      · simp
    · have := norm_le_pi_norm (![-Real.exp (-u), 1] : Fin 2 → ℝ) 1
      simpa using this
  unfold PolyPIVP.arcLength
  rw [intervalIntegral.integral_congr h]
  simp

/-- Non-vacuity of `IsBGPPolyLengthComputable`: `0` is BGP-poly-length-computable by
`expDecaySys` with `Ω(μ) = μ`. -/
theorem expDecaySys_isBGPPolyLengthComputable : IsBGPPolyLengthComputable 0 := by
  refine ⟨2, expDecaySys, expDecaySol, Polynomial.X, fun t μ ht _ hL => ?_, fun t ht => ?_⟩
  · rw [Polynomial.eval_X, expDecaySys_arcLength ht] at hL
    show |Real.exp (-t) - 0| ≤ Real.exp (-μ)
    rw [sub_zero, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [expDecaySys_arcLength ht]

/-- [BAC] Thm 4.6 applied to `expDecaySys` (degree-1 field, `N = 2`, `deg Ω = 1`): `0` is
computed by a bounded ℚ-PIVP with modulus `O((r+1)^3)`. -/
theorem expDecaySys_polyTime : IsPolyTimeComputable 0 3 := by
  have hdeg : ∀ i, (expDecaySys.field i).totalDegree ≤ 2 := by
    intro i
    fin_cases i
    · show (-MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ).totalDegree ≤ 2
      rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]; norm_num
    · show (1 : MvPolynomial (Fin 2) ℚ).totalDegree ≤ 2
      rw [MvPolynomial.totalDegree_one]; norm_num
  have h := bounded_polyTime_of_bgpPolyLength (α := 0) expDecaySys expDecaySol Polynomial.X
    (fun t μ ht _ hL => by
      rw [Polynomial.eval_X, expDecaySys_arcLength ht] at hL
      show |Real.exp (-t) - 0| ≤ Real.exp (-μ)
      rw [sub_zero, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith))
    (fun t ht => by rw [expDecaySys_arcLength ht]) (N := 2) even_two hdeg
  simpa [Polynomial.natDegree_X] using h

end Ripple

/-
  Ripple.Core.ProductClockCompilation — bounded surrogate compilation with the product clock

  The second instance of the joint construction (BC.md §1.6, comparison of routes): the clock is
  the product `Q(y) = Πᵢ (1 + yᵢ^N)` of [BAC] Construction 3.1 applied to every coordinate at
  once, and the surrogates are per coordinate, `U_{i,m} = yᵢ^m / (1 + yᵢ^N)` for `m ≤ N`. Then
  `y^β / Q(y) = Πⱼ U_{j,βⱼ}` for every exponent `β ≤ N` (no splitting lemma), and
  - `U_{i,m}' = (m U_{i,m−1} − N U_{i,N−1} U_{i,m}) Fᵢ^U` with `q^U = Σ_β c_β Πⱼ U_{j,βⱼ}`;
  - the compiled dimension is `1 + d (N + 1)`, linear in `d` and in `N` (`productDim_eq`),
    which is the count of [BAC] Thm 4.5 ("dimensional overhead polynomial in the degree");
  - the modulus exponent is `k (1 + d N)` instead of `k (N + 1)` for the sum clock.

  Main results: `bounded_compilation_productClock_certified` ([BAC] Thm 3.3) and
  `bounded_compilation_productClock_polyTime_certified` ([BAC] Thm 4.5 with the linear
  dimension clause).

  Numbering of [BAC]: the DNA 32 version, as in `docs/refactor/BC.md` (journal-draft labels in
  the header of `Ripple.Core.SurrogateCompilation`).
-/

import Ripple.Core.SurrogateCompilation

namespace Ripple

open MvPolynomial Filter

variable {d : ℕ}

/-! ## Indices, clock and surrogates -/

/-- Coordinates of the product-clock compiled system: `none` is the kept output, `some (i, m)`
the surrogate `U_{i,m}`. -/
abbrev ProductIndex (d N : ℕ) := Option (Fin d × Fin (N + 1))

/-- Dimension of the product-clock compiled system. -/
abbrev productDim (d N : ℕ) : ℕ := Fintype.card (ProductIndex d N)

/-- [BAC] Thm 4.5, dimension clause, product clock: `1 + d (N + 1)`. -/
theorem productDim_eq (d N : ℕ) : productDim d N = 1 + d * (N + 1) := by
  simp only [productDim, ProductIndex, Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The product clock `Q(y) = Πᵢ (1 + yᵢ^N)`, so that `dt/dτ = 1/Q`. -/
noncomputable def productClock (N : ℕ) (y : Fin d → ℝ) : ℝ := ∏ i, (1 + y i ^ N)

/-- The surrogate `U_{i,m}(y) = yᵢ^m / (1 + yᵢ^N)`. -/
noncomputable def coordSurrogate (N : ℕ) (i : Fin d) (m : ℕ) (y : Fin d → ℝ) : ℝ :=
  y i ^ m / (1 + y i ^ N)

theorem one_le_one_add_pow {N : ℕ} (hN : Even N) (x : ℝ) : 1 ≤ 1 + x ^ N := by
  linarith [hN.pow_nonneg x]

theorem productClock_ge_one {N : ℕ} (hN : Even N) (y : Fin d → ℝ) : 1 ≤ productClock N y :=
  Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
    (fun i _ => one_le_one_add_pow hN (y i))

theorem productClock_pos {N : ℕ} (hN : Even N) (y : Fin d → ℝ) : 0 < productClock N y :=
  lt_of_lt_of_le one_pos (productClock_ge_one hN y)

theorem continuous_productClock (N : ℕ) : Continuous (productClock (d := d) N) :=
  continuous_finsetProd _ fun i _ => continuous_const.add ((continuous_apply i).pow N)

/-- `|x^m| ≤ 1 + x^N` for `m ≤ N`, `N` even. -/
theorem abs_pow_le_one_add_pow {N m : ℕ} (hN : Even N) (hm : m ≤ N) (x : ℝ) :
    |x ^ m| ≤ 1 + x ^ N := by
  rw [abs_pow]
  rcases le_or_gt |x| 1 with h | h
  · have : |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    linarith [hN.pow_nonneg x]
  · have : |x| ^ m ≤ |x| ^ N := pow_le_pow_right₀ h.le hm
    rw [hN.pow_abs] at this
    linarith

/-- The surrogates lie in `[-1, 1]`. -/
theorem coordSurrogate_abs_le_one {N : ℕ} (hN : Even N) (i : Fin d) (m : Fin (N + 1))
    (y : Fin d → ℝ) : |coordSurrogate N i m y| ≤ 1 := by
  have hpos : 0 < 1 + y i ^ N := lt_of_lt_of_le one_pos (one_le_one_add_pow hN _)
  unfold coordSurrogate
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  exact abs_pow_le_one_add_pow hN (Nat.lt_succ_iff.mp m.2) _

theorem continuous_coordSurrogate {N : ℕ} (hN : Even N) (i : Fin d) (m : ℕ) :
    Continuous (coordSurrogate N i m) :=
  ((continuous_apply i).pow m).div (continuous_const.add ((continuous_apply i).pow N))
    fun y => (lt_of_lt_of_le one_pos (one_le_one_add_pow hN (y i))).ne'

/-- `y^β / Q(y) = Πⱼ U_{j,βⱼ}`. -/
theorem eval_div_productClock {N : ℕ} (b : MIndex d N) (y : Fin d → ℝ) :
    b.eval y / productClock N y = ∏ j, coordSurrogate N j (b j) y := by
  unfold MIndex.eval productClock coordSurrogate
  rw [Finset.prod_div_distrib]

/-! ## The lifted field `q^U` -/

/-- `q^U = Σ_β c_β Πⱼ U_{j,βⱼ}` for `q = Σ_β c_β y^β`. -/
noncomputable def productLift (N : ℕ) (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (ProductIndex d N) ℚ :=
  ∑ b : MIndex d N, C (q.coeff b.toFinsupp) * ∏ j, X (some (j, b j))

/-- `q^U(U(y)) = q(y)/Q(y)` when `deg q ≤ N`. -/
theorem productLift_eval₂ {N : ℕ} {q : MvPolynomial (Fin d) ℚ} (hq : q.totalDegree ≤ N)
    (y : Fin d → ℝ) (v : ProductIndex d N → ℝ)
    (hv : ∀ i (m : Fin (N + 1)), v (some (i, m)) = coordSurrogate N i m y) :
    (productLift N q).eval₂ (Rat.castHom ℝ) v =
      q.eval₂ (Rat.castHom ℝ) y / productClock N y := by
  rw [eval₂_as_mindex_sum q hq y, Finset.sum_div]
  simp only [productLift, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X, hv]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_div_assoc, eval_div_productClock]
  simp

/-! ## The compiled field -/

/-- `m − 1` (saturating) as an exponent `≤ N`. -/
def predExp {N : ℕ} (m : Fin (N + 1)) : Fin (N + 1) :=
  ⟨(m : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) m.2⟩

/-- `N − 1` (saturating) as an exponent `≤ N`. -/
def topExp (N : ℕ) : Fin (N + 1) := ⟨N - 1, by omega⟩

/-- The compiled surrogate line: `U_{i,m}' = (m U_{i,m−1} − N U_{i,N−1} U_{i,m}) Fᵢ^U`. -/
noncomputable def productField (P : PolyPIVP d) (N : ℕ) (i : Fin d) (m : Fin (N + 1)) :
    MvPolynomial (ProductIndex d N) ℚ :=
  (C (((m : ℕ) : ℚ)) * X (some (i, predExp m)) -
      C ((N : ℚ)) * X (some (i, topExp N)) * X (some (i, m))) *
    productLift N (P.field i)

/-- The derivative identity: along a curve with `z' = F(z)/Q(z)`, every surrogate `U_{i,m}(z)`
satisfies the compiled surrogate line. -/
theorem hasDerivAt_coordSurrogate (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (i : Fin d) (m : Fin (N + 1))
    (z : ℝ → Fin d → ℝ) (τ : ℝ)
    (hz : HasDerivAt (fun σ => z σ i) (P.evalField (z τ) i / productClock N (z τ)) τ)
    (v : ProductIndex d N → ℝ)
    (hv : ∀ j (l : Fin (N + 1)), v (some (j, l)) = coordSurrogate N j l (z τ)) :
    HasDerivAt (fun σ => coordSurrogate N i m (z σ))
      ((productField P N i m).eval₂ (Rat.castHom ℝ) v) τ := by
  have hh : 0 < 1 + z τ i ^ N := lt_of_lt_of_le one_pos (one_le_one_add_pow hN _)
  have hQ : productClock N (z τ) ≠ 0 := (productClock_pos hN (z τ)).ne'
  have hl : (productLift N (P.field i)).eval₂ (Rat.castHom ℝ) v =
      P.evalField (z τ) i / productClock N (z τ) := productLift_eval₂ (hdeg i) (z τ) v hv
  show HasDerivAt (fun σ => z σ i ^ (m : ℕ) / (1 + z σ i ^ N)) _ τ
  refine ((hz.pow (m : ℕ)).div ((hz.pow N).const_add 1) hh.ne').congr_deriv ?_
  simp only [productField, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X, hv, hl, coordSurrogate, predExp, topExp, eq_ratCast,
    Rat.cast_natCast, Pi.pow_apply]
  field_simp

/-! ## The compiled system -/

/-- Compiled field over the index type: the kept output `x̄' = F_o^U` and the surrogate lines. -/
noncomputable def productFieldAll (P : PolyPIVP d) (N : ℕ) :
    ProductIndex d N → MvPolynomial (ProductIndex d N) ℚ
  | none => productLift N (P.field P.output)
  | some (i, m) => productField P N i m

/-- Compiled initial value: `x̄(0) = y₀_o`, `U_{i,m}(0) = y₀ᵢ^m / (1 + y₀ᵢ^N)`. -/
noncomputable def productInit (P : PolyPIVP d) (N : ℕ) : ProductIndex d N → ℚ
  | none => P.init P.output
  | some (i, m) => P.init i ^ (m : ℕ) / (1 + P.init i ^ N)

/-- The product-clock compiled ℚ-PIVP, in dimension `productDim d N = 1 + d (N + 1)`. -/
noncomputable def PolyPIVP.productClockCompile (P : PolyPIVP d) (N : ℕ) :
    PolyPIVP (productDim d N) :=
  PolyPIVP.ofIndexed (productFieldAll P N) (productInit P N) none

theorem productClockCompile_output (P : PolyPIVP d) (N : ℕ) :
    (P.productClockCompile N).output = Fintype.equivFin (ProductIndex d N) none := rfl

/-- The coordinate of the surrogate `U_{i,m}` in the compiled system. -/
noncomputable def productCoord {N : ℕ} (i : Fin d) (m : Fin (N + 1)) : Fin (productDim d N) :=
  Fintype.equivFin (ProductIndex d N) (some (i, m))

theorem productCoord_cases {N : ℕ} (j : Fin (productDim d N)) :
    j = Fintype.equivFin (ProductIndex d N) none ∨ ∃ i m, j = productCoord (N := N) i m := by
  obtain ⟨k, rfl⟩ := (Fintype.equivFin (ProductIndex d N)).surjective j
  rcases k with _ | ⟨i, m⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, m, rfl⟩

/-- The compiled curve over the index type. -/
noncomputable def productCurve (N : ℕ) (o : Fin d) (z : ℝ → Fin d → ℝ) (τ : ℝ) :
    ProductIndex d N → ℝ
  | none => z τ o
  | some (i, m) => coordSurrogate N i m (z τ)

/-- A curve `z` with `z(0) = y₀` and `z' = F(z)/Q(z)` on `[0, ∞)` gives the solution
`τ ↦ (z_o(τ), (U_{i,m}(z(τ)))_{i,m})` of the product-clock compiled system. -/
theorem PolyPIVP.productClockCompile_solution_of_curve (P : PolyPIVP d) {N : ℕ}
    (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (z : ℝ → Fin d → ℝ)
    (hz0 : z 0 = fun i => (P.init i : ℝ))
    (hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => z σ i)
      (P.evalField (z τ) i / productClock N (z τ)) τ) :
    ∃ sol' : PIVP.Solution (P.productClockCompile N).toPIVP,
      (∀ τ, sol'.trajectory τ (P.productClockCompile N).output = z τ P.output) ∧
      (∀ τ i (m : Fin (N + 1)),
        sol'.trajectory τ (productCoord i m) = coordSurrogate N i m (z τ)) ∧
      (Continuous z → Continuous sol'.trajectory) := by
  have hZ0 : ∀ k, productCurve N P.output z 0 k = (productInit P N k : ℝ) := by
    intro k
    rcases k with _ | ⟨i, m⟩
    · simp [productCurve, productInit, hz0]
    · simp [productCurve, productInit, hz0, coordSurrogate]
  have hZd : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => productCurve N P.output z σ k)
      ((productFieldAll P N k).eval₂ (Rat.castHom ℝ) (productCurve N P.output z τ)) τ := by
    intro τ hτ k
    rcases k with _ | ⟨i, m⟩
    · change HasDerivAt (fun σ => z σ P.output)
        ((productLift N (P.field P.output)).eval₂ (Rat.castHom ℝ)
          (productCurve N P.output z τ)) τ
      rw [productLift_eval₂ (hdeg _) (z τ) _ (fun _ _ => rfl)]
      exact hz τ hτ P.output
    · exact hasDerivAt_coordSurrogate P hN hdeg i m z τ (hz τ hτ i) _ (fun _ _ => rfl)
  obtain ⟨sol', hsol'⟩ :=
    PolyPIVP.ofIndexed_solution (productFieldAll P N) (productInit P N) none _ hZ0 hZd
  refine ⟨sol', fun τ => ?_, fun τ i m => ?_, fun hzc => ?_⟩
  · rw [hsol']
    simp only [productClockCompile_output, Equiv.symm_apply_apply]
    rfl
  · rw [hsol']
    simp only [productCoord, Equiv.symm_apply_apply]
    rfl
  · rw [hsol']
    refine continuous_pi fun j => ?_
    rcases h : (Fintype.equivFin (ProductIndex d N)).symm j with _ | ⟨i, m⟩
    · simpa [productCurve, h] using (continuous_apply P.output).comp hzc
    · simpa [productCurve, h] using (continuous_coordSurrogate hN i m).comp hzc

/-- [BAC] Construction 3.1 + Prop 3.2 (`T* = ∞`), product clock: the compiled system has the
solution `τ ↦ (y_o(s τ), (U_{i,m}(y(s τ)))_{i,m})` on `[0, ∞)`, where `s` inverts
`θ(t) = ∫₀ᵗ Q(y)`. -/
theorem PolyPIVP.productClockCompile_solution (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (sol : PIVP.Solution P.toPIVP) :
    ∃ (sol' : PIVP.Solution (P.productClockCompile N).toPIVP) (s : ℝ → ℝ),
      Continuous sol'.trajectory ∧ s 0 = 0 ∧ StrictMono s ∧
      Tendsto s atTop atTop ∧
      (∀ t, 0 ≤ t → s (∫ u in (0 : ℝ)..t, productClock N (sol.trajectory u)) = t) ∧
      (∀ τ, 0 ≤ τ → sol'.trajectory τ (P.productClockCompile N).output
          = sol.trajectory (s τ) P.output) ∧
      (∀ τ, 0 ≤ τ → ∀ i (m : Fin (N + 1)),
          sol'.trajectory τ (productCoord i m) = coordSurrogate N i m (sol.trajectory (s τ))) := by
  obtain ⟨solc, hcont, heq⟩ := sol.exists_continuous
  have hyd : ∀ t, 0 ≤ t →
      HasDerivAt solc.trajectory (P.evalField (solc.trajectory t)) t := solc.is_solution
  have hρc : Continuous fun t => productClock N (solc.trajectory t) :=
    (continuous_productClock N).comp hcont
  have hρ1 : ∀ u, 1 ≤ (fun t => productClock N (solc.trajectory t)) u :=
    fun u => productClock_ge_one hN (solc.trajectory u)
  obtain ⟨s, hs0, hsd, hsc, hsm, hst, hsθ, -⟩ := exists_inverse_timeChange hρc hρ1
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  have hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => solc.trajectory (s σ) i)
      (P.evalField (solc.trajectory (s τ)) i / productClock N (solc.trajectory (s τ))) τ := by
    intro τ hτ i
    have h := (hyd (s τ) (hs_nn τ hτ)).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp h i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hz0 : solc.trajectory (s 0) = fun i => (P.init i : ℝ) := by
    rw [hs0, solc.init_cond]; rfl
  obtain ⟨sol', hout, hsur, hcont'⟩ :=
    P.productClockCompile_solution_of_curve hN hdeg (fun σ => solc.trajectory (s σ)) hz0 hz
  refine ⟨sol', s, hcont' (hcont.comp hsc), hs0, hsm, hst, ?_, ?_, ?_⟩
  · intro t ht
    have hint : (∫ u in (0 : ℝ)..t, productClock N (sol.trajectory u)) =
        clockIntegral (fun t => productClock N (solc.trajectory t)) t := by
      unfold clockIntegral
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le ht] at hu
      change productClock N (sol.trajectory u) = productClock N (solc.trajectory u)
      rw [heq u hu.1]
    rw [hint, hsθ]
  · intro τ hτ
    rw [hout τ]
    change solc.trajectory (s τ) P.output = _
    rw [heq (s τ) (hs_nn τ hτ)]
  · intro τ hτ i m
    rw [hsur τ i m]
    change coordSurrogate N i m (solc.trajectory (s τ)) = _
    rw [heq (s τ) (hs_nn τ hτ)]

/-- The compiled trajectory is bounded when the kept output is. -/
theorem productClockCompile_isBounded (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (sol' : PIVP.Solution (P.productClockCompile N).toPIVP) (z : ℝ → Fin d → ℝ)
    (hout : ∀ τ, 0 ≤ τ → sol'.trajectory τ (P.productClockCompile N).output = z τ P.output)
    (hsur : ∀ τ, 0 ≤ τ → ∀ i (m : Fin (N + 1)),
      sol'.trajectory τ (productCoord i m) = coordSurrogate N i m (z τ))
    {M : ℝ} (hM : ∀ τ, 0 ≤ τ → |z τ P.output| ≤ M) :
    (P.productClockCompile N).toPIVP.IsBounded sol'.trajectory := by
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun τ hτ => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_right _ _))).2 fun j => ?_
  rw [Real.norm_eq_abs]
  rcases productCoord_cases j with rfl | ⟨i, m, rfl⟩
  · rw [← productClockCompile_output, hout τ hτ]
    exact (hM τ hτ).trans (le_max_left _ _)
  · rw [hsur τ hτ i m]
    exact (coordSurrogate_abs_le_one hN i m _).trans (le_max_right _ _)

/-- [BAC] Thm 3.3 with the product clock, certified form: the bounded ℚ-PIVP
`P.productClockCompile N`, of dimension `1 + d (N + 1)`, computes `α`. -/
theorem bounded_compilation_productClock_certified {α : ℝ} (P : PolyPIVP d) {N : ℕ}
    (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (sol : PIVP.Solution P.toPIVP)
    (hlim : Tendsto (fun t => sol.trajectory t P.output) atTop (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (productDim d N) α,
      btc.pivp = P.productClockCompile N := by
  obtain ⟨sol', s, hcont, hs0, hsm, hst, -, hout, hsur⟩ :=
    P.productClockCompile_solution hN hdeg sol
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_tendsto
    (fun t ht => (continuous_apply P.output).continuousAt.comp
      ((sol.is_solution t ht).continuousAt)) hlim
  have hbd := productClockCompile_isBounded P hN sol' (fun τ => sol.trajectory (s τ)) hout hsur
    (fun τ hτ => hM _ (hs_nn τ hτ))
  have hlim' : Tendsto (fun τ => sol'.trajectory τ (P.productClockCompile N).output)
      atTop (nhds α) := by
    refine (hlim.comp hst).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hout τ hτ).symm
  obtain ⟨btc, hbtc, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol' hbd hcont hlim'
  exact ⟨btc, hbtc⟩

/-- [BAC] Thm 4.5 with the product clock (linear dimension): under the hypotheses of
`bounded_compilation_polyTime_certified`, the bounded compiled system
`P.productClockCompile N`, of dimension `1 + d (N + 1)` (`productDim_eq`), computes `α` with a
time modulus at most `C' (r+1)^{k(1 + d N)}`, and its own trajectory length grows at most
linearly. -/
theorem bounded_compilation_productClock_polyTime_certified {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (μ : TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)))
    (hμ : ∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ r : ℕ, P.arcLength sol.trajectory (μ r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ btc : CertifiedBoundedTimeComputable (productDim d N) α,
      btc.pivp = P.productClockCompile N ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ r : ℕ, btc.modulus r ≤ C' * ((r : ℝ) + 1) ^ (k * (1 + d * N))) ∧
      (∃ v : ℝ, 0 ≤ v ∧ ∀ τ, 0 ≤ τ → btc.pivp.arcLength btc.sol.trajectory τ ≤ v * τ) := by
  obtain ⟨sol', s, -, hs0, hsm, -, hclock, hout, hsur⟩ :=
    P.productClockCompile_solution hN hdeg sol
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  have hlim := tendsto_of_modulus μ hconv
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_tendsto
    (fun t ht => (continuous_apply P.output).continuousAt.comp
      ((sol.is_solution t ht).continuousAt)) hlim
  have hbd := productClockCompile_isBounded P hN sol' (fun τ => sol.trajectory (s τ)) hout hsur
    (fun τ hτ => hM _ (hs_nn τ hτ))
  have hclk_cont : ∀ a b, 0 ≤ a →
      ContinuousOn (fun u => productClock N (sol.trajectory u)) (Set.Icc a b) :=
    fun a b ha u hu => ((continuous_productClock N).continuousAt.comp
      (P.solution_continuousAt sol (ha.trans hu.1))).continuousWithinAt
  have hθ_nn : ∀ t, 0 ≤ t → 0 ≤ ∫ u in (0 : ℝ)..t, productClock N (sol.trajectory u) :=
    fun t ht => intervalIntegral.integral_nonneg ht
      fun u _ => zero_le_one.trans (productClock_ge_one hN _)
  have hconv' : ∀ r : ℕ, ∀ τ : ℝ,
      τ > (fun r : ℕ => ∫ u in (0 : ℝ)..(μ r), productClock N (sol.trajectory u)) r →
      |sol'.trajectory τ (P.productClockCompile N).output - α| < Real.exp (-(r : ℝ)) := by
    intro r τ hτ
    have hτ0 : 0 ≤ τ := (hθ_nn _ (hμ r).1).trans hτ.le
    have hsτ : μ r < s τ := by
      have := hsm hτ
      rwa [hclock _ (hμ r).1] at this
    rw [hout τ hτ0]
    exact hconv r (s τ) hsτ
  obtain ⟨btc, hbtc, hmod, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_solution _ sol' hbd _ hconv'
  refine ⟨btc, hbtc, ?_, ?_⟩
  · have hC : 0 ≤ C := by
      have := (hμ 0).1.trans (hμ 0).2
      simpa using this
    obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = ∑ i, |(P.init i : ℝ)| := ⟨_, rfl⟩
    have hc₀_nn : 0 ≤ c₀ := hc₀ ▸ Finset.sum_nonneg fun i _ => abs_nonneg _
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * (1 + (c₀ + C) ^ N) ^ d := ⟨_, rfl⟩
    refine ⟨max K 1, lt_max_of_lt_right one_pos, fun r => ?_⟩
    rw [hmod r, max_eq_right (hθ_nn _ (hμ r).1)]
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((r : ℝ) + 1) ^ k := ⟨_, rfl⟩
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) r; linarith
    have hq1 : 1 ≤ q := hq ▸ one_le_pow₀ hr1
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = c₀ + C * q := ⟨_, rfl⟩
    have hLr : P.arcLength sol.trajectory (μ r) ≤ C * q := hq ▸ hL r
    have hcoord : ∀ u ∈ Set.Icc 0 (μ r), ∀ i, |sol.trajectory u i| ≤ B := by
      intro u hu i
      have h1 := P.abs_sub_init_le_arcLength sol i hu.1
      have h2 := P.arcLength_mono sol hu.1 hu.2
      have h3 : |(P.init i : ℝ)| ≤ c₀ := hc₀ ▸
        Finset.single_le_sum (f := fun i => |(P.init i : ℝ)|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      have h4 := abs_sub_abs_le_abs_sub (sol.trajectory u i) (P.init i : ℝ)
      rw [hB]
      linarith
    have hclk_le : ∀ u ∈ Set.Icc 0 (μ r),
        productClock N (sol.trajectory u) ≤ (1 + B ^ N) ^ d := by
      intro u hu
      unfold productClock
      have : ∏ i, (1 + sol.trajectory u i ^ N) ≤ ∏ _i : Fin d, (1 + B ^ N) :=
        Finset.prod_le_prod (fun i _ => zero_le_one.trans (one_le_one_add_pow hN _))
          fun i _ => by
            have : sol.trajectory u i ^ N ≤ B ^ N := by
              rw [← hN.pow_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hcoord u hu i) N
            linarith
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
    have hθle : (∫ u in (0 : ℝ)..(μ r), productClock N (sol.trajectory u)) ≤
        μ r * (1 + B ^ N) ^ d := by
      have h := intervalIntegral.integral_mono_on (hμ r).1
        ((hclk_cont 0 (μ r) le_rfl).intervalIntegrable_of_Icc
          (μ := MeasureTheory.volume) (hμ r).1)
        ((continuous_const : Continuous fun _ : ℝ => (1 + B ^ N) ^ d).intervalIntegrable
          (μ := MeasureTheory.volume) _ _)
        hclk_le
      simpa [mul_comm] using h
    have hB_le : B ≤ (c₀ + C) * q := by
      have : c₀ ≤ c₀ * q := le_mul_of_one_le_right hc₀_nn hq1
      rw [hB]; nlinarith
    have hB_nn : 0 ≤ B := by rw [hB]; positivity
    have hBN : B ^ N ≤ (c₀ + C) ^ N * q ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hB_nn hB_le N
    have hqN1 : 1 ≤ q ^ N := one_le_pow₀ hq1
    have hfac : 1 + B ^ N ≤ (1 + (c₀ + C) ^ N) * q ^ N := by
      calc 1 + B ^ N ≤ q ^ N + (c₀ + C) ^ N * q ^ N := by linarith
        _ = (1 + (c₀ + C) ^ N) * q ^ N := by ring
    have hpow : q * (q ^ N) ^ d = ((r : ℝ) + 1) ^ (k * (1 + d * N)) := by
      rw [hq, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    have hμr : μ r ≤ C * q := hq ▸ (hμ r).2
    have hfac_nn : 0 ≤ 1 + B ^ N := zero_le_one.trans (one_le_one_add_pow hN _)
    calc (∫ u in (0 : ℝ)..(μ r), productClock N (sol.trajectory u))
        ≤ μ r * (1 + B ^ N) ^ d := hθle
      _ ≤ (C * q) * ((1 + (c₀ + C) ^ N) * q ^ N) ^ d := by
          gcongr
      _ = C * (1 + (c₀ + C) ^ N) ^ d * (q * (q ^ N) ^ d) := by rw [mul_pow]; ring
      _ = K * ((r : ℝ) + 1) ^ (k * (1 + d * N)) := by rw [hpow, hK]
      _ ≤ max K 1 * ((r : ℝ) + 1) ^ (k * (1 + d * N)) := by
          gcongr; exact le_max_left _ _
  · exact btc.pivp.arcLength_le_of_bounded btc.sol btc.bounded

end Ripple

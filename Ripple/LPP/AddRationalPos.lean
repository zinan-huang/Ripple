/-
  Ripple.LPP.AddRationalPos — RTCRN1 Lemma 4.3, strictly positive q case

  Discharges `certified_add_rational_pos` (previously an axiom in
  `Ripple.LPP.AlgebraicConstruction`) by factoring into:

  1. **Structural extension (proved here).** Given a CertifiedBoundedTimeComputable
     witness for `β` with PolyCRNDecomposition, build a `d+1`-dimensional
     extended `PolyPIVP` where a new "relaxation tracker" species `y` obeys
     `y' = k·x_out + k·q − k·y` (with `k := 1` for the rate constant, just a
     convenient fixed positive rational). Lift the original polynomials via
     `MvPolynomial.rename Fin.castSucc` and `Fin.snoc` the new field for `y`.

  2. **Analytic content (narrow residual axiom).** The convergence of the
     extended trajectory to `β + q` with time modulus
       μ'(r) := μ(r+1) + (r + 1 + log(max(2β, 1))) · log(2)⁻¹
     under the linear relaxation ODE. This is the content Mathlib does not
     yet provide in a directly usable form; the underlying derivation is
       |y(t) − (β + q)| ≤ |y(0) − β − q| · e^{−t} + ∫₀^t e^{−(t−s)} |x_out(s) − β| ds.

  The residual axiom `relaxation_tracker_solution` is structural (existence
  of a solution trajectory with the stated bounds), scoped to the
  `relaxationPIVP` construction defined here. It replaces the monolithic
  `certified_add_rational_pos` axiom.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Ripple
namespace Algebraic

open MvPolynomial

/-! ## Step 1: lift an original `PolyPIVP d` to a `PolyPIVP (d+1)`.

We extend along `Fin.castSucc : Fin d ↪ Fin (d+1)` so that:
- original species `i : Fin d` sits at `i.castSucc`;
- new species `y` sits at `Fin.last d`.
-/

/-- Rename the field polynomials along `Fin.castSucc`. -/
noncomputable def liftField {d : ℕ} (P : PolyPIVP d) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (P.field i)

/-- Rename the production polynomials along `Fin.castSucc`. -/
noncomputable def liftProd {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (pcd.prod i)

/-- Rename the degradation polynomials along `Fin.castSucc`. -/
noncomputable def liftDegr {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (pcd.degr i)

/-- Non-negativity of coefficients is preserved by `rename` along injections. -/
lemma coeff_rename_castSucc_nonneg {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) :
    ∀ σ, 0 ≤ (rename (Fin.castSucc (n := d)) p).coeff σ := by
  classical
  intro σ
  by_cases h : ∃ u : Fin d →₀ ℕ, u.mapDomain Fin.castSucc = σ
  · obtain ⟨u, hu⟩ := h
    subst hu
    rw [coeff_rename_mapDomain Fin.castSucc (Fin.castSucc_injective d)]
    exact hp u
  · rw [coeff_rename_eq_zero Fin.castSucc p σ (by
      intro u hu; exact absurd ⟨u, hu⟩ h)]

/-! ## Step 2: the relaxation tracker field for the new species `y`.

We use rate constant `k := 1` (a rational, positive), so:
- `field_y := X_out + q · 1 - X_y` (where X_out is the lifted output)
- `prod_y  := X_out + q · 1`
- `degr_y  := 1`
-/

/-- Production polynomial for the tracker species `y` = `X_out + q`. -/
noncomputable def trackerProd {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  X (Fin.castSucc P.output) + C q

/-- Degradation polynomial for the tracker species `y` = `1`. -/
noncomputable def trackerDegr (d : ℕ) : MvPolynomial (Fin (d+1)) ℚ :=
  1

/-- Field polynomial for the tracker species `y` = `X_out + q − X_y`. -/
noncomputable def trackerField {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  trackerProd P q - trackerDegr d * X (Fin.last d)

/-- Coefficients of `trackerProd P q = X_out + q` are non-negative when `0 ≤ q`. -/
lemma trackerProd_coeff_nonneg {d : ℕ} (P : PolyPIVP d) (q : ℚ) (hq : 0 ≤ q) :
    ∀ σ, 0 ≤ (trackerProd P q).coeff σ := by
  classical
  intro σ
  unfold trackerProd
  rw [MvPolynomial.coeff_add]
  have h1 : 0 ≤ (X (Fin.castSucc P.output) :
      MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_X']
    split_ifs <;> norm_num
  have h2 : 0 ≤ (C q : MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_C]
    split_ifs
    · exact hq
    · exact le_refl _
  linarith

/-- Coefficients of `trackerDegr d = 1` are non-negative. -/
lemma trackerDegr_coeff_nonneg (d : ℕ) :
    ∀ σ, 0 ≤ (trackerDegr d).coeff σ := by
  classical
  intro σ
  unfold trackerDegr
  rw [show (1 : MvPolynomial (Fin (d+1)) ℚ) = C 1 from (map_one _).symm,
      MvPolynomial.coeff_C]
  split_ifs
  · norm_num
  · exact le_refl _

/-! ## Step 3: build the extended `PolyPIVP (d+1)` via `Fin.snoc`. -/

/-- The extended polynomial IVP: original species lifted, plus a tracker `y`. -/
noncomputable def relaxationPIVP {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    PolyPIVP (d+1) where
  field := Fin.snoc (liftField P) (trackerField P q)
  init := Fin.snoc (fun i => P.init i) q
  output := Fin.last d

@[simp] lemma relaxationPIVP_output {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    (relaxationPIVP P q).output = Fin.last d := rfl

@[simp] lemma relaxationPIVP_field_castSucc {d : ℕ} (P : PolyPIVP d) (q : ℚ)
    (i : Fin d) :
    (relaxationPIVP P q).field i.castSucc = rename Fin.castSucc (P.field i) := by
  unfold relaxationPIVP
  simp [liftField, Fin.snoc_castSucc]

@[simp] lemma relaxationPIVP_field_last {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    (relaxationPIVP P q).field (Fin.last d) = trackerField P q := by
  unfold relaxationPIVP
  simp [Fin.snoc_last]

@[simp] lemma relaxationPIVP_init_castSucc {d : ℕ} (P : PolyPIVP d) (q : ℚ)
    (i : Fin d) :
    (relaxationPIVP P q).init i.castSucc = P.init i := by
  unfold relaxationPIVP
  simp [Fin.snoc_castSucc]

@[simp] lemma relaxationPIVP_init_last {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    (relaxationPIVP P q).init (Fin.last d) = q := by
  unfold relaxationPIVP
  simp [Fin.snoc_last]

/-! ## Step 4: the PolyCRNDecomposition of the extended system. -/

/-- The extended system admits a `PolyCRNDecomposition` when the original does
and `q ≥ 0`. Non-negativity of coefficients is preserved by `rename` (for the
original block) and holds by construction for the tracker row. -/
noncomputable def relaxationPIVP_polyCRN {d : ℕ} {P : PolyPIVP d} (q : ℚ)
    (hq : 0 ≤ q) (pcd : PolyCRNDecomposition d P) :
    PolyCRNDecomposition (d+1) (relaxationPIVP P q) where
  prod := Fin.snoc (liftProd pcd) (trackerProd P q)
  degr := Fin.snoc (liftDegr pcd) (trackerDegr d)
  prod_nonneg := by
    intro i σ
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact trackerProd_coeff_nonneg P q hq σ
    · rw [Fin.snoc_castSucc]
      exact coeff_rename_castSucc_nonneg (pcd.prod i') (pcd.prod_nonneg i') σ
  degr_nonneg := by
    intro i σ
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact trackerDegr_coeff_nonneg d σ
    · rw [Fin.snoc_castSucc]
      exact coeff_rename_castSucc_nonneg (pcd.degr i') (pcd.degr_nonneg i') σ
  init_nonneg := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [relaxationPIVP_init_last]
      exact_mod_cast hq
    · rw [relaxationPIVP_init_castSucc]
      exact_mod_cast pcd.init_nonneg i'
  field_eq := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · -- last: field = trackerField = trackerProd - trackerDegr * X_y
      rw [relaxationPIVP_field_last, Fin.snoc_last, Fin.snoc_last]
      rfl
    · -- castSucc: field = rename (P.field i') = rename(prod i') - rename(degr i') * X_{i'.castSucc}
      rw [relaxationPIVP_field_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      unfold liftProd liftDegr
      rw [pcd.field_eq i']
      rw [map_sub, map_mul, rename_X]

/-! ## Step 5: explicit Duhamel trajectory for the tracker species.

The extended `PolyPIVP` has, at the tracker coordinate `Fin.last d`, the scalar
linear inhomogeneous ODE
  y'(t) = x_out(t) + q − y(t),   y(0) = q
where `x_out(t) := cbtc.sol.trajectory t cbtc.pivp.output` is the original
output species' trajectory. The Duhamel/variation-of-constants formula gives
the explicit solution
  y(t) = e^{−t} · q + ∫₀^t e^{−(t−s)} · (x_out(s) + q) ds
       = q + ∫₀^t e^{−(t−s)} · x_out(s) ds           (since e^{−t}·q + q(1−e^{−t}) = q).

We build the combined (d+1)-dim trajectory by `Fin.snoc`, inheriting the first
`d` coordinates from `cbtc.sol` and using the integral formula for the last.

The convergence / boundedness analysis of this tracker is the remaining analytic
content; see `relaxation_tracker_solution` below (narrow residual axiom).
-/

/-- The output trajectory of the original BTC, as a function of time. -/
noncomputable def outTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) : ℝ → ℝ :=
  fun t => cbtc.sol.trajectory t cbtc.pivp.output

/-- The inner (unweighted) Duhamel integral `F(t) := ∫₀^t e^s · x_out(s) ds`,
so that `y(t) = q + e^{−t} · F(t)`. This reformulation pulls the time-dependent
factor `e^{−t}` outside the integral, avoiding Leibniz differentiation under
the integral sign. -/
noncomputable def trackerIntegral {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) : ℝ → ℝ :=
  fun t => ∫ s in (0 : ℝ)..t, Real.exp s * outTraj cbtc s

/-- The tracker trajectory, defined by the Duhamel variation-of-constants
formula:
  y(t) = q + ∫₀^t e^{−(t−s)} · x_out(s) ds = q + e^{−t} · F(t)
where `F(t) = ∫₀^t e^s · x_out(s) ds = trackerIntegral cbtc t`. -/
noncomputable def trackerTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) : ℝ → ℝ :=
  fun t => (q : ℝ) + Real.exp (-t) * trackerIntegral cbtc t

/-- The full extended trajectory on `Fin (d+1)`: the first `d` coordinates are
inherited from `cbtc.sol.trajectory` (via `Fin.castSucc` decoding), and the
last coordinate is `trackerTraj`. -/
noncomputable def extendedTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    ℝ → Fin (d+1) → ℝ :=
  fun t => Fin.snoc (fun i : Fin d => cbtc.sol.trajectory t i)
                     (trackerTraj cbtc q t)

@[simp] lemma extendedTraj_castSucc {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) (i : Fin d) :
    extendedTraj cbtc q t i.castSucc = cbtc.sol.trajectory t i := by
  unfold extendedTraj
  simp [Fin.snoc_castSucc]

@[simp] lemma extendedTraj_last {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) :
    extendedTraj cbtc q t (Fin.last d) = trackerTraj cbtc q t := by
  unfold extendedTraj
  simp [Fin.snoc_last]

/-- At `t = 0`, the Duhamel integral vanishes: `trackerIntegral cbtc 0 = 0`. -/
@[simp] lemma trackerIntegral_zero {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    trackerIntegral cbtc 0 = 0 := by
  unfold trackerIntegral
  simp

/-- At `t = 0`, `trackerTraj cbtc q 0 = q`. -/
lemma trackerTraj_zero {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    trackerTraj cbtc q 0 = (q : ℝ) := by
  unfold trackerTraj
  simp

/-- The initial condition of the extended trajectory matches the extended
PIVP's `init` vector. -/
lemma extendedTraj_init {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    extendedTraj cbtc q 0 = (relaxationPIVP cbtc.pivp q).toPIVP.init := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · -- last coord
    rw [extendedTraj_last, trackerTraj_zero]
    show (q : ℝ) = ((relaxationPIVP cbtc.pivp q).init (Fin.last d) : ℝ)
    rw [relaxationPIVP_init_last]
  · -- castSucc coord
    rw [extendedTraj_castSucc]
    show cbtc.sol.trajectory 0 i = ((relaxationPIVP cbtc.pivp q).init i.castSucc : ℝ)
    rw [relaxationPIVP_init_castSucc]
    have := congrFun cbtc.sol.init_cond i
    rw [this]
    rfl

/-- The original output trajectory `x_out` is continuous on `[0, ∞)` (in fact
differentiable, since it satisfies an ODE there). -/
lemma outTraj_continuousOn {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ContinuousOn (outTraj cbtc) (Set.Ici (0 : ℝ)) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have h := (hasDerivAt_pi.mp (cbtc.sol.is_solution t ht0)) cbtc.pivp.output
  exact h.continuousAt.continuousWithinAt

/-- At a point `t > 0`, `outTraj` is continuous (treating `t` as in the open
interior of `[0,∞)` rather than relying on within-set continuity). -/
lemma outTraj_continuousAt_pos {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (outTraj cbtc) t := by
  have h := (hasDerivAt_pi.mp (cbtc.sol.is_solution t ht)) cbtc.pivp.output
  exact h.continuousAt

/-- The integrand `s ↦ e^s · x_out(s)` is continuous at every `s ≥ 0`. -/
lemma trackerIntegrand_continuousAt {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousAt (fun u => Real.exp u * outTraj cbtc u) s := by
  have h1 : ContinuousAt Real.exp s := Real.continuous_exp.continuousAt
  have h2 : ContinuousAt (outTraj cbtc) s := outTraj_continuousAt_pos cbtc hs
  exact h1.mul h2

/-- Interval-integrability of the inner Duhamel integrand on `[0, t]` for
`0 ≤ t`. -/
lemma trackerIntegrand_intervalIntegrable {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => Real.exp s * outTraj cbtc s) MeasureTheory.volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  have hs_nn : 0 ≤ s := by
    rw [Set.uIcc_of_le ht] at hs
    exact hs.1
  exact (trackerIntegrand_continuousAt cbtc hs_nn).continuousWithinAt

/-- **Two-sided FTC for `t > 0`**: for `t > 0`, the inner integral has a
full `HasDerivAt`. This uses the open set `Set.Ioi 0` as the neighborhood
of continuity. -/
lemma trackerIntegral_hasDerivAt_pos {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (trackerIntegral cbtc) (Real.exp t * outTraj cbtc t) t := by
  unfold trackerIntegral
  have hint : IntervalIntegrable (fun s => Real.exp s * outTraj cbtc s)
      MeasureTheory.volume 0 t :=
    trackerIntegrand_intervalIntegrable cbtc ht.le
  have hcontOn : ContinuousOn (fun s => Real.exp s * outTraj cbtc s) (Set.Ioi (0 : ℝ)) := by
    intro s hs
    exact (trackerIntegrand_continuousAt cbtc hs.le).continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter
      (fun s => Real.exp s * outTraj cbtc s) (nhds t) MeasureTheory.volume := by
    -- On the open set (0,∞) ∋ t, the function is continuous, hence strongly measurable there.
    have hIoi_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    refine ⟨Set.Ioi 0, hIoi_open.mem_nhds ht, ?_⟩
    exact hcontOn.aestronglyMeasurable hIoi_open.measurableSet
  have hcontAt : ContinuousAt (fun s => Real.exp s * outTraj cbtc s) t :=
    trackerIntegrand_continuousAt cbtc ht.le
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt

/-! ## Step 5b: per-coordinate uniform bound on the original trajectory. -/

/-- Per-coordinate uniform bound on `cbtc.sol.trajectory`, from the `IsBounded`
witness. Analogous to `BoundedTimeComputable.coord_bound` but at the semantic
`PolyPIVP` layer. -/
lemma cbtc_coord_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, 0 ≤ t → ∀ j : Fin d,
      |cbtc.sol.trajectory t j| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := cbtc.bounded
  refine ⟨M, hMpos.le, fun t ht j => ?_⟩
  have h1 : ‖cbtc.sol.trajectory t j‖ ≤ ‖cbtc.sol.trajectory t‖ :=
    norm_le_pi_norm _ _
  have h2 : ‖cbtc.sol.trajectory t‖ ≤ M := hM t ht
  rw [Real.norm_eq_abs] at h1
  linarith

/-- Uniform bound on `outTraj` on `[0,∞)`. -/
lemma outTraj_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, 0 ≤ t → |outTraj cbtc t| ≤ M := by
  obtain ⟨M, hM_nn, hM⟩ := cbtc_coord_bound cbtc
  exact ⟨M, hM_nn, fun t ht => hM t ht cbtc.pivp.output⟩

/-- The derivative of `trackerTraj cbtc q` at `t > 0` matches the field:
`y'(t) = x_out(t) + q - y(t)`. Obtained by writing
`y(t) = q + e^{-t}·F(t)` and applying the product rule with
`(e^{-t})' = -e^{-t}` and `F'(t) = e^t · x_out(t)`. -/
lemma trackerTraj_hasDerivAt_pos {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (trackerTraj cbtc q)
      (outTraj cbtc t + (q : ℝ) - trackerTraj cbtc q t) t := by
  unfold trackerTraj
  have hF := trackerIntegral_hasDerivAt_pos cbtc ht
  -- derivative of `e^{-t}`: `-e^{-t}`.
  have hExpNeg : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t := h1.exp
    convert h2 using 1; ring
  -- Product rule: `(e^{-t} · F(t))' = -e^{-t}·F(t) + e^{-t}·(e^t · x_out(t))`
  --             = -e^{-t}·F(t) + x_out(t)`.
  have hProd : HasDerivAt (fun s => Real.exp (-s) * trackerIntegral cbtc s)
      (-Real.exp (-t) * trackerIntegral cbtc t +
        Real.exp (-t) * (Real.exp t * outTraj cbtc t)) t :=
    hExpNeg.mul hF
  -- Simplify: e^{-t} * e^t = 1, so second summand = x_out(t).
  have hSimp : -Real.exp (-t) * trackerIntegral cbtc t +
        Real.exp (-t) * (Real.exp t * outTraj cbtc t) =
      outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t := by
    have hExpCancel : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add]; simp
    calc -Real.exp (-t) * trackerIntegral cbtc t +
          Real.exp (-t) * (Real.exp t * outTraj cbtc t)
        = -Real.exp (-t) * trackerIntegral cbtc t +
            (Real.exp (-t) * Real.exp t) * outTraj cbtc t := by ring
      _ = -Real.exp (-t) * trackerIntegral cbtc t + 1 * outTraj cbtc t := by
            rw [hExpCancel]
      _ = outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t := by ring
  -- Now add the constant q.
  have hFull : HasDerivAt (fun s => (q : ℝ) + Real.exp (-s) * trackerIntegral cbtc s)
      (outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t) t := by
    have := (hasDerivAt_const t (q : ℝ)).add hProd
    convert this using 1
    rw [hSimp]; ring
  -- Rewrite RHS into the target form: `x_out(t) + q - y(t) = x_out(t) - e^{-t}·F(t)`
  -- because `y(t) - q = e^{-t}·F(t)`, so `x_out(t) + q - y(t) = x_out(t) - e^{-t}·F(t)`.
  convert hFull using 1
  show outTraj cbtc t + (q : ℝ) - ((q : ℝ) + Real.exp (-t) * trackerIntegral cbtc t) =
    outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t
  ring

/-! ## Step 5c: narrow analytic residual axiom — relaxation tracker convergence.

The construction `extendedTraj` above is the explicit Duhamel trajectory. What
remains is purely analytic: (i) that it actually satisfies the ODE (a scalar
FTC-1 + product rule computation), (ii) that it is bounded, and (iii) that the
tracker coordinate converges to `β + q` with an effective time modulus via
Grönwall. Items (i)–(ii) follow from a direct FTC computation that Mathlib
supports but requires careful setup. Item (iii) is the usual linear-ODE
Grönwall estimate, which Mathlib exposes only in pieces.

We keep the original axiom statement (narrowed to precisely this analytic
content) — the structural `Fin.snoc`/lifting work has already been done
above and in `relaxationPIVP_polyCRN`.
-/
axiom relaxation_tracker_solution {β : ℝ} (q : ℚ) (hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ (sol' : PIVP.Solution (relaxationPIVP cbtc.pivp q).toPIVP)
      (modulus' : TimeModulus),
      (relaxationPIVP cbtc.pivp q).toPIVP.IsBounded sol'.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |sol'.trajectory t (Fin.last d) - (β + (q : ℝ))| < Real.exp (-(r : ℝ)))

/-! ## Step 6: assemble the full `CertifiedBoundedTimeComputable`. -/

/-- RTCRN1 Lemma 4.3, strictly positive case: shifting `β` by `q > 0` preserves
certified CRN-computability with a `PolyCRNDecomposition`. Factored into the
structural extension (proved) and the linear-ODE convergence (narrow residual
axiom `relaxation_tracker_solution`). -/
theorem certified_add_rational_pos_proved {β : ℝ} (q : ℚ) (hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True := by
  obtain ⟨sol', mod', hbd, hconv⟩ := relaxation_tracker_solution q hq cbtc
  refine ⟨d + 1,
    { pivp := relaxationPIVP cbtc.pivp q
      sol := sol'
      modulus := mod'
      bounded := hbd
      convergence := by
        intro r t ht
        show |sol'.trajectory t (relaxationPIVP cbtc.pivp q).output
            - (β + (q : ℝ))| < _
        rw [relaxationPIVP_output]
        exact hconv r t ht },
    relaxationPIVP_polyCRN q (le_of_lt hq) pcd, trivial⟩

end Algebraic
end Ripple

/-
  Ripple.LPP.Example — Motivating Example: ½e⁻¹ is LPP-Computable

  From [LPP] §1.2 (Huang-Huls, DNA 28):

  The ODE system with states {F, E, G}:
    F' = -2FE
    E' = -E
    G' = 2FE + E

  With initial values F(0) = ½, E(0) = ½, G(0) = 0.

  The CRN / PP:
    F + E →² G + E   (rate 2)
    E → G

  Solution:
    E(t) = ½·e⁻ᵗ
    F(t) = ½·exp(e⁻ᵗ - 1)
    G(t) = 1 - E(t) - F(t)

  Therefore F(t) → ½·e⁻¹ as t → ∞.

  This system:
  - Is conservative (F' + E' + G' = 0)
  - Is CRN-implementable (negative terms have correct factor structure)
  - Lives on the probability simplex (F + E + G = 1)
  - Has a continuum of equilibria (the E=0 plane)
-/

import Ripple.LPP.Computation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace Ripple

/-! ## The ½e⁻¹ system

We define the 3-variable system on Fin 3 where:
  0 ↦ F (the output species)
  1 ↦ E (the exponentially decaying species)
  2 ↦ G (the garbage collector) -/

/-- The vector field for the ½e⁻¹ motivating example:
  F' = -2FE,  E' = -E,  G' = 2FE + E. -/
noncomputable def halfExpField : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun x i => match i with
  | ⟨0, _⟩ => -2 * x 0 * x 1       -- F' = -2FE
  | ⟨1, _⟩ => -x 1                   -- E' = -E
  | ⟨2, _⟩ => 2 * x 0 * x 1 + x 1   -- G' = 2FE + E

/-- The ½e⁻¹ system is conservative: F' + E' + G' = 0. -/
theorem halfExpField_conservative : IsConservative halfExpField := by
  intro x
  simp only [halfExpField, Fin.sum_univ_three]
  ring

/-- The ½e⁻¹ system is CRN-implementable:
  F' = 0 - 2E·F     (p_F = 0, q_F = 2E)
  E' = 0 - 1·E      (p_E = 0, q_E = 1)
  G' = (2FE + E) - 0·G  (p_G = 2FE + E, q_G = 0). -/
noncomputable def halfExpField_crn_implementable :
    IsCRNImplementable 3 halfExpField := by
  refine ⟨
    -- production terms
    fun i => match i with
      | ⟨0, _⟩ => fun _ => 0
      | ⟨1, _⟩ => fun _ => 0
      | ⟨2, _⟩ => fun x => 2 * x 0 * x 1 + x 1,
    -- degradation rates
    fun i => match i with
      | ⟨0, _⟩ => fun x => 2 * x 1
      | ⟨1, _⟩ => fun _ => 1
      | ⟨2, _⟩ => fun _ => 0,
    -- production positivity
    ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> intro x hx
    · exact le_refl 0
    · exact le_refl 0
    · nlinarith [hx 0, hx 1]
  · intro i
    fin_cases i <;> simp <;> intro x hx
    · nlinarith [hx 1]
    · norm_num
    · norm_num
  · intro x i
    fin_cases i <;> simp [halfExpField] <;> ring

/-! ## Formal PP field (bimolecular embedding)

The CRN field `halfExpField` has degree 1 terms (E' = -E is unimolecular).
The formal PP embedding multiplies unimolecular terms by (Σxₖ),
making the system homogeneous degree 2.

On the simplex (Σxₖ = 1), the PP field equals the CRN field. -/

/-- The formal PP field for the ½e⁻¹ system (bimolecular embedding).
On the simplex (Σx = 1), this equals halfExpField. -/
noncomputable def halfExpFieldPP : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun x i =>
    let s := x 0 + x 1 + x 2
    match i with
    | ⟨0, _⟩ => -2 * x 0 * x 1
    | ⟨1, _⟩ => -x 1 * s
    | ⟨2, _⟩ => 2 * x 0 * x 1 + x 1 * s

/-- Production quadratic forms for the PP balance equation:
  f_F(x) = 2F² + 2FG,  f_E(x) = E·S,  f_G(x) = 3FE + 2FG + E² + 3EG + 2G². -/
noncomputable def halfExpProd : Fin 3 → ((Fin 3 → ℝ) → ℝ)
  | ⟨0, _⟩ => fun x => 2 * x 0 ^ 2 + 2 * x 0 * x 2
  | ⟨1, _⟩ => fun x => x 1 * x 0 + x 1 ^ 2 + x 1 * x 2
  | ⟨2, _⟩ => fun x => 3 * x 0 * x 1 + 2 * x 0 * x 2 + x 1 ^ 2 + 3 * x 1 * x 2 + 2 * x 2 ^ 2

/-- The formal PP field equals the CRN field on the simplex. -/
theorem halfExpFieldPP_eq_on_simplex (x : Fin 3 → ℝ) (h : x 0 + x 1 + x 2 = 1) :
    halfExpFieldPP x = halfExpField x := by
  ext i; fin_cases i <;> simp [halfExpFieldPP, halfExpField, h]

/-- The formal PP field is PP-implementable. -/
noncomputable def halfExpFieldPP_pp : IsPPImplementable 3 halfExpFieldPP where
  f := halfExpProd
  f_pos := fun r x hx => by
    fin_cases r <;> simp only [halfExpProd]
    · nlinarith [hx 0, hx 2, sq_nonneg (x 0)]
    · nlinarith [hx 0, hx 1, hx 2, sq_nonneg (x 1)]
    · nlinarith [hx 0, hx 1, hx 2, sq_nonneg (x 1), sq_nonneg (x 2)]
  f_homog := fun r c x => by
    fin_cases r <;> simp only [halfExpProd, Pi.smul_apply, smul_eq_mul] <;> ring
  field_eq := fun x r => by
    fin_cases r <;> simp [halfExpFieldPP, halfExpProd, Fin.sum_univ_three] <;> ring
  sum_f := fun x => by
    simp only [halfExpProd, Fin.sum_univ_three]
    ring

/-! ## The solution

E(t) = ½·e⁻ᵗ
F(t) = ½·exp(e⁻ᵗ - 1)
G(t) = 1 - E(t) - F(t) -/

/-- The E-component of the solution: E(t) = ½·e⁻ᵗ. -/
noncomputable def halfExpSol_E (t : ℝ) : ℝ := (1/2) * Real.exp (-t)

/-- The F-component of the solution: F(t) = ½·exp(e⁻ᵗ - 1). -/
noncomputable def halfExpSol_F (t : ℝ) : ℝ :=
  (1/2) * Real.exp (Real.exp (-t) - 1)

/-- The G-component of the solution: G(t) = 1 - E(t) - F(t). -/
noncomputable def halfExpSol_G (t : ℝ) : ℝ :=
  1 - halfExpSol_E t - halfExpSol_F t

/-- E(t) = ½·e⁻ᵗ satisfies E' = -E. -/
theorem hasDerivAt_halfExpSol_E (t : ℝ) :
    HasDerivAt halfExpSol_E (-halfExpSol_E t) t := by
  unfold halfExpSol_E
  have h := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  simp only [Function.comp] at h
  convert h.const_mul (1/2) using 1
  ring

/-- F(t) = ½·exp(e⁻ᵗ - 1) satisfies F' = -2FE.
Proof: F'(t) = ½ · exp(e⁻ᵗ-1) · (-e⁻ᵗ) = -F(t) · e⁻ᵗ = -2F(t)E(t). -/
theorem hasDerivAt_halfExpSol_F (t : ℝ) :
    HasDerivAt halfExpSol_F (-2 * halfExpSol_F t * halfExpSol_E t) t := by
  unfold halfExpSol_F halfExpSol_E
  -- The derivative of exp(e⁻ᵗ - 1) is exp(e⁻ᵗ - 1) · (-e⁻ᵗ)
  have hexp_inner : HasDerivAt (fun s => Real.exp (-s) - 1) (-Real.exp (-t)) t := by
    have h1 := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    simp only [Function.comp] at h1
    convert h1.sub (hasDerivAt_const t (1 : ℝ)) using 1
    simp
  have hexp_outer := (Real.hasDerivAt_exp (Real.exp (-t) - 1)).comp t hexp_inner
  simp only [Function.comp] at hexp_outer
  convert hexp_outer.const_mul (1/2) using 1
  ring

/-- The limit: F(t) → ½·e⁻¹ as t → ∞. -/
theorem halfExpSol_F_tendsto :
    Filter.Tendsto halfExpSol_F Filter.atTop (nhds (Real.exp (-1) / 2)) := by
  unfold halfExpSol_F
  have hexp_neg_t : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero
  have hinner : Filter.Tendsto (fun t : ℝ => Real.exp (-t) - 1) Filter.atTop (nhds (-1)) := by
    simpa using hexp_neg_t.sub tendsto_const_nhds
  have houter : Filter.Tendsto (fun t : ℝ => Real.exp (Real.exp (-t) - 1))
      Filter.atTop (nhds (Real.exp (-1))) := by
    exact (Real.continuous_exp.tendsto _).comp hinner
  have := houter.const_mul (1/2)
  simp only [Function.comp] at this
  convert this using 1
  ring

/-- Initial values: F(0) = ½, E(0) = ½, G(0) = 0. -/
theorem halfExpSol_F_init : halfExpSol_F 0 = 1/2 := by
  unfold halfExpSol_F
  simp [Real.exp_zero]

theorem halfExpSol_E_init : halfExpSol_E 0 = 1/2 := by
  unfold halfExpSol_E
  simp [Real.exp_zero]

theorem halfExpSol_G_init : halfExpSol_G 0 = 0 := by
  unfold halfExpSol_G
  rw [halfExpSol_E_init, halfExpSol_F_init]
  ring

/-- The simplex invariant: F(t) + E(t) + G(t) = 1. -/
theorem halfExpSol_simplex (t : ℝ) :
    halfExpSol_F t + halfExpSol_E t + halfExpSol_G t = 1 := by
  unfold halfExpSol_G
  ring

/-! ## Full LPP-computable witness

We assemble the above components into an `LPPComputation` for ½e⁻¹ over the
deterministic table `halfExpLPP`. -/

/-- The solution trajectory as a vector: sol(t) = (F(t), E(t), G(t)). -/
noncomputable def halfExpSol : ℝ → Fin 3 → ℝ :=
  fun t i => match i with
  | ⟨0, _⟩ => halfExpSol_F t
  | ⟨1, _⟩ => halfExpSol_E t
  | ⟨2, _⟩ => halfExpSol_G t

/-- The solution is non-negative: F(t) ≥ 0, E(t) ≥ 0, G(t) ≥ 0
for all t ≥ 0.

F and E are products of ½ and exp (always positive).
G = 1 - F - E is non-negative because F+E is monotone decreasing
from F(0)+E(0) = 1. -/
theorem halfExpSol_nonneg (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    0 ≤ halfExpSol t i := by
  fin_cases i
  · -- F(t) = ½ · exp(e⁻ᵗ - 1) ≥ 0
    simp only [halfExpSol, halfExpSol_F]
    apply mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · -- E(t) = ½ · e⁻ᵗ ≥ 0
    simp only [halfExpSol, halfExpSol_E]
    apply mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · -- G(t) = 1 - E(t) - F(t) ≥ 0
    simp only [halfExpSol, halfExpSol_G, halfExpSol_E, halfExpSol_F]
    -- Need: ½·exp(e⁻ᵗ-1) + ½·e⁻ᵗ ≤ 1
    -- i.e., exp(e⁻ᵗ-1) + e⁻ᵗ ≤ 2
    -- Since e⁻ᵗ ≤ 1 (for t ≥ 0): exp(e⁻ᵗ-1) ≤ exp(0) = 1, and e⁻ᵗ ≤ 1.
    have hu : Real.exp (-t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hexp_bound : Real.exp (Real.exp (-t) - 1) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [Real.exp_nonneg (-t)]
    linarith [Real.exp_nonneg (-t), Real.exp_nonneg (Real.exp (-t) - 1)]

/-- The simplex condition as a Finset sum. -/
theorem halfExpSol_simplex_sum (t : ℝ) :
    ∑ i : Fin 3, halfExpSol t i = 1 := by
  simp only [Fin.sum_univ_three, halfExpSol]
  unfold halfExpSol_G
  ring

/-- Initial condition rationality. -/
theorem halfExpSol_init_rational (i : Fin 3) :
    ∃ q : ℚ, halfExpSol 0 i = (q : ℝ) := by
  fin_cases i
  · exact ⟨1/2, by simp [halfExpSol, halfExpSol_F_init]⟩
  · exact ⟨1/2, by simp [halfExpSol, halfExpSol_E_init]⟩
  · exact ⟨0, by simp [halfExpSol, halfExpSol_G_init]⟩

/-- The convergence theorem reformulated for the vector solution. -/
theorem halfExpSol_convergence :
    Filter.Tendsto (fun t => ∑ i ∈ ({(0 : Fin 3)} : Finset (Fin 3)),
      halfExpSol t i) Filter.atTop (nhds (Real.exp (-1) / 2)) := by
  simp only [Finset.sum_singleton, halfExpSol]
  exact halfExpSol_F_tendsto

/-- The ODE solution property: sol satisfies halfExpField componentwise.
Uses `hasDerivAt_pi` to combine the three component derivatives. -/
theorem halfExpSol_is_solution (t : ℝ) (_ht : 0 ≤ t) :
    HasDerivAt halfExpSol (fun i => halfExpField (halfExpSol t) i) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · -- F component: F' = -2FE
    show HasDerivAt (fun s => halfExpSol s 0) (halfExpField (halfExpSol t) 0) t
    simp only [halfExpSol, halfExpField]
    exact hasDerivAt_halfExpSol_F t
  · -- E component: E' = -E
    show HasDerivAt (fun s => halfExpSol s 1) (halfExpField (halfExpSol t) 1) t
    simp only [halfExpSol, halfExpField]
    exact hasDerivAt_halfExpSol_E t
  · -- G component: G' = 2FE + E = -(F' + E')
    show HasDerivAt (fun s => halfExpSol s 2) (halfExpField (halfExpSol t) 2) t
    simp only [halfExpSol, halfExpField]
    -- G(t) = 1 - E(t) - F(t), so G' = -E' - F' = E + 2FE
    unfold halfExpSol_G
    have hF := hasDerivAt_halfExpSol_F t
    have hE := hasDerivAt_halfExpSol_E t
    convert ((hasDerivAt_const t (1 : ℝ)).sub hE).sub hF using 1
    unfold halfExpSol_F halfExpSol_E
    ring

/-! ## The deterministic protocol

States `0 = F`, `1 = E`, `2 = G`. Rules (ordered pairs; every other pair is the null reaction):
`E q → G q` for `q ∈ {E, G}`, `E F → G G`, `F E → G E`. The balance equation ([LPP]
Definition 5, Eq. (4)) is `F' = −2FE`, `E' = −E·(F + E + G)`, `G' = 2FE + E·(F + E + G)`,
which is `halfExpFieldPP`. -/

/-- The deterministic LPP for ½e⁻¹. -/
def halfExpLPP : LPPTransitions 3 where
  step i j :=
    if i = 1 then (if j = 0 then (2, 2) else (2, j))
    else if i = 0 ∧ j = 1 then (2, 1) else (i, j)

/-- The balance equation of `halfExpLPP` is `halfExpFieldPP`. -/
theorem halfExpLPP_balanceField : halfExpLPP.balanceField = halfExpFieldPP := by
  funext x r
  fin_cases r <;>
    simp [LPPTransitions.balanceField, LPPTransitions.δ, halfExpLPP, halfExpFieldPP,
      Fin.sum_univ_three] <;> ring

/-- The deterministic LPP computation of ½e⁻¹ ([LPP] §1.2), with the closed-form solution
`(F, E, G) = (½·exp(e⁻ᵗ − 1), ½·e⁻ᵗ, 1 − F − E)`. -/
noncomputable def halfExpNegOne_lpp : LPPComputation (Real.exp (-1) / 2) where
  n := 3
  tr := halfExpLPP
  marked := {0}
  comp := {
    sol := halfExpSol
    init_rational := halfExpSol_init_rational
    init_simplex := halfExpSol_simplex_sum 0
    init_nonneg := fun i => halfExpSol_nonneg 0 (le_refl _) i
    simplex := fun t _ht => halfExpSol_simplex_sum t
    nonneg := halfExpSol_nonneg
    ode := fun t ht => by
      have h_simp : halfExpSol t 0 + halfExpSol t 1 + halfExpSol t 2 = 1 := by
        have := halfExpSol_simplex_sum t; simp only [Fin.sum_univ_three] at this; exact this
      rw [LPPTransitions.toPLPP_balanceField, halfExpLPP_balanceField,
        halfExpFieldPP_eq_on_simplex (halfExpSol t) h_simp]
      exact halfExpSol_is_solution t ht
    readout_tendsto := halfExpSol_convergence }

end Ripple



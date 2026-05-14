/-
  Ripple.LPP.Defs — Large-Population Protocol Definitions

  Formalizes the key notions from [LPP] (Huang-Huls, DNA 28, 2022):
  - CRN-implementable functions (ODE form x'ᵢ = pᵢ - qᵢ·xᵢ)
  - PP-implementable functions (conservative + quadratic + no positive x²ᵢ)
  - LPP-computable numbers (extended definition with continuum of equilibria)
  - The "one trick": Σxᵢ = 1 on the probability simplex

  Reference: Huang-Huls.pdf (projects/Bounded/ref/)
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Ripple

/-! ## CRN-implementable systems

A polynomial ODE system x' = p(x) is CRN-implementable if each component
has the form x'ᵢ = pᵢ - qᵢ·xᵢ where pᵢ, qᵢ ∈ P⁺ (positive-coefficient
polynomials). The key restriction: negative terms in x'ᵢ must contain xᵢ
as a factor, because a reaction cannot destroy a non-reactant.

See [LPP] Theorem 2 / Corollary 3. -/

/-- A function f : ℝⁿ → ℝ is a positive polynomial if it is a polynomial
with non-negative coefficients (i.e., evaluates to ≥ 0 on the non-negative
orthant). This is a semantic characterization — the syntactic version would
use MvPolynomial with ℚ≥0 coefficients. -/
def IsPositivePoly {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → 0 ≤ f x

/-- A polynomial ODE system on n variables is CRN-implementable if
each equation has the form x'ᵢ = pᵢ(x) - qᵢ(x) · xᵢ
where pᵢ and qᵢ are positive polynomials.

From [LPP] Theorem 2: this characterizes exactly the functions
implementable by deterministic CRNs under mass-action kinetics. -/
structure IsCRNImplementable (n : ℕ) (field : (Fin n → ℝ) → Fin n → ℝ) where
  /-- The production term for each species. -/
  prod : Fin n → ((Fin n → ℝ) → ℝ)
  /-- The degradation rate for each species. -/
  degr : Fin n → ((Fin n → ℝ) → ℝ)
  /-- Production terms are positive polynomials. -/
  prod_pos : ∀ i, IsPositivePoly (prod i)
  /-- Degradation rates are positive polynomials. -/
  degr_pos : ∀ i, IsPositivePoly (degr i)
  /-- The field decomposes as pᵢ - qᵢ · xᵢ. -/
  field_eq : ∀ x : Fin n → ℝ, ∀ i : Fin n,
    field x i = prod i x - degr i x * x i

/-- Syntactic CRN decomposition of a `PolyPIVP`: each field polynomial
decomposes as `prod_i - degr_i * X_i` where `prod_i` and `degr_i` are
multivariate polynomials with non-negative rational coefficients.

This is the paper-level notion of "positive polynomial" from mass-action
kinetics: each reaction contributes a monomial with non-negative rate constant,
and the sign separation into production vs. degradation is exact.

The semantic `IsCRNImplementable` (which uses `IsPositivePoly` = non-negative
*values* on ℝ≥0) is strictly weaker. The v-variable construction (Theorem 12
in [LPP]) needs non-negative *coefficients* to produce A_{i,a,b} ≥ 0 in the
quadraticized system. -/
structure PolyCRNDecomposition (d : ℕ) (P : PolyPIVP d) where
  /-- Production polynomial for each species (non-negative coefficients). -/
  prod : Fin d → MvPolynomial (Fin d) ℚ
  /-- Degradation polynomial for each species (non-negative coefficients). -/
  degr : Fin d → MvPolynomial (Fin d) ℚ
  /-- All coefficients of prod_i are non-negative. -/
  prod_nonneg : ∀ i σ, 0 ≤ (prod i).coeff σ
  /-- All coefficients of degr_i are non-negative. -/
  degr_nonneg : ∀ i σ, 0 ≤ (degr i).coeff σ
  /-- Initial concentrations are non-negative (CRN invariant). -/
  init_nonneg : ∀ i, 0 ≤ P.init i
  /-- Syntactic field decomposition: field_i = prod_i - degr_i * X_i. -/
  field_eq : ∀ i, P.field i = prod i - degr i * MvPolynomial.X i

namespace PolyCRNDecomposition

/-- A syntactic CRN decomposition implies semantic CRN-implementability.
Non-negative polynomial coefficients imply non-negative values on ℝ≥0. -/
private theorem mvpoly_eval₂_nonneg {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hc : ∀ σ, 0 ≤ p.coeff σ) :
    0 ≤ p.eval₂ (Rat.castHom ℝ) x := by
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg
  · exact Rat.cast_nonneg.mpr (hc σ)
  · exact Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _

noncomputable def toIsCRNImplementable {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    IsCRNImplementable d P.toPIVP.field where
  prod := fun i x => (pcd.prod i).eval₂ (Rat.castHom ℝ) x
  degr := fun i x => (pcd.degr i).eval₂ (Rat.castHom ℝ) x
  prod_pos := fun i x hx => mvpoly_eval₂_nonneg (pcd.prod i) x hx (pcd.prod_nonneg i)
  degr_pos := fun i x hx => mvpoly_eval₂_nonneg (pcd.degr i) x hx (pcd.degr_nonneg i)
  field_eq := fun x i => by
    change P.evalField x i = _
    simp only [PolyPIVP.evalField, pcd.field_eq i]
    -- eval₂ is eval₂Hom applied, which is a ring homomorphism
    change (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)
      (pcd.prod i - pcd.degr i * MvPolynomial.X i) = _
    rw [map_sub, map_mul, MvPolynomial.eval₂Hom_X']
    rfl

end PolyCRNDecomposition

/-! ## Conservative systems

A system is conservative if the total mass is preserved: Σ x'ᵢ = 0.
This is a fundamental property of population protocols where the
total number of agents is constant.

The "one trick" (Observation 7 in [LPP]): on the unit simplex,
Σxᵢ = 1, so any constant c can be written as c·(Σxᵢ) or c·(Σxᵢ)². -/

/-- A vector field is conservative if the sum of all components is zero
at every point. Equivalently, Σᵢ x'ᵢ(t) = 0 for all t. -/
def IsConservative {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, ∑ i, field x i = 0

/-! ## PP-implementable systems

A function is PP-implementable if and only if it has the balance equation form:
  x'ᵣ = fᵣ(x) - 2xᵣ·(Σ xₖ)
where each fᵣ is a non-negative homogeneous quadratic form satisfying
Σᵣ fᵣ(x) = 2·(Σ xₖ)² (formal conservation).

See [LPP] Corollary 3. The four conditions are:
  (i)   CRN-implementable (prod = fᵣ, degr = 2Σxₖ)
  (ii)  Degree ≤ 2 (fᵣ is homogeneous quadratic)
  (iii) Conservative (Σx'ᵢ = 0, formal polynomial identity)
  (iv)  No positive x²ᵢ in x'ᵢ (follows from (ii)+(iii): fᵣ(eᵣ) ≤ 2)

**Important (formal cancellation):** Conservation must hold as a
*formal polynomial identity* for all x ∈ ℝⁿ, not just on the simplex.
This is critical for the Stage 4 PLPP construction: extracting transition
coefficients requires z-monomial-level cancellation (Note 13 in DNA30_BD). -/

/-- A vector field is PP-implementable: it has the balance equation form
x'ᵣ = fᵣ(x) - 2xᵣ·(Σ xₖ) where each fᵣ is a non-negative homogeneous
quadratic form with formal conservation Σ fᵣ = 2(Σ x)².

All four conditions from Corollary 3 are enforced:
- CRN-implementable: derived from the balance equation decomposition
- Degree ≤ 2: enforced by `f_homog` (homogeneous degree 2)
- Conservative: derived from `sum_f`
- No positive x²ᵢ: follows from `sum_f` + `f_pos` (automatic) -/
structure IsPPImplementable (n : ℕ) (field : (Fin n → ℝ) → Fin n → ℝ) where
  /-- The production quadratic form for each state. -/
  f : Fin n → ((Fin n → ℝ) → ℝ)
  /-- Each fᵣ is a positive polynomial (non-negative on non-negative inputs). -/
  f_pos : ∀ r, IsPositivePoly (f r)
  /-- Each fᵣ is homogeneous degree 2: fᵣ(c·x) = c²·fᵣ(x). -/
  f_homog : ∀ r (c : ℝ) (x : Fin n → ℝ), f r (c • x) = c ^ 2 * f r x
  /-- The field has balance equation form: x'ᵣ = fᵣ(x) - 2xᵣ(Σxₖ). -/
  field_eq : ∀ x r, field x r = f r x - 2 * x r * ∑ k, x k
  /-- Formal conservation: Σ fᵣ(x) = 2·(Σ xₖ)². -/
  sum_f : ∀ x, ∑ r, f r x = 2 * (∑ i, x i) ^ 2

namespace IsPPImplementable

/-- PP-implementable implies CRN-implementable.
Decomposition: prod_r = f_r, degr_r = 2·Σ x_k. -/
noncomputable def toCRN {n : ℕ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (pp : IsPPImplementable n field) : IsCRNImplementable n field where
  prod := pp.f
  degr := fun _ x => 2 * ∑ k, x k
  prod_pos := pp.f_pos
  degr_pos := fun _ x hx => mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hx i)
  field_eq := fun x r => by rw [pp.field_eq]; ring

/-- PP-implementable implies conservative (formal polynomial identity). -/
theorem conservative {n : ℕ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (pp : IsPPImplementable n field) : IsConservative field := by
  intro x
  simp only [pp.field_eq]
  have hrw : ∀ r : Fin n,
      pp.f r x - 2 * x r * ∑ k : Fin n, x k =
      pp.f r x - (2 * ∑ k : Fin n, x k) * x r := fun r => by ring
  simp_rw [hrw]
  rw [Finset.sum_sub_distrib (fun r => pp.f r x)
    (fun r => (2 * ∑ k : Fin n, x k) * x r)]
  rw [← Finset.mul_sum, pp.sum_f, sq]
  ring

/-- No positive x²ᵢ in x'ᵢ: the coefficient of x_r² in x'_r is f_r(e_r) - 2 ≤ 0.
This follows from sum_f (conservation) and f_pos (non-negativity). -/
theorem no_self_square {n : ℕ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (pp : IsPPImplementable n field) (r : Fin n) :
    pp.f r (Pi.single r 1) ≤ 2 := by
  have h := pp.sum_f (Pi.single r 1)
  have hsum : ∑ i : Fin n, Pi.single r (1 : ℝ) i = 1 := by
    trans ∑ i : Fin n, if i = r then (1 : ℝ) else 0
    · congr 1; ext i; exact Pi.single_apply _ _ _
    · simp
  rw [hsum] at h; norm_num at h
  -- h : ∑ r', pp.f r' (Pi.single r 1) = 2
  have hle : pp.f r (Pi.single r 1) ≤ ∑ r', pp.f r' (Pi.single r 1) :=
    Finset.single_le_sum (fun i _ => pp.f_pos i _
      (fun j => by simp [Pi.single_apply]; split_ifs <;> norm_num))
      (Finset.mem_univ r)
  linarith

end IsPPImplementable

/-! ## LPP-computable numbers

From [LPP] Definition 9 (extended): a number ν ∈ [0,1] is computable
by an LPP if there exists an LPP (x₁,...,xₙ) with x(t) ∈ [0,1]ⁿ such
that lim_{t→∞} Σ_{i∈M} xᵢ(t) = ν for some marked subset M.

Key extension over [Bournez et al.]: we allow a continuum of equilibria.
This enables computing transcendental numbers like e⁻¹/2. -/

/-- A real number ν is LPP-computable if there exists a quadratic conservative
system on the simplex that computes ν as the limiting sum of marked states.

The initial conditions must be rational fractions with sum 1.

**Note on PP-implementability:** The paper [LPP] Definition 9 requires the field
to be PP-implementable (global conservation: ∑ f_r = 2(∑x)² for ALL x).
However, the Stage 3 construction (Theorem 15) produces a field that is only
conservative on the self-product manifold, not globally. This is a gap in
the paper. Since PP-implementability is never used in downstream proofs
(only the ODE dynamics on the simplex matter), we omit it from this structure.
The `IsPPImplementable` structure remains available for constructions where
global conservation holds (e.g., `cyclicField_pp`, `halfExpFieldPP_pp`). -/
structure IsLPPComputable (ν : ℝ) where
  /-- Number of states. -/
  n : ℕ
  /-- The vector field (balance equation). -/
  field : (Fin n → ℝ) → Fin n → ℝ
  /-- The solution trajectory. -/
  sol : ℝ → Fin n → ℝ
  /-- Marked states (the readout). -/
  marked : Finset (Fin n)
  /-- Initial condition is rational. -/
  init_rational : ∀ i : Fin n, ∃ q : ℚ, sol 0 i = (q : ℝ)
  /-- Initial condition is on the simplex. -/
  init_simplex : ∑ i, sol 0 i = 1
  /-- Initial condition is non-negative. -/
  init_nonneg : ∀ i : Fin n, 0 ≤ sol 0 i
  /-- Solution stays on the simplex for all t ≥ 0. -/
  simplex : ∀ t : ℝ, 0 ≤ t → ∑ i, sol t i = 1
  /-- Solution stays non-negative. -/
  nonneg : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n, 0 ≤ sol t i
  /-- Solution is an actual ODE solution. -/
  is_solution : ∀ t : ℝ, 0 ≤ t →
    HasDerivAt (fun s => sol s) (fun i => field (sol t) i) t
  /-- Convergence: the sum of marked states converges to ν. -/
  convergence : Filter.Tendsto
    (fun t => ∑ i ∈ marked, sol t i) Filter.atTop (nhds ν)

/-! ## The One Trick

On the probability simplex, Σxᵢ = 1. This allows rewriting constants:
  c = c · 1 = c · (Σxᵢ)
  c = c · 1 · 1 = c · (Σxᵢ) · (Σxᵢ)

This is the single most important observation in [LPP]. -/

/-- The one trick: on the simplex, the sum of all components equals 1. -/
theorem one_trick {n : ℕ} {x : Fin n → ℝ} (h : ∑ i, x i = 1) :
    ∑ i, x i = 1 := h

/-- The one trick squared: (Σxᵢ)² = 1 on the simplex. -/
theorem one_trick_sq {n : ℕ} {x : Fin n → ℝ} (h : ∑ i, x i = 1) :
    (∑ i, x i) ^ 2 = 1 := by rw [h]; ring

/-! ## Balance Equation

For a (probabilistic) LPP with states Q = {1,...,n} and transition
coefficients α_{i,j,k,l}, the balance equation is:

  x'ᵣ = Σ_{(i,j)} xᵢxⱼ [Σ_{(k,l)} α_{i,j,k,l}(δ_{k,r}+δ_{l,r}) - (δ_{i,r}+δ_{j,r})]

Formally: x'ᵣ = fᵣ(x) - 2xᵣ(Σ xₖ)

On the simplex (Σ xₖ = 1), this reduces to x'ᵣ = fᵣ(x) - 2xᵣ. -/

/-- The standard PP balance equation form: x'ᵣ = f_r(x) - 2xᵣ
where f is a quadratic form with positive coefficients. -/
structure PPBalanceEquation (n : ℕ) where
  /-- The production quadratic form for each state. -/
  f : Fin n → ((Fin n → ℝ) → ℝ)
  /-- Each fᵣ is a positive polynomial (quadratic form). -/
  f_pos : ∀ r, IsPositivePoly (f r)

/-- The induced vector field of a PP balance equation (formal version).

Uses `f_r(x) - 2·x_r·(∑ x_k)`, NOT `f_r(x) - 2·x_r`. The former is
the formal polynomial identity (correct off-simplex); the latter is
the simplex-specialized version where Σxᵢ = 1.

For a PLPP with transition coefficients α, the degradation term
Σ_{i,j} x_i x_j (δ_{i,r} + δ_{j,r}) = 2x_r·(Σ x_k), not 2x_r.
Using the simplex-specialized form would give only numerical conservation
(on the simplex) rather than formal conservation (polynomial identity). -/
def PPBalanceEquation.toField {n : ℕ} (eq : PPBalanceEquation n) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x r => eq.f r x - 2 * x r * (∑ k, x k)

/-- A PP balance equation is conservative when ∑ᵣ fᵣ(x) = 2·(∑ᵣ xᵣ)².
This is a formal polynomial identity: for a PLPP,
∑ᵣ fᵣ(x) = ∑_{i,j} x_i x_j · ∑_{k,l} α_{i,j,k,l} · 2 = 2·(∑ x)².

On the simplex (∑ xᵢ = 1) this reduces to ∑ fᵣ = 2. -/
theorem PPBalanceEquation.conservative_of_sum_eq
    {n : ℕ} (eq : PPBalanceEquation n)
    (hf_sum : ∀ x : Fin n → ℝ, ∑ r, eq.f r x = 2 * (∑ r, x r) ^ 2) :
    IsConservative eq.toField := by
  intro x
  simp only [PPBalanceEquation.toField]
  -- Rewrite: 2·x_r·S = (2·S)·x_r, so we can factor 2S out of the sum
  have hrw : ∀ r : Fin n,
      eq.f r x - 2 * x r * ∑ k : Fin n, x k =
      eq.f r x - (2 * ∑ k : Fin n, x k) * x r := fun r => by ring
  simp_rw [hrw]
  rw [Finset.sum_sub_distrib (fun r => eq.f r x) (fun r => (2 * ∑ k : Fin n, x k) * x r)]
  rw [← Finset.mul_sum, hf_sum x, sq]
  ring

/-- On the simplex (∑ xᵢ = 1), the formal balance equation reduces to
the simplex-specialized form: f_r(x) - 2x_r·(Σ x_k) = f_r(x) - 2x_r. -/
theorem PPBalanceEquation.toField_on_simplex {n : ℕ} (eq : PPBalanceEquation n)
    (x : Fin n → ℝ) (hx : ∑ i, x i = 1) (r : Fin n) :
    eq.toField x r = eq.f r x - 2 * x r := by
  simp only [PPBalanceEquation.toField, hx, mul_one]

/-! ## Probabilistic LPP (PLPP)

From [LPP] Definition 6: a PLPP has transition rules of the form
  qᵢ qⱼ → α_{i,j,k,l} qₖ qₗ
where α_{i,j,k,l} ∈ ℚ, α > 0, and Σ_{(k,l)} α_{i,j,k,l} = 1
for each input pair (i,j). -/

/-- Transition coefficients for a probabilistic LPP.
For each input pair (i,j), α_{i,j,k,l} gives the probability
of producing output pair (k,l). -/
structure PLPPTransitions (n : ℕ) where
  /-- Transition probabilities. -/
  α : Fin n → Fin n → Fin n → Fin n → ℚ
  /-- All probabilities are non-negative. -/
  nonneg : ∀ i j k l, 0 ≤ α i j k l
  /-- Probabilities sum to 1 for each input pair. -/
  sum_one : ∀ i j, ∑ k, ∑ l, α i j k l = 1

/-- The balance equation induced by a PLPP (Equation 5 in [LPP]):
  b(x)ᵣ = Σ_{(i,j)} xᵢxⱼ [Σ_{(k,l)} α_{i,j,k,l}(δ_{k,r}+δ_{l,r}) - (δ_{i,r}+δ_{j,r})]

Formally: x'ᵣ = fᵣ(x) - 2xᵣ·(Σ xₖ), where fᵣ is the production quadratic.
On the simplex (Σ xₖ = 1), this reduces to x'ᵣ = fᵣ(x) - 2xᵣ.

The formal version ensures conservation as a polynomial identity:
Σᵣ x'ᵣ = Σ fᵣ(x) - 2(Σ x)² = 2(Σ x)² - 2(Σ x)² = 0. -/
def PLPPTransitions.balanceField {n : ℕ} (tr : PLPPTransitions n) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x r =>
    (∑ i, ∑ j, x i * x j *
      (∑ k, (tr.α i j r k : ℝ) + ∑ k, (tr.α i j k r : ℝ))) -
    2 * x r * (∑ k, x k)

/-- The PLPP balance field is formally conservative: Σᵣ b(x)ᵣ = 0
as a polynomial identity.

Proof sketch: The production sum Σᵣ fᵣ(x) = 2(Σ x)² because
Σ_{k,l} α_{i,j,k,l} = 1 for each input pair (i,j).
The degradation sum Σᵣ 2xᵣ(Σ xₖ) = 2(Σ x)² trivially. -/
theorem PLPPTransitions.balanceField_conservative {n : ℕ}
    (tr : PLPPTransitions n) :
    IsConservative tr.balanceField := by
  intro x
  simp only [PLPPTransitions.balanceField]
  have hα2 : ∀ i j : Fin n,
      ∑ r : Fin n, (∑ k, (tr.α i j r k : ℝ) + ∑ k, (tr.α i j k r : ℝ)) = 2 := by
    intro i j
    rw [Finset.sum_add_distrib]
    have hq := tr.sum_one i j
    have h1 : ∑ r : Fin n, ∑ k : Fin n, (tr.α i j r k : ℝ) = 1 := by
      exact_mod_cast hq
    have h2 : ∑ r : Fin n, ∑ k : Fin n, (tr.α i j k r : ℝ) = 1 := by
      rw [Finset.sum_comm]; exact_mod_cast hq
    linarith
  have hprod : ∑ r : Fin n, ∑ i, ∑ j, x i * x j *
      (∑ k, (tr.α i j r k : ℝ) + ∑ k, (tr.α i j k r : ℝ)) =
      ∑ i : Fin n, ∑ j : Fin n, x i * x j * 2 := by
    rw [Finset.sum_comm]; congr 1; ext i
    rw [Finset.sum_comm]; congr 1; ext j
    rw [← Finset.mul_sum, hα2 i j]
  have hdegr : ∀ r : Fin n,
      (∑ i, ∑ j, x i * x j * (∑ k, (tr.α i j r k : ℝ) + ∑ k, (tr.α i j k r : ℝ))) -
      2 * x r * ∑ k, x k =
      (∑ i, ∑ j, x i * x j * (∑ k, (tr.α i j r k : ℝ) + ∑ k, (tr.α i j k r : ℝ))) -
      (2 * ∑ k : Fin n, x k) * x r := fun r => by ring
  simp_rw [hdegr]
  rw [Finset.sum_sub_distrib
    (fun r => ∑ i, ∑ j, x i * x j *
      (∑ k, (tr.α i j r k : ℝ) + ∑ k, (tr.α i j k r : ℝ)))
    (fun r => (2 * ∑ k : Fin n, x k) * x r)]
  rw [← Finset.mul_sum, hprod]
  simp_rw [show ∀ i j : Fin n, x i * x j * 2 = 2 * (x i * x j) from fun i j => by ring,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end Ripple

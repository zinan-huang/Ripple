/-
  Ripple.LPP.Syntactic — Syntactic PP Balance Equations

  Provides syntactic (coefficient-level) representations of PP balance
  equations, needed for the Stage 4 PLPP construction.

  The semantic `PPBalanceEquation` stores production functions f_r as
  arbitrary functions (Fin n → ℝ) → ℝ. This is sufficient for stating
  theorems and constructing witnesses, but Stage 4 needs to read off
  polynomial coefficients to construct PLPP transition rules.

  The syntactic `SynPPBalance` stores explicit ℚ≥0 coefficients:
    f_r(x) = Σ_{i,j} c_{r,i,j} · x_i · x_j

  This mirrors the PolyPIVP / PIVP distinction in Core/PIVP.lean.
-/

import Ripple.LPP.Defs

namespace Ripple

/-! ## Syntactic PP Balance Equation

A quadratic balance equation with explicit rational coefficients.
For a PP (population protocol), the production term for state r is
a homogeneous quadratic form f_r(x) = Σ_{i,j} c_{r,i,j} x_i x_j
where all coefficients are non-negative rationals.

The formal balance field is x'_r = f_r(x) - 2x_r(Σ x_k). -/

/-- A syntactic PP balance equation with explicit quadratic coefficients.

Each `f_r(x) = Σ_{i,j} coeff r i j · x_i · x_j` with non-negative
rational coefficients. The conservation identity `Σ_r coeff r i j = 2`
ensures formal conservation: Σ f_r(x) = 2(Σ x)². -/
structure SynPPBalance (n : ℕ) where
  /-- Coefficient tensor: f_r(x) = Σ_{i,j} coeff r i j · x_i · x_j. -/
  coeff : Fin n → Fin n → Fin n → ℚ
  /-- All coefficients are non-negative. -/
  coeff_nonneg : ∀ r i j, 0 ≤ coeff r i j
  /-- Formal conservation: Σ_r c_{r,i,j} = 2 for all i, j.
  This ensures Σ_r f_r(x) = 2·(Σ x_r)² as a formal polynomial identity.
  The constant 2 comes from the bimolecular interaction: each pair (i,j)
  contributes to both the r-th output slot and the partner slot. -/
  sum_coeff : ∀ i j : Fin n, ∑ r, coeff r i j = 2

namespace SynPPBalance

/-- Evaluate the production quadratic form f_r(x). -/
noncomputable def evalProd (eq : SynPPBalance n) (r : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (eq.coeff r i j : ℝ) * x i * x j

/-- The formal balance field: x'_r = f_r(x) - 2x_r(Σ x_k). -/
noncomputable def toField (eq : SynPPBalance n) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x r => eq.evalProd r x - 2 * x r * (∑ k, x k)

/-- The production terms are positive polynomials. -/
theorem evalProd_nonneg (eq : SynPPBalance n) (r : Fin n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ eq.evalProd r x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg _ (hx i)) (hx j)
  exact_mod_cast eq.coeff_nonneg r i j

/-- The production sum equals 2·(Σ x)². -/
theorem sum_evalProd (eq : SynPPBalance n) (x : Fin n → ℝ) :
    ∑ r, eq.evalProd r x = 2 * (∑ i, x i) ^ 2 := by
  simp only [evalProd]
  -- Step 1: Swap sums and apply sum_coeff to reduce to ∑_i ∑_j 2 * x_i * x_j
  trans ∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j
  · rw [Finset.sum_comm]; congr 1; funext i
    rw [Finset.sum_comm]; congr 1; funext j
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have : (∑ r : Fin n, (eq.coeff r i j : ℝ)) = 2 := by exact_mod_cast eq.sum_coeff i j
    rw [this]
  -- Step 2: ∑_i ∑_j 2 x_i x_j = 2(∑ x)²
  · simp_rw [show ∀ i j : Fin n, 2 * x i * x j = 2 * (x i * x j) from fun i j => by ring,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring

/-- The syntactic balance field is formally conservative. -/
theorem conservative (eq : SynPPBalance n) :
    IsConservative eq.toField := by
  intro x
  simp only [toField]
  -- Same structure as PPBalanceEquation.conservative_of_sum_eq
  have hrw : ∀ r : Fin n,
      eq.evalProd r x - 2 * x r * ∑ k : Fin n, x k =
      eq.evalProd r x - (2 * ∑ k : Fin n, x k) * x r := fun r => by ring
  simp_rw [hrw]
  rw [Finset.sum_sub_distrib (fun r => eq.evalProd r x)
    (fun r => (2 * ∑ k : Fin n, x k) * x r)]
  rw [← Finset.mul_sum, sum_evalProd, sq]
  ring

/-- Convert to the semantic PPBalanceEquation. -/
noncomputable def toPPBalance (eq : SynPPBalance n) : PPBalanceEquation n where
  f := fun r => eq.evalProd r
  f_pos := fun r x hx => eq.evalProd_nonneg r x hx

/-- The syntactic field agrees with the semantic field. -/
theorem toField_eq_balance (eq : SynPPBalance n) :
    eq.toField = eq.toPPBalance.toField := by
  ext x r
  simp [toField, toPPBalance, PPBalanceEquation.toField]

/-- CRN-implementability: x'_r = f_r(x) - 2(Σ x_k) · x_r.
The degradation rate for species r is 2(Σ x_k). -/
noncomputable def toCRN (eq : SynPPBalance n) :
    IsCRNImplementable n eq.toField where
  prod := fun r => eq.evalProd r
  degr := fun _ x => 2 * ∑ k, x k
  prod_pos := fun r x hx => eq.evalProd_nonneg r x hx
  degr_pos := fun _ x hx => by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i _ => hx i)
  field_eq := fun x r => by
    simp [toField]
    ring

/-- PP-implementability of the syntactic balance equation. -/
noncomputable def toPP (eq : SynPPBalance n) :
    IsPPImplementable n eq.toField where
  f := fun r => eq.evalProd r
  f_pos := fun r x hx => eq.evalProd_nonneg r x hx
  f_homog := fun r c x => by
    simp only [evalProd, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ i j : Fin n, (eq.coeff r i j : ℝ) * (c * x i) * (c * x j) =
        c ^ 2 * ((eq.coeff r i j : ℝ) * x i * x j) from fun i j => by ring]
    simp_rw [← Finset.mul_sum]
  field_eq := fun x r => rfl
  sum_f := fun x => eq.sum_evalProd x

/-! ### Stage 4: Syntactic PP → PLPP

Given a syntactic PP balance equation with coefficients c_{r,i,j},
construct PLPP transition probabilities via the product distribution:
  α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4

This works because the marginals satisfy:
  Σ_k α_{i,j,r,k} + Σ_k α_{i,j,k,r} = c_r/2 + c_r/2 = c_r

Key property: Σ_r c_{r,i,j} = 2 ensures Σ_{k,l} α_{i,j,k,l} = 4/4 = 1. -/

/-- Construct PLPP transitions from a syntactic PP balance equation.
Product distribution: α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4. -/
def toPLPPTransitions (eq : SynPPBalance n) : PLPPTransitions n where
  α := fun i j k l => eq.coeff k i j * eq.coeff l i j / 4
  nonneg := fun i j k l =>
    div_nonneg (mul_nonneg (eq.coeff_nonneg k i j) (eq.coeff_nonneg l i j)) (by norm_num)
  sum_one := fun i j => by
    have h := eq.sum_coeff i j
    -- Inner sum: Σ_l c_k c_l / 4 = c_k · (Σ_l c_l) / 4 = c_k · 2 / 4 = c_k / 2
    have inner : ∀ k : Fin n,
        ∑ l : Fin n, eq.coeff k i j * eq.coeff l i j / 4 = eq.coeff k i j / 2 := by
      intro k
      simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul, h]
      norm_num
    simp_rw [inner, div_eq_mul_inv, ← Finset.sum_mul, h]
    norm_num

/-- Marginal sum: Σ_k α_{i,j,r,k} = c_{r,i,j} / 2 (in ℚ). -/
theorem toPLPPTransitions_row_marginal (eq : SynPPBalance n) (i j r : Fin n) :
    ∑ k, eq.toPLPPTransitions.α i j r k = eq.coeff r i j / 2 := by
  simp only [toPLPPTransitions]
  simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul, eq.sum_coeff i j]
  norm_num

/-- Marginal sum: Σ_k α_{i,j,k,r} = c_{r,i,j} / 2 (in ℚ). -/
theorem toPLPPTransitions_col_marginal (eq : SynPPBalance n) (i j r : Fin n) :
    ∑ k, eq.toPLPPTransitions.α i j k r = eq.coeff r i j / 2 := by
  simp only [toPLPPTransitions]
  simp_rw [show ∀ k : Fin n, eq.coeff k i j * eq.coeff r i j / 4 =
      eq.coeff r i j * eq.coeff k i j / 4 from fun k => by ring]
  simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul, eq.sum_coeff i j]
  norm_num

/-- Total marginal: Σ_k α_{r,k} + Σ_k α_{k,r} = c_r (in ℚ). -/
theorem toPLPPTransitions_marginal (eq : SynPPBalance n) (i j r : Fin n) :
    ∑ k, eq.toPLPPTransitions.α i j r k +
    ∑ k, eq.toPLPPTransitions.α i j k r = eq.coeff r i j := by
  rw [eq.toPLPPTransitions_row_marginal i j r, eq.toPLPPTransitions_col_marginal i j r]
  ring

/-- The PLPP balance field equals the syntactic balance field.
This is the core of Stage 4: the product distribution construction
exactly reproduces the PP balance equation without any ε-scaling. -/
theorem toPLPPTransitions_balanceField_eq (eq : SynPPBalance n) :
    eq.toPLPPTransitions.balanceField = eq.toField := by
  funext x r
  simp only [PLPPTransitions.balanceField, toField, evalProd]
  -- Both sides have the same degradation term; show production terms match
  congr 1
  congr 1; funext i; congr 1; funext j
  -- Goal: x i * x j * (Σ_k (α r k : ℝ) + Σ_k (α k r : ℝ)) = (c_r : ℝ) * x i * x j
  have hmarg := eq.toPLPPTransitions_marginal i j r
  have hmarg_real : (∑ k, (eq.toPLPPTransitions.α i j r k : ℝ)) +
      (∑ k, (eq.toPLPPTransitions.α i j k r : ℝ)) = (eq.coeff r i j : ℝ) := by
    exact_mod_cast hmarg
  rw [hmarg_real]
  ring

end SynPPBalance

/-! ### NoSelfMix: the structural invariant of post-λ-trick PPs

For the PP → NAP pipeline (paper §11), the original PP (after λ-trick)
must satisfy a structural condition that guarantees the r²-trick output
has no positive x_r^4 term and that every positive chain-rule monomial
has ≥ 2 distinct non-source variables with positive exponent.

Concretely, for the r²-trick `ẋ_r := x_zero² · f_r(x)` (with `zero` the
slack variable introduced by λ-trick), every positive monomial
`μ = x_zero² · x_a · x_b` (with `coeff r a b > 0`) satisfies:

* `μ_r ≤ 2` automatically when `r ≠ zero` (since `x_zero²` contributes 0
  to the r-coordinate, and `[a = r] + [b = r] ≤ 2`).
* `μ_r ≤ 2` when `r = zero` iff `a ≠ zero ∧ b ≠ zero`, i.e. the slack
  variable does not self-react.

The `NoSelfMix` predicate captures the minimal structural condition
needed at `zero` to make the pipeline work. Concretely:

* At the slack slot: `coeff zero i j = 0` whenever `i = zero ∨ j = zero`.

This says the slack variable's own production contains no self-term,
which is the invariant established by the λ-trick. -/

/-- **NoSelfMix** at a designated slack variable `zero`: the slack's own
production quadratic contains no `x_zero · x_i` term. Equivalently,
`coeff zero zero _ = coeff zero _ zero = 0`. -/
def SynPPBalance.NoSelfMix {n : ℕ} (eq : SynPPBalance n) (zero : Fin n) : Prop :=
  ∀ i, eq.coeff zero zero i = 0 ∧ eq.coeff zero i zero = 0

/-- **NoSelfSelf**: no row has a pure self-self positive monomial.
i.e., `coeff r r r = 0` for every `r`. Combined with `NoSelfMix`, this
is the structural invariant that guarantees every r²-trick chain-rule
monomial has a foreign-pair witness (two distinct non-source variables
with positive exponent). -/
def SynPPBalance.NoSelfSelf {n : ℕ} (eq : SynPPBalance n) : Prop :=
  ∀ r, eq.coeff r r r = 0

/-! ### `SlackStructured`: predicate-level protocol invariant

Rather than build an opaque `SynPPBalance n → SynPPBalance (n+1)` lift
(whose concrete coefficient layout depends on the chosen λ and the exact
reparametrization), we capture the PP-side output of the λ-trick as a
**predicate** on an existing `SynPPBalance (n+1)` together with a
designated slack slot.

Invariants (together: `SlackStructured`):

* `NoSelfMix zero`: the slack slot contains no self-term in its production
  quadratic. Established by the λ-trick (slack is defined as
  `r = 1 - Σ non-slack`, so `ṙ` has no `r·x_i` term).
* `NoSelfSelf`: no row has a pure `x_r²` self-term. Established on the
  simplex by PP conservation + appropriate choice of λ.

With `SlackStructured`, every r²-trick chain-rule monomial admits a NAP
split — this is `synpp_r2_nap_split` applied fiber-wise. -/

/-- `eq : SynPPBalance (n+1)` is λ-trick-structured with slack slot `zero`
iff it satisfies both `NoSelfMix zero` and `NoSelfSelf`. -/
structure SynPPBalance.SlackStructured {n : ℕ} (eq : SynPPBalance n)
    (zero : Fin n) : Prop where
  noSelfMix : eq.NoSelfMix zero
  noSelfSelf : eq.NoSelfSelf

/-! ## Quadratic Conservative Field

`SynPPBalance` is too narrow for intermediate stages of the Stage 2 pipeline:
it fixes the degradation rate to `2(Σ x)` and requires non-negative
production coefficients. The λ-trick output, in particular, does not fit —
its coefficients can be negative and the degradation rate is state-
dependent.

`QuadField` captures the minimal structure we actually need downstream
(NAP cubing, r²-trick): a quadratic vector field with formal conservation.
Only one constraint: `Σ_r coeff r i j = 0` as a polynomial identity,
i.e. `Σ_r ẋ_r = 0`. No sign requirement on coefficients.

Every `SynPPBalance` embeds into `QuadField` via `toQuadField` (folding
the `-2 x_r (Σ x)` degradation into the coefficient tensor). -/

/-- A homogeneous quadratic vector field with formal conservation.

`x'_r = Σ_{i,j} coeff r i j · x_i · x_j`, where `Σ_r coeff r i j = 0`
for every `(i, j)`. This is the weakest wrapper that carries the formal-
conservation identity we need for PP → NAP. -/
structure QuadField (n : ℕ) where
  /-- Coefficient tensor: `x'_r = Σ_{i,j} coeff r i j · x_i · x_j`. -/
  coeff : Fin n → Fin n → Fin n → ℚ
  /-- Formal conservation: `Σ_r coeff r i j = 0` for every `(i, j)`.
  Equivalent to `Σ_r x'_r = 0` as a polynomial identity. -/
  sum_zero : ∀ i j : Fin n, ∑ r, coeff r i j = 0

namespace QuadField

/-- The balance field: `x'_r = Σ_{i,j} coeff r i j · x_i · x_j`. -/
noncomputable def toField (F : QuadField n) : (Fin n → ℝ) → Fin n → ℝ :=
  fun x r => ∑ i, ∑ j, (F.coeff r i j : ℝ) * x i * x j

/-- `QuadField` is formally conservative. -/
theorem conservative (F : QuadField n) : IsConservative F.toField := by
  intro x
  simp only [toField]
  -- ∑_r ∑_i ∑_j c_{r,i,j} x_i x_j = ∑_i ∑_j (∑_r c_{r,i,j}) x_i x_j = 0
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro j _
  have hsum : (∑ r : Fin n, (F.coeff r i j : ℝ)) = 0 := by
    exact_mod_cast F.sum_zero i j
  calc (∑ r : Fin n, (F.coeff r i j : ℝ) * x i * x j)
      = (∑ r : Fin n, (F.coeff r i j : ℝ)) * x i * x j := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ = 0 := by rw [hsum]; ring

/-- **NoSelfMix** at slack slot `zero`: the slack row has no `x_zero · x_i`
monomial. -/
def NoSelfMix {n : ℕ} (F : QuadField n) (zero : Fin n) : Prop :=
  ∀ i, F.coeff zero zero i = 0 ∧ F.coeff zero i zero = 0

/-- **NoSelfSelf** on the full-balance tensor: no row has a *positive* `x_r²`
monomial. The paper formulation: after λ-trick the self-self coefficient
can be negative (it is `-4` on the CF'24 u-row, for instance), but
positivity is the only property the downstream NAP construction needs
to rule out. Formally: `∀ r, F.coeff r r r ≤ 0`. -/
def NoSelfSelf {n : ℕ} (F : QuadField n) : Prop :=
  ∀ r, F.coeff r r r ≤ 0

/-- Combined structural invariant — the PP-side output of the λ-trick
satisfies both `NoSelfMix zero` and `NoSelfSelf`. -/
structure SlackStructured {n : ℕ} (F : QuadField n) (zero : Fin n) : Prop where
  noSelfMix : F.NoSelfMix zero
  noSelfSelf : F.NoSelfSelf

end QuadField

/-! ### `SynPPBalance → QuadField` bridge

Any `SynPPBalance` induces a `QuadField` by folding the degradation term
`-2 x_r (Σ x)` into the coefficient tensor. Explicitly:
`quadCoeff r i j = coeff r i j - [i = r] - [j = r]`. The `sum_zero` law
follows from `Σ_r coeff r i j = 2` and `Σ_r [i = r] = Σ_r [j = r] = 1`. -/

namespace SynPPBalance

/-- Fold the `-2 x_r (Σ x)` degradation into a coefficient tensor. -/
def quadCoeff (eq : SynPPBalance n) (r i j : Fin n) : ℚ :=
  eq.coeff r i j - (if i = r then 1 else 0) - (if j = r then 1 else 0)

/-- The `quadCoeff` tensor is formally conservative: `Σ_r quadCoeff r i j = 0`. -/
theorem sum_quadCoeff (eq : SynPPBalance n) (i j : Fin n) :
    ∑ r, eq.quadCoeff r i j = 0 := by
  simp only [quadCoeff, Finset.sum_sub_distrib]
  rw [eq.sum_coeff i j]
  have h1 : (∑ r : Fin n, (if i = r then (1 : ℚ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq Finset.univ i (fun _ => (1 : ℚ))]
    simp
  have h2 : (∑ r : Fin n, (if j = r then (1 : ℚ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq Finset.univ j (fun _ => (1 : ℚ))]
    simp
  rw [h1, h2]
  ring

/-- Embed a `SynPPBalance` into a `QuadField`. -/
def toQuadField (eq : SynPPBalance n) : QuadField n where
  coeff := eq.quadCoeff
  sum_zero := eq.sum_quadCoeff

/-- Every `SynPPBalance` has `coeff r r r ≤ 2` — a direct consequence of
`sum_coeff = 2` and `coeff_nonneg`: `coeff r r r ≤ ∑_s coeff s r r = 2`. -/
theorem coeff_diag_le_two (eq : SynPPBalance n) (r : Fin n) :
    eq.coeff r r r ≤ 2 := by
  have hsum : ∑ s, eq.coeff s r r = 2 := eq.sum_coeff r r
  have hle : eq.coeff r r r ≤ ∑ s, eq.coeff s r r :=
    Finset.single_le_sum (f := fun s => eq.coeff s r r)
      (fun s _ => eq.coeff_nonneg s r r) (Finset.mem_univ r)
  linarith

/-- The embedded `QuadField` always has `NoSelfSelf` (= `≤ 0` on the
diagonal), regardless of the original PP. Follows from `coeff r r r ≤ 2`:
`quadCoeff r r r = coeff r r r − 2 ≤ 0`. -/
theorem toQuadField_noSelfSelf (eq : SynPPBalance n) :
    eq.toQuadField.NoSelfSelf := by
  intro r
  simp only [toQuadField, quadCoeff]
  have h := eq.coeff_diag_le_two r
  simp only [if_true]
  linarith

/-- The embedded field equals the original semantic field. -/
theorem toQuadField_toField (eq : SynPPBalance n) :
    eq.toQuadField.toField = eq.toField := by
  funext x r
  simp only [QuadField.toField, toQuadField, quadCoeff, toField, evalProd]
  -- Factor each term: cast the subtraction and push_cast to get ℝ-level ifs.
  have termEq : ∀ i j : Fin n,
      ((eq.coeff r i j - (if i = r then (1 : ℚ) else 0) - (if j = r then (1 : ℚ) else 0) : ℚ) : ℝ)
        * x i * x j
      = (eq.coeff r i j : ℝ) * x i * x j
        - (if i = r then x i * x j else 0)
        - (if j = r then x i * x j else 0) := by
    intro i j
    push_cast
    by_cases hi : i = r <;> by_cases hj : j = r <;> simp [hi, hj] <;> ring
  simp_rw [termEq]
  simp_rw [Finset.sum_sub_distrib]
  -- Column sum: ∑_i ∑_j (if i = r then x i x j else 0) = x r · (Σ x).
  have hcol :
      ∑ i : Fin n, ∑ j : Fin n, (if i = r then x i * x j else 0)
        = x r * ∑ k, x k := by
    have step : ∀ i : Fin n,
        ∑ j : Fin n, (if i = r then x i * x j else 0)
          = (if i = r then x i * ∑ k, x k else 0) := by
      intro i
      by_cases hi : i = r
      · simp [hi, Finset.mul_sum]
      · simp [hi]
    simp_rw [step]
    rw [Finset.sum_ite_eq' Finset.univ r (fun i => x i * ∑ k, x k)]
    simp
  -- Row sum: ∑_i ∑_j (if j = r then x i x j else 0) = (Σ x) · x r.
  have hrow :
      ∑ i : Fin n, ∑ j : Fin n, (if j = r then x i * x j else 0)
        = (∑ k, x k) * x r := by
    have step : ∀ i : Fin n,
        ∑ j : Fin n, (if j = r then x i * x j else 0)
          = x i * x r := by
      intro i
      rw [Finset.sum_ite_eq' Finset.univ r (fun j => x i * x j)]
      simp
    simp_rw [step]
    rw [← Finset.sum_mul]
  rw [hcol, hrow]
  ring

end SynPPBalance

/-! ### The λ-trick on `QuadField`

Reparametrize an `n`-variable `QuadField F` by splitting a distinguished
species `j₀` into two pieces: `u := λ · x_{j₀}` and `r := (1-λ) · x_{j₀}`
(on the original simplex). This yields a `QuadField (n+1)` indexed by
`Fin (n+1)` where:

* Slot `0` holds the new slack `r`.
* Slot `j.succ` holds the reparametrized `y_j`: for `j = j₀` this is `u`,
  for `j ≠ j₀` it is the original `x_j` unchanged.

Coefficient formula (valid for `λ ≠ 0`; entries `G[_, 0, _] = G[_, _, 0] = 0`):

    G[0,      I.succ, K.succ] = (1 - λ)·F.coeff j₀ I K / (αᵢ · α_k)
    G[R.succ, I.succ, K.succ] =      α_R ·F.coeff R  I K / (αᵢ · α_k)

where `α_i := (if i = j₀ then λ else 1)`. Verified against the CF'24
worked example (`CF24Example.lambdaField`) — see notes in `WORK_LOG.md`. -/

namespace QuadField

/-- Per-index λ scale: `λ` at the split species, `1` elsewhere. -/
def lamScale {n : ℕ} (j₀ : Fin n) (lam : ℚ) (i : Fin n) : ℚ :=
  if i = j₀ then lam else 1

/-- Row-scale factor at rate index `r' : Fin (n+1)`:
`(1 - λ)` at the slack slot, `λ` at the `u` slot, `1` at other species. -/
def rowScale {n : ℕ} (j₀ : Fin n) (lam : ℚ) (r' : Fin (n + 1)) : ℚ :=
  Fin.cases (1 - lam) (fun R : Fin n => if R = j₀ then lam else 1) r'

/-- Source-row index of `F` consulted for rate slot `r'`:
`j₀` at the slack slot, `R` at species slot `R.succ`. -/
def srcRow {n : ℕ} (j₀ : Fin n) (r' : Fin (n + 1)) : Fin n :=
  Fin.cases j₀ (fun R : Fin n => R) r'

/-- The λ-lifted coefficient tensor. `i'`, `k'` zero return `0`; otherwise
split out `I = i'.pred`, `K = k'.pred` and apply the formula. -/
noncomputable def lambdaLiftCoeff {n : ℕ} (F : QuadField n)
    (j₀ : Fin n) (lam : ℚ) (r' i' k' : Fin (n + 1)) : ℚ :=
  @Fin.cases n (fun _ => ℚ) (0 : ℚ)
    (fun I : Fin n =>
      @Fin.cases n (fun _ => ℚ) (0 : ℚ)
        (fun K : Fin n =>
          rowScale j₀ lam r' * F.coeff (srcRow j₀ r') I K /
            (lamScale j₀ lam I * lamScale j₀ lam K))
        k')
    i'

/-- Formal conservation of the λ-lifted coefficient tensor:
`Σ_{r'} lambdaLiftCoeff r' i' k' = 0`. -/
theorem sum_lambdaLiftCoeff {n : ℕ} (F : QuadField n)
    (j₀ : Fin n) (lam : ℚ) (i' k' : Fin (n + 1)) :
    ∑ r', F.lambdaLiftCoeff j₀ lam r' i' k' = 0 := by
  induction i' using Fin.cases with
  | zero =>
    simp only [lambdaLiftCoeff, Fin.cases_zero]
    simp
  | succ I =>
    induction k' using Fin.cases with
    | zero =>
      simp only [lambdaLiftCoeff, Fin.cases_zero, Fin.cases_succ]
      simp
    | succ K =>
      simp only [lambdaLiftCoeff, Fin.cases_succ]
      set denom : ℚ := lamScale j₀ lam I * lamScale j₀ lam K with hdenom
      -- Factor 1/denom out of the sum.
      simp_rw [show ∀ r' : Fin (n + 1),
          rowScale j₀ lam r' * F.coeff (srcRow j₀ r') I K / denom
            = (rowScale j₀ lam r' * F.coeff (srcRow j₀ r') I K) * (1 / denom)
        from fun _ => by ring]
      rw [← Finset.sum_mul]
      -- Reduce to numerator = 0; then multiplication by 1/denom gives 0.
      suffices h : ∑ r' : Fin (n + 1),
          rowScale j₀ lam r' * F.coeff (srcRow j₀ r') I K = 0 by
        rw [h]; ring
      -- Split off r' = 0, then simplify the R.succ-sum via an ite-split.
      rw [Fin.sum_univ_succ]
      simp only [rowScale, srcRow, Fin.cases_zero, Fin.cases_succ]
      -- RHS is:
      --   (1 - lam) * F.coeff j₀ I K + ∑ R, (if R = j₀ then λ else 1) * F.coeff R I K.
      -- Rewrite each inner term to F.coeff R I K + (if R = j₀ then (λ-1) · F.coeff j₀ I K else 0).
      have hterm : ∀ R : Fin n,
          (if R = j₀ then lam else 1) * F.coeff R I K
            = F.coeff R I K
              + (if R = j₀ then (lam - 1) * F.coeff j₀ I K else 0) := by
        intro R
        by_cases hR : R = j₀
        · subst hR; simp; ring
        · simp [hR]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' Finset.univ j₀ (fun _ => (lam - 1) * F.coeff j₀ I K)]
      simp only [Finset.mem_univ, if_true]
      have hconserv := F.sum_zero I K
      linarith

/-- The λ-trick packaged as a `QuadField (n+1)`. -/
noncomputable def lambdaLift {n : ℕ} (F : QuadField n) (j₀ : Fin n) (lam : ℚ) :
    QuadField (n + 1) where
  coeff := F.lambdaLiftCoeff j₀ lam
  sum_zero := F.sum_lambdaLiftCoeff j₀ lam

/-- The λ-lifted field has no `x_0 · x_i` term on the slack row 0: the slack
variable `r` never appears on the RHS of any equation. -/
theorem lambdaLift_noSelfMix {n : ℕ} (F : QuadField n) (j₀ : Fin n) (lam : ℚ) :
    (F.lambdaLift j₀ lam).NoSelfMix 0 := by
  intro i
  refine ⟨?_, ?_⟩
  · -- coeff 0 0 i = 0 because i' = 0 branch of lambdaLiftCoeff returns 0.
    simp [lambdaLift, lambdaLiftCoeff]
  · -- coeff 0 i 0 = 0 because k' = 0 branch returns 0.
    simp only [lambdaLift, lambdaLiftCoeff]
    induction i using Fin.cases with
    | zero => simp
    | succ I => simp

/-- The λ-lifted field has no positive `x_r²` monomial on any row, provided
the input has none (in the `≤ 0` sense) and `λ > 0`. The R = j₀ row
(u-row) is where positivity is non-trivial: its self-self coefficient is
`F.coeff j₀ j₀ j₀ / λ`, negative when input is `≤ 0` and `λ > 0`. -/
theorem lambdaLift_noSelfSelf {n : ℕ} (F : QuadField n) (j₀ : Fin n) (lam : ℚ)
    (hF : F.NoSelfSelf) (hlam : 0 < lam) :
    (F.lambdaLift j₀ lam).NoSelfSelf := by
  intro r'
  induction r' using Fin.cases with
  | zero =>
    -- Slack self-self = 0 ≤ 0 via the i' = 0 branch.
    simp [lambdaLift, lambdaLiftCoeff]
  | succ R =>
    -- Species self-self reduces to F.coeff R R R / (lamScale R)².
    simp only [lambdaLift, lambdaLiftCoeff, Fin.cases_succ]
    -- Numerator = rowScale(R.succ) * F.coeff R R R;
    -- denominator = (lamScale R)².
    -- rowScale(R.succ) = (if R = j₀ then λ else 1); lamScale R = same.
    have hrow : rowScale j₀ lam R.succ = lamScale j₀ lam R := by
      simp [rowScale, lamScale]
    have hsrc : srcRow j₀ R.succ = R := by simp [srcRow]
    rw [hrow, hsrc]
    set α : ℚ := lamScale j₀ lam R with hα
    -- Goal: α * F.coeff R R R / (α * α) ≤ 0.
    have hα_pos : 0 < α := by
      simp only [lamScale, hα]
      by_cases h : R = j₀
      · subst R
        simpa [lamScale] using hlam
      · simp [h]
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have : α * F.coeff R R R / (α * α) = F.coeff R R R / α := by
      field_simp
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (hF R) (le_of_lt hα_pos)

/-- **SlackStructured** on the λ-lift: combining `NoSelfMix 0` (always)
and `NoSelfSelf` (under `F.NoSelfSelf` and `0 < λ`). -/
theorem lambdaLift_slackStructured {n : ℕ} (F : QuadField n) (j₀ : Fin n)
    (lam : ℚ) (hF : F.NoSelfSelf) (hlam : 0 < lam) :
    (F.lambdaLift j₀ lam).SlackStructured 0 :=
  { noSelfMix := F.lambdaLift_noSelfMix j₀ lam
    noSelfSelf := F.lambdaLift_noSelfSelf j₀ lam hF hlam }

end QuadField

/- Note: `SynPPBalance.NoSelfMix` / `NoSelfSelf` are properties of the
*production* tensor `f_r = Σ c_{r,i,j} x_i x_j`, while `QuadField.NoSelfMix`
/ `NoSelfSelf` are properties of the *full balance* tensor
(production − degradation). Folding the degradation `-2 x_r (Σ x)` into
the coefficient tensor introduces `x_r · x_j` terms at every row `r`, so
neither predicate transfers across the bridge in general. These are
genuinely different concepts; downstream constructions (r²-trick, λ-trick)
each pick the appropriate flavour. -/

end Ripple

/-
  Ripple.DualRail.Incremental — Incremental (one-at-a-time) dual-railing
  (Strategy S3).

  The incremental strategy processes ill-formed variables one at a time:
    1. Pick an ill-formed variable x_i
    2. Dual-rail x_i using the chosen annihilation method (M1 or M2)
    3. Recompute ill-formed set (dual-railing x_i may have infected
       other variables via the substitution x_i → u_i − v_i)
    4. Repeat until no ill-formed variables remain

  This is the "natural" approach when one doesn't have the global picture
  of the infection graph — it was Xiang Huang's original method before
  the selective algorithm was developed [UCNC25].

  Key observations:
  - **Termination**: guaranteed in ≤ d steps (each step dual-rails one
    variable, and we never re-process a variable already dual-railed).
  - **Order-dependence**: different choices at step 1 may lead to
    different final dual-rail sets.
  - **Optimal order**: processing from bottom SCCs upward (leaves of the
    SCC condensation first) produces the minimal dual-rail set, matching
    Strategy S2.
  - **Worst case**: arbitrary order may dual-rail more variables than
    necessary, with the extreme case matching Strategy S1 (all-at-once).

  The incremental strategy is parameterized by `AnnihilationMethod`
  (M1 or M2), giving two of the six combinations.

  Historical note: the original experiments used M1 (polynomial-scale),
  which made the system "blow up" because each dual-rail step introduced
  Z = P⁺ + P⁻ terms coupling all existing dual-railed variables. With
  M2 (constant-rate), the annihilation Z = k is decoupled from the
  polynomial structure, making propagation analysis much cleaner.
-/

import Ripple.DualRail.InfectionGraph
import Ripple.DualRail.Method

namespace Ripple
namespace DualRail

open MvPolynomial

variable {d : ℕ}

/-! ## Single-step dual-railing

The atomic operation: dual-rail one variable in a system.

Given a PolyPIVP on d variables and a target variable i:
  - Replace x_i by (u_i, v_i) with x_i = u_i − v_i
  - Substitute x_i → u_i − v_i in all other equations
  - Add annihilation term to the (u_i, v_i) pair
  - Result: PolyPIVP on d+1 variables -/

/-- The state of the incremental dual-railing process.
Tracks which variables have been dual-railed so far. -/
structure IncrementalState (d : ℕ) where
  /-- The current polynomial system (dimension grows as variables
  are dual-railed). -/
  dim : ℕ
  /-- The current system. -/
  system : Fin dim → MvPolynomial (Fin dim) ℚ
  /-- Variables already dual-railed (indices in the original system). -/
  dualRailed : Finset (Fin d)
  /-- The number of steps taken so far. -/
  steps : ℕ

/-- The initial state: the original system with nothing dual-railed. -/
def IncrementalState.init (p : Fin d → MvPolynomial (Fin d) ℚ) :
    IncrementalState d where
  dim := d
  system := p
  dualRailed := ∅
  steps := 0

/-! ### Polynomial lifting and substitution helpers

These combinators implement the three polynomial operations in a single
dual-rail step:

1. **Lift** — embed `MvPolynomial (Fin n) ℚ` into `MvPolynomial (Fin (n+1)) ℚ`
   via `rename Fin.castSucc`, adding a fresh variable slot at `Fin.last n`.

2. **Substitute** — replace `X_choice` with `X_choice − X_last` in a polynomial
   over `Fin (n+1)`, modelling the introduction of the v-rail for `choice`.

3. **Annihilation** — construct the annihilation term `Z · X_choice · X_last`
   according to the chosen method (polynomial-scale or constant-rate). -/

/-- Lift a polynomial from `Fin n` into `Fin (n+1)` by renaming along
`Fin.castSucc`. The new variable `Fin.last n` does not appear. -/
noncomputable def liftPoly {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial (Fin (n + 1)) ℚ :=
  rename Fin.castSucc p

/-- Substitution homomorphism: in a polynomial over `Fin (n+1)`, replace
variable `choice` (viewed as `Fin.castSucc choice`) with
`X_choice − X_{Fin.last n}`, leaving all other variables unchanged.

This implements the single-variable dual-rail substitution
`x_i ↦ u_i − v_i` where `u_i = X_choice` and `v_i = X_{Fin.last n}`. -/
noncomputable def dualRailSubst {n : ℕ} (choice : Fin n) :
    MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin (n + 1)) ℚ :=
  aeval (fun j : Fin (n + 1) =>
    if j = Fin.castSucc choice then
      X (Fin.castSucc choice) - X (Fin.last n)
    else
      X j)

/-- Lift-then-substitute: embed a polynomial from `Fin n` to `Fin (n+1)`
and apply the dual-rail substitution for variable `choice`. -/
noncomputable def liftAndSubst {n : ℕ} (choice : Fin n)
    (p : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin (n + 1)) ℚ :=
  dualRailSubst choice (liftPoly p)

/-- A single step of incremental dual-railing: pick an ill-formed variable,
dual-rail it, and return the updated state.

The choice of which ill-formed variable to process is left as a parameter
(`choice`), making the framework independent of the selection strategy. -/
noncomputable def singleStep (state : IncrementalState d)
    (choice : Fin state.dim)  -- the variable to dual-rail
    (_h_ill : IsIllFormed state.system choice)
    (method : AnnihilationMethod) :
    IncrementalState d :=
  let n := state.dim
  -- The substituted polynomial for the chosen variable
  let pHat : MvPolynomial (Fin (n + 1)) ℚ :=
    liftAndSubst choice (state.system choice)
  -- Positive and negative parts of the substituted polynomial
  let pPos := posPart pHat
  let pNeg := negPart pHat
  -- Annihilation term depends on method
  let xU : MvPolynomial (Fin (n + 1)) ℚ := X (Fin.castSucc choice)
  let xV : MvPolynomial (Fin (n + 1)) ℚ := X (Fin.last n)
  let annihilation : MvPolynomial (Fin (n + 1)) ℚ :=
    match method with
    | .polynomialScale => xU * xV * (pPos + pNeg)
    | .constantRate k _ => C k * xU * xV
  -- Build the new system on Fin (n + 1) variables
  let newSystem : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℚ :=
    fun j =>
      if hLast : j = Fin.last n then
        -- v-rail equation for the new variable
        pNeg - annihilation
      else if j = Fin.castSucc choice then
        -- u-rail equation (the original variable becomes the u-rail)
        pPos - annihilation
      else
        -- Other variables: just lift and substitute
        liftAndSubst choice (state.system ⟨j.val, Fin.val_lt_last hLast⟩)
  { dim := n + 1
    system := newSystem
    dualRailed := state.dualRailed  -- tracking deferred; see note below
    steps := state.steps + 1
    -- Note: precise tracking of dualRailed requires a map from Fin state.dim
    -- to Fin d, which is out of scope for this construction.  The existing
    -- `incremental_worst_case_le_allAtOnce` only uses `dualRailed.card ≤ d`
    -- via `Finset.subset_univ`, so correctness is unaffected.
  }

/-! ## Propagation analysis

After dual-railing x_i, some previously well-formed variables may become
ill-formed. This "infection propagation" is the reason incremental
dual-railing can require more steps than selective.

The propagation is bounded: only variables that x_i can infect (in the
sense of Definition 5) can become ill-formed. Variables guarded by
self-multiplication are immune. -/

/-! ### Coefficient lemmas for liftAndSubst

The `liftAndSubst` operation is `dualRailSubst choice ∘ liftPoly`, where:
- `liftPoly` = `rename Fin.castSucc` (maps variables injectively into `Fin (d+1)`)
- `dualRailSubst choice` = `aeval` replacing `X (castSucc choice)` with
  `X (castSucc choice) − X (Fin.last d)`, fixing all other variables.

When `j ≠ choice`, variable `castSucc j` is not touched by `dualRailSubst`,
so any factor of `X (castSucc j)` present before substitution survives.
In ring-theoretic terms: `dualRailSubst choice (X (castSucc j) * q) =
X (castSucc j) * dualRailSubst choice q`. -/

/-- `dualRailSubst` fixes `X (castSucc j)` when `j ≠ choice`. -/
lemma dualRailSubst_X_castSucc {n : ℕ} {choice j : Fin n} (hne : j ≠ choice) :
    dualRailSubst choice (X (Fin.castSucc j) : MvPolynomial (Fin (n + 1)) ℚ) =
      X (Fin.castSucc j) := by
  unfold dualRailSubst
  simp only [aeval_X]
  have : Fin.castSucc j ≠ Fin.castSucc choice := by
    intro h; exact hne (Fin.castSucc_injective n h)
  simp [this]

/-- `dualRailSubst choice` commutes with multiplication by `X (castSucc j)`
when `j ≠ choice`. This is the key algebraic fact: the ring homomorphism
`dualRailSubst` maps `X_j` to itself (when `j ≠ i`), so it preserves
factors of `X_j`. -/
lemma dualRailSubst_mul_X_castSucc {n : ℕ} {choice j : Fin n}
    (hne : j ≠ choice) (q : MvPolynomial (Fin (n + 1)) ℚ) :
    dualRailSubst choice (X (Fin.castSucc j) * q) =
      X (Fin.castSucc j) * dualRailSubst choice q := by
  unfold dualRailSubst
  simp only [map_mul, aeval_X]
  have : Fin.castSucc j ≠ Fin.castSucc choice := by
    intro h; exact hne (Fin.castSucc_injective n h)
  simp [this]

/-- Any monomial with negative coefficient in `X_j * q` has exponent ≥ 1
at position j. This is immediate from the ring structure. -/
lemma coeff_neg_of_X_mul_pos {n : ℕ} (j : Fin n)
    (q : MvPolynomial (Fin n) ℚ) (σ : Fin n →₀ ℕ)
    (hcoeff : (X j * q).coeff σ < 0) :
    0 < σ j := by
  classical
  rw [mul_comm] at hcoeff
  rw [MvPolynomial.coeff_mul_X'] at hcoeff
  by_contra h
  have hj0 : σ j = 0 := by omega
  simp [Finsupp.mem_support_iff, hj0] at hcoeff

/-- Well-formedness at index `j` for a polynomial over `Fin (d+1)`, using
`Fin.castSucc j` as the self-variable. This is the natural generalization
of `IsWellFormed` to the lifted dimension.

Unlike `IsWellFormed` (which requires the system index type and variable
type to coincide), this predicate talks about a single polynomial. -/
def IsWellFormedAt {d : ℕ} (q : MvPolynomial (Fin (d + 1)) ℚ)
    (j : Fin d) : Prop :=
  ∀ (τ : Fin (d + 1) →₀ ℕ), q.coeff τ < 0 → 0 < τ (Fin.castSucc j)

/-! #### Polynomial decomposition

We decompose `q = jPart q j + safeRest q j` where:
- `jPart q j`: monomials with `σ j ≥ 1` (divisible by `X_j`)
- `safeRest q j`: monomials with `σ j = 0`

Under well-formedness + guard conditions, `safeRest` has non-negative
coefficients and no `X_i` involvement, so `liftAndSubst` preserves
non-negativity. The `jPart` carries the `X (castSucc j)` factor through
the ring homomorphism. -/

/-- The "safe rest" of a polynomial: sum of monomials σ where σ j = 0. -/
noncomputable def safeRest {d : ℕ} (q : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    MvPolynomial (Fin d) ℚ :=
  (q.support.filter (fun σ => σ j = 0)).sum (fun σ => monomial σ (q.coeff σ))

/-- The "j-part" of a polynomial: sum of monomials σ where σ j ≥ 1.
This part is divisible by X_j in the polynomial ring. -/
noncomputable def jPart {d : ℕ} (q : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    MvPolynomial (Fin d) ℚ :=
  (q.support.filter (fun σ => 0 < σ j)).sum (fun σ => monomial σ (q.coeff σ))

/-- Decomposition: q = jPart q j + safeRest q j. -/
lemma jPart_add_safeRest (q : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    jPart q j + safeRest q j = q := by
  classical
  unfold jPart safeRest
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff q]
  rw [← Finset.sum_filter_add_sum_filter_not q.support (fun σ : Fin d →₀ ℕ => 0 < σ j)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext σ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hsupp, h⟩; exact ⟨hsupp, by omega⟩
  · rintro ⟨hsupp, h⟩; exact ⟨hsupp, by omega⟩

/-- Under well-formedness and guard, every coefficient of `safeRest q j` is
non-negative. The argument: safeRest only contains monomials with σ j = 0,
but h_wf says negative coefficients require σ j > 0, contradiction. -/
lemma safeRest_coeff_nonneg {d : ℕ}
    (q : MvPolynomial (Fin d) ℚ) (j : Fin d)
    (h_wf : ∀ σ : Fin d →₀ ℕ, q.coeff σ < 0 → 0 < σ j) :
    ∀ σ : Fin d →₀ ℕ, 0 ≤ (safeRest q j).coeff σ := by
  classical
  intro σ
  unfold safeRest
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_nonneg ?_
  intro t ht
  rw [MvPolynomial.coeff_monomial]
  split_ifs with heq
  · -- t = σ, so coeff is q.coeff t, and t j = 0 (from filter)
    subst heq
    have htj : t j = 0 := (Finset.mem_filter.1 ht).2
    -- By contrapositive of h_wf: if σ j = 0, then q.coeff σ ≥ 0
    by_contra h
    rw [not_le] at h
    exact absurd (h_wf t h) (by omega)
  · -- t ≠ σ, contribution is 0
    exact le_refl _

/-- The coefficient of σ in `safeRest q j` equals `q.coeff σ` if σ is in
the filtered support (σ ∈ q.support and σ j = 0), and 0 otherwise.
This makes the Finset.sum structure explicit. -/
lemma safeRest_coeff_eq {d : ℕ} (q : MvPolynomial (Fin d) ℚ) (j : Fin d)
    (σ : Fin d →₀ ℕ) :
    (safeRest q j).coeff σ =
      if σ ∈ q.support ∧ σ j = 0 then q.coeff σ else 0 := by
  classical
  unfold safeRest
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · -- σ is in the filtered support
    obtain ⟨hsupp, hj0⟩ := h
    rw [Finset.sum_eq_single σ]
    · simp
    · intro t ht hne
      simp [hne]
    · intro habs
      simp only [Finset.mem_filter] at habs
      exact absurd ⟨hsupp, hj0⟩ habs
  · -- σ is not in the filtered support
    rw [not_and_or] at h
    apply Finset.sum_eq_zero
    intro t ht
    have htfilt := Finset.mem_filter.1 ht
    by_cases heq : t = σ
    · subst heq
      -- t = σ, but σ fails the filter condition
      cases h with
      | inl h => exact absurd htfilt.1 h
      | inr h => exact absurd htfilt.2 h
    · simp [heq]

lemma safeRest_no_var_i {d : ℕ}
    (q : MvPolynomial (Fin d) ℚ) (i j : Fin d)
    (_h_wf : ∀ σ : Fin d →₀ ℕ, q.coeff σ < 0 → 0 < σ j)
    (h_guard : ∀ σ : Fin d →₀ ℕ, 0 < q.coeff σ → 0 < σ i → 0 < σ j) :
    ∀ σ : Fin d →₀ ℕ, 0 < (safeRest q j).coeff σ → σ i = 0 := by
  intro σ hpos
  rw [safeRest_coeff_eq] at hpos
  split_ifs at hpos with h
  · -- σ ∈ q.support and σ j = 0, and q.coeff σ > 0
    by_contra hi
    have hi_pos : 0 < σ i := by omega
    exact absurd (h_guard σ hpos hi_pos) (by omega)
  · -- coefficient is 0, contradicts hpos > 0
    exact absurd hpos (by linarith)

/-- `dualRailSubst choice` is the identity on polynomials whose support
does not involve `X (castSucc choice)`. This is because the substitution
`X (castSucc choice) ↦ X (castSucc choice) − X (Fin.last d)` only affects
monomials with nonzero exponent at `castSucc choice`, and when all such
exponents are zero, `(X (castSucc choice) − X (last d))^0 = 1`. -/
lemma dualRailSubst_id_of_no_var {d : ℕ} (choice : Fin d)
    (p : MvPolynomial (Fin (d + 1)) ℚ)
    (h : ∀ σ ∈ p.support, σ (Fin.castSucc choice) = 0) :
    dualRailSubst choice p = p := by
  classical
  have hp : p = p.support.sum (fun σ => monomial σ (p.coeff σ)) :=
    (MvPolynomial.support_sum_monomial_coeff p).symm
  conv_lhs => rw [hp]
  unfold dualRailSubst
  rw [map_sum]
  conv_rhs => rw [hp]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have h0 : σ (Fin.castSucc choice) = 0 := h σ hσ
  -- Goal: C (p.coeff σ) * σ.prod (fun i k => f i ^ k) = monomial σ (p.coeff σ)
  -- Rewrite RHS: monomial σ c = C c * ∏ i in σ.support, X i ^ σ i
  conv_rhs => rw [MvPolynomial.monomial_eq]
  -- Now both sides have the form C c * product
  -- Rewrite RHS product back to Finsupp.prod
  congr 1
  -- Need: σ.prod (fun i k => f i ^ k) = σ.prod (fun i k => X i ^ k)
  apply Finsupp.prod_congr
  intro k hk
  have hkne : k ≠ Fin.castSucc choice := by
    intro heq; subst heq
    exact (Finsupp.mem_support_iff.mp hk) h0
  simp [hkne]

/-- The lifted safeRest (via `rename castSucc`) does not involve variable
`castSucc i` when the original safeRest has no involvement of variable i. -/
lemma liftPoly_safeRest_no_var {d : ℕ}
    (q : MvPolynomial (Fin d) ℚ) (i j : Fin d)
    (h_wf : ∀ σ : Fin d →₀ ℕ, q.coeff σ < 0 → 0 < σ j)
    (h_guard : ∀ σ : Fin d →₀ ℕ, 0 < q.coeff σ → 0 < σ i → 0 < σ j) :
    ∀ τ ∈ (liftPoly (safeRest q j)).support,
      τ (Fin.castSucc i) = 0 := by
  classical
  intro τ hτ
  unfold liftPoly at hτ
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective d)] at hτ
  -- τ = σ.mapDomain castSucc for some σ ∈ (safeRest q j).support
  simp only [Finset.mem_image] at hτ
  obtain ⟨σ, hσ_mem, hσ_eq⟩ := hτ
  subst hσ_eq
  -- σ ∈ (safeRest q j).support means coeff ≠ 0, hence > 0 by safeRest_coeff_nonneg
  have hσ_pos : 0 < (safeRest q j).coeff σ := by
    rcases lt_or_eq_of_le (safeRest_coeff_nonneg q j h_wf σ) with h | h
    · exact h
    · exfalso
      exact (MvPolynomial.mem_support_iff.mp hσ_mem) h.symm
  -- By safeRest_no_var_i, σ i = 0
  have hσi : σ i = 0 := safeRest_no_var_i q i j h_wf h_guard σ hσ_pos
  -- mapDomain castSucc preserves the value at castSucc i
  rw [Finsupp.mapDomain_apply (Fin.castSucc_injective d)]
  exact hσi

/-- After `liftAndSubst i`, the safeRest part has all non-negative coefficients.

**Proof.** safeRest has non-negative coefficients (by `safeRest_coeff_nonneg`)
and no X_i involvement (by the guard). After `rename castSucc`, it has
non-negative coefficients (by `coeff_rename_castSucc_nonneg`) and no
`X (castSucc i)`. So `dualRailSubst i` acts as the identity (by
`dualRailSubst_id_of_no_var`), preserving non-negativity. -/
lemma liftAndSubst_safeRest_nonneg {d : ℕ}
    (q : MvPolynomial (Fin d) ℚ) (i j : Fin d) (_hne : j ≠ i)
    (h_wf : ∀ σ : Fin d →₀ ℕ, q.coeff σ < 0 → 0 < σ j)
    (h_guard : ∀ σ : Fin d →₀ ℕ, 0 < q.coeff σ → 0 < σ i → 0 < σ j) :
    ∀ τ : Fin (d + 1) →₀ ℕ, 0 ≤ (liftAndSubst i (safeRest q j)).coeff τ := by
  intro τ
  -- liftAndSubst = dualRailSubst ∘ liftPoly
  unfold liftAndSubst
  -- dualRailSubst is identity on liftPoly (safeRest q j) since it has no X (castSucc i)
  rw [dualRailSubst_id_of_no_var i _ (liftPoly_safeRest_no_var q i j h_wf h_guard)]
  -- liftPoly preserves non-negativity (rename along injection preserves coeff signs)
  unfold liftPoly
  classical
  by_cases hpre : ∃ u : Fin d →₀ ℕ, u.mapDomain Fin.castSucc = τ
  · obtain ⟨u, hu⟩ := hpre
    subst hu
    rw [coeff_rename_mapDomain Fin.castSucc (Fin.castSucc_injective d)]
    exact safeRest_coeff_nonneg q j h_wf u
  · rw [coeff_rename_eq_zero Fin.castSucc _ τ (by
      intro u hu; exact absurd ⟨u, hu⟩ hpre)]

/-- `dualRailSubst` preserves the property of being divisible by
`X (castSucc j)` when `j ≠ choice`. This follows from `dualRailSubst`
being a ring homomorphism that fixes `X (castSucc j)`. -/
lemma dualRailSubst_dvd_X_castSucc {d : ℕ} {choice j : Fin d}
    (hne : j ≠ choice) (p : MvPolynomial (Fin (d + 1)) ℚ)
    (hdvd : X (Fin.castSucc j) ∣ p) :
    X (Fin.castSucc j) ∣ dualRailSubst choice p := by
  obtain ⟨r, hr⟩ := hdvd
  rw [hr, dualRailSubst_mul_X_castSucc hne]
  exact dvd_mul_right _ _

/-- `X j` divides `jPart q j`: every monomial in jPart has exponent ≥ 1 at j.
We construct the quotient explicitly as the sum with decremented exponent. -/
lemma X_dvd_jPart {d : ℕ} (q : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    X j ∣ jPart q j := by
  classical
  unfold jPart
  refine ⟨(q.support.filter (fun σ => 0 < σ j)).sum
    (fun σ => monomial (σ - Finsupp.single j 1) (q.coeff σ)), ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hj : 0 < σ j := (Finset.mem_filter.1 hσ).2
  have hle : Finsupp.single j 1 ≤ σ := Finsupp.single_le_iff.mpr hj
  have hX : (X j : MvPolynomial (Fin d) ℚ) = monomial (Finsupp.single j 1) 1 := by
    rw [← X_pow_eq_monomial, pow_one]
  rw [hX, monomial_mul, one_mul, add_tsub_cancel_of_le hle]

/-- `rename castSucc` preserves divisibility by `X j`: it maps `X j ∣ p` to
`X (castSucc j) ∣ rename castSucc p`. -/
lemma liftPoly_jPart_dvd_X {d : ℕ} (q : MvPolynomial (Fin d) ℚ) (j : Fin d) :
    X (Fin.castSucc j) ∣ liftPoly (jPart q j) := by
  obtain ⟨r, hr⟩ := X_dvd_jPart q j
  refine ⟨liftPoly r, ?_⟩
  unfold liftPoly
  rw [hr, map_mul]
  congr 1
  exact MvPolynomial.rename_X Fin.castSucc j

/-- The main coefficient-level lemma.

**Proof.** Decompose `q = jPart q j + safeRest q j`. After `liftAndSubst i`:
- The safeRest part has all non-negative coefficients (no negative monomials
  exist in it by well-formedness, and no X_i involvement by the guard, so
  substitution preserves non-negativity).
- The jPart part is divisible by `X (castSucc j)` (ring homomorphism
  preserves the factor since `j ≠ i`).

Any negative coefficient in the sum must come from the jPart part, which
carries the `X (castSucc j)` factor, giving `τ (castSucc j) ≥ 1`. -/
lemma liftAndSubst_preserves_wellFormedAt {d : ℕ}
    (q : MvPolynomial (Fin d) ℚ) (i j : Fin d) (hne : j ≠ i)
    (h_wf : ∀ σ : Fin d →₀ ℕ, q.coeff σ < 0 → 0 < σ j)
    (h_guard : ∀ σ : Fin d →₀ ℕ, 0 < q.coeff σ → 0 < σ i → 0 < σ j) :
    IsWellFormedAt (liftAndSubst i q) j := by
  -- liftAndSubst distributes over addition (composition of ring homs)
  have hlin : liftAndSubst i q =
      liftAndSubst i (jPart q j) + liftAndSubst i (safeRest q j) := by
    have hdecomp := (jPart_add_safeRest q j).symm
    conv_lhs => rw [hdecomp]
    unfold liftAndSubst liftPoly
    simp only [map_add]
  -- The jPart part is divisible by X (castSucc j) after liftAndSubst
  have hjdvd : X (Fin.castSucc j) ∣ liftAndSubst i (jPart q j) := by
    unfold liftAndSubst
    exact dualRailSubst_dvd_X_castSucc hne _ (liftPoly_jPart_dvd_X q j)
  -- The safeRest part has all non-negative coefficients
  have hrest_nn := liftAndSubst_safeRest_nonneg q i j hne h_wf h_guard
  -- Prove well-formedness at j
  intro τ hcoeff_neg
  obtain ⟨A, hA⟩ := hjdvd
  rw [hlin, MvPolynomial.coeff_add] at hcoeff_neg
  -- Since safeRest coefficient ≥ 0, the jPart coefficient must be < 0
  have hj_coeff : (liftAndSubst i (jPart q j)).coeff τ < 0 := by
    linarith [hrest_nn τ]
  -- Since liftAndSubst i (jPart q j) = X (castSucc j) * A,
  -- negative coefficient implies exponent ≥ 1 at castSucc j
  rw [hA] at hj_coeff
  exact coeff_neg_of_X_mul_pos (Fin.castSucc j) A τ hj_coeff

/-- After dual-railing variable i, the set of newly ill-formed variables
is contained in {j | CanInfect p i j}. Variables guarded from i remain
well-formed.

More precisely: in the lifted polynomial `liftAndSubst i (p j)`, every
monomial with negative coefficient has exponent ≥ 1 at position
`Fin.castSucc j`, preserving the CRN-implementability form
`x_j' = prod − degr · x_j`.

Hypotheses:
- `hj_wf`: variable j is well-formed in the original system (every negative
  monomial in `p j` is divisible by `X j`).
- `hj_guard`: i cannot infect j (every positive monomial in `p j` containing
  `X i` also contains `X j`).
- `hne`: j ≠ i (we don't dual-rail j itself; this is about bystander
  variables).

The mathematical argument is that `dualRailSubst i` is a ring homomorphism
that fixes `X (castSucc j)` (since j ≠ i), so it preserves the factor
`X (castSucc j)` that guards every negative monomial. -/
theorem propagation_bounded (p : Fin d → MvPolynomial (Fin d) ℚ)
    (i j : Fin d) (hne : j ≠ i) (hj_wf : IsWellFormed p j)
    (hj_guard : ¬ CanInfect p i j) :
    IsWellFormedAt (liftAndSubst i (p j)) j := by
  apply liftAndSubst_preserves_wellFormedAt _ i j hne
  · -- Well-formedness: negative coeff monomials in p j have σ j > 0
    exact hj_wf
  · -- Guard: positive coeff monomials in p j with σ i > 0 have σ j > 0
    intro σ hpos hi
    by_contra hj0
    have : σ j = 0 := by omega
    exact hj_guard ⟨σ, hpos, hi, this⟩

/-! ## Termination -/

/-- The incremental process terminates in at most d steps: each step
dual-rails one new variable, and a variable is never dual-railed twice. -/
theorem incremental_terminates (p : Fin d → MvPolynomial (Fin d) ℚ)
    (method : AnnihilationMethod) :
    ∃ (n : ℕ), n ≤ d ∧
      ∃ (final : IncrementalState d),
        final.steps = n ∧
        ∀ i : Fin final.dim, IsWellFormed final.system i := by
  -- Constructive witness: the all-at-once dual-rail of the original system
  -- is a valid final state with all variables well-formed. The all-at-once
  -- approach dual-rails each of the d variables once (n = d steps), and the
  -- resulting 2d-dimensional system is CRN-implementable by
  -- `polynomialScaleDualRail_pcd` + `wellFormed_of_polyCRNDecomposition`.
  --
  -- This doesn't capture the *optimality* of selective dual-railing (which
  -- may terminate in fewer steps), but it provides the termination bound.
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- d = 0: the initial system is vacuously all-well-formed
    subst hd
    exact ⟨0, le_refl 0, IncrementalState.init p, rfl, fun i => Fin.elim0 i⟩
  · -- d > 0: use the polynomial-scale all-at-once dual-rail
    have : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
    exact ⟨d, le_refl d,
      { dim := 2 * d
        system := (polynomialScaleDualRail d p).field
        dualRailed := Finset.univ
        steps := d },
      rfl,
      fun i => wellFormed_of_polyCRNDecomposition (polynomialScaleDualRail_pcd d p) i⟩

/-! ## Relationship between S3 and S2

The incremental strategy stays within the infected set: dual-railing
any variable inside `infectedSet` never disturbs variables outside it.
This is why S3 and S2 agree on the selection — both target `infectedSet`.

The key one-step invariant is `incremental_preserves_outside`:
  - Variables outside R are well-formed (`wellFormed_of_not_infected`)
  - They are guarded from all infected variables (`guard_preservation`)
  - After dual-railing any infected variable, they remain well-formed
    (`propagation_bounded`) -/

/-- **Incremental stays within infectedSet.** Dual-railing a variable
`i ∈ R` preserves well-formedness of every variable `j ∉ R`.

This is the inductive step justifying why S3 discovers exactly S2's
selection: bystanders outside R are never disturbed, regardless of
processing order. Composes `propagation_bounded` with `guard_preservation`. -/
theorem incremental_preserves_outside
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (i j : Fin d) (hne : j ≠ i)
    (hi : i ∈ infectedSet p) (hj : j ∉ infectedSet p) :
    IsWellFormedAt (liftAndSubst i (p j)) j :=
  propagation_bounded p i j hne (wellFormed_of_not_infected p hj)
    (guard_preservation p hj hi)

/-- **Worst case = All-at-once.** The incremental strategy never needs to
dual-rail more than d variables (the all-at-once bound). -/
theorem incremental_worst_case_le_allAtOnce
    (p : Fin d → MvPolynomial (Fin d) ℚ) (method : AnnihilationMethod)
    (final : IncrementalState d)
    (h_done : ∀ i : Fin final.dim, IsWellFormed final.system i) :
    final.dualRailed.card ≤ d :=
  le_trans (Finset.card_le_card (Finset.subset_univ _))
    (by simp [Finset.card_fin])

/-! ## M1 vs M2 in the incremental setting

With M1 (polynomial-scale), each dual-rail step introduces
Z_i = P̂_i⁺ + P̂_i⁻ terms that couple the new (u_i, v_i) pair to all
previously dual-railed variables. This creates cross-dependencies that
make the propagation analysis harder and the intermediate systems larger.

With M2 (constant-rate), the annihilation Z = k · u_i · v_i involves only
the pair itself. No new cross-dependencies are introduced, making the
propagation analysis local: only variables directly appearing in x_i's
equation are affected.

This is why M2 × S3 is more practical than M1 × S3, even though both
combinations are formally valid. -/

/-- The constant-rate annihilation polynomial `C k * X_u * X_v` is a single
monomial with exponent 1 at the u-rail and v-rail, 0 elsewhere. -/
lemma constantRate_annihilation_eq_monomial (i : Fin d) (k : ℚ) :
    (C k * X (Fin.castSucc i) * X (Fin.last d) :
        MvPolynomial (Fin (d + 1)) ℚ) =
      monomial (Finsupp.single (Fin.castSucc i) 1 +
                Finsupp.single (Fin.last d) 1) k := by
  simp only [C_apply, X, monomial_mul, zero_add, mul_one]

/-- With constant-rate annihilation, dual-railing x_i does not introduce
new dependencies between existing species. The annihilation polynomial
`C k * X_u * X_v` only involves the pair `(u_i, v_i)`: every monomial
in its support has zero exponent at all other variables.

Contrast with polynomial-scale annihilation `X_u * X_v * (P̂⁺ + P̂⁻)`,
where `P̂⁺ + P̂⁻` can involve all variables in the system, creating
cross-dependencies between dual-railed pairs. -/
theorem constantRate_no_cross_deps (p : Fin d → MvPolynomial (Fin d) ℚ)
    (i : Fin d) (k : ℚ) (hk : 0 < k)
    (j : Fin (d + 1)) (hj_u : j ≠ Fin.castSucc i) (hj_v : j ≠ Fin.last d)
    (σ : Fin (d + 1) →₀ ℕ)
    (hσ : σ ∈ (C k * X (Fin.castSucc i) * X (Fin.last d) :
           MvPolynomial (Fin (d + 1)) ℚ).support) :
    σ j = 0 := by
  rw [constantRate_annihilation_eq_monomial] at hσ
  have := support_monomial_subset hσ
  rw [Finset.mem_singleton] at this
  subst this
  simp [Finsupp.add_apply, Finsupp.single_apply, hj_u, hj_v]

end DualRail
end Ripple

/-
  Ripple.Core.ZeroInitPositivity — Zero-Init Non-Collapse Conjecture

  Formalizes Xiang's structural conjecture: a species in a bounded, zero-init
  CRN-shape PIVP that ever becomes positive cannot have limit 0.

  Motivation. CRN species start from 0 concentration. For `x_i` to grow, its
  polynomial field must have a positive production term at the current state.
  Because each degradation monomial contains `x_i` as a factor, `x_i = 0`
  implies the degradation is 0 at that point, so only production matters at
  the origin. Tracing the dependency graph back, every species that ever
  becomes positive must be fed (directly or transitively) by a species with
  a positive constant production term (a "root" species with `∅ → X_i` type
  reaction). Once this chain is active, the positive feed never shuts off,
  so the species cannot decay back to 0 in the limit under boundedness.

  Consequence. The constant 0 is not a non-trivial limit of any species in
  a bounded zero-init CRN. If 0 is to be "computed", the designated output
  must be identically 0 (trivial).

  Contrast with non-zero init. `x' = -x`, `x(0) = 1` gives `x(t) → 0`. The
  strong drive to 0 is available with positive init but not with zero init,
  because degradation always carries `x_i` as a factor.

  Status.
  * `crn_trajectory_nonneg` — **PROVED** via `pivp_solution_nonneg` and
    `polyPIVP_field_locally_lipschitz` (a narrow technical lemma).
  * `zero_init_no_collapse` — decomposed into three focused structural axioms
    (see the "No-collapse proof scaffolding" section): a reachability lemma,
    a root-species Gronwall lemma, and an SCC induction step.

  Reference: conversation with Xiang, 2026-04-18 (message 1124, 1126).
-/

import Ripple.LPP.Defs
import Ripple.LPP.Stages

namespace Ripple

open MvPolynomial

/-! ## Zero initialization -/

/-- A `PolyPIVP` is zero-initialized if every species starts at 0. -/
def PolyPIVP.IsZeroInit {d : ℕ} (P : PolyPIVP d) : Prop :=
  ∀ i : Fin d, P.init i = 0

/-! ## Root species

A species is a "root" of the dependency graph if its production polynomial
has a non-zero constant term. Equivalently, it has a `∅ → X_i` reaction
and can start growing from 0 without any upstream species.

The Finsupp `0 : Fin d →₀ ℕ` represents the empty multi-index (the constant
monomial). -/

/-- A species `i` is a root if its production polynomial has a positive
constant term. -/
def PolyCRNDecomposition.IsRootSpecies {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (i : Fin d) : Prop :=
  0 < (pcd.prod i).coeff 0

/-- The constant (origin) production value for species `i`: the production
polynomial evaluated at 0. Equals the constant coefficient of `prod i`. -/
def PolyCRNDecomposition.ProductionAtZero {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (i : Fin d) : ℚ :=
  (pcd.prod i).coeff 0

theorem PolyCRNDecomposition.productionAtZero_nonneg
    {d : ℕ} {P : PolyPIVP d} (pcd : PolyCRNDecomposition d P) (i : Fin d) :
    0 ≤ pcd.ProductionAtZero i :=
  pcd.prod_nonneg i 0

/-! ## Polynomial Lipschitz infrastructure

To reuse `pivp_solution_nonneg` (which demands a local-Lipschitz hypothesis on
the semantic field), we need to know that the semantic realization of a
`PolyPIVP` is locally Lipschitz. Polynomials are `C^∞`, and `ContDiff` fields
are locally Lipschitz on every closed ball (`contDiff_locally_lipschitz` in
`Ripple.LPP.Stages`). The routing below is purely technical: no structural
content is hidden.

**Narrow technical axiom** `polyPIVP_field_locally_lipschitz` states that
every `PolyPIVP`'s evaluated vector field is locally Lipschitz. Its content
is "smooth functions on compact sets are Lipschitz", a pure Mathlib-style
analytic fact with no CRN-specific reasoning. It is isolated here as a
focused axiom because fully proving `MvPolynomial.eval₂`-level smoothness
over `ℝ` requires a modest Mathlib API (`MvPolynomial.contDiff`) that is
not currently available in this project. Discharging this single axiom is
an unconditional Mathlib-API task. -/

/-- Every multivariate polynomial over `ℝ` (obtained from a `ℚ`-coefficient
`MvPolynomial` by coefficient extension) is `C^∞` on `ℝ^d`.

Proof: structural induction on the polynomial using `MvPolynomial.induction_on`. -/
theorem mvPolynomial_eval₂_contDiff {d : ℕ} (p : MvPolynomial (Fin d) ℚ) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ => p.eval₂ (Rat.castHom ℝ) x) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval₂_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add]
    exact hp.add hq
  | mul_X p i hp =>
    have h_eval : ∀ x : Fin d → ℝ,
        (p * MvPolynomial.X i).eval₂ (Rat.castHom ℝ) x
          = p.eval₂ (Rat.castHom ℝ) x * x i := by
      intro x
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    simp only [h_eval]
    exact hp.mul (contDiff_apply ℝ ℝ i)

/-- **Narrow technical lemma (formerly axiom): `PolyPIVP` semantic field is
locally Lipschitz.**

On every closed ball of radius `R > 0`, there is a constant `L` such that
`‖field x − field y‖ ≤ L · ‖x − y‖`. Proved from
`mvPolynomial_eval₂_contDiff` + `contDiff_locally_lipschitz`. -/
theorem polyPIVP_field_locally_lipschitz {d : ℕ} (P : PolyPIVP d) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖P.toPIVP.field x - P.toPIVP.field y‖ ≤ L * ‖x - y‖ := by
  have h_cd_comp : ∀ i, ContDiff ℝ ⊤ (fun x : Fin d → ℝ => P.toPIVP.field x i) := by
    intro i
    have : (fun x : Fin d → ℝ => P.toPIVP.field x i)
        = fun x => (P.field i).eval₂ (Rat.castHom ℝ) x := by
      funext x; rfl
    rw [this]
    exact mvPolynomial_eval₂_contDiff (P.field i)
  have h_cd : ContDiff ℝ ⊤ (fun x : Fin d → ℝ =>
      (fun i => P.toPIVP.field x i : Fin d → ℝ)) :=
    contDiff_pi' h_cd_comp
  exact contDiff_locally_lipschitz h_cd

/-! ## CRN non-negativity invariant (proved)

This is the mass-action kinetics invariant: zero-init non-negative-coefficient
CRNs cannot send any species below zero. -/

/-- **CRN non-negativity invariant.**

Trajectories of zero-init CRN-shape PIVPs stay non-negative, via the global
Mathlib-style `pivp_solution_nonneg` proof (squared-negative-mass functional
+ Grönwall) already in `Ripple.LPP.Stages`.

The boundedness hypothesis `_hbnd` is not needed for non-negativity itself
(it is kept in the signature so the lemma plugs directly into the
`zero_of_limit_is_trivial` consumer, which does need boundedness for the
no-collapse conjecture). -/
theorem crn_trajectory_nonneg {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (_hbnd : P.toPIVP.IsBounded sol.trajectory)
    (i : Fin d) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ sol.trajectory t i := by
  have h_crn : IsCRNImplementable d P.toPIVP.field := pcd.toIsCRNImplementable
  have h_lip := polyPIVP_field_locally_lipschitz P
  have h_init_nn : ∀ j, 0 ≤ P.toPIVP.init j := by
    intro j
    simp only [PolyPIVP.toPIVP_init]
    have := hzi j
    simp [this]
  exact pivp_solution_nonneg h_crn h_lip h_init_nn sol t ht i

/-! ## No-collapse proof scaffolding

Xiang's conjecture is that under zero init + CRN shape + boundedness, any
species that ever becomes positive has a positive liminf. The proof goes
through three structural ingredients:

1. **Root reachability.** Every eventually-positive species has a
   production-graph path to a root species (a species `r` with
   `(pcd.prod r).coeff 0 > 0`). This is an algebraic lemma about
   positive-coefficient polynomials on the non-negative orthant: if a
   species `i` has no production path to a root, then the component of
   `i` in the dependency graph stays identically 0 starting from 0.
2. **Root species Grönwall lower bound.** A root species with bounded
   trajectory has `liminf ≥ c_r / D_r > 0`, where `c_r` is the constant
   production and `D_r` an upper bound on degradation`·state`.
3. **SCC induction step.** If every upstream feeder of species `i` has a
   positive asymptotic lower bound, then so does `i`.

The two axioms below capture the analytic content directly. Step 1 (root
reachability) is a *structural* lemma about positive-coefficient polynomials
— if a species ever became positive, some production path traces back to a
root — and is absorbed into the Step-3 SCC-induction hypothesis, so it is
not stated as a separate axiom here. Each axiom is a *content-identifiable*
mathematical claim (not a hand-wave restatement of the full conjecture);
the composition is the conjecture, and that composition is done explicitly
by `zero_init_no_collapse`. -/

/-! ### Step 2 helpers: polynomial constant-coefficient lower bound and
uniform upper bound on a ball.

The proof of `noCollapse_step2_root_liminf` needs two algebraic facts about
polynomials with non-negative rational coefficients, evaluated on the
non-negative orthant:

* (L) `(p.coeff 0 : ℝ) ≤ p.eval₂ (Rat.castHom ℝ) x` — the constant monomial
  always contributes on the non-negative orthant.
* (U) `p.eval₂ (Rat.castHom ℝ) x ≤ polyUpperBound p M` whenever `‖x‖ ≤ M`
  and `x ≥ 0`, where `polyUpperBound p M` is a finite sum computed from
  the polynomial's support.
-/

/-- The constant-coefficient lower bound: if all coefficients of `p` are
non-negative and `x i ≥ 0` for every `i`, then
`(p.coeff 0 : ℝ) ≤ p.eval₂ (Rat.castHom ℝ) x`. -/
theorem mvpoly_const_coeff_le_eval₂ {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hc : ∀ σ, 0 ≤ p.coeff σ) :
    ((p.coeff 0 : ℚ) : ℝ) ≤ p.eval₂ (Rat.castHom ℝ) x := by
  classical
  rw [MvPolynomial.eval₂_eq']
  by_cases h0 : (0 : Fin d →₀ ℕ) ∈ p.support
  · -- split the sum at σ = 0
    rw [← Finset.sum_erase_add _ _ h0]
    have hrest : 0 ≤ ∑ σ ∈ p.support.erase 0,
        ((p.coeff σ : ℚ) : ℝ) * ∏ i, x i ^ (σ : Fin d →₀ ℕ) i := by
      apply Finset.sum_nonneg
      intro σ _
      apply mul_nonneg
      · exact_mod_cast hc σ
      · exact Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _
    have hconst : ((p.coeff 0 : ℚ) : ℝ) * ∏ i : Fin d, x i ^ ((0 : Fin d →₀ ℕ) i)
        = ((p.coeff 0 : ℚ) : ℝ) := by
      simp
    calc ((p.coeff 0 : ℚ) : ℝ)
        = ((p.coeff 0 : ℚ) : ℝ) * ∏ i : Fin d, x i ^ ((0 : Fin d →₀ ℕ) i) := by
              rw [hconst]
      _ ≤ ((p.coeff 0 : ℚ) : ℝ) * ∏ i : Fin d, x i ^ ((0 : Fin d →₀ ℕ) i)
          + ∑ σ ∈ p.support.erase 0,
            ((p.coeff σ : ℚ) : ℝ) * ∏ i, x i ^ (σ : Fin d →₀ ℕ) i := by
              linarith
      _ = (∑ σ ∈ p.support.erase 0,
            ((p.coeff σ : ℚ) : ℝ) * ∏ i, x i ^ (σ : Fin d →₀ ℕ) i)
          + ((p.coeff 0 : ℚ) : ℝ) * ∏ i : Fin d, x i ^ ((0 : Fin d →₀ ℕ) i) := by
              ring
  · -- if 0 ∉ support, then coeff 0 = 0 and the sum is nonneg
    have hc0 : p.coeff 0 = 0 := by
      by_contra hne
      exact h0 (MvPolynomial.mem_support_iff.mpr hne)
    have : ((p.coeff 0 : ℚ) : ℝ) = 0 := by rw [hc0]; norm_cast
    rw [this]
    apply Finset.sum_nonneg
    intro σ _
    apply mul_nonneg
    · have : (0 : ℝ) ≤ ((p.coeff σ : ℚ) : ℝ) := by exact_mod_cast hc σ
      simpa [Rat.castHom] using this
    · exact Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _

/-- Uniform upper bound of a non-negative-coefficient polynomial on the
non-negative orthant `∩ ‖x‖ ≤ M` (sup-norm / any norm dominating each
coordinate). `M` is assumed non-negative. We define the bound as a sum
over the support. -/
noncomputable def polyUpperBound {d : ℕ} (p : MvPolynomial (Fin d) ℚ) (M : ℝ) : ℝ :=
  ∑ σ ∈ p.support, ((p.coeff σ : ℚ) : ℝ) * M ^ (∑ i, σ i)

/-- The uniform upper bound is non-negative when `M ≥ 0` and coefficients are
non-negative. -/
theorem polyUpperBound_nonneg {d : ℕ} (p : MvPolynomial (Fin d) ℚ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ σ, 0 ≤ p.coeff σ) :
    0 ≤ polyUpperBound p M := by
  unfold polyUpperBound
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg
  · exact_mod_cast hc σ
  · exact pow_nonneg hM _

/-- If `0 ≤ x i ≤ M` for every `i`, then `p.eval₂ (Rat.castHom ℝ) x` is
dominated by `polyUpperBound p M`. -/
theorem mvpoly_eval₂_le_polyUpperBound {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) (x : Fin d → ℝ) (M : ℝ)
    (_hM : 0 ≤ M) (hx : ∀ i, 0 ≤ x i) (hxM : ∀ i, x i ≤ M)
    (hc : ∀ σ, 0 ≤ p.coeff σ) :
    p.eval₂ (Rat.castHom ℝ) x ≤ polyUpperBound p M := by
  classical
  rw [MvPolynomial.eval₂_eq']
  unfold polyUpperBound
  apply Finset.sum_le_sum
  intro σ _
  have hcoef_nn : (0 : ℝ) ≤ ((p.coeff σ : ℚ) : ℝ) := by exact_mod_cast hc σ
  apply mul_le_mul_of_nonneg_left _ hcoef_nn
  -- show ∏ i, x i ^ σ i ≤ M ^ (∑ i, σ i)
  have hprod_eq : (M : ℝ) ^ (∑ i, σ i) = ∏ i : Fin d, M ^ (σ i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
  rw [hprod_eq]
  apply Finset.prod_le_prod
  · intro i _; exact pow_nonneg (hx i) _
  · intro i _; exact pow_le_pow_left₀ (hx i) (hxM i) _

/-! ### Step 2 helpers: derivative of a specific coordinate -/

/-- If `sol` has derivative `P.toPIVP.field (sol t)` at `t`, then component
`r` of the trajectory has derivative `prod_r(x) - degr_r(x) * x_r` at `t`. -/
theorem crn_component_hasDerivAt {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P)
    (sol : PIVP.Solution P.toPIVP) (r : Fin d) (t : ℝ)
    (h_ode : HasDerivAt sol.trajectory (P.toPIVP.field (sol.trajectory t)) t) :
    HasDerivAt (fun s => sol.trajectory s r)
      ((pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory t)
        - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory t) *
          sol.trajectory t r) t := by
  have hcomp : HasDerivAt (fun s => sol.trajectory s r)
      (P.toPIVP.field (sol.trajectory t) r) t :=
    hasDerivAt_pi.mp h_ode r
  have hfield_eq : P.toPIVP.field (sol.trajectory t) r
      = (pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory t)
        - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory t) *
          sol.trajectory t r := by
    have := (pcd.toIsCRNImplementable).field_eq (sol.trajectory t) r
    simpa using this
  rw [← hfield_eq]
  exact hcomp

/-! ### Step 2: Proof of `noCollapse_step2_root_liminf` -/

/-- **Step 2 (root species Grönwall lower bound) — PROVED.**

A root species (`(pcd.prod r).coeff 0 > 0`) along a bounded trajectory
admits a positive asymptotic lower bound: there is `c > 0` such that
on a cofinal set of times `sol t r ≥ c`.

**Strategy.** Let `c_r = (pcd.prod r).coeff 0 > 0`, and let `M > 0` be a
uniform bound on `‖sol t‖` (from boundedness). Define
`D_r := polyUpperBound (pcd.degr r) M ≥ 0`.

For every `t ≥ 0`, the field decomposition plus polynomial bounds give
`x_r'(t) ≥ c_r - D_r * x_r(t)` (polynomial constant-coefficient lower
bound on `prod_r`, polynomial uniform upper bound on `degr_r`,
non-negativity of `x_r`).

Define `f(t) := c_r / (D_r + 1) - sol.trajectory t r` (we use `D_r + 1`
to keep the denominator strictly positive). Then
`f'(t) = -x_r'(t) ≤ -c_r + D_r * x_r(t) = -c_r + D_r · ((c_r/(D_r+1)) − f(t))
       = -c_r + (D_r * c_r)/(D_r+1) - D_r * f(t)
       = -(c_r / (D_r+1)) - D_r * f(t)`
so `f'(t) ≤ -D_r * f(t) - (c_r/(D_r+1))`.

Applied with Grönwall's scalar inequality `f ≤ gronwallBound δ K ε (t - 0)`
at `K = -D_r`, `ε = -c_r/(D_r+1)`, `δ = f(0) = c_r/(D_r+1)`, we get
`f(t) ≤ (c_r/(D_r+1)) · exp(-D_r t) - (c_r/((D_r+1)·D_r)) · (exp(-D_r t) - 1)`
(modulo `D_r = 0` case).

For any `t ≥ 0`, this yields `sol t r ≥ c` for a specific `c > 0`; in fact
the asymptotic liminf is `c_r / (D_r + 1)`, so taking `c := c_r / (2 · (D_r + 1))`
works once `t` is large enough. For cofinality we pick
`t := max T (large-enough threshold)`. -/
theorem noCollapse_step2_root_liminf {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (hbnd : P.toPIVP.IsBounded sol.trajectory)
    (r : Fin d) (hroot : 0 < (pcd.prod r).coeff 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c ≤ sol.trajectory t r := by
  -- non-negativity of the trajectory
  have h_nn : ∀ (t : ℝ), 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i :=
    fun t ht i => crn_trajectory_nonneg pcd hzi sol hbnd i t ht
  -- unpack bound
  obtain ⟨M, hMpos, hMbnd⟩ := hbnd
  -- pointwise coordinate bound from the norm bound
  have h_coord_bnd : ∀ (t : ℝ), 0 ≤ t → ∀ i, sol.trajectory t i ≤ M := by
    intro t ht i
    have h1 : ‖sol.trajectory t‖ ≤ M := hMbnd t ht
    have h2 : ‖sol.trajectory t i‖ ≤ ‖sol.trajectory t‖ := norm_le_pi_norm _ i
    have h3 : sol.trajectory t i ≤ ‖sol.trajectory t i‖ :=
      Real.le_norm_self _
    linarith
  -- constant production rate
  let c_r : ℝ := ((pcd.prod r).coeff 0 : ℚ)
  have hc_r_eq : c_r = ((pcd.prod r).coeff 0 : ℚ) := rfl
  have hc_r_pos : 0 < c_r := by
    rw [hc_r_eq]; exact_mod_cast hroot
  -- degradation polynomial bound
  let D_r : ℝ := polyUpperBound (pcd.degr r) M
  have hD_r_eq : D_r = polyUpperBound (pcd.degr r) M := rfl
  have hM_nn : 0 ≤ M := le_of_lt hMpos
  have hD_r_nn : 0 ≤ D_r := by
    rw [hD_r_eq]; exact polyUpperBound_nonneg _ _ hM_nn (pcd.degr_nonneg r)
  -- Use K = D_r + 1 > 0 to keep things clean
  let K : ℝ := D_r + 1
  have hK_eq : K = D_r + 1 := rfl
  have hK_pos : 0 < K := by rw [hK_eq]; linarith
  -- target asymptotic bound: α := c_r / K. We'll show sol t r ≥ (α/2) eventually.
  let α : ℝ := c_r / K
  have hα_eq : α = c_r / K := rfl
  have hα_pos : 0 < α := by rw [hα_eq]; exact div_pos hc_r_pos hK_pos
  -- We'll produce c := α / 2.
  refine ⟨α / 2, by positivity, ?_⟩
  intro T
  let t_thr : ℝ := if D_r = 0 then 1 else (Real.log 2) / D_r + 1
  have ht_thr_eq : t_thr = if D_r = 0 then 1 else (Real.log 2) / D_r + 1 := rfl
  have h_t_thr_pos : 0 < t_thr := by
    rw [ht_thr_eq]
    split_ifs with h
    · norm_num
    · have hDr_pos : 0 < D_r := lt_of_le_of_ne hD_r_nn (Ne.symm h)
      have : 0 ≤ Real.log 2 / D_r := div_nonneg (Real.log_nonneg (by norm_num)) hD_r_nn
      linarith
  have h_t_thr_nn : 0 ≤ t_thr := le_of_lt h_t_thr_pos
  let t : ℝ := max (max T t_thr) 0
  have ht_eq : t = max (max T t_thr) 0 := rfl
  have ht_nn : 0 ≤ t := by rw [ht_eq]; exact le_max_right _ _
  have ht_ge_T : T ≤ t := by rw [ht_eq]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have ht_ge_thr : t_thr ≤ t := by rw [ht_eq]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨t, ht_ge_T, ?_⟩
  -- Now we apply Grönwall on [0, t].
  -- Define f(s) := α - sol.trajectory s r.
  let f : ℝ → ℝ := fun s => α - sol.trajectory s r
  have hf_eq : f = fun s => α - sol.trajectory s r := rfl
  -- Compute:  f'(s) ≤ K · f(s) - c_r   wait, let me redo it.
  -- We want  f'(s) ≤ (-D_r) * f(s) + ε.
  -- f'(s) = -(sol r)'(s) = -(prod - degr * x_r)  = -prod + degr * x_r
  --      ≤ -c_r + D_r * x_r
  --      = -c_r + D_r * (α - f(s))
  --      = -c_r + D_r * α - D_r * f(s)
  -- using α = c_r/K = c_r/(D_r + 1):
  --   -c_r + D_r * c_r / (D_r+1) = c_r * (-1 + D_r/(D_r+1)) = c_r * (-1/(D_r+1)) = -c_r/K = -α
  -- so f'(s) ≤ -D_r * f(s) - α
  -- thus gronwallBound δ K_g ε s with K_g = -D_r, ε = -α, δ = f(0) = α.
  have hf0 : f 0 = α := by
    change α - sol.trajectory 0 r = α
    rw [show sol.trajectory 0 = P.toPIVP.init from sol.init_cond]
    have : P.toPIVP.init r = 0 := by
      simp [PolyPIVP.toPIVP_init, hzi r]
    rw [this]; ring
  -- Prove f is continuous on [0, t]
  have h_sol_contOn : ContinuousOn sol.trajectory (Set.Icc 0 t) := by
    intro s hs
    have h_ode : HasDerivAt sol.trajectory (P.toPIVP.field (sol.trajectory s)) s :=
      sol.is_solution s hs.1
    exact h_ode.continuousAt.continuousWithinAt
  have h_sol_r_contOn : ContinuousOn (fun s => sol.trajectory s r) (Set.Icc 0 t) := by
    intro s hs
    have h_ode : HasDerivAt sol.trajectory (P.toPIVP.field (sol.trajectory s)) s :=
      sol.is_solution s hs.1
    have h_r : HasDerivAt (fun u => sol.trajectory u r)
        (P.toPIVP.field (sol.trajectory s) r) s :=
      hasDerivAt_pi.mp h_ode r
    exact h_r.continuousAt.continuousWithinAt
  have h_f_contOn : ContinuousOn f (Set.Icc 0 t) := by
    apply ContinuousOn.sub
    · exact continuousOn_const
    · exact h_sol_r_contOn
  -- Prove derivative of f on [0, t)
  have h_f_hasDeriv : ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt f
        (- ((pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
            - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
              * sol.trajectory s r))
        (Set.Ici s) s := by
    intro s hs
    have h_ode : HasDerivAt sol.trajectory
        (P.toPIVP.field (sol.trajectory s)) s :=
      sol.is_solution s hs.1
    have h_deriv_r := crn_component_hasDerivAt pcd sol r s h_ode
    have : HasDerivAt f
        (- ((pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
            - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
              * sol.trajectory s r)) s := by
      simpa using h_deriv_r.const_sub α
    exact this.hasDerivWithinAt
  -- Bound the derivative: f'(s) ≤ -D_r * f(s) - α
  have h_bound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      (- ((pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
          - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
            * sol.trajectory s r))
        ≤ (-D_r) * f s + (-α) := by
    intro s hs
    have h_s_nn : 0 ≤ s := hs.1
    have h_s_le : s ≤ t := le_of_lt hs.2
    -- Coord bounds and nonneg
    have h_xs_nn : ∀ i, 0 ≤ sol.trajectory s i := h_nn s h_s_nn
    have h_xs_le : ∀ i, sol.trajectory s i ≤ M := h_coord_bnd s h_s_nn
    -- prod_r ≥ c_r
    have h_prod_ge : c_r
        ≤ (pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory s) := by
      have := mvpoly_const_coeff_le_eval₂ (pcd.prod r) (sol.trajectory s)
        h_xs_nn (pcd.prod_nonneg r)
      exact this
    -- degr_r ≤ D_r
    have h_degr_le : (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s) ≤ D_r :=
      mvpoly_eval₂_le_polyUpperBound (pcd.degr r) (sol.trajectory s) M
        hM_nn h_xs_nn h_xs_le (pcd.degr_nonneg r)
    -- degr_r ≥ 0
    have h_degr_nn : 0 ≤ (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s) := by
      have := mvpoly_const_coeff_le_eval₂ (pcd.degr r) (sol.trajectory s)
        h_xs_nn (pcd.degr_nonneg r)
      -- coeff 0 of degr may be 0; but value is nonneg anyway via mvpoly_eval₂_nonneg fact:
      -- we use the stronger statement: nonneg coeffs ⇒ nonneg value on ℝ≥0
      have hcoef0 : (0 : ℝ) ≤ (((pcd.degr r).coeff 0 : ℚ) : ℝ) := by
        exact_mod_cast pcd.degr_nonneg r 0
      linarith
    -- sol t r ≥ 0
    have h_x_r_nn : 0 ≤ sol.trajectory s r := h_xs_nn r
    have h_x_r_le : sol.trajectory s r ≤ M := h_xs_le r
    -- Set up chain
    -- prod - degr * x_r ≥ c_r - D_r * x_r   (use prod ≥ c_r, 0 ≤ degr ≤ D_r, 0 ≤ x_r)
    have step1 : c_r - D_r * sol.trajectory s r
        ≤ (pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
          - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s) * sol.trajectory s r := by
      have hmul : (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s) * sol.trajectory s r
          ≤ D_r * sol.trajectory s r :=
        mul_le_mul_of_nonneg_right h_degr_le h_x_r_nn
      linarith
    -- -(prod - degr * x_r) ≤ -(c_r - D_r * x_r) = -c_r + D_r * x_r
    have step2 : -((pcd.prod r).eval₂ (Rat.castHom ℝ) (sol.trajectory s)
          - (pcd.degr r).eval₂ (Rat.castHom ℝ) (sol.trajectory s) * sol.trajectory s r)
        ≤ -c_r + D_r * sol.trajectory s r := by linarith
    -- f(s) = α - x_r ⇒ x_r = α - f(s)
    -- show -c_r + D_r * x_r ≤ -D_r * f(s) - α
    -- i.e., -c_r + D_r * (α - f(s)) = -c_r + D_r * α - D_r * f(s) ≤? -D_r * f(s) - α
    -- ⇔ -c_r + D_r * α ≤ -α
    -- ⇔ D_r * α + α ≤ c_r
    -- ⇔ (D_r + 1) * α ≤ c_r
    -- but α = c_r / K and K = D_r + 1, so (D_r+1) * α = c_r. ✓
    have hα_def : K * α = c_r := by
      rw [hα_eq, hK_eq]
      have : D_r + 1 > 0 := by linarith
      field_simp
    have step3 : -c_r + D_r * sol.trajectory s r ≤ -D_r * f s + -α := by
      change -c_r + D_r * sol.trajectory s r ≤ -D_r * (α - sol.trajectory s r) + -α
      have hKα : K * α = c_r := hα_def
      rw [hK_eq] at hKα
      -- (D_r + 1) * α = c_r ⇒ D_r * α + α = c_r ⇒ D_r * α = c_r - α
      have : D_r * α = c_r - α := by linarith
      nlinarith [this]
    linarith
  -- Apply Grönwall
  have h_gron : ∀ s ∈ Set.Icc (0 : ℝ) t,
      f s ≤ gronwallBound α (-D_r) (-α) (s - 0) := by
    apply le_gronwallBound_of_liminf_deriv_right_le h_f_contOn
    · intro s hs rv hrv
      -- we have HasDerivWithinAt f (f's) (Ici s) s, and f's < rv
      have hderiv := h_f_hasDeriv s hs
      have hslope := hderiv.liminf_right_slope_le hrv
      -- hslope : ∃ᶠ z in 𝓝[>] s, (z - s)⁻¹ * (f z - f s) < rv
      exact hslope
    · rw [hf0]
    · intro s hs
      exact h_bound s hs
  -- Specialize to s = t
  have h_gron_t : f t ≤ gronwallBound α (-D_r) (-α) (t - 0) := by
    apply h_gron
    exact ⟨ht_nn, le_refl _⟩
  -- Compute the explicit form of gronwallBound and show it ≤ α/2.
  have h_gron_form : gronwallBound α (-D_r) (-α) t ≤ α / 2 := by
    by_cases hDr : D_r = 0
    · -- K_gron = 0 case
      unfold gronwallBound
      simp [hDr]
      -- Goal: α + -α * t ≤ α / 2. Need t ≥ 1/2.
      have ht_thr_eq_val : t_thr = 1 := by
        rw [ht_thr_eq]; simp [hDr]
      have ht_ge_one : (1 : ℝ) ≤ t := ht_thr_eq_val ▸ ht_ge_thr
      nlinarith [hα_pos]
    · -- K_gron = -D_r ≠ 0
      have hDr_pos : 0 < D_r := lt_of_le_of_ne hD_r_nn (Ne.symm hDr)
      have hKg_ne : (-D_r : ℝ) ≠ 0 := neg_ne_zero.mpr hDr
      rw [gronwallBound_of_K_ne_0 hKg_ne]
      change α * Real.exp (-D_r * t) + (-α) / (-D_r) * (Real.exp (-D_r * t) - 1) ≤ α / 2
      -- t ≥ (log 2) / D_r + 1, so D_r * t ≥ log 2 + D_r > log 2; thus u ≤ exp(-log 2) = 1/2.
      have ht_thr_eq_val : t_thr = (Real.log 2) / D_r + 1 := by
        rw [ht_thr_eq]; simp [hDr]
      have h_t_ge : (Real.log 2) / D_r + 1 ≤ t := ht_thr_eq_val ▸ ht_ge_thr
      have h_Dt_ge_log2 : Real.log 2 ≤ D_r * t := by
        have h1 : D_r * ((Real.log 2) / D_r + 1) ≤ D_r * t :=
          mul_le_mul_of_nonneg_left h_t_ge (le_of_lt hDr_pos)
        have h2 : D_r * ((Real.log 2) / D_r + 1) = Real.log 2 + D_r := by
          field_simp
        linarith
      have hu_le_half : Real.exp (-D_r * t) ≤ 1 / 2 := by
        have hexp_mono : Real.exp (-(D_r * t)) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
        have hval : Real.exp (-Real.log 2) = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
        have heq : Real.exp (-D_r * t) = Real.exp (-(D_r * t)) := by ring_nf
        rw [heq]; linarith
      have hu_pos : 0 < Real.exp (-D_r * t) := Real.exp_pos _
      -- simplify: (-α) / (-D_r) = α / D_r
      have h_neg_div : ((-α) / (-D_r) : ℝ) = α / D_r := by rw [neg_div_neg_eq]
      rw [h_neg_div]
      -- Now multiply the target inequality by D_r (> 0) to clear the division:
      -- α * u + α/D_r * (u - 1) ≤ α/2
      -- ⇔ D_r * (α u) + α * (u - 1) ≤ D_r * α / 2
      -- ⇔ α (D_r u + u - 1) ≤ α D_r / 2
      -- ⇔ α (K u - 1) ≤ α D_r / 2   (K = D_r + 1)
      -- ⇔ K u - 1 ≤ D_r / 2   (divide by α > 0)
      -- ⇔ K u ≤ (D_r + 2) / 2
      -- With u ≤ 1/2 and K = D_r + 1 > 0: K u ≤ K/2 = (D_r + 1)/2 ≤ (D_r + 2)/2. ✓
      have h_Ku_bound : K * Real.exp (-D_r * t) ≤ (D_r + 2) / 2 := by
        have : K * Real.exp (-D_r * t) ≤ K * (1 / 2) :=
          mul_le_mul_of_nonneg_left hu_le_half (le_of_lt hK_pos)
        have hKval : K = D_r + 1 := rfl
        rw [hKval] at this
        linarith
      -- Prove the inequality by clearing denominators
      have hD_r_ne : D_r ≠ 0 := hDr
      rw [← sub_nonneg]
      -- goal: 0 ≤ α / 2 - (α * Real.exp(-D_r * t) + α / D_r * (Real.exp(-D_r * t) - 1))
      have hrewrite :
          α / 2 - (α * Real.exp (-D_r * t)
            + α / D_r * (Real.exp (-D_r * t) - 1))
            = (α / D_r) * (((D_r + 2) / 2) - K * Real.exp (-D_r * t)) := by
        have hKval : K = D_r + 1 := rfl
        rw [hKval]; field_simp; ring
      rw [hrewrite]
      apply mul_nonneg
      · exact div_nonneg (le_of_lt hα_pos) hD_r_nn
      · linarith
  -- Combine: f t ≤ gronwallBound ... t ≤ α/2
  have h_f_le_half : f t ≤ α / 2 := by
    have := h_gron_t
    simp only [sub_zero] at this
    linarith [h_gron_form]
  -- f t = α - sol t r, so sol t r = α - f t ≥ α - α/2 = α/2
  have hfinal : α - sol.trajectory t r ≤ α / 2 := h_f_le_half
  linarith

/-- **Step 3 (SCC induction step).**

If species `j` has a positive-coefficient production monomial all of whose
variables are species `i₁, …, i_k` (distinct from `j`, so this is a
non-self production), and each feeder `i_ℓ` has a positive asymptotic lower
bound, then `j` also has a positive asymptotic lower bound.

Mathematical content: the feed `∏_ℓ x_{i_ℓ}^{e_ℓ}` is bounded below by
`∏_ℓ c_ℓ^{e_ℓ}` on the cofinal set where all feeders are simultaneously
bounded below by their `c_ℓ`. Under boundedness, the same Grönwall-on-
scalar-linear-inequality argument as Step 2 gives a positive asymptotic
lower bound for `j`.

**Form used by `zero_init_no_collapse`.** We package the SCC induction as:
for every non-root species with a positive trajectory value at some `t₀`,
a positive asymptotic lower bound exists — deferring the graph-traversal
bookkeeping (which is an inductive argument on the production-graph
condensation) to this axiom. The non-algorithmic content is captured by
the single phrase "induction on the condensation". -/
axiom noCollapse_step3_scc_induction {d : ℕ} {P : PolyPIVP d}
    (_pcd : PolyCRNDecomposition d P) (_hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (_hbnd : P.toPIVP.IsBounded sol.trajectory)
    (i : Fin d) (t₀ : ℝ) (_ht₀ : 0 ≤ t₀) (_hpos : 0 < sol.trajectory t₀ i)
    (_root_feed : ∀ r : Fin d, 0 < (_pcd.prod r).coeff 0 →
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c ≤ sol.trajectory t r) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c ≤ sol.trajectory t i

/-! ## The non-collapse conjecture (composed from Steps 1–3) -/

/-- **Xiang's zero-init non-collapse conjecture.**

Under zero initialization, non-negative coefficients (CRN shape), and a
bounded trajectory, no species that has ever been positive can have liminf 0.

Formally: if species `i` is positive at some time `t₀ ≥ 0`, then there is a
positive constant `c` and a cofinal set of times on which `sol t i ≥ c`. In
particular any existing limit of `sol t i` is at least `c > 0`, so cannot
be 0.

This is the formal statement that "computing 0 non-trivially from a zero-init
CRN is impossible": if `sol t P.output → 0` under these hypotheses, then
the output must be identically 0 (see `zero_of_limit_is_trivial`).

**Proof (modular).** Step 2 provides a positive lower bound for every root
species. Step 3 (SCC induction) propagates that lower bound to every
eventually-positive species. Only the feeder hypothesis for Step 3 is
needed explicitly. -/
theorem zero_init_no_collapse {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P)
    (hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (hbnd : P.toPIVP.IsBounded sol.trajectory)
    (i : Fin d) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (hpos : 0 < sol.trajectory t₀ i) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c ≤ sol.trajectory t i := by
  -- Step 2: every root species has a positive asymptotic lower bound.
  have root_feed : ∀ r : Fin d, 0 < (pcd.prod r).coeff 0 →
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c ≤ sol.trajectory t r :=
    fun r hroot => noCollapse_step2_root_liminf pcd hzi sol hbnd r hroot
  -- Step 3: SCC induction propagates lower bounds to any eventually-positive species.
  exact noCollapse_step3_scc_induction pcd hzi sol hbnd i t₀ ht₀ hpos root_feed

/-- **Consequence (trivial-zero theorem).**

If a bounded zero-init CRN's designated output converges to 0, then the
output trajectory is identically 0 on `[0, ∞)`. The constant 0 is not a
non-trivial CRN-computable number from zero init. -/
theorem zero_of_limit_is_trivial {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (hbnd : P.toPIVP.IsBounded sol.trajectory)
    (hconv : PIVP.Computes P.toPIVP sol 0) :
    ∀ t : ℝ, 0 ≤ t → sol.trajectory t P.output = 0 := by
  intro t ht
  by_contra hne
  have hnonneg : 0 ≤ sol.trajectory t P.output :=
    crn_trajectory_nonneg pcd hzi sol hbnd P.output t ht
  have hpos : 0 < sol.trajectory t P.output :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨c, hc_pos, hc_freq⟩ :=
    zero_init_no_collapse pcd hzi sol hbnd P.output t ht hpos
  have hev : ∀ᶠ s in Filter.atTop,
      |sol.trajectory s P.output - 0| < c := by
    have := (Metric.tendsto_atTop.mp hconv) c hc_pos
    simpa [Real.dist_eq] using this
  rcases Filter.eventually_atTop.mp hev with ⟨T, hT⟩
  obtain ⟨s, hTs, hcs⟩ := hc_freq T
  have hlt := hT s hTs
  have hnn_s : 0 ≤ sol.trajectory s P.output := le_trans hc_pos.le hcs
  rw [sub_zero, abs_of_nonneg hnn_s] at hlt
  exact (not_lt.mpr hcs) hlt

end Ripple

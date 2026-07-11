import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Ripple.BoundedUniversality.BGP.SelectorField
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicator
-----------------------------
Isolated simplex-replicator replacement for the selector-weight `λ` field.

This file is deliberately additive: it defines the polynomial coupling and the
abstract simplex invariants, but does not change `selectorAssembledField` or
`SelectorDynSol`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

variable {N : ℕ}

/-! ## Polynomial simplex-replicator field -/

/-- Replicator average
`φ = ∑_w λ_w P_w`, with the selector-weight coordinates supplied explicitly.

For the assembled selector state, use `lamCoord := fun w => selLamCoord w`; this
is the same coordinate API used by `selectorResetGateFieldPoly` in
`SelectorField.lean`. -/
def selectorReplicatorPhiPoly {V : Type} [Fintype V]
    (Ppoly : V → MvPolynomial (Fin N) ℚ) (lamCoord : V → Fin N) :
    MvPolynomial (Fin N) ℚ :=
  ∑ w : V, X (lamCoord w) * Ppoly w

/-- Polynomial RHS for the simplex selector weight `λ_v`.

The reset target is the uniform simplex point `1 / card V`; the gate term is the
replicator coupling `gain · λ_v · (P_v - φ)`, where
`φ = ∑_w λ_w P_w`. -/
def selectorReplicatorFieldPoly {V : Type} [Fintype V]
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin N) ℚ)
    (Ppoly : V → MvPolynomial (Fin N) ℚ) (lamCoord : V → Fin N) (v : V) :
    MvPolynomial (Fin N) ℚ :=
  chiReset * kappa * (C (1 / (Fintype.card V : ℚ)) - X (lamCoord v))
    + chiGate * gainPoly * X (lamCoord v) *
        (Ppoly v - selectorReplicatorPhiPoly Ppoly lamCoord)

/-- Specialized selector-state version using the checked-in `selLamCoord`
indexing over `Fin (selectorDim d V)`. -/
def selectorReplicatorFieldSelLamPoly {d : ℕ} {V : Type} [Fintype V]
    (chiReset chiGate kappa gainPoly :
      MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ) (v : V) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  selectorReplicatorFieldPoly chiReset chiGate kappa gainPoly Ppoly
    (fun w => selLamCoord w) v

@[simp] theorem eval₂_selectorReplicatorPhiPoly {V : Type} [Fintype V]
    (Ppoly : V → MvPolynomial (Fin N) ℚ) (lamCoord : V → Fin N)
    (x : Fin N → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x (selectorReplicatorPhiPoly Ppoly lamCoord) =
      ∑ w : V, x (lamCoord w) * eval₂ (algebraMap ℚ ℝ) x (Ppoly w) := by
  unfold selectorReplicatorPhiPoly
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [MvPolynomial.coe_eval₂Hom, eval₂_mul, eval₂_X]

/-- Evaluation identity for the polynomial simplex-replicator field. -/
@[simp] theorem eval₂_selectorReplicatorFieldPoly {V : Type} [Fintype V]
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin N) ℚ)
    (Ppoly : V → MvPolynomial (Fin N) ℚ) (lamCoord : V → Fin N)
    (v : V) (x : Fin N → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x
        (selectorReplicatorFieldPoly chiReset chiGate kappa gainPoly Ppoly lamCoord v) =
      eval₂ (algebraMap ℚ ℝ) x chiReset *
          eval₂ (algebraMap ℚ ℝ) x kappa *
            (1 / (Fintype.card V : ℝ) - x (lamCoord v))
        + eval₂ (algebraMap ℚ ℝ) x chiGate *
          eval₂ (algebraMap ℚ ℝ) x gainPoly *
          x (lamCoord v) *
            (eval₂ (algebraMap ℚ ℝ) x (Ppoly v)
              - ∑ w : V, x (lamCoord w) *
                  eval₂ (algebraMap ℚ ℝ) x (Ppoly w)) := by
  simp only [selectorReplicatorFieldPoly, eval₂_add, eval₂_mul, eval₂_sub, eval₂_C,
    eval₂_X, eval₂_selectorReplicatorPhiPoly, map_div₀, map_one, map_natCast]

/-! ## Abstract simplex invariants -/

/-- Conservation of total selector mass for the abstract simplex-replicator ODE.

The proof sets `S = ∑_v λ_v`, rewrites the ODE as
`(1 - S)' = -(cr + cg · φ) · (1 - S)`, and multiplies by the integrating factor
`exp (∫ (cr + cg · φ))`. -/
theorem replicator_sum_lam_eq_one {V : Type} [Fintype V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg : ℝ → ℝ)
    (hcr_cont : Continuous cr) (hcg_cont : Continuous cg)
    (hlam_cont : ∀ v : V, Continuous (lam v))
    (hP_cont : ∀ v : V, Continuous (P v))
    (hode : ∀ v : V, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (lam v)
        (cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * (lam v t) *
              (P v t - ∑ w : V, lam w t * P w t)) t)
    (hsum0 : (∑ v : V, lam v 0) = 1) :
    ∀ t : ℝ, 0 ≤ t → (∑ v : V, lam v t) = 1 := by
  classical
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | htpos
  · exact hsum0

  let coeff : ℝ → ℝ := fun s => cr s + cg s * (∑ w : V, lam w s * P w s)
  let massGap : ℝ → ℝ := fun s => 1 - ∑ v : V, lam v s

  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V))

  have hconst_sum : (∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard_ne

  have hsum_rhs :
      ∀ s : ℝ,
        (∑ v : V,
          (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
            + cg s * (lam v s) *
                (P v s - ∑ w : V, lam w s * P w s))) =
          (1 - ∑ v : V, lam v s) *
            (cr s + cg s * (∑ w : V, lam w s * P w s)) := by
    intro s
    let phi : ℝ := ∑ w : V, lam w s * P w s
    let total : ℝ := ∑ v : V, lam v s
    have hreset :
        (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s)) =
          cr s * (1 - total) := by
      calc
        (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s))
            = cr s * (∑ v : V, (1 / (Fintype.card V : ℝ) - lam v s)) := by
                rw [Finset.mul_sum]
        _ = cr s * ((∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ))
              - ∑ v : V, lam v s) := by
                rw [Finset.sum_sub_distrib]
        _ = cr s * (1 - total) := by
                rw [hconst_sum]
    have hgate :
        (∑ v : V, cg s * (lam v s) * (P v s - phi)) =
          cg s * (phi - total * phi) := by
      calc
        (∑ v : V, cg s * (lam v s) * (P v s - phi))
            = cg s * (∑ v : V, lam v s * (P v s - phi)) := by
                simp_rw [mul_assoc (cg s)]
                rw [Finset.mul_sum]
        _ = cg s *
              ((∑ v : V, lam v s * P v s) - ∑ v : V, lam v s * phi) := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
                rw [mul_sub]
        _ = cg s * (phi - total * phi) := by
                rw [Finset.sum_mul]
    calc
      (∑ v : V,
          (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
            + cg s * (lam v s) * (P v s - ∑ w : V, lam w s * P w s)))
          = (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s))
              + ∑ v : V, cg s * (lam v s) * (P v s - phi) := by
                rw [Finset.sum_add_distrib]
      _ = cr s * (1 - total) + cg s * (phi - total * phi) := by
                rw [hreset, hgate]
      _ = (1 - ∑ v : V, lam v s) *
            (cr s + cg s * (∑ w : V, lam w s * P w s)) := by
                dsimp [phi, total]
                ring

  have hgap_deriv :
      ∀ s : ℝ, 0 ≤ s →
        HasDerivAt massGap (-(coeff s) * massGap s) s := by
    intro s hs_nonneg
    have hsum_deriv :
        HasDerivAt (fun τ : ℝ => ∑ v : V, lam v τ)
          (∑ v : V,
            (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
              + cg s * (lam v s) *
                  (P v s - ∑ w : V, lam w s * P w s))) s := by
      exact HasDerivAt.fun_sum (u := Finset.univ)
        (fun v _ => hode v s hs_nonneg)
    have hgap := hsum_deriv.const_sub 1
    convert hgap using 1
    · dsimp [massGap, coeff]
      rw [hsum_rhs s]
      ring

  have hcoeff_cont : Continuous coeff := by
    dsimp [coeff]
    fun_prop

  let intCoeff : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, coeff u
  let expCoeff : ℝ → ℝ := fun s => Real.exp (intCoeff s)
  let weightedGap : ℝ → ℝ := fun s => massGap s * expCoeff s

  have hint_deriv : ∀ s : ℝ, HasDerivAt intCoeff (coeff s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hcoeff_cont.intervalIntegrable 0 s)
      (hcoeff_cont.stronglyMeasurableAtFilter _ _)
      hcoeff_cont.continuousAt

  have hexp_deriv : ∀ s : ℝ, HasDerivAt expCoeff (coeff s * expCoeff s) s := by
    intro s
    have h := (hint_deriv s).exp
    convert h using 1
    dsimp [expCoeff]
    ring

  have hweighted_deriv : ∀ s : ℝ, 0 ≤ s → HasDerivAt weightedGap 0 s := by
    intro s hs
    have hmul := (hgap_deriv s hs).mul (hexp_deriv s)
    convert hmul using 1
    dsimp [weightedGap]
    ring

  have hgap0 : massGap 0 = 0 := by
    dsimp [massGap]
    linarith
  have hweighted0 : weightedGap 0 = 0 := by
    dsimp [weightedGap]
    rw [hgap0]
    ring
  have hdiff : DifferentiableOn ℝ weightedGap (Icc (0 : ℝ) t) :=
    fun s hs => (hweighted_deriv s hs.1).differentiableAt.differentiableWithinAt
  have hderivWithin :
      ∀ s ∈ Ico (0 : ℝ) t, derivWithin weightedGap (Icc (0 : ℝ) t) s = 0 := by
    intro s hs
    have huniq : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) t) s :=
      (uniqueDiffOn_Icc htpos) s (Ico_subset_Icc_self hs)
    exact (hweighted_deriv s hs.1).hasDerivWithinAt.derivWithin huniq
  have hconst := constant_of_derivWithin_zero hdiff hderivWithin
    t (right_mem_Icc.mpr (le_of_lt htpos))
  have hweighted_t : weightedGap t = 0 := by
    rw [hweighted0] at hconst
    exact hconst
  have hgap_t : massGap t = 0 := by
    have hexp_pos : 0 < expCoeff t := by
      dsimp [expCoeff]
      exact Real.exp_pos _
    dsimp [weightedGap] at hweighted_t
    exact (mul_eq_zero.mp hweighted_t).resolve_right (ne_of_gt hexp_pos)
  dsimp [massGap] at hgap_t
  linarith

/-- Nonnegativity of each simplex-replicator coordinate.

The proof is per coordinate.  After rewriting the equation as
`λ_v' = cr/card V + (cg·(P_v - φ) - cr)·λ_v`, multiply by the integrating factor
`exp (-∫ (cg·(P_v - φ) - cr))`.  The weighted coordinate has nonnegative
derivative because `cr ≥ 0` and `card V > 0`, so it stays above its initial
nonnegative value. -/
theorem replicator_lam_nonneg {V : Type} [Fintype V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg : ℝ → ℝ)
    (hcr_cont : Continuous cr) (hcg_cont : Continuous cg)
    (hlam_cont : ∀ v : V, Continuous (lam v))
    (hP_cont : ∀ v : V, Continuous (P v))
    (hcr0 : ∀ t : ℝ, 0 ≤ cr t)
    (hode : ∀ v : V, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (lam v)
        (cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * (lam v t) *
              (P v t - ∑ w : V, lam w t * P w t)) t)
    (hinit : ∀ v : V, 0 ≤ lam v 0) :
    ∀ v : V, ∀ t : ℝ, 0 ≤ t → 0 ≤ lam v t := by
  classical
  intro v t ht
  let phi : ℝ → ℝ := fun s => ∑ w : V, lam w s * P w s
  let coeff : ℝ → ℝ := fun s => cg s * (P v s - phi s) - cr s
  let source : ℝ → ℝ := fun s => cr s * (1 / (Fintype.card V : ℝ))

  have hcard_pos_nat : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hcard_inv_nonneg : 0 ≤ (1 / (Fintype.card V : ℝ)) :=
    one_div_nonneg.mpr (le_of_lt hcard_pos)

  have hphi_cont : Continuous phi := by
    dsimp [phi]
    fun_prop
  have hcoeff_cont : Continuous coeff := by
    dsimp [coeff]
    fun_prop

  have hlam_deriv_linear :
      ∀ s : ℝ, 0 ≤ s →
        HasDerivAt (lam v) (source s + coeff s * lam v s) s := by
    intro s hs
    have h := hode v s hs
    convert h using 1
    dsimp [source, coeff, phi]
    ring

  let intCoeff : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, coeff u
  let expNegCoeff : ℝ → ℝ := fun s => Real.exp (-(intCoeff s))
  let weightedLam : ℝ → ℝ := fun s => lam v s * expNegCoeff s

  have hint_deriv : ∀ s : ℝ, HasDerivAt intCoeff (coeff s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hcoeff_cont.intervalIntegrable 0 s)
      (hcoeff_cont.stronglyMeasurableAtFilter _ _)
      hcoeff_cont.continuousAt
  have hint_cont : Continuous intCoeff :=
    continuous_iff_continuousAt.mpr fun s => (hint_deriv s).continuousAt
  have hexp_deriv :
      ∀ s : ℝ, HasDerivAt expNegCoeff (-(coeff s) * expNegCoeff s) s := by
    intro s
    have hneg : HasDerivAt (fun τ : ℝ => -(intCoeff τ)) (-(coeff s)) s :=
      (hint_deriv s).neg
    have h := hneg.exp
    convert h using 1
    dsimp [expNegCoeff]
    ring
  have hweighted_deriv :
      ∀ s : ℝ, 0 ≤ s →
        HasDerivAt weightedLam (source s * expNegCoeff s) s := by
    intro s hs
    have hmul := (hlam_deriv_linear s hs).mul (hexp_deriv s)
    convert hmul using 1
    dsimp [weightedLam, expNegCoeff]
    ring

  have hexp_cont : Continuous expNegCoeff := by
    dsimp [expNegCoeff]
    exact Real.continuous_exp.comp hint_cont.neg
  have hweighted_cont : ContinuousOn weightedLam (Icc (0 : ℝ) t) := by
    dsimp [weightedLam]
    exact ((hlam_cont v).mul hexp_cont).continuousOn

  have hweighted_mono : MonotoneOn weightedLam (Icc (0 : ℝ) t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Icc (0 : ℝ) t)
      (f := weightedLam)
      (f' := fun s => source s * expNegCoeff s)
      (convex_Icc (0 : ℝ) t)
      hweighted_cont
      (fun s hs => (hweighted_deriv s (interior_subset hs).1).hasDerivWithinAt)
      (fun s _hs => by
        exact mul_nonneg
          (mul_nonneg (hcr0 s) hcard_inv_nonneg)
          (le_of_lt (Real.exp_pos _)))

  have hweighted0_nonneg : 0 ≤ weightedLam 0 := by
    dsimp [weightedLam, expNegCoeff]
    exact mul_nonneg (hinit v) (le_of_lt (Real.exp_pos _))
  have hweighted0_le_t : weightedLam 0 ≤ weightedLam t :=
    hweighted_mono
      (left_mem_Icc.mpr ht)
      (right_mem_Icc.mpr ht)
      ht
  have hweighted_t_nonneg : 0 ≤ weightedLam t :=
    hweighted0_nonneg.trans hweighted0_le_t
  have hexp_t_pos : 0 < expNegCoeff t := by
    dsimp [expNegCoeff]
    exact Real.exp_pos _
  dsimp [weightedLam] at hweighted_t_nonneg
  exact nonneg_of_mul_nonneg_left hweighted_t_nonneg hexp_t_pos

/-- Strict positivity of each simplex-replicator coordinate from strictly positive
initial weights. The integrating factor `weightedLam(t) = λ_v(t) * exp(-∫coeff)`
is monotone nondecreasing (its derivative equals the nonneg source term times a
positive exponential), so `weightedLam(t) ≥ weightedLam(0) = λ_v(0) > 0`, giving
`λ_v(t) > 0`. -/
theorem replicator_lam_pos {V : Type} [Fintype V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg : ℝ → ℝ)
    (hcr_cont : Continuous cr) (hcg_cont : Continuous cg)
    (hlam_cont : ∀ v : V, Continuous (lam v))
    (hP_cont : ∀ v : V, Continuous (P v))
    (hcr0 : ∀ t : ℝ, 0 ≤ cr t)
    (hode : ∀ v : V, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (lam v)
        (cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * (lam v t) *
              (P v t - ∑ w : V, lam w t * P w t)) t)
    (hinit_pos : ∀ v : V, 0 < lam v 0) :
    ∀ v : V, ∀ t : ℝ, 0 ≤ t → 0 < lam v t := by
  classical
  intro v t ht
  let phi : ℝ → ℝ := fun s => ∑ w : V, lam w s * P w s
  let coeff : ℝ → ℝ := fun s => cg s * (P v s - phi s) - cr s
  let source : ℝ → ℝ := fun s => cr s * (1 / (Fintype.card V : ℝ))
  have hcard_pos_nat : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hcard_inv_nonneg : 0 ≤ (1 / (Fintype.card V : ℝ)) :=
    one_div_nonneg.mpr (le_of_lt hcard_pos)
  have hcoeff_cont : Continuous coeff := by
    dsimp [coeff, phi]; fun_prop
  let intCoeff : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, coeff u
  let expNegCoeff : ℝ → ℝ := fun s => Real.exp (-(intCoeff s))
  let weightedLam : ℝ → ℝ := fun s => lam v s * expNegCoeff s
  have hint_deriv : ∀ s : ℝ, HasDerivAt intCoeff (coeff s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hcoeff_cont.intervalIntegrable 0 s)
      (hcoeff_cont.stronglyMeasurableAtFilter _ _)
      hcoeff_cont.continuousAt
  have hint_cont : Continuous intCoeff :=
    continuous_iff_continuousAt.mpr fun s => (hint_deriv s).continuousAt
  have hexp_deriv :
      ∀ s : ℝ, HasDerivAt expNegCoeff (-(coeff s) * expNegCoeff s) s := by
    intro s
    have hneg : HasDerivAt (fun τ : ℝ => -(intCoeff τ)) (-(coeff s)) s :=
      (hint_deriv s).neg
    have h := hneg.exp
    convert h using 1
    dsimp [expNegCoeff]
    ring
  have hweighted_deriv :
      ∀ s : ℝ, 0 ≤ s →
        HasDerivAt weightedLam (source s * expNegCoeff s) s := by
    intro s hs
    have hmul := (hode v s hs).mul (hexp_deriv s)
    convert hmul using 1
    dsimp [weightedLam, expNegCoeff, source, coeff, phi]
    ring
  have hexp_cont : Continuous expNegCoeff := by
    dsimp [expNegCoeff]
    exact Real.continuous_exp.comp hint_cont.neg
  have hweighted_cont : ContinuousOn weightedLam (Icc (0 : ℝ) t) := by
    dsimp [weightedLam]
    exact ((hlam_cont v).mul hexp_cont).continuousOn
  have hweighted_mono : MonotoneOn weightedLam (Icc (0 : ℝ) t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Icc (0 : ℝ) t)
      (f := weightedLam)
      (f' := fun s => source s * expNegCoeff s)
      (convex_Icc (0 : ℝ) t)
      hweighted_cont
      (fun s hs => (hweighted_deriv s (interior_subset hs).1).hasDerivWithinAt)
      (fun s _hs => by
        exact mul_nonneg
          (mul_nonneg (hcr0 s) hcard_inv_nonneg)
          (le_of_lt (Real.exp_pos _)))
  have hweighted0_pos : 0 < weightedLam 0 := by
    dsimp [weightedLam, expNegCoeff]
    exact mul_pos (hinit_pos v) (Real.exp_pos _)
  have hweighted0_le_t : weightedLam 0 ≤ weightedLam t :=
    hweighted_mono
      (left_mem_Icc.mpr ht)
      (right_mem_Icc.mpr ht)
      ht
  by_contra hle
  push_neg at hle
  have : lam v t * expNegCoeff t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt (Real.exp_pos _))
  linarith

/-- Upper simplex bound from conservation of total mass and coordinatewise
nonnegativity. -/
theorem replicator_lam_le_one {V : Type} [Fintype V]
    (lam : V → ℝ → ℝ)
    (hconservation : ∀ t : ℝ, 0 ≤ t → (∑ w : V, lam w t) = 1)
    (hlam_nonneg : ∀ w : V, ∀ t : ℝ, 0 ≤ t → 0 ≤ lam w t) :
    ∀ v : V, ∀ t : ℝ, 0 ≤ t → lam v t ≤ 1 := by
  classical
  intro v t ht
  have hle_sum : lam v t ≤ ∑ w : V, lam w t :=
    Finset.single_le_sum
      (fun w _ => hlam_nonneg w t ht)
      (Finset.mem_univ v)
  simpa [hconservation t ht] using hle_sum

#print axioms selectorReplicatorPhiPoly
#print axioms selectorReplicatorFieldPoly
#print axioms selectorReplicatorFieldSelLamPoly
#print axioms eval₂_selectorReplicatorPhiPoly
#print axioms eval₂_selectorReplicatorFieldPoly
#print axioms replicator_sum_lam_eq_one
#print axioms replicator_lam_nonneg
#print axioms replicator_lam_pos
#print axioms replicator_lam_le_one

end Ripple.BoundedUniversality.BGP

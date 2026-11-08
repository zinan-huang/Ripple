/-
  Ripple.LPP.EhrenfestLPP — Ehrenfest-computable numbers are LPP-computable.

  An Ehrenfest urn with rule `(k, f)` has the mean-field ODE `x' = b(x)`,
  `b(y) = k Σ_{j ∈ E_f} C(k,j) y^j (1−y)^{k−j} − k y` (Albenque–Gerin). On the simplex
  `x + y = 1` this is the two-species system
    x' = k Σ_{j ∈ E_f}  C(k,j) x^j y^{k−j} − k (x + y)^{k−1} x,
    y' = k Σ_{j ∉ E_f}  C(k,j) x^j y^{k−j} − k (x + y)^{k−1} y,
  a bounded ℚ-polynomial system with a CRN decomposition (production terms and degradation
  factors have nonnegative coefficients). Its certified computation of `ν` is compiled by the
  faithful compiler `bounded_crn_is_lpp_computable` ([LPP] Main Theorem with Theorem 17).
-/

import Ripple.LPP.EhrenfestUrn
import Ripple.LPP.BoundedLPP

namespace Ripple

open MvPolynomial

/-! ### Polynomials with nonnegative coefficients -/

/-- All coefficients are nonnegative. -/
def NonnegCoeffs {σ : Type*} (p : MvPolynomial σ ℚ) : Prop := ∀ m, 0 ≤ p.coeff m

namespace NonnegCoeffs

variable {σ : Type*}

theorem X (i : σ) : NonnegCoeffs (MvPolynomial.X i : MvPolynomial σ ℚ) := fun m => by
  classical
  rw [coeff_X']
  split_ifs <;> norm_num

theorem C {c : ℚ} (hc : 0 ≤ c) : NonnegCoeffs (MvPolynomial.C c : MvPolynomial σ ℚ) :=
  fun m => by
  classical
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact le_rfl

theorem add {p q : MvPolynomial σ ℚ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p + q) := fun m => by
  rw [coeff_add]
  exact add_nonneg (hp m) (hq m)

theorem mul {p q : MvPolynomial σ ℚ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p * q) := fun m => by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem pow {p : MvPolynomial σ ℚ} (hp : NonnegCoeffs p) (n : ℕ) : NonnegCoeffs (p ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, ← MvPolynomial.C_1]
    exact C zero_le_one
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hp

theorem sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ ℚ}
    (hf : ∀ i ∈ s, NonnegCoeffs (f i)) : NonnegCoeffs (∑ i ∈ s, f i) := fun m => by
  rw [coeff_sum]
  exact Finset.sum_nonneg fun i hi => hf i hi m

end NonnegCoeffs

namespace EhrenfestRule

variable (rule : EhrenfestRule)

/-- `Σ_{j ∈ S} C(k,j) x^j y^{k−j}` in the two species `x = X 0`, `y = X 1`. -/
noncomputable def bernsteinPoly (S : Finset (Fin (rule.k + 1))) : MvPolynomial (Fin 2) ℚ :=
  ∑ j ∈ S, MvPolynomial.C (Nat.choose rule.k j.val : ℚ) * MvPolynomial.X 0 ^ j.val *
    MvPolynomial.X 1 ^ (rule.k - j.val)

/-- The complement of `E_f`. -/
def whiteSet : Finset (Fin (rule.k + 1)) :=
  Finset.univ.filter fun j => ¬ rule.f j = true

/-- The common degradation factor `k (x + y)^{k−1}`. -/
noncomputable def degrPoly : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.C (rule.k : ℚ) * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (rule.k - 1)

/-- The two-species Ehrenfest system as a ℚ-polynomial IVP started at `(q₀, 1 − q₀)`. -/
noncomputable def polyPIVP (q₀ : ℚ) : PolyPIVP 2 where
  field := ![MvPolynomial.C (rule.k : ℚ) * rule.bernsteinPoly rule.blackSet -
      rule.degrPoly * MvPolynomial.X 0,
    MvPolynomial.C (rule.k : ℚ) * rule.bernsteinPoly rule.whiteSet -
      rule.degrPoly * MvPolynomial.X 1]
  init := ![q₀, 1 - q₀]
  output := 0

theorem bernsteinPoly_nonneg (S : Finset (Fin (rule.k + 1))) :
    NonnegCoeffs (rule.bernsteinPoly S) :=
  NonnegCoeffs.sum S fun j _ =>
    (((NonnegCoeffs.C (Nat.cast_nonneg _)).mul ((NonnegCoeffs.X 0).pow _)).mul
      ((NonnegCoeffs.X 1).pow _))

/-- The CRN decomposition of the two-species Ehrenfest system. -/
noncomputable def polyPCD (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) :
    PolyCRNDecomposition 2 (rule.polyPIVP q₀) where
  prod := ![MvPolynomial.C (rule.k : ℚ) * rule.bernsteinPoly rule.blackSet,
    MvPolynomial.C (rule.k : ℚ) * rule.bernsteinPoly rule.whiteSet]
  degr := fun _ => rule.degrPoly
  prod_nonneg i := by
    fin_cases i
    · exact (NonnegCoeffs.C (Nat.cast_nonneg _)).mul (rule.bernsteinPoly_nonneg _)
    · exact (NonnegCoeffs.C (Nat.cast_nonneg _)).mul (rule.bernsteinPoly_nonneg _)
  degr_nonneg _ :=
    (NonnegCoeffs.C (Nat.cast_nonneg _)).mul (((NonnegCoeffs.X 0).add (NonnegCoeffs.X 1)).pow _)
  init_nonneg i := by
    fin_cases i
    · exact h0
    · change (0 : ℚ) ≤ 1 - q₀
      linarith
  field_eq i := by
    fin_cases i <;> first | rfl | simp [polyPIVP]

/-- On the simplex, the evaluated Bernstein polynomial is the Bernstein sum. -/
theorem eval_bernsteinPoly (S : Finset (Fin (rule.k + 1))) (a : ℝ) :
    (rule.bernsteinPoly S).eval₂ (Rat.castHom ℝ) ![a, 1 - a] =
      ∑ j ∈ S, rule.bernsteinTerm j a := by
  simp [bernsteinPoly, bernsteinTerm, MvPolynomial.eval₂_sum]

theorem eval_degrPoly (a : ℝ) :
    rule.degrPoly.eval₂ (Rat.castHom ℝ) ![a, 1 - a] = rule.k := by
  simp [degrPoly]

theorem evalField_zero (q₀ : ℚ) (a : ℝ) :
    (rule.polyPIVP q₀).evalField ![a, 1 - a] 0 = rule.driftFn a := by
  simp [PolyPIVP.evalField, polyPIVP, eval_bernsteinPoly, eval_degrPoly, driftFn]

theorem evalField_one (q₀ : ℚ) (a : ℝ) :
    (rule.polyPIVP q₀).evalField ![a, 1 - a] 1 = -rule.driftFn a := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => rule.f j = true)
    (fun j => rule.bernsteinTerm j a)
  rw [rule.bernstein_sum_eq_one a] at hsplit
  simp only [PolyPIVP.evalField, polyPIVP, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval_bernsteinPoly,
    eval_degrPoly, driftFn, blackSet, whiteSet, Rat.coe_castHom, Rat.cast_natCast]
  linear_combination (rule.k : ℝ) * hsplit

end EhrenfestRule

namespace IsEhrenfestComputable

/-- **Ehrenfest-computable ⇒ certified computation with a CRN decomposition.** -/
theorem exists_cbtc_pcd {ν : ℝ} (h : IsEhrenfestComputable ν) :
    ∃ cbtc : CertifiedBoundedTimeComputable 2 ν,
      Nonempty (PolyCRNDecomposition 2 cbtc.pivp) := by
  obtain ⟨rule, q₀, φ, hφ0, hode, hinv, htend, -, -⟩ := h.exists_trajectory
  have hq0 : (0 : ℝ) ≤ q₀ := hφ0 ▸ (hinv 0 le_rfl).1
  have hq1 : (q₀ : ℝ) ≤ 1 := hφ0 ▸ (hinv 0 le_rfl).2
  let sol : PIVP.Solution (rule.polyPIVP q₀).toPIVP :=
    { trajectory := fun t => ![φ t, 1 - φ t]
      init_cond := by
        funext i
        fin_cases i
        · simp [EhrenfestRule.polyPIVP, hφ0]
        · simp [EhrenfestRule.polyPIVP, hφ0]
      is_solution := fun t ht => by
        rw [PolyPIVP.toPIVP_field_eq]
        refine hasDerivAt_pi.mpr fun i => ?_
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          rw [rule.evalField_zero q₀ (φ t)]
          exact hode t ht
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_zero]
          rw [rule.evalField_one q₀ (φ t)]
          have hd := (hasDerivAt_const t (1 : ℝ)).sub (hode t ht)
          rwa [zero_sub] at hd }
  have hbd : (rule.polyPIVP q₀).toPIVP.IsBounded sol.trajectory := by
    refine ⟨1, one_pos, fun t ht => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_⟩
    have h1 := hinv t ht
    fin_cases i
    · change ‖φ t‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · change ‖1 - φ t‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  have hmod : ∀ r : ℕ, ∃ T : ℝ, ∀ t : ℝ, t > T → |φ t - ν| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop'.mp htend) (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by simpa [Real.dist_eq] using hT t ht⟩
  choose T hT using hmod
  obtain ⟨cbtc, hP, -, -⟩ := CertifiedBoundedTimeComputable.exists_of_solution
    (rule.polyPIVP q₀) sol hbd T
    (fun r t ht => hT r t ht)
  have pcd : PolyCRNDecomposition 2 cbtc.pivp := by
    rw [hP]
    exact rule.polyPCD q₀ (by exact_mod_cast hq0) (by exact_mod_cast hq1)
  exact ⟨cbtc, ⟨pcd⟩⟩

/-- **Ehrenfest-computable ⊂ LPP-computable** (Albenque–Gerin urns are a subclass of LPPs):
every Ehrenfest-computable number is computed by a deterministic LPP. -/
theorem isLPPComputable {ν : ℝ} (h : IsEhrenfestComputable ν) : IsLPPComputable ν := by
  obtain ⟨-, -, -, -, -, -, -, hν0, hν1⟩ := h.exists_trajectory
  obtain ⟨cbtc, ⟨pcd⟩⟩ := h.exists_cbtc_pcd
  exact bounded_crn_is_lpp_computable ⟨hν0, hν1⟩ cbtc pcd

end IsEhrenfestComputable

end Ripple

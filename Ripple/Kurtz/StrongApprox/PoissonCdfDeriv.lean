/-
  Ripple.Kurtz.StrongApprox.PoissonCdfDeriv — derivative of the Poisson cdf in the parameter

  First ingredient of the direct proof of the Poisson intersection (PI).

  `poisTerm j λ = e^{−λ} λ^j / j!`, `poisCdf k λ = Σ_{j<k} poisTerm j λ = P(Pois(λ) ≤ k−1)`.
  The finite sum telescopes under differentiation: `d/dλ poisCdf (k+1) λ = −poisTerm k λ`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

/-- Poisson point mass `e^{−λ} λ^j / j!` as a function of the parameter. -/
noncomputable def poisTerm (j : ℕ) (l : ℝ) : ℝ := Real.exp (-l) * l ^ j / (j.factorial : ℝ)

/-- `P(Pois(λ) ≤ k − 1) = Σ_{j < k} poisTerm j λ`. -/
noncomputable def poisCdf (k : ℕ) (l : ℝ) : ℝ := ∑ j ∈ Finset.range k, poisTerm j l

theorem poisTerm_nonneg (j : ℕ) {l : ℝ} (hl : 0 ≤ l) : 0 ≤ poisTerm j l := by
  unfold poisTerm; positivity

theorem hasDerivAt_poisTerm_zero (l : ℝ) :
    HasDerivAt (poisTerm 0) (-(Real.exp (-l))) l := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-l) * (-1)) l :=
    (hasDerivAt_neg l).exp
  convert h1 using 1
  · funext x; simp [poisTerm]
  · ring

theorem hasDerivAt_poisTerm_succ (j : ℕ) (l : ℝ) :
    HasDerivAt (poisTerm (j + 1)) (poisTerm j l - poisTerm (j + 1) l) l := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-l) * (-1)) l :=
    (hasDerivAt_neg l).exp
  have h2 : HasDerivAt (fun x : ℝ => x ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * l ^ (j + 1 - 1)) l :=
    hasDerivAt_pow (j + 1) l
  have h3 := (h1.mul h2).div_const ((j + 1).factorial : ℝ)
  refine h3.congr_deriv ?_
  unfold poisTerm
  rw [Nat.factorial_succ]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- `d/dλ P(Pois(λ) ≤ k) = −e^{−λ} λ^k / k!`. -/
theorem hasDerivAt_poisCdf (k : ℕ) (l : ℝ) :
    HasDerivAt (poisCdf (k + 1)) (-(poisTerm k l)) l := by
  induction k with
  | zero =>
    have : poisCdf 1 = poisTerm 0 := by funext x; simp [poisCdf]
    rw [this]
    convert hasDerivAt_poisTerm_zero l using 1
    simp [poisTerm]
  | succ k ih =>
    have hfun : poisCdf (k + 2) = fun x => poisCdf (k + 1) x + poisTerm (k + 1) x := by
      funext x; simp [poisCdf, Finset.sum_range_succ]
    rw [hfun]
    convert ih.add (hasDerivAt_poisTerm_succ k l) using 1
    ring

end Ripple.Kurtz.StrongApprox

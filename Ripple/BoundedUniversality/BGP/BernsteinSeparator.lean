import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Ripple.BoundedUniversality.BGP.LatchAssembly

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Polynomial

/-- Evaluate a rational univariate polynomial as a real polynomial. -/
def evalR (H : Polynomial ℚ) (x : ℝ) : ℝ :=
  (H.map (algebraMap ℚ ℝ)).eval x

/-- A deterministic natural strictly above a real threshold. -/
def bernsteinDegreeAbove (x : ℝ) : ℕ :=
  Nat.ceil x + 1

theorem lt_bernsteinDegreeAbove (x : ℝ) :
    x < (bernsteinDegreeAbove x : ℝ) := by
  unfold bernsteinDegreeAbove
  have hxceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hlt : (Nat.ceil x : ℝ) < (Nat.ceil x + 1 : ℕ) := by
    exact_mod_cast Nat.lt_succ_self (Nat.ceil x)
  exact lt_of_le_of_lt hxceil hlt

theorem bernsteinDegreeAbove_pos (x : ℝ) :
    0 < bernsteinDegreeAbove x := by
  unfold bernsteinDegreeAbove
  exact Nat.succ_pos _

theorem bernsteinDegreeAbove_ne_zero (x : ℝ) :
    bernsteinDegreeAbove x ≠ 0 :=
  (bernsteinDegreeAbove_pos x).ne'

theorem bernsteinDegreeAbove_le_add_two {x : ℝ} (hx : 0 ≤ x) :
    (bernsteinDegreeAbove x : ℝ) ≤ x + 2 := by
  unfold bernsteinDegreeAbove
  have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hceil_le : (Nat.ceil x : ℝ) ≤ x + 1 := le_of_lt hceil
  norm_num
  linarith

/-- Public affine transport `[-C,C] -> [0,1]` for rational Bernstein atoms. -/
def bernsteinAffinePhi (C : ℚ) : Polynomial ℚ :=
  Polynomial.C (1 / (2 * C)) * Polynomial.X + Polynomial.C (1 / 2)

/-- Explicit Bernstein polynomial with rational samples after affine transport. -/
def bernstein01Poly
    (C : ℚ) (n : ℕ) (g : Fin (n + 1) → ℚ) : Polynomial ℚ :=
  ∑ k : Fin (n + 1),
    Polynomial.C (g k) *
      (bernsteinPolynomial ℚ n k).comp (bernsteinAffinePhi C)

private def affinePhi (C : ℚ) : Polynomial ℚ :=
  bernsteinAffinePhi C

/-- The rational grid point used by the explicit Bernstein slab constructors. -/
def rationalBernsteinSamplePoint (C : ℚ) (n : ℕ) (k : Fin (n + 1)) : ℚ :=
  2 * C * ((k : ℚ) / (n : ℚ)) - C

/-- Deterministic degree for a finite point separator on a slab. -/
def rationalBernsteinSeparatorDegree (C etaH : ℚ) : ℕ :=
  bernsteinDegreeAbove (64 * (C : ℝ) ^ 2 / (etaH : ℝ))

/-- Explicit samples for a finite point separator. -/
def rationalBernsteinSeparatorSample
    (C : ℚ) (n : ℕ) (ones : Finset ℝ) (rho : ℚ) :
    Fin (n + 1) → ℚ :=
  fun k =>
    if ∃ a ∈ ones, |(rationalBernsteinSamplePoint C n k : ℝ) - a| ≤
        (rho : ℝ) + 1 / 4 then 1 else 0

/-- Explicit deterministic finite point separator polynomial. -/
def rationalBernsteinSeparatorPoly
    (C etaH : ℚ) (ones : Finset ℝ) (rho : ℚ) : Polynomial ℚ :=
  let n := rationalBernsteinSeparatorDegree C etaH
  bernstein01Poly C n (rationalBernsteinSeparatorSample C n ones rho)

/-- Deterministic degree for a one-sided interval step on a slab. -/
def rationalBernsteinOneSidedDegree (C : ℚ) (mu : ℝ) (etaH : ℚ) : ℕ :=
  let delta : ℝ := mu / (2 * (C : ℝ))
  bernsteinDegreeAbove (1 / (4 * (etaH : ℝ) * delta ^ 2))

/-- Explicit samples for a one-sided threshold step. -/
def rationalBernsteinOneSidedSample
    (C : ℚ) (n : ℕ) (theta : ℝ) : Fin (n + 1) → ℚ :=
  fun k => if theta ≤ (rationalBernsteinSamplePoint C n k : ℝ) then 1 else 0

/-- Explicit deterministic one-sided threshold step. -/
def rationalBernsteinOneSidedStepPoly
    (C : ℚ) (theta mu : ℝ) (etaH : ℚ) : Polynomial ℚ :=
  let n := rationalBernsteinOneSidedDegree C mu etaH
  bernstein01Poly C n (rationalBernsteinOneSidedSample C n theta)

/-- Explicit deterministic two-sided interval atom. -/
def rationalBernsteinIntervalAtomPoly
    (C : ℚ) (tlo thi mu : ℝ) (etaH : ℚ) : Polynomial ℚ :=
  rationalBernsteinOneSidedStepPoly C tlo mu etaH *
    (1 - rationalBernsteinOneSidedStepPoly C thi mu etaH)

/-- Explicit deterministic code-indexed interval atom family. -/
def rationalBernsteinIntervalAtomFamilyPoly
    (C : ℚ) {A : Type} (lo hi : A → ℝ) (gap : ℝ)
    (etaH : ℚ) (a : A) : Polynomial ℚ :=
  rationalBernsteinIntervalAtomPoly C (lo a - gap / 2) (hi a + gap / 2)
    (gap / 2) etaH

private lemma evalR_affinePhi (C : ℚ) (hC : 0 < C) (x : ℝ) :
    evalR (affinePhi C) x = (x + (C : ℝ)) / (2 * (C : ℝ)) := by
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  simp [evalR, affinePhi, bernsteinAffinePhi]
  field_simp [hC0]

private lemma affinePhi_mem_Icc (C : ℚ) (hC : 0 < C) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    0 ≤ (x + (C : ℝ)) / (2 * (C : ℝ)) ∧
      (x + (C : ℝ)) / (2 * (C : ℝ)) ≤ 1 := by
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hxlo : -(C : ℝ) ≤ x := by
    exact (abs_le.mp hx).1
  have hxhi : x ≤ (C : ℝ) := (abs_le.mp hx).2
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_one (by positivity)]
    linarith

private lemma bernsteinPolynomial_eval_nonneg (n k : ℕ) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval y := by
  rw [bernsteinPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have h1 : 0 ≤ 1 - y := by linarith
  positivity

private lemma bernsteinPolynomial_eval_sum (n : ℕ) (y : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval y) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval y) (bernsteinPolynomial.sum (R := ℝ) n)
  simpa [Polynomial.eval_finset_sum] using h

private lemma bernsteinPolynomial_eval_variance
    (n : ℕ) (hn0 : n ≠ 0) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∑ k : Fin (n + 1), (y - (k : ℝ) / (n : ℝ)) ^ 2 *
      (bernsteinPolynomial ℝ n k).eval y) = y * (1 - y) / n := by
  let yI : Set.Icc (0 : ℝ) 1 := ⟨y, hy0, hy1⟩
  have h := bernstein.variance hn0 yI
  simpa [bernstein, yI] using h

private lemma bernsteinPolynomial_eval_bad_mass_le
    (n : ℕ) (hn0 : n ≠ 0) {y δ : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hδ : 0 < δ) (S : Finset (Fin (n + 1)))
    (hS : ∀ k ∈ S, δ ≤ |y - (k : ℝ) / (n : ℝ)|) :
    ∑ k ∈ S, (bernsteinPolynomial ℝ n k).eval y ≤
      1 / (4 * (n : ℝ) * δ ^ 2) := by
  have hvar := bernsteinPolynomial_eval_variance n hn0 hy0 hy1
  calc
    ∑ k ∈ S, (bernsteinPolynomial ℝ n k).eval y
        ≤ ∑ k ∈ S, ((y - (k : ℝ) / (n : ℝ)) ^ 2 / δ ^ 2) *
            (bernsteinPolynomial ℝ n k).eval y := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hb : 0 ≤ (bernsteinPolynomial ℝ n k).eval y :=
            bernsteinPolynomial_eval_nonneg n k hy0 hy1
          have habs : |δ| ≤ |y - (k : ℝ) / (n : ℝ)| := by
            simpa [abs_of_pos hδ] using hS k hk
          have hsq : δ ^ 2 ≤ (y - (k : ℝ) / (n : ℝ)) ^ 2 :=
            sq_le_sq.mpr habs
          have hone : 1 ≤ (y - (k : ℝ) / (n : ℝ)) ^ 2 / δ ^ 2 := by
            rw [one_le_div₀]
            · exact hsq
            · exact sq_pos_of_pos hδ
          calc
            (bernsteinPolynomial ℝ n k).eval y =
                1 * (bernsteinPolynomial ℝ n k).eval y := by ring
            _ ≤ ((y - (k : ℝ) / (n : ℝ)) ^ 2 / δ ^ 2) *
                (bernsteinPolynomial ℝ n k).eval y := by gcongr
    _ ≤ ∑ k : Fin (n + 1), ((y - (k : ℝ) / (n : ℝ)) ^ 2 / δ ^ 2) *
            (bernsteinPolynomial ℝ n k).eval y := by
          refine Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ ?_
          intro k _ _
          have hb : 0 ≤ (bernsteinPolynomial ℝ n k).eval y :=
            bernsteinPolynomial_eval_nonneg n k hy0 hy1
          positivity
    _ = (∑ k : Fin (n + 1), (y - (k : ℝ) / (n : ℝ)) ^ 2 *
            (bernsteinPolynomial ℝ n k).eval y) / δ ^ 2 := by
          calc
            ∑ k : Fin (n + 1), ((y - (k : ℝ) / (n : ℝ)) ^ 2 / δ ^ 2) *
                (bernsteinPolynomial ℝ n k).eval y
                = ∑ k : Fin (n + 1), ((y - (k : ℝ) / (n : ℝ)) ^ 2 *
                    (bernsteinPolynomial ℝ n k).eval y) / δ ^ 2 := by
                    refine Finset.sum_congr rfl fun k _ => by ring
            _ = (∑ k : Fin (n + 1), (y - (k : ℝ) / (n : ℝ)) ^ 2 *
                    (bernsteinPolynomial ℝ n k).eval y) / δ ^ 2 := by
                    rw [Finset.sum_div]
    _ = (y * (1 - y) / n) / δ ^ 2 := by rw [hvar]
    _ ≤ 1 / (4 * (n : ℝ) * δ ^ 2) := by
          have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
          have hyprod : y * (1 - y) ≤ 1 / 4 := by
            nlinarith [sq_nonneg (y - 1 / 2)]
          have hden : 0 < (n : ℝ) * δ ^ 2 := by positivity
          calc
            (y * (1 - y) / n) / δ ^ 2 =
                (y * (1 - y)) / ((n : ℝ) * δ ^ 2) := by ring
            _ ≤ (1 / 4) / ((n : ℝ) * δ ^ 2) := by gcongr
            _ = 1 / (4 * (n : ℝ) * δ ^ 2) := by ring

private lemma bernsteinPolynomial_eval_bad_mass_le_C
    (C : ℚ) (hC : 0 < C) (n : ℕ) (hn0 : n ≠ 0) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (S : Finset (Fin (n + 1)))
    (hS : ∀ k ∈ S, 1 / (8 * (C : ℝ)) ≤ |y - (k : ℝ) / (n : ℝ)|) :
    ∑ k ∈ S, (bernsteinPolynomial ℝ n k).eval y ≤
      16 * (C : ℝ) ^ 2 / (n : ℝ) := by
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  calc
    ∑ k ∈ S, (bernsteinPolynomial ℝ n k).eval y
        ≤ 1 / (4 * (n : ℝ) * (1 / (8 * (C : ℝ))) ^ 2) :=
          bernsteinPolynomial_eval_bad_mass_le n hn0 hy0 hy1
            (by positivity) S hS
    _ = 16 * (C : ℝ) ^ 2 / (n : ℝ) := by
          have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
          field_simp [hCr.ne', hnpos.ne']
          ring

private lemma bernstein_subconvex_range
    (n : ℕ) (g : Fin (n + 1) → ℚ) (hg : ∀ k, g k = 0 ∨ g k = 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (∑ k : Fin (n + 1), (g k : ℝ) * (bernsteinPolynomial ℝ n k).eval y) ∧
      (∑ k : Fin (n + 1), (g k : ℝ) * (bernsteinPolynomial ℝ n k).eval y) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun k _ => by
      rcases hg k with h | h <;> simp [h, bernsteinPolynomial_eval_nonneg n k hy0 hy1]
  · calc
      (∑ k : Fin (n + 1), (g k : ℝ) * (bernsteinPolynomial ℝ n k).eval y)
          ≤ ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval y := by
            refine Finset.sum_le_sum fun k _ => ?_
            have hb := bernsteinPolynomial_eval_nonneg n k hy0 hy1
            rcases hg k with h | h <;> simp [h, hb]
      _ = ∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval y := by
            simpa [Finset.sum_range]
      _ = 1 := bernsteinPolynomial_eval_sum n y

private lemma evalR_bernstein_sum
    (C : ℚ) (hC : 0 < C) (n : ℕ) (g : Fin (n + 1) → ℚ) (x : ℝ) :
    evalR (∑ k : Fin (n + 1),
        Polynomial.C (g k) * (bernsteinPolynomial ℚ n k).comp (affinePhi C)) x =
      ∑ k : Fin (n + 1), (g k : ℝ) *
        (bernsteinPolynomial ℝ n k).eval ((x + (C : ℝ)) / (2 * (C : ℝ))) := by
  unfold evalR
  simp only [Polynomial.map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [Polynomial.map_comp, Polynomial.eval_comp]
  have hphi := evalR_affinePhi C hC x
  unfold evalR at hphi
  rw [hphi, bernsteinPolynomial.map]
  simp

private lemma eval₂_polynomial_aeval_X {d : ℕ} (stateCoord : Fin d)
    (H : Polynomial ℚ) (x : Fin d → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
        (Polynomial.aeval (MvPolynomial.X stateCoord) H) =
      evalR H (x stateCoord) := by
  rw [show evalR H (x stateCoord) =
      Polynomial.eval₂ (algebraMap ℚ ℝ) (x stateCoord) H by
        simp [evalR, Polynomial.eval₂_eq_eval_map]]
  induction H using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | monomial n a =>
      simp

/-- Rational Bernstein separator on a rational slab.  The construction is the
Bernstein polynomial with rational `0/1` samples after the affine transport
`[-C,C] -> [0,1]`. -/
theorem rationalBernsteinSeparatorPoly_spec
    (C : ℚ) (hC : 0 < C)
    (ones zeros : Finset ℝ)
    (hgap : ∀ a ∈ ones, ∀ b ∈ zeros, 1 ≤ |a - b|)
    (hin : ∀ v ∈ ones ∪ zeros, |v| + 1 ≤ (C : ℝ))
    (rho etaH : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1/4)
    (heta : 0 < etaH) :
    (∀ x : ℝ, |x| ≤ (C : ℝ) →
        0 ≤ evalR (rationalBernsteinSeparatorPoly C etaH ones rho) x ∧
          evalR (rationalBernsteinSeparatorPoly C etaH ones rho) x ≤ 1) ∧
      (∀ a ∈ ones, ∀ x : ℝ, |x - a| ≤ (rho : ℝ) →
        1 - (etaH : ℝ) ≤
          evalR (rationalBernsteinSeparatorPoly C etaH ones rho) x) ∧
      (∀ b ∈ zeros, ∀ x : ℝ, |x - b| ≤ (rho : ℝ) →
        evalR (rationalBernsteinSeparatorPoly C etaH ones rho) x ≤
          (etaH : ℝ)) := by
  classical
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hetaR : 0 < (etaH : ℝ) := by exact_mod_cast heta
  let n : ℕ := rationalBernsteinSeparatorDegree C etaH
  have hnlarge : (64 * (C : ℝ) ^ 2) / (etaH : ℝ) < (n : ℝ) := by
    simpa [n, rationalBernsteinSeparatorDegree] using
      lt_bernsteinDegreeAbove (64 * (C : ℝ) ^ 2 / (etaH : ℝ))
  have hn0 : n ≠ 0 := by
    simpa [n, rationalBernsteinSeparatorDegree] using
      bernsteinDegreeAbove_ne_zero (64 * (C : ℝ) ^ 2 / (etaH : ℝ))
  let samplePoint : Fin (n + 1) → ℚ :=
    fun k => 2 * C * ((k : ℚ) / (n : ℚ)) - C
  let g : Fin (n + 1) → ℚ :=
    fun k => if ∃ a ∈ ones, |(samplePoint k : ℝ) - a| ≤
      (rho : ℝ) + 1 / 4 then 1 else 0
  let H : Polynomial ℚ := rationalBernsteinSeparatorPoly C etaH ones rho
  have hHeval : ∀ x : ℝ,
      evalR H x =
        ∑ k : Fin (n + 1), (g k : ℝ) *
          (bernsteinPolynomial ℝ n k).eval
            ((x + (C : ℝ)) / (2 * (C : ℝ))) := by
    intro x
    simpa [H, rationalBernsteinSeparatorPoly, n, g, samplePoint,
      rationalBernsteinSeparatorSample, rationalBernsteinSamplePoint,
      bernstein01Poly, affinePhi, bernsteinAffinePhi] using
      evalR_bernstein_sum C hC n g x
  change
    (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ a ∈ ones, ∀ x : ℝ, |x - a| ≤ (rho : ℝ) →
        1 - (etaH : ℝ) ≤ evalR H x) ∧
      (∀ b ∈ zeros, ∀ x : ℝ, |x - b| ≤ (rho : ℝ) →
        evalR H x ≤ (etaH : ℝ))
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hy := affinePhi_mem_Icc C hC hx
    have hg : ∀ k, g k = 0 ∨ g k = 1 := by
      intro k
      by_cases h : ∃ a ∈ ones, |(samplePoint k : ℝ) - a| ≤
          (rho : ℝ) + 1 / 4
      · right
        dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
          rationalBernsteinSamplePoint]
        rw [if_pos h]
      · left
        dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
          rationalBernsteinSamplePoint]
        rw [if_neg h]
    simpa [hHeval x] using
      bernstein_subconvex_range n g hg hy.1 hy.2
  · intro a ha x hx
    let y : ℝ := (x + (C : ℝ)) / (2 * (C : ℝ))
    have hslab : |x| ≤ (C : ℝ) := by
      have hain : a ∈ ones ∪ zeros := by simp [ha]
      have haC := hin a hain
      have hxa' : |x| ≤ |a| + (rho : ℝ) := by
        calc
          |x| = |(x - a) + a| := by
            congr 1
            ring
          _ ≤ |x - a| + |a| := by exact abs_add_le _ _
          _ ≤ |a| + (rho : ℝ) := by linarith
      have hrho_le_one : (rho : ℝ) ≤ 1 := by
        exact_mod_cast (le_trans hrho4 (by norm_num : (1 / 4 : ℚ) ≤ 1))
      linarith
    have hy := affinePhi_mem_Icc C hC hslab
    have hg : ∀ k, g k = 0 ∨ g k = 1 := by
        intro k
        by_cases h : ∃ a ∈ ones, |(samplePoint k : ℝ) - a| ≤
            (rho : ℝ) + 1 / 4
        · right
          dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
            rationalBernsteinSamplePoint]
          rw [if_pos h]
        · left
          dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
            rationalBernsteinSamplePoint]
          rw [if_neg h]
    have hmain : 1 - (etaH : ℝ) ≤ evalR H x := by
      let B : Fin (n + 1) → ℝ := fun k => (bernsteinPolynomial ℝ n k).eval y
      let bad : Finset (Fin (n + 1)) := Finset.univ.filter fun k => g k = 0
      have hsumB : (∑ k : Fin (n + 1), B k) = 1 := by
        simpa [B, Finset.sum_range] using bernsteinPolynomial_eval_sum n y
      have hcompl :
          1 - (∑ k : Fin (n + 1), (g k : ℝ) * B k) =
            ∑ k ∈ bad, B k := by
        rw [← hsumB, ← Finset.sum_sub_distrib, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        rcases hg k with h0 | h1
        · simp [bad, h0]
        · simp [bad, h1]
      have hbad_far :
          ∀ k ∈ bad, 1 / (8 * (C : ℝ)) ≤ |y - (k : ℝ) / (n : ℝ)| := by
        intro k hk
        have hk0 : g k = 0 := by simpa [bad] using hk
        have hnot : ¬ ∃ a ∈ ones, |(samplePoint k : ℝ) - a| ≤
            (rho : ℝ) + 1 / 4 := by
          intro hex
          have hg1 : g k = 1 := by
            dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
              rationalBernsteinSamplePoint]
            rw [if_pos hex]
          norm_num [hk0] at hg1
        have hnotle : ¬ |(samplePoint k : ℝ) - a| ≤ (rho : ℝ) + 1 / 4 := by
          intro hle
          exact hnot ⟨a, ha, hle⟩
        have hspa : (rho : ℝ) + 1 / 4 < |(samplePoint k : ℝ) - a| :=
          lt_of_not_ge hnotle
        have htri : |(samplePoint k : ℝ) - a| ≤
            |(samplePoint k : ℝ) - x| + |x - a| := by
          calc
            |(samplePoint k : ℝ) - a| =
                |((samplePoint k : ℝ) - x) + (x - a)| := by
                  congr 1
                  ring
            _ ≤ |(samplePoint k : ℝ) - x| + |x - a| := abs_add_le _ _
        have hspx : (1 / 4 : ℝ) ≤ |(samplePoint k : ℝ) - x| := by
          nlinarith
        have hsample :
            (samplePoint k : ℝ) =
              2 * (C : ℝ) * ((k : ℝ) / (n : ℝ)) - (C : ℝ) := by
          dsimp [samplePoint, rationalBernsteinSamplePoint]
          push_cast
          ring
        have hyx : x = 2 * (C : ℝ) * y - (C : ℝ) := by
          dsimp [y]
          field_simp [(ne_of_gt hCr).symm]
          ring
        have hspx_eq :
            |(samplePoint k : ℝ) - x| =
              2 * (C : ℝ) * |y - (k : ℝ) / (n : ℝ)| := by
          rw [hsample, hyx]
          have :
              2 * (C : ℝ) * ((k : ℝ) / (n : ℝ)) - (C : ℝ) -
                  (2 * (C : ℝ) * y - (C : ℝ)) =
                2 * (C : ℝ) * ((k : ℝ) / (n : ℝ) - y) := by ring
          rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * (C : ℝ)),
            abs_sub_comm]
        rw [hspx_eq] at hspx
        rw [mul_comm] at hspx
        have hdiv : (1 / 4 : ℝ) / (2 * (C : ℝ)) ≤
            |y - (k : ℝ) / (n : ℝ)| :=
          (div_le_iff₀ (by positivity : 0 < 2 * (C : ℝ))).mpr hspx
        convert hdiv using 1
        field_simp [(ne_of_gt hCr).symm]
        ring
      have hbad_le :
          ∑ k ∈ bad, B k ≤ (etaH : ℝ) := by
        have hmass :=
          bernsteinPolynomial_eval_bad_mass_le_C C hC n hn0 hy.1 hy.2 bad hbad_far
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have h64 : 64 * (C : ℝ) ^ 2 < (etaH : ℝ) * n := by
          have := mul_lt_mul_of_pos_right hnlarge hetaR
          field_simp [(ne_of_gt hetaR).symm] at this
          linarith
        have h16 : 16 * (C : ℝ) ^ 2 / (n : ℝ) ≤ (etaH : ℝ) := by
          rw [div_le_iff₀ hnpos]
          nlinarith [sq_nonneg (C : ℝ)]
        exact le_trans (by simpa [B] using hmass) h16
      have heval :
          evalR H x = ∑ k : Fin (n + 1), (g k : ℝ) * B k := by
        simpa [B, y] using hHeval x
      rw [heval]
      have : 1 - (∑ k : Fin (n + 1), (g k : ℝ) * B k) ≤ (etaH : ℝ) := by
        rw [hcompl]
        exact hbad_le
      linarith
    exact hmain
  · intro b hb x hx
    let y : ℝ := (x + (C : ℝ)) / (2 * (C : ℝ))
    have hslab : |x| ≤ (C : ℝ) := by
      have hbin : b ∈ ones ∪ zeros := by simp [hb]
      have hbC := hin b hbin
      have hxb' : |x| ≤ |b| + (rho : ℝ) := by
        calc
          |x| = |(x - b) + b| := by
            congr 1
            ring
          _ ≤ |x - b| + |b| := by exact abs_add_le _ _
          _ ≤ |b| + (rho : ℝ) := by linarith
      have hrho_le_one : (rho : ℝ) ≤ 1 := by
        exact_mod_cast (le_trans hrho4 (by norm_num : (1 / 4 : ℚ) ≤ 1))
      linarith
    have hy := affinePhi_mem_Icc C hC hslab
    have hg : ∀ k, g k = 0 ∨ g k = 1 := by
        intro k
        by_cases h : ∃ a ∈ ones, |(samplePoint k : ℝ) - a| ≤
            (rho : ℝ) + 1 / 4
        · right
          dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
            rationalBernsteinSamplePoint]
          rw [if_pos h]
        · left
          dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
            rationalBernsteinSamplePoint]
          rw [if_neg h]
    have hmain : evalR H x ≤ (etaH : ℝ) := by
      let B : Fin (n + 1) → ℝ := fun k => (bernsteinPolynomial ℝ n k).eval y
      let good : Finset (Fin (n + 1)) := Finset.univ.filter fun k => g k = 1
      have hgood_sum :
          (∑ k : Fin (n + 1), (g k : ℝ) * B k) =
            ∑ k ∈ good, B k := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        rcases hg k with h0 | h1
        · simp [good, h0]
        · simp [good, h1]
      have hgood_far :
          ∀ k ∈ good, 1 / (8 * (C : ℝ)) ≤ |y - (k : ℝ) / (n : ℝ)| := by
        intro k hk
        have hk1 : g k = 1 := by simpa [good] using hk
        have hex : ∃ a ∈ ones, |(samplePoint k : ℝ) - a| ≤
            (rho : ℝ) + 1 / 4 := by
          by_contra hnone
          have hg0 : g k = 0 := by
            dsimp [g, rationalBernsteinSeparatorSample, samplePoint,
              rationalBernsteinSamplePoint]
            rw [if_neg hnone]
          norm_num [hk1] at hg0
        obtain ⟨a, ha, hka⟩ := hex
        have hab : 1 ≤ |a - b| := hgap a ha b hb
        have htri : |a - b| ≤ |a - (samplePoint k : ℝ)| +
            |(samplePoint k : ℝ) - x| + |x - b| := by
          calc
            |a - b| =
                |(a - (samplePoint k : ℝ)) + (((samplePoint k : ℝ) - x) + (x - b))| := by
                  congr 1
                  ring
            _ ≤ |a - (samplePoint k : ℝ)| +
                |((samplePoint k : ℝ) - x) + (x - b)| := abs_add_le _ _
            _ ≤ |a - (samplePoint k : ℝ)| +
                (|(samplePoint k : ℝ) - x| + |x - b|) := by
                  gcongr
                  exact abs_add_le _ _
            _ = |a - (samplePoint k : ℝ)| +
                |(samplePoint k : ℝ) - x| + |x - b| := by ring
        have hrhoR : (rho : ℝ) ≤ (1 / 4 : ℝ) := by
          have hcast : (rho : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) :=
            (Rat.cast_le (K := ℝ)).mpr hrho4
          norm_num at hcast
          exact hcast
        have hka' : |a - (samplePoint k : ℝ)| ≤ (rho : ℝ) + 1 / 4 := by
          simpa [abs_sub_comm] using hka
        have hspx : (1 / 4 : ℝ) ≤ |(samplePoint k : ℝ) - x| := by
          nlinarith
        have hsample :
            (samplePoint k : ℝ) =
              2 * (C : ℝ) * ((k : ℝ) / (n : ℝ)) - (C : ℝ) := by
          dsimp [samplePoint, rationalBernsteinSamplePoint]
          push_cast
          ring
        have hyx : x = 2 * (C : ℝ) * y - (C : ℝ) := by
          dsimp [y]
          field_simp [(ne_of_gt hCr).symm]
          ring
        have hspx_eq :
            |(samplePoint k : ℝ) - x| =
              2 * (C : ℝ) * |y - (k : ℝ) / (n : ℝ)| := by
          rw [hsample, hyx]
          have :
              2 * (C : ℝ) * ((k : ℝ) / (n : ℝ)) - (C : ℝ) -
                  (2 * (C : ℝ) * y - (C : ℝ)) =
                2 * (C : ℝ) * ((k : ℝ) / (n : ℝ) - y) := by ring
          rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * (C : ℝ)),
            abs_sub_comm]
        rw [hspx_eq] at hspx
        rw [mul_comm] at hspx
        have hdiv : (1 / 4 : ℝ) / (2 * (C : ℝ)) ≤
            |y - (k : ℝ) / (n : ℝ)| :=
          (div_le_iff₀ (by positivity : 0 < 2 * (C : ℝ))).mpr hspx
        convert hdiv using 1
        field_simp [(ne_of_gt hCr).symm]
        ring
      have hgood_le :
          ∑ k ∈ good, B k ≤ (etaH : ℝ) := by
        have hmass :=
          bernsteinPolynomial_eval_bad_mass_le_C C hC n hn0 hy.1 hy.2 good hgood_far
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have h64 : 64 * (C : ℝ) ^ 2 < (etaH : ℝ) * n := by
          have := mul_lt_mul_of_pos_right hnlarge hetaR
          field_simp [(ne_of_gt hetaR).symm] at this
          linarith
        have h16 : 16 * (C : ℝ) ^ 2 / (n : ℝ) ≤ (etaH : ℝ) := by
          rw [div_le_iff₀ hnpos]
          nlinarith [sq_nonneg (C : ℝ)]
        exact le_trans (by simpa [B] using hmass) h16
      have heval :
          evalR H x = ∑ k : Fin (n + 1), (g k : ℝ) * B k := by
        simpa [B, y] using hHeval x
      rw [heval, hgood_sum]
      exact hgood_le
    exact hmain

theorem rational_bernstein_separator
    (C : ℚ) (hC : 0 < C)
    (ones zeros : Finset ℝ)
    (hgap : ∀ a ∈ ones, ∀ b ∈ zeros, 1 ≤ |a - b|)
    (hin : ∀ v ∈ ones ∪ zeros, |v| + 1 ≤ (C : ℝ))
    (rho etaH : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1/4)
    (heta : 0 < etaH) :
    ∃ H : Polynomial ℚ,
      (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ a ∈ ones, ∀ x : ℝ, |x - a| ≤ (rho : ℝ) →
        1 - (etaH : ℝ) ≤ evalR H x) ∧
      (∀ b ∈ zeros, ∀ x : ℝ, |x - b| ≤ (rho : ℝ) →
        evalR H x ≤ (etaH : ℝ)) := by
  exact ⟨rationalBernsteinSeparatorPoly C etaH ones rho,
    rationalBernsteinSeparatorPoly_spec C hC ones zeros hgap hin rho etaH
      hrho hrho4 heta⟩

/--
One-sided Bernstein step on a rational slab `|x| ≤ C`.

`evalR H` stays in `[0,1]` on the slab, drops to `≤ etaH` for `x ≤ θ - μ`, and
rises to `≥ 1 - etaH` for `θ + μ ≤ x`.  Same subconvex-Bernstein machinery as
`rational_bernstein_separator`, specialised to a one-sided threshold indicator
`g k = 1 ↔ θ ≤ samplePoint k`.  The two tails are symmetric Chebyshev bounds.
-/
theorem rationalBernsteinOneSidedStepPoly_spec
    (C : ℚ) (hC : 0 < C) (θ μ : ℝ) (hμ : 0 < μ)
    (etaH : ℚ) (heta : 0 < etaH) :
    (∀ x : ℝ, |x| ≤ (C : ℝ) →
        0 ≤ evalR (rationalBernsteinOneSidedStepPoly C θ μ etaH) x ∧
          evalR (rationalBernsteinOneSidedStepPoly C θ μ etaH) x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → x ≤ θ - μ →
        evalR (rationalBernsteinOneSidedStepPoly C θ μ etaH) x ≤
          (etaH : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → θ + μ ≤ x →
        1 - (etaH : ℝ) ≤
          evalR (rationalBernsteinOneSidedStepPoly C θ μ etaH) x) := by
  classical
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hetaR : 0 < (etaH : ℝ) := by exact_mod_cast heta
  set δ : ℝ := μ / (2 * (C : ℝ)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  let n : ℕ := rationalBernsteinOneSidedDegree C μ etaH
  have hnlarge : 1 / (4 * (etaH : ℝ) * δ ^ 2) < (n : ℝ) := by
    have harg :
        1 / (4 * (etaH : ℝ) * δ ^ 2) =
          ((μ / (2 * (C : ℝ))) ^ 2)⁻¹ * (((etaH : ℝ))⁻¹ * 4⁻¹) := by
      rw [hδdef]
      field_simp [hCr.ne', hetaR.ne', hμ.ne']
    rw [harg]
    simpa [n, rationalBernsteinOneSidedDegree] using
      lt_bernsteinDegreeAbove
        (((μ / (2 * (C : ℝ))) ^ 2)⁻¹ * (((etaH : ℝ))⁻¹ * 4⁻¹))
  have hn0 : n ≠ 0 := by
    simpa [n, rationalBernsteinOneSidedDegree] using
      bernsteinDegreeAbove_ne_zero
        (((μ / (2 * (C : ℝ))) ^ 2)⁻¹ * (((etaH : ℝ))⁻¹ * 4⁻¹))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  -- degree large enough that the Chebyshev mass bound clears `etaH`
  have hmass_bound : 1 / (4 * (n : ℝ) * δ ^ 2) ≤ (etaH : ℝ) := by
    have hpos2 : 0 < 4 * (etaH : ℝ) * δ ^ 2 := by positivity
    have hcancel : 1 / (4 * (etaH : ℝ) * δ ^ 2) * (4 * (etaH : ℝ) * δ ^ 2) = 1 := by
      field_simp
    have hkey := mul_lt_mul_of_pos_right hnlarge hpos2
    rw [hcancel] at hkey
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (n : ℝ) * δ ^ 2)]
    nlinarith [hkey]
  let samplePoint : Fin (n + 1) → ℚ :=
    fun k => 2 * C * ((k : ℚ) / (n : ℚ)) - C
  let g : Fin (n + 1) → ℚ :=
    fun k => if θ ≤ (samplePoint k : ℝ) then 1 else 0
  let H : Polynomial ℚ := rationalBernsteinOneSidedStepPoly C θ μ etaH
  have hHeval : ∀ x : ℝ,
      evalR H x =
        ∑ k : Fin (n + 1), (g k : ℝ) *
          (bernsteinPolynomial ℝ n k).eval
            ((x + (C : ℝ)) / (2 * (C : ℝ))) := by
    intro x
    simpa [H, rationalBernsteinOneSidedStepPoly,
      rationalBernsteinOneSidedDegree, n, g, samplePoint,
      rationalBernsteinOneSidedSample, rationalBernsteinSamplePoint,
      bernstein01Poly, affinePhi, bernsteinAffinePhi, δ, hδdef] using
      evalR_bernstein_sum C hC n g x
  have hg : ∀ k, g k = 0 ∨ g k = 1 := by
    intro k
    by_cases h : θ ≤ (samplePoint k : ℝ)
    · right; dsimp [g]; rw [if_pos h]
    · left; dsimp [g]; rw [if_neg h]
  -- coordinate algebra shared by both tails:
  -- |samplePoint k - x| = 2C |y - k/n| with y = (x+C)/(2C)
  have hsample_y : ∀ (k : Fin (n + 1)) (x : ℝ),
      |(samplePoint k : ℝ) - x| =
        2 * (C : ℝ) * |((x + (C : ℝ)) / (2 * (C : ℝ))) - (k : ℝ) / (n : ℝ)| := by
    intro k x
    have hCne : (C : ℝ) ≠ 0 := hCr.ne'
    have hsample : (samplePoint k : ℝ) =
        2 * (C : ℝ) * ((k : ℝ) / (n : ℝ)) - (C : ℝ) := by
      dsimp [samplePoint]; push_cast; ring
    have key : (samplePoint k : ℝ) - x =
        2 * (C : ℝ) * (((k : ℝ) / (n : ℝ)) - (x + (C : ℝ)) / (2 * (C : ℝ))) := by
      rw [hsample]; field_simp; ring
    rw [key, abs_mul, abs_of_pos (by positivity : 0 < 2 * (C : ℝ)), abs_sub_comm]
  change
    (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → x ≤ θ - μ →
        evalR H x ≤ (etaH : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → θ + μ ≤ x →
        1 - (etaH : ℝ) ≤ evalR H x)
  refine ⟨?_, ?_, ?_⟩
  · -- range on slab
    intro x hx
    have hy := affinePhi_mem_Icc C hC hx
    simpa [hHeval x] using
      bernstein_subconvex_range n g hg hy.1 hy.2
  · -- low tail: x ≤ θ - μ ⟹ evalR H x ≤ etaH
    intro x hxslab hxlo
    have hy := affinePhi_mem_Icc C hC hxslab
    let y : ℝ := (x + (C : ℝ)) / (2 * (C : ℝ))
    let B : Fin (n + 1) → ℝ := fun k => (bernsteinPolynomial ℝ n k).eval y
    let good : Finset (Fin (n + 1)) := Finset.univ.filter fun k => g k = 1
    have hgood_sum :
        (∑ k : Fin (n + 1), (g k : ℝ) * B k) = ∑ k ∈ good, B k := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases hg k with h0 | h1
      · simp [good, h0]
      · simp [good, h1]
    have hgood_far :
        ∀ k ∈ good, δ ≤ |y - (k : ℝ) / (n : ℝ)| := by
      intro k hk
      have hk1 : g k = 1 := by simpa [good] using hk
      have hthr : θ ≤ (samplePoint k : ℝ) := by
        by_contra hno
        have hg0 : g k = 0 := by dsimp [g]; rw [if_neg hno]
        norm_num [hk1] at hg0
      have hge : μ ≤ (samplePoint k : ℝ) - x := by linarith
      have habs : μ ≤ |(samplePoint k : ℝ) - x| :=
        le_trans hge (le_abs_self _)
      have := hsample_y k x
      have hδle : δ ≤ |y - (k : ℝ) / (n : ℝ)| := by
        have h2 : μ ≤ 2 * (C : ℝ) * |y - (k : ℝ) / (n : ℝ)| := by
          rw [show (2 * (C : ℝ) * |y - (k : ℝ) / (n : ℝ)|) =
              |(samplePoint k : ℝ) - x| by rw [this]]
          exact habs
        rw [hδdef]
        rw [div_le_iff₀ (by positivity : 0 < 2 * (C : ℝ))]
        linarith [h2]
      exact hδle
    have hmass :=
      bernsteinPolynomial_eval_bad_mass_le n hn0 hy.1 hy.2 hδ good hgood_far
    have heval :
        evalR H x = ∑ k : Fin (n + 1), (g k : ℝ) * B k := by
      simpa [B, y] using hHeval x
    rw [heval, hgood_sum]
    exact le_trans (by simpa [B] using hmass) hmass_bound
  · -- high tail: θ + μ ≤ x ⟹ 1 - etaH ≤ evalR H x
    intro x hxslab hxhi
    have hy := affinePhi_mem_Icc C hC hxslab
    let y : ℝ := (x + (C : ℝ)) / (2 * (C : ℝ))
    let B : Fin (n + 1) → ℝ := fun k => (bernsteinPolynomial ℝ n k).eval y
    let bad : Finset (Fin (n + 1)) := Finset.univ.filter fun k => g k = 0
    have hsumB : (∑ k : Fin (n + 1), B k) = 1 := by
      simpa [B, Finset.sum_range] using bernsteinPolynomial_eval_sum n y
    have hcompl :
        1 - (∑ k : Fin (n + 1), (g k : ℝ) * B k) = ∑ k ∈ bad, B k := by
      rw [← hsumB, ← Finset.sum_sub_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases hg k with h0 | h1
      · simp [bad, h0]
      · simp [bad, h1]
    have hbad_far :
        ∀ k ∈ bad, δ ≤ |y - (k : ℝ) / (n : ℝ)| := by
      intro k hk
      have hk0 : g k = 0 := by simpa [bad] using hk
      have hthr : ¬ θ ≤ (samplePoint k : ℝ) := by
        intro hle
        have hg1 : g k = 1 := by dsimp [g]; rw [if_pos hle]
        norm_num [hk0] at hg1
      have hlt : (samplePoint k : ℝ) < θ := lt_of_not_ge hthr
      have hge : μ ≤ x - (samplePoint k : ℝ) := by linarith
      have habs : μ ≤ |(samplePoint k : ℝ) - x| := by
        rw [abs_sub_comm]
        exact le_trans hge (le_abs_self _)
      have := hsample_y k x
      have h2 : μ ≤ 2 * (C : ℝ) * |y - (k : ℝ) / (n : ℝ)| := by
        rw [show (2 * (C : ℝ) * |y - (k : ℝ) / (n : ℝ)|) =
            |(samplePoint k : ℝ) - x| by rw [this]]
        exact habs
      rw [hδdef, div_le_iff₀ (by positivity : 0 < 2 * (C : ℝ))]
      linarith [h2]
    have hmass :=
      bernsteinPolynomial_eval_bad_mass_le n hn0 hy.1 hy.2 hδ bad hbad_far
    have hbad_le : ∑ k ∈ bad, B k ≤ (etaH : ℝ) :=
      le_trans (by simpa [B] using hmass) hmass_bound
    have heval :
        evalR H x = ∑ k : Fin (n + 1), (g k : ℝ) * B k := by
      simpa [B, y] using hHeval x
    rw [heval]
    have hfin : 1 - (∑ k : Fin (n + 1), (g k : ℝ) * B k) ≤ (etaH : ℝ) := by
      rw [hcompl]; exact hbad_le
    linarith [hfin]

theorem rational_bernstein_onesided_step
    (C : ℚ) (hC : 0 < C) (θ μ : ℝ) (hμ : 0 < μ)
    (etaH : ℚ) (heta : 0 < etaH) :
    ∃ H : Polynomial ℚ,
      (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → x ≤ θ - μ → evalR H x ≤ (etaH : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → θ + μ ≤ x → 1 - (etaH : ℝ) ≤ evalR H x) := by
  exact ⟨rationalBernsteinOneSidedStepPoly C θ μ etaH,
    rationalBernsteinOneSidedStepPoly_spec C hC θ μ hμ etaH heta⟩

private lemma evalR_mul (P Q : Polynomial ℚ) (x : ℝ) :
    evalR (P * Q) x = evalR P x * evalR Q x := by
  simp [evalR, Polynomial.map_mul, Polynomial.eval_mul]

private lemma evalR_one_sub (U : Polynomial ℚ) (x : ℝ) :
    evalR (1 - U) x = 1 - evalR U x := by
  simp [evalR, Polynomial.map_sub, Polynomial.map_one, Polynomial.eval_sub,
    Polynomial.eval_one]

/--
Two-sided Bernstein interval atom on a rational slab `|x| ≤ C`.

`H = L · (1 - U)` where `L` rises at the left threshold `tlo` and `U` rises at
the right threshold `thi`.  On the interval `[tlo+μ, thi-μ]` the atom is
`≥ 1 - 2·etaH`; left of `tlo-μ` or right of `thi+μ` it is `≤ etaH`.  Range
`[0,1]` on the whole slab.
-/
theorem rationalBernsteinIntervalAtomPoly_spec
    (C : ℚ) (hC : 0 < C) (tlo thi μ : ℝ) (hμ : 0 < μ)
    (etaH : ℚ) (heta : 0 < etaH) :
    (∀ x : ℝ, |x| ≤ (C : ℝ) →
        0 ≤ evalR (rationalBernsteinIntervalAtomPoly C tlo thi μ etaH) x ∧
          evalR (rationalBernsteinIntervalAtomPoly C tlo thi μ etaH) x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → tlo + μ ≤ x → x ≤ thi - μ →
        1 - 2 * (etaH : ℝ) ≤
          evalR (rationalBernsteinIntervalAtomPoly C tlo thi μ etaH) x) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → x ≤ tlo - μ →
        evalR (rationalBernsteinIntervalAtomPoly C tlo thi μ etaH) x ≤
          (etaH : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → thi + μ ≤ x →
        evalR (rationalBernsteinIntervalAtomPoly C tlo thi μ etaH) x ≤
          (etaH : ℝ)) := by
  let L : Polynomial ℚ := rationalBernsteinOneSidedStepPoly C tlo μ etaH
  let U : Polynomial ℚ := rationalBernsteinOneSidedStepPoly C thi μ etaH
  let H : Polynomial ℚ := rationalBernsteinIntervalAtomPoly C tlo thi μ etaH
  have hH : H = L * (1 - U) := by rfl
  have hLspec := rationalBernsteinOneSidedStepPoly_spec C hC tlo μ hμ etaH heta
  have hUspec := rationalBernsteinOneSidedStepPoly_spec C hC thi μ hμ etaH heta
  have hLrange := hLspec.1
  have hLlo := hLspec.2.1
  have hLhi := hLspec.2.2
  have hUrange := hUspec.1
  have hUlo := hUspec.2.1
  have hUhi := hUspec.2.2
  change
    (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → tlo + μ ≤ x → x ≤ thi - μ →
        1 - 2 * (etaH : ℝ) ≤ evalR H x) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → x ≤ tlo - μ → evalR H x ≤ (etaH : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → thi + μ ≤ x → evalR H x ≤ (etaH : ℝ))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hH, evalR_mul, evalR_one_sub]
    obtain ⟨hL0, hL1⟩ := hLrange x hx
    obtain ⟨hU0, hU1⟩ := hUrange x hx
    have h1U : 0 ≤ 1 - evalR U x := by linarith
    constructor
    · exact mul_nonneg hL0 h1U
    · nlinarith [mul_le_mul_of_nonneg_right hL1 h1U]
  · intro x hx hxlo hxhi
    rw [hH, evalR_mul, evalR_one_sub]
    have hLge := hLhi x hx hxlo
    have hUle := hUlo x hx hxhi
    have hetaR : 0 ≤ (etaH : ℝ) := by exact_mod_cast heta.le
    obtain ⟨hU0, hU1⟩ := hUrange x hx
    have h1U : 0 ≤ 1 - evalR U x := by linarith
    have hs : 0 ≤ evalR L x - (1 - (etaH : ℝ)) := by linarith
    nlinarith [mul_nonneg hetaR hU0, mul_nonneg hs h1U]
  · intro x hx hxlo
    rw [hH, evalR_mul, evalR_one_sub]
    have hLle := hLlo x hx hxlo
    have hetaR : 0 ≤ (etaH : ℝ) := by exact_mod_cast heta.le
    obtain ⟨hL0, _⟩ := hLrange x hx
    obtain ⟨hU0, hU1⟩ := hUrange x hx
    have h1U : 0 ≤ 1 - evalR U x := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hLle h1U, mul_nonneg hetaR hU0]
  · intro x hx hxhi
    rw [hH, evalR_mul, evalR_one_sub]
    have hUge := hUhi x hx hxhi
    obtain ⟨hL0, hL1⟩ := hLrange x hx
    obtain ⟨_, hU1⟩ := hUrange x hx
    have h1U : 0 ≤ 1 - evalR U x := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hL1 h1U]

theorem rational_bernstein_interval_atom
    (C : ℚ) (hC : 0 < C) (tlo thi μ : ℝ) (hμ : 0 < μ)
    (etaH : ℚ) (heta : 0 < etaH) :
    ∃ H : Polynomial ℚ,
      (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → tlo + μ ≤ x → x ≤ thi - μ →
        1 - 2 * (etaH : ℝ) ≤ evalR H x) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → x ≤ tlo - μ → evalR H x ≤ (etaH : ℝ)) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → thi + μ ≤ x → evalR H x ≤ (etaH : ℝ)) := by
  exact ⟨rationalBernsteinIntervalAtomPoly C tlo thi μ etaH,
    rationalBernsteinIntervalAtomPoly_spec C hC tlo thi μ hμ etaH heta⟩

/--
Code-indexed interval atom family.  Each code `a : A` occupies the interval
`[lo a, hi a]`; distinct codes are separated by at least `gap`.  The atom for
code `a` is `≈ 1` on `[lo a, hi a]` and `≈ 0` on any other code's interval.

Thresholds sit at the gap midpoints with margin `gap/2`, so the on-guarantee
holds on the full closed interval (no tube shrinkage) and the off-guarantee
holds on every other closed interval.
-/
theorem rationalBernsteinIntervalAtomFamilyPoly_spec
    (C : ℚ) (hC : 0 < C)
    {A : Type} (lo hi : A → ℝ) (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ a b : A, a ≠ b → hi a + gap ≤ lo b ∨ hi b + gap ≤ lo a)
    (etaH : ℚ) (heta : 0 < etaH) (a : A) :
    (∀ x : ℝ, |x| ≤ (C : ℝ) →
        0 ≤ evalR (rationalBernsteinIntervalAtomFamilyPoly C lo hi gap etaH a) x ∧
          evalR (rationalBernsteinIntervalAtomFamilyPoly C lo hi gap etaH a) x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → lo a ≤ x → x ≤ hi a →
        1 - 2 * (etaH : ℝ) ≤
          evalR (rationalBernsteinIntervalAtomFamilyPoly C lo hi gap etaH a) x) ∧
      (∀ b : A, b ≠ a → ∀ x : ℝ, |x| ≤ (C : ℝ) → lo b ≤ x → x ≤ hi b →
        evalR (rationalBernsteinIntervalAtomFamilyPoly C lo hi gap etaH a) x ≤
          (etaH : ℝ)) := by
  let H : Polynomial ℚ := rationalBernsteinIntervalAtomFamilyPoly C lo hi gap etaH a
  have hspec :=
    rationalBernsteinIntervalAtomPoly_spec C hC (lo a - gap / 2) (hi a + gap / 2)
      (gap / 2) (by positivity) etaH heta
  have hrange := hspec.1
  have hon := hspec.2.1
  have hoffL := hspec.2.2.1
  have hoffR := hspec.2.2.2
  change
    (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → lo a ≤ x → x ≤ hi a →
        1 - 2 * (etaH : ℝ) ≤ evalR H x) ∧
      (∀ b : A, b ≠ a → ∀ x : ℝ, |x| ≤ (C : ℝ) → lo b ≤ x → x ≤ hi b →
        evalR H x ≤ (etaH : ℝ))
  refine ⟨hrange, ?_, ?_⟩
  · intro x hx hxlo hxhi
    exact hon x hx (by linarith) (by linarith)
  · intro b hba x hx hxlo hxhi
    rcases hsep a b (fun h => hba h.symm) with h | h
    · -- hi a + gap ≤ lo b : b is above a, reject on the right
      exact hoffR x hx (by linarith)
    · -- hi b + gap ≤ lo a : b is below a, reject on the left
      exact hoffL x hx (by linarith)

theorem rational_bernstein_interval_atom_family
    (C : ℚ) (hC : 0 < C)
    {A : Type} (lo hi : A → ℝ) (gap : ℝ) (hgap : 0 < gap)
    (hsep : ∀ a b : A, a ≠ b → hi a + gap ≤ lo b ∨ hi b + gap ≤ lo a)
    (etaH : ℚ) (heta : 0 < etaH) (a : A) :
    ∃ H : Polynomial ℚ,
      (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ (C : ℝ) → lo a ≤ x → x ≤ hi a →
        1 - 2 * (etaH : ℝ) ≤ evalR H x) ∧
      (∀ b : A, b ≠ a → ∀ x : ℝ, |x| ≤ (C : ℝ) → lo b ≤ x → x ≤ hi b →
        evalR H x ≤ (etaH : ℝ)) := by
  exact ⟨rationalBernsteinIntervalAtomFamilyPoly C lo hi gap etaH a,
    rationalBernsteinIntervalAtomFamilyPoly_spec C hC lo hi gap hgap hsep etaH heta a⟩

/-- Primed splice theorem with the exact statement of
`LatchAssembly.haltIndicator_exists`. -/
theorem haltIndicator_exists
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (Cwidth : ℚ) (hCw : 0 < Cwidth)
    (stateCoord : Fin d) (haltLevels : Finset ℤ)
    (hfin : (Set.range fun c => E.enc c stateCoord).Finite)
    (hlevels : ∀ c : Conf, Mch.halted c = true ↔
      ∃ v ∈ haltLevels, E.enc c stateCoord = (v : ℝ))
    -- R2#5: per-coordinate margin — running configs sit at least 1
    -- away from every halt level IN THE STATE COORDINATE (the global
    -- exists-coordinate separation is not enough; codex counterexample
    -- recorded in notes/bgp-adversarial-rounds.md round 2)
    (hmargin : ∀ c : Conf, Mch.halted c = false →
      ∀ v ∈ haltLevels, 1 ≤ |E.enc c stateCoord - (v : ℝ)|)
    (ηH : ℚ) (h0 : 0 < ηH) (h1 : ηH < 1/8) :
    -- R3#4: ρ must ALSO be bounded above by the state-coordinate
    -- margin (1/4 < margin/2), else halted and running tubes overlap
    -- in the state coordinate when r₀ is large
    ∃ I : HaltIndicator Mch d E, I.ηH = ηH ∧
      min ((S.r₀ : ℝ) / 2) (1/4) ≤ (I.ρ : ℝ) ∧ (I.ρ : ℝ) ≤ 1/4 ∧
      -- R2#6: the working set is a state-coordinate SLAB, so that
      -- trajectory membership is dischargeable from the moving box
      -- (transit values of the state coordinate stay bounded); a
      -- tube-union W is NOT dischargeable (trajectories leave all
      -- tubes mid-transition)
      ∃ C : ℚ, Cwidth ≤ C ∧ I.W = {x | |x stateCoord| ≤ (C : ℝ)} := by
  classical
  let ρ : ℚ := min (S.r₀ / 2) (1 / 4)
  have hρpos : 0 < ρ := by
    have hhalf : 0 < S.r₀ / 2 := by
      exact div_pos S.r₀_pos (by norm_num : (0 : ℚ) < 2)
    have hquarter : 0 < (1 / 4 : ℚ) := by norm_num
    exact lt_min hhalf hquarter
  have hρ4 : ρ ≤ 1 / 4 := by
    exact min_le_right _ _
  have hρR4 : (ρ : ℝ) ≤ (1 / 4 : ℝ) := by
    have hcast : (ρ : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hρ4
    norm_num at hcast
    exact hcast
  have hρR1 : (ρ : ℝ) ≤ 1 := by nlinarith
  let ones : Finset ℝ := haltLevels.image fun v : ℤ => (v : ℝ)
  let vals : Finset ℝ := hfin.toFinset
  let zeros : Finset ℝ := vals.filter fun z => z ∉ ones
  let allVals : Finset ℝ := ones ∪ zeros
  let R : ℝ := ∑ v ∈ allVals, (|v| + 1)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max R 1 < (N : ℝ) := exists_nat_gt (max R 1)
  let Cbase : ℚ := N
  let C : ℚ := max Cbase Cwidth
  have hNpos : 0 < N := by
    have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_right R 1) hN
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hN1)
  have hCbasepos : 0 < Cbase := by
    dsimp [Cbase]
    exact_mod_cast hNpos
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCbasepos (le_max_left Cbase Cwidth)
  have hCwidth_le : Cwidth ≤ C := by
    dsimp [C]
    exact le_max_right Cbase Cwidth
  have hCbound : ∀ v ∈ allVals, |v| + 1 ≤ (C : ℝ) := by
    intro v hv
    have hterm_nonneg : ∀ u ∈ allVals, 0 ≤ |u| + 1 := by
      intro u hu
      positivity
    have hleR : |v| + 1 ≤ R := by
      dsimp [R]
      exact Finset.single_le_sum hterm_nonneg hv
    have hRN : R < (N : ℝ) := lt_of_le_of_lt (le_max_left R 1) hN
    have hNC : (N : ℝ) ≤ (C : ℝ) := by
      have hbaseC : Cbase ≤ C := by
        dsimp [C]
        exact le_max_left Cbase Cwidth
      dsimp [Cbase] at hbaseC
      exact_mod_cast hbaseC
    linarith
  have henc_all : ∀ c : Conf, E.enc c stateCoord ∈ allVals := by
    intro c
    cases hc : Mch.halted c with
    | true =>
        obtain ⟨v, hv, henc⟩ := (hlevels c).mp hc
        have hone : E.enc c stateCoord ∈ ones := by
          rw [henc]
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        exact Finset.mem_union.mpr (Or.inl hone)
    | false =>
        have hval : E.enc c stateCoord ∈ vals := by
          rw [Set.Finite.mem_toFinset hfin]
          exact Set.mem_range_self c
        have hnot : E.enc c stateCoord ∉ ones := by
          intro hone
          rcases Finset.mem_image.mp hone with ⟨v, hv, hvenc⟩
          have hhalt : Mch.halted c = true :=
            (hlevels c).mpr ⟨v, hv, hvenc.symm⟩
          simp [hc] at hhalt
        have hzero : E.enc c stateCoord ∈ zeros := by
          rw [Finset.mem_filter]
          exact ⟨hval, hnot⟩
        exact Finset.mem_union.mpr (Or.inr hzero)
  have hgap :
      ∀ a ∈ ones, ∀ b ∈ zeros, 1 ≤ |a - b| := by
    intro a ha b hb
    rcases Finset.mem_image.mp ha with ⟨v, hv, rfl⟩
    have hb' := (Finset.mem_filter.mp hb)
    have hbvals : b ∈ vals := hb'.1
    have hbnot : b ∉ ones := hb'.2
    rw [Set.Finite.mem_toFinset hfin] at hbvals
    rcases Set.mem_range.mp hbvals with ⟨c, hc⟩
    have hrun : Mch.halted c = false := by
      cases hhalt : Mch.halted c with
      | false => rfl
      | true =>
          obtain ⟨w, hw, hwenc⟩ := (hlevels c).mp hhalt
          have : b ∈ ones := by
            rw [← hc, hwenc]
            exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
          exact False.elim (hbnot this)
    have hm := hmargin c hrun v hv
    rw [← hc]
    simpa [abs_sub_comm] using hm
  obtain ⟨H, hunit, hones, hzeros⟩ :=
    rational_bernstein_separator C hCpos ones zeros hgap hCbound ρ ηH hρpos hρ4 h0
  let Hmv : MvPolynomial (Fin d) ℚ := Polynomial.aeval (MvPolynomial.X stateCoord) H
  let W : Set (Fin d → ℝ) := {x | |x stateCoord| ≤ (C : ℝ)}
  let I : HaltIndicator Mch d E :=
    { H := Hmv
      W := W
      ρ := ρ
      ηH := ηH
      ρ_pos := hρpos
      ηH_pos := h0
      ηH_lt := h1
      tubes_subset := by
        intro c x hx
        have hencC := hCbound (E.enc c stateCoord) (henc_all c)
        have hxcoord := hx stateCoord
        dsimp [W]
        have hxa : |x stateCoord| ≤ |E.enc c stateCoord| + (ρ : ℝ) := by
          calc
            |x stateCoord| =
                |(x stateCoord - E.enc c stateCoord) + E.enc c stateCoord| := by
                  congr 1
                  ring
            _ ≤ |x stateCoord - E.enc c stateCoord| + |E.enc c stateCoord| :=
                abs_add_le _ _
            _ ≤ |E.enc c stateCoord| + (ρ : ℝ) := by linarith
        linarith
      in_unit := by
        intro x hx
        dsimp [Hmv, W] at hx ⊢
        rw [eval₂_polynomial_aeval_X]
        exact hunit (x stateCoord) hx
      on_halted := by
        intro c hc x hx
        dsimp [Hmv]
        rw [eval₂_polynomial_aeval_X]
        obtain ⟨v, hv, henc⟩ := (hlevels c).mp hc
        have hvones : (v : ℝ) ∈ ones :=
          Finset.mem_image.mpr ⟨v, hv, rfl⟩
        exact hones (v : ℝ) hvones (x stateCoord) (by
          simpa [henc] using hx stateCoord)
      on_running := by
        intro c hc x hx
        dsimp [Hmv]
        rw [eval₂_polynomial_aeval_X]
        have hval : E.enc c stateCoord ∈ vals := by
          rw [Set.Finite.mem_toFinset hfin]
          exact Set.mem_range_self c
        have hnot : E.enc c stateCoord ∉ ones := by
          intro hone
          rcases Finset.mem_image.mp hone with ⟨v, hv, hvenc⟩
          have hhalt : Mch.halted c = true :=
            (hlevels c).mpr ⟨v, hv, hvenc.symm⟩
          simp [hc] at hhalt
        have hbzero : E.enc c stateCoord ∈ zeros := by
          rw [Finset.mem_filter]
          exact ⟨hval, hnot⟩
        exact hzeros (E.enc c stateCoord) hbzero (x stateCoord) (hx stateCoord) }
  refine ⟨I, rfl, ?_, ?_, ?_⟩
  · dsimp [I, ρ]
    simp
  · dsimp [I]
    exact hρR4
  · refine ⟨C, hCwidth_le, ?_⟩
    rfl

private theorem cycle_cover {t : ℝ} (ht : 0 ≤ t) :
    ∃ j : ℕ, t ∈ Set.Icc (2 * Real.pi * (j : ℝ))
      (2 * Real.pi * ((j : ℝ) + 1)) := by
  let p : ℝ := 2 * Real.pi
  have hp : 0 < p := by dsimp [p]; positivity
  let x : ℝ := t / p
  have hx0 : 0 ≤ x := by exact div_nonneg ht hp.le
  refine ⟨Nat.floor x, ?_, ?_⟩
  · have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hmul := mul_le_mul_of_nonneg_left hfloor hp.le
    have hpx : p * x = t := by dsimp [x]; field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
  · have hlt : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hpx : p * x = t := by dsimp [x]; field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith

private theorem HaltIndicator_evalH_continuous_along
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ}
    {E : LatticeEncoding Mch d} (I : HaltIndicator Mch d E)
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀) :
    Continuous fun t => I.evalH (sol.z t) := by
  have hz : Continuous fun t => sol.z t :=
    continuous_pi fun i => sol.cont_z i
  unfold HaltIndicator.evalH
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) I.H)).comp hz
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.z t) I.H

/-- Primed splice theorem for P11.  This is the `LatchAssembly`
statement with the extra smallness hypothesis needed by
`tracking_feasibility`; see `HANDOFF/p11-mismatches.md`. -/
theorem assembled_euclidean_simulation
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (stateCoord : Fin d) (haltLevels : Finset ℤ)
    (hfin : (Set.range fun c => E.enc c stateCoord).Finite)
    (hlevels : ∀ c : Conf, Mch.halted c = true ↔
      ∃ v ∈ haltLevels, E.enc c stateCoord = (v : ℝ))
    (hmargin : ∀ c : Conf, Mch.halted c = false →
      ∀ v ∈ haltLevels, 1 ≤ |E.enc c stateCoord - (v : ℝ)|)
    (D_K : ℝ) (hD : 0 < D_K)
    (hstepSmall :
      2 * (S.ηstep : ℝ) < min ((S.r₀ : ℝ) / 2) (1 / 4) / 2)
    (hsupply : ∀ (A : ℚ) (M : ℕ) (w : ℕ), 0 < A →
      ∃ sol : IteratorSol d S.evalF (A : ℝ) M (orbitPoint Mch E w 0),
        MovingBox S sol D_K) :
    ∃ (I : HaltIndicator Mch d E) (A : ℚ) (M : ℕ) (K : ℚ) (R : ℕ),
      0 < A ∧ 0 < K ∧
      ∀ w : ℕ,
        ∃ (sol : IteratorSol d S.evalF (A : ℝ) M (orbitPoint Mch E w 0))
          (L : LatchSol sol I.evalH (K : ℝ) R),
          (Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 3/4 ≤ L.a t ∧ L.a t ≤ 1) ∧
          (¬ Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 0 ≤ L.a t ∧ L.a t ≤ 1/4) := by
  classical
  let vals : Finset ℝ := hfin.toFinset
  let maxAbs : ℝ := ∑ v ∈ vals, |v|
  have hmaxAbs_nonneg : 0 ≤ maxAbs := by
    dsimp [maxAbs]
    positivity
  have henc_bound : ∀ c : Conf, |E.enc c stateCoord| ≤ maxAbs := by
    intro c
    have hval : E.enc c stateCoord ∈ vals := by
      rw [Set.Finite.mem_toFinset hfin]
      exact Set.mem_range_self c
    have hterm_nonneg : ∀ v ∈ vals, 0 ≤ |v| := by
      intro v hv
      exact abs_nonneg v
    exact Finset.single_le_sum hterm_nonneg hval
  obtain ⟨Cwidth, hCwidth_gt⟩ : ∃ q : ℚ, maxAbs + D_K < (q : ℝ) :=
    exists_rat_gt (maxAbs + D_K)
  have hCwidth_pos : 0 < Cwidth := by
    have hCwidth_posR : (0 : ℝ) < (Cwidth : ℝ) := by
      nlinarith [hmaxAbs_nonneg, hD, hCwidth_gt]
    exact Rat.cast_pos.mp hCwidth_posR
  obtain ⟨I, hIη, hIρ_low, hIρ_high, C, hCwidth_le_C, hIW⟩ :=
    haltIndicator_exists Mch d E S Cwidth hCwidth_pos stateCoord haltLevels
      hfin hlevels hmargin (1 / 16) (by norm_num) (by norm_num)
  let η : ℝ := min ((S.r₀ : ℝ) / 2) (1 / 4) / 2
  have hmin_pos : 0 < min ((S.r₀ : ℝ) / 2) (1 / 4) := by
    have hr0R : 0 < (S.r₀ : ℝ) := by exact_mod_cast S.r₀_pos
    apply lt_min
    · linarith
    · norm_num
  have hη_pos : 0 < η := by
    dsimp [η]
    nlinarith [hmin_pos]
  have hη_le_r0_half : η ≤ (S.r₀ : ℝ) / 2 := by
    dsimp [η]
    have hleft := min_le_left ((S.r₀ : ℝ) / 2) (1 / 4)
    nlinarith [hmin_pos, hleft]
  have hη_le_Iρ : η ≤ (I.ρ : ℝ) := by
    dsimp [η]
    nlinarith [hmin_pos, hIρ_low]
  obtain ⟨A, M, hA, hcasc₀, hcasc₁, hcasc₂⟩ :=
    tracking_feasibility S.r₀ S.ηstep S.ηstep_pos S.ηstep_lt_r₀
      D_K hD η hstepSmall hη_le_r0_half
  have hAℝ : 0 < (A : ℝ) := by exact_mod_cast hA
  obtain ⟨K, R, hK, hlatch⟩ := halt_latch_eventual_readout Mch d E S I
  refine ⟨I, A, M, K, R, hA, hK, ?_⟩
  intro w
  obtain ⟨sol, hbox⟩ := hsupply A M w hA
  have hsampleη :=
    all_time_tracking Mch d E S (A : ℝ) hAℝ M w sol D_K hD hbox
      η hη_pos hcasc₀ hcasc₁ hcasc₂
  have hsampleI : ∀ j : ℕ, ∀ i,
      |sol.z (2 * Real.pi * (j : ℝ)) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ) ∧
      |sol.u (2 * Real.pi * (j : ℝ)) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ) := by
    intro j i
    have h := hsampleη j i
    exact ⟨le_trans h.1 hη_le_Iρ, le_trans h.2 hη_le_Iρ⟩
  have hχD_nonneg : 0 ≤ trackingChi (A : ℝ) M * D_K := by
    unfold trackingChi
    positivity
  have hκ_nonneg : 0 ≤ trackingKappa (A : ℝ) M := by
    unfold trackingKappa
    exact (Real.exp_pos _).le
  have hstable_radius :
      trackingKappa (A : ℝ) M * (η + D_K) + (S.ηstep : ℝ)
          + trackingChi (A : ℝ) M * D_K ≤ η := by
    nlinarith [hcasc₁, hstepSmall, hκ_nonneg, hχD_nonneg]
  have hstableI : ∀ j : ℕ,
      ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6),
        ∀ i, |sol.z t i - orbitPoint Mch E w (j + 1) i| ≤ (I.ρ : ℝ) := by
    intro j t ht i
    have hst :=
      stable_window_tracking Mch d E S (A : ℝ) hAℝ M w sol D_K hD hbox
        η hη_pos hcasc₀ hcasc₁ hcasc₂ j t ht i
    exact le_trans hst (le_trans hstable_radius hη_le_Iρ)
  have hzW : ∀ t : ℝ, 0 ≤ t → sol.z t ∈ I.W := by
    intro t ht
    obtain ⟨j, htcycle⟩ := cycle_cover ht
    have hzD := (hbox j t htcycle).2.1 stateCoord
    have horbit := henc_bound (Mch.step^[j] (Mch.init w))
    have hz_abs : |sol.z t stateCoord| ≤ maxAbs + D_K := by
      calc
        |sol.z t stateCoord| =
            |(sol.z t stateCoord - orbitPoint Mch E w j stateCoord) +
              orbitPoint Mch E w j stateCoord| := by
              congr 1
              ring
        _ ≤ |sol.z t stateCoord - orbitPoint Mch E w j stateCoord| +
            |orbitPoint Mch E w j stateCoord| := abs_add_le _ _
        _ ≤ D_K + maxAbs := by
            gcongr
            simpa [orbitPoint] using horbit
        _ = maxAbs + D_K := by ring
    rw [hIW]
    have hCwidth_le_Cℝ : (Cwidth : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCwidth_le_C
    change |sol.z t stateCoord| ≤ (C : ℝ)
    linarith
  have hHcont : Continuous fun t => I.evalH (sol.z t) :=
    HaltIndicator_evalH_continuous_along I sol
  obtain ⟨L⟩ := latch_solution_exists sol I.evalH hHcont (K : ℝ) R
  exact ⟨sol, L, hlatch (A : ℝ) hAℝ M w sol hsampleI hzW hstableI L⟩

end Ripple.BoundedUniversality.BGP

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Ripple.BoundedUniversality.BGP.BGPParamsN
import Ripple.BoundedUniversality.BGP.SelectorReplicatorActiveQSSP

/-!
Ripple.BoundedUniversality.BGP.BernsteinSlope
-------------------------

Quantitative sidecar facts for Bernstein-backed selector atoms.  This file
keeps the existing atom APIs unchanged: the slope data is carried by public
definitions and theorems rather than by new fields on `AtomicSelectorData` or
`CoordAtomData`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Polynomial
open MachineInstance UniversalMachine
open Turing.PartrecToTM2

local instance : Fintype (SuppLabel c_f) := by
  unfold SuppLabel
  infer_instance

namespace BernsteinSlope

/-! ## Deterministic Bernstein degree and explicit polynomial -/

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

/-- Public affine transport `[-C,C] -> [0,1]` used by the rational Bernstein atoms. -/
def bernsteinAffinePhi (C : ℚ) : Polynomial ℚ :=
  Polynomial.C (1 / (2 * C)) * Polynomial.X + Polynomial.C (1 / 2)

theorem evalR_bernsteinAffinePhi (C : ℚ) (hC : 0 < C) (x : ℝ) :
    evalR (bernsteinAffinePhi C) x = (x + (C : ℝ)) / (2 * (C : ℝ)) := by
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  simp [evalR, bernsteinAffinePhi]
  field_simp [hC0]

theorem bernsteinAffinePhi_mem_Icc
    (C : ℚ) (hC : 0 < C) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    0 ≤ (x + (C : ℝ)) / (2 * (C : ℝ)) ∧
      (x + (C : ℝ)) / (2 * (C : ℝ)) ≤ 1 := by
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hxlo : -(C : ℝ) ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ (C : ℝ) := (abs_le.mp hx).2
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_one (by positivity)]
    linarith

/-- Explicit Bernstein polynomial with rational samples after affine transport. -/
def bernstein01Poly
    (C : ℚ) (n : ℕ) (g : Fin (n + 1) → ℚ) : Polynomial ℚ :=
  ∑ k : Fin (n + 1),
    Polynomial.C (g k) *
      (bernsteinPolynomial ℚ n k).comp (bernsteinAffinePhi C)

theorem bernsteinPolynomial_eval_nonneg_public (n k : ℕ) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval y := by
  rw [bernsteinPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have h1 : 0 ≤ 1 - y := by linarith
  positivity

theorem bernsteinPolynomial_eval_sum_public (n : ℕ) (y : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval y) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval y)
    (bernsteinPolynomial.sum (R := ℝ) n)
  simpa [Polynomial.eval_finsetSum] using h

theorem bernstein_subconvex_range_public
    (n : ℕ) (g : Fin (n + 1) → ℚ) (hg : ∀ k, g k = 0 ∨ g k = 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (∑ k : Fin (n + 1), (g k : ℝ) *
        (bernsteinPolynomial ℝ n k).eval y) ∧
      (∑ k : Fin (n + 1), (g k : ℝ) *
        (bernsteinPolynomial ℝ n k).eval y) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun k _ => by
      rcases hg k with h | h <;>
        simp [h, bernsteinPolynomial_eval_nonneg_public n k hy0 hy1]
  · calc
      (∑ k : Fin (n + 1), (g k : ℝ) * (bernsteinPolynomial ℝ n k).eval y)
          ≤ ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval y := by
            refine Finset.sum_le_sum fun k _ => ?_
            have hb := bernsteinPolynomial_eval_nonneg_public n k hy0 hy1
            rcases hg k with h | h <;> simp [h, hb]
      _ = ∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval y := by
            simpa [Finset.sum_range]
      _ = 1 := bernsteinPolynomial_eval_sum_public n y

theorem evalR_bernstein01Poly
    (C : ℚ) (hC : 0 < C) (n : ℕ) (g : Fin (n + 1) → ℚ) (x : ℝ) :
    evalR (bernstein01Poly C n g) x =
      ∑ k : Fin (n + 1), (g k : ℝ) *
        (bernsteinPolynomial ℝ n k).eval ((x + (C : ℝ)) / (2 * (C : ℝ))) := by
  unfold evalR bernstein01Poly
  simp only [Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [Polynomial.map_comp, Polynomial.eval_comp]
  have hphi := evalR_bernsteinAffinePhi C hC x
  unfold evalR at hphi
  rw [hphi, bernsteinPolynomial.map]
  simp

theorem evalR_bernstein01Poly_range
    (C : ℚ) (hC : 0 < C) (n : ℕ) (g : Fin (n + 1) → ℚ)
    (hg : ∀ k, g k = 0 ∨ g k = 1) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    0 ≤ evalR (bernstein01Poly C n g) x ∧
      evalR (bernstein01Poly C n g) x ≤ 1 := by
  have hy := bernsteinAffinePhi_mem_Icc C hC hx
  simpa [evalR_bernstein01Poly C hC n g x] using
    bernstein_subconvex_range_public n g hg hy.1 hy.2

/-! ## Bernstein derivative slope -/

private def bernsteinNatPolyR (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (a k) * bernsteinPolynomial ℝ n k

private theorem bernstein_shift_sum_eval
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (y : ℝ) :
    (∑ k ∈ Finset.range n,
        a (k + 1) * (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) +
      a 0 * (bernsteinPolynomial ℝ (n - 1) 0).eval y =
      ∑ k ∈ Finset.range n,
        a k * (bernsteinPolynomial ℝ (n - 1) k).eval y := by
  have htop :
      (bernsteinPolynomial ℝ (n - 1) n).eval y = 0 := by
    have hlt : n - 1 < n := Nat.sub_one_lt (ne_of_gt hn)
    simpa using congrArg (fun p : Polynomial ℝ => p.eval y)
      (bernsteinPolynomial.eq_zero_of_lt (R := ℝ) hlt)
  calc
    (∑ k ∈ Finset.range n,
        a (k + 1) * (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) +
      a 0 * (bernsteinPolynomial ℝ (n - 1) 0).eval y
        = ∑ k ∈ Finset.range (n + 1),
            a k * (bernsteinPolynomial ℝ (n - 1) k).eval y := by
          rw [Finset.sum_range_succ']
    _ = (∑ k ∈ Finset.range n,
            a k * (bernsteinPolynomial ℝ (n - 1) k).eval y) +
          a n * (bernsteinPolynomial ℝ (n - 1) n).eval y := by
          rw [Finset.sum_range_succ]
    _ = ∑ k ∈ Finset.range n,
            a k * (bernsteinPolynomial ℝ (n - 1) k).eval y := by
          rw [htop]
          ring

private theorem eval_derivative_bernsteinNatPolyR
    (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (y : ℝ) :
    (Polynomial.derivative (bernsteinNatPolyR n a)).eval y =
      (n : ℝ) *
        ∑ k ∈ Finset.range n,
          (a (k + 1) - a k) *
            (bernsteinPolynomial ℝ (n - 1) k).eval y := by
  unfold bernsteinNatPolyR
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_C_mul, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_eq_add_one, bernsteinPolynomial.derivative_succ,
    bernsteinPolynomial.derivative_zero, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_sub, Polynomial.eval_neg]
  have hshift := bernstein_shift_sum_eval n hn a y
  calc
    (∑ k ∈ Finset.range n,
        a (k + 1) *
          ((n : ℝ) *
            ((bernsteinPolynomial ℝ (n - 1) k).eval y -
              (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y))) +
      a 0 * (-(n : ℝ) * (bernsteinPolynomial ℝ (n - 1) 0).eval y)
        =
      (n : ℝ) *
        ((∑ k ∈ Finset.range n,
            a (k + 1) * (bernsteinPolynomial ℝ (n - 1) k).eval y) -
          ((∑ k ∈ Finset.range n,
              a (k + 1) *
                (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) +
            a 0 * (bernsteinPolynomial ℝ (n - 1) 0).eval y)) := by
          have hsum :
              (∑ k ∈ Finset.range n,
                  a (k + 1) *
                    ((n : ℝ) *
                      ((bernsteinPolynomial ℝ (n - 1) k).eval y -
                        (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y))) =
                (n : ℝ) *
                  ((∑ k ∈ Finset.range n,
                      a (k + 1) *
                        (bernsteinPolynomial ℝ (n - 1) k).eval y) -
                    ∑ k ∈ Finset.range n,
                      a (k + 1) *
                        (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) := by
            calc
              (∑ k ∈ Finset.range n,
                  a (k + 1) *
                    ((n : ℝ) *
                      ((bernsteinPolynomial ℝ (n - 1) k).eval y -
                        (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y)))
                  =
                ∑ k ∈ Finset.range n,
                  (n : ℝ) *
                    (a (k + 1) * (bernsteinPolynomial ℝ (n - 1) k).eval y -
                      a (k + 1) *
                        (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                ring
              _ =
                (n : ℝ) *
                  ∑ k ∈ Finset.range n,
                    (a (k + 1) * (bernsteinPolynomial ℝ (n - 1) k).eval y -
                      a (k + 1) *
                        (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) := by
                rw [← Finset.mul_sum]
              _ =
                (n : ℝ) *
                  ((∑ k ∈ Finset.range n,
                      a (k + 1) *
                        (bernsteinPolynomial ℝ (n - 1) k).eval y) -
                    ∑ k ∈ Finset.range n,
                      a (k + 1) *
                        (bernsteinPolynomial ℝ (n - 1) (k + 1)).eval y) := by
                rw [Finset.sum_sub_distrib]
          rw [hsum]
          ring
    _ =
      (n : ℝ) *
        ((∑ k ∈ Finset.range n,
            a (k + 1) * (bernsteinPolynomial ℝ (n - 1) k).eval y) -
          ∑ k ∈ Finset.range n,
            a k * (bernsteinPolynomial ℝ (n - 1) k).eval y) := by
          rw [hshift]
    _ =
      (n : ℝ) *
        ∑ k ∈ Finset.range n,
          (a (k + 1) - a k) *
            (bernsteinPolynomial ℝ (n - 1) k).eval y := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          ring

private def bernsteinBaseR
    (n : ℕ) (g : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (n + 1),
    Polynomial.C (g k) * bernsteinPolynomial ℝ n k

private def bernsteinFinSamplesNat
    (n : ℕ) (g : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  fun k => if hk : k < n + 1 then g ⟨k, hk⟩ else 0

private theorem bernsteinBaseR_eq_nat
    (n : ℕ) (g : Fin (n + 1) → ℝ) :
    bernsteinBaseR n g = bernsteinNatPolyR n (bernsteinFinSamplesNat n g) := by
  unfold bernsteinBaseR bernsteinNatPolyR bernsteinFinSamplesNat
  have h := Fin.sum_univ_eq_sum_range
    (f := fun k =>
      Polynomial.C (if hk : k < n + 1 then g ⟨k, hk⟩ else 0) *
        bernsteinPolynomial ℝ n k)
    (n := n + 1)
  calc
    (∑ k : Fin (n + 1), Polynomial.C (g k) * bernsteinPolynomial ℝ n ↑k)
        =
      ∑ k : Fin (n + 1),
        Polynomial.C (if hk : (k : ℕ) < n + 1 then g ⟨k, hk⟩ else 0) *
          bernsteinPolynomial ℝ n ↑k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [k.isLt]
    _ =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (if hk : k < n + 1 then g ⟨k, hk⟩ else 0) *
          bernsteinPolynomial ℝ n k := h

private theorem eval_derivative_bernsteinBaseR
    (n : ℕ) (hn : 0 < n) (g : Fin (n + 1) → ℝ) (y : ℝ) :
    (Polynomial.derivative (bernsteinBaseR n g)).eval y =
      (n : ℝ) *
        ∑ k : Fin n,
          (g k.succ - g k.castSucc) *
            (bernsteinPolynomial ℝ (n - 1) k).eval y := by
  rw [bernsteinBaseR_eq_nat n g,
    eval_derivative_bernsteinNatPolyR n hn (bernsteinFinSamplesNat n g) y]
  congr 1
  have h := (Fin.sum_univ_eq_sum_range
    (f := fun k =>
      (bernsteinFinSamplesNat n g (k + 1) - bernsteinFinSamplesNat n g k) *
        (bernsteinPolynomial ℝ (n - 1) k).eval y)
    (n := n)).symm
  simpa [bernsteinFinSamplesNat] using h

private theorem map_bernstein01Poly_eq_baseR_comp
    (C : ℚ) (n : ℕ) (g : Fin (n + 1) → ℚ) :
    (bernstein01Poly C n g).map (algebraMap ℚ ℝ) =
      (bernsteinBaseR n (fun k => (g k : ℝ))).comp
        ((bernsteinAffinePhi C).map (algebraMap ℚ ℝ)) := by
  unfold bernstein01Poly bernsteinBaseR
  simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, bernsteinPolynomial.map]

private theorem derivative_bernsteinAffinePhi_map
    (C : ℚ) :
    Polynomial.derivative ((bernsteinAffinePhi C).map (algebraMap ℚ ℝ)) =
      Polynomial.C (1 / (2 * (C : ℝ))) := by
  simp [bernsteinAffinePhi]

private theorem eval_map_bernsteinAffinePhi
    (C : ℚ) (hC : 0 < C) (x : ℝ) :
    (((bernsteinAffinePhi C).map (algebraMap ℚ ℝ)).eval x) =
      (x + (C : ℝ)) / (2 * (C : ℝ)) := by
  simpa [evalR] using evalR_bernsteinAffinePhi C hC x

private theorem bernstein_sample_diff_abs_le_one
    {n : ℕ} (g : Fin (n + 1) → ℚ)
    (hg : ∀ k, g k = 0 ∨ g k = 1) (k : Fin n) :
    |(g k.succ : ℝ) - (g k.castSucc : ℝ)| ≤ 1 := by
  rcases hg k.succ with hsucc | hsucc <;>
    rcases hg k.castSucc with hcast | hcast <;>
      simp [hsucc, hcast]

theorem evalR_derivative_bernstein01Poly_abs_le
    (C : ℚ) (hC : 0 < C)
    (n : ℕ) (hn : 0 < n)
    (g : Fin (n + 1) → ℚ)
    (hg : ∀ k, g k = 0 ∨ g k = 1)
    {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    |evalR (Polynomial.derivative (bernstein01Poly C n g)) x| ≤
      (n : ℝ) / (2 * (C : ℝ)) := by
  classical
  let y : ℝ := (x + (C : ℝ)) / (2 * (C : ℝ))
  have hy := bernsteinAffinePhi_mem_Icc C hC hx
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hfactor_nonneg : 0 ≤ 1 / (2 * (C : ℝ)) := by positivity
  have hmap := congrArg Polynomial.derivative
    (map_bernstein01Poly_eq_baseR_comp C n g)
  have heq :
      evalR (Polynomial.derivative (bernstein01Poly C n g)) x =
        (1 / (2 * (C : ℝ))) *
          ((Polynomial.derivative (bernsteinBaseR n fun k => (g k : ℝ))).eval y) := by
    unfold evalR
    rw [← Polynomial.derivative_map, hmap]
    rw [Polynomial.derivative_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_comp]
    rw [derivative_bernsteinAffinePhi_map C]
    rw [Polynomial.eval_C]
    rw [eval_map_bernsteinAffinePhi C hC x]
  rw [heq, eval_derivative_bernsteinBaseR n hn (fun k => (g k : ℝ)) y]
  have hsum_abs :
      |∑ k : Fin n,
          ((g k.succ : ℝ) - (g k.castSucc : ℝ)) *
            (bernsteinPolynomial ℝ (n - 1) k).eval y| ≤ 1 := by
    calc
      |∑ k : Fin n,
          ((g k.succ : ℝ) - (g k.castSucc : ℝ)) *
            (bernsteinPolynomial ℝ (n - 1) k).eval y|
          ≤ ∑ k : Fin n,
              |((g k.succ : ℝ) - (g k.castSucc : ℝ)) *
                (bernsteinPolynomial ℝ (n - 1) k).eval y| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n,
              |(g k.succ : ℝ) - (g k.castSucc : ℝ)| *
                (bernsteinPolynomial ℝ (n - 1) k).eval y := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [abs_mul]
            rw [abs_of_nonneg (bernsteinPolynomial_eval_nonneg_public
              (n - 1) k hy.1 hy.2)]
      _ ≤ ∑ k : Fin n,
              (bernsteinPolynomial ℝ (n - 1) k).eval y := by
            refine Finset.sum_le_sum fun k _ => ?_
            have hb : 0 ≤ (bernsteinPolynomial ℝ (n - 1) k).eval y :=
              bernsteinPolynomial_eval_nonneg_public (n - 1) k hy.1 hy.2
            exact mul_le_of_le_one_left hb
              (bernstein_sample_diff_abs_le_one g hg k)
      _ = ∑ k ∈ Finset.range n,
              (bernsteinPolynomial ℝ (n - 1) k).eval y := by
            simpa [Finset.sum_range]
      _ = 1 := by
            have hnsub : n - 1 + 1 = n :=
              Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
            simpa [hnsub] using bernsteinPolynomial_eval_sum_public (n - 1) y
  calc
    |(1 / (2 * (C : ℝ))) *
        ((n : ℝ) *
          ∑ k : Fin n,
            ((g k.succ : ℝ) - (g k.castSucc : ℝ)) *
              (bernsteinPolynomial ℝ (n - 1) k).eval y)|
        = (1 / (2 * (C : ℝ))) *
            ((n : ℝ) *
              |∑ k : Fin n,
                ((g k.succ : ℝ) - (g k.castSucc : ℝ)) *
                  (bernsteinPolynomial ℝ (n - 1) k).eval y|) := by
          rw [abs_mul, abs_of_nonneg hfactor_nonneg, abs_mul,
            abs_of_nonneg (by exact_mod_cast hn.le)]
    _ ≤ (1 / (2 * (C : ℝ))) * ((n : ℝ) * 1) := by
          gcongr
    _ = (n : ℝ) / (2 * (C : ℝ)) := by ring

/-- The root deterministic Bernstein polynomial is definitionally the same
construction as the local copy in this sidecar namespace. -/
theorem root_bernstein01Poly_eq
    (C : ℚ) (n : ℕ) (g : Fin (n + 1) → ℚ) :
    Ripple.BoundedUniversality.BGP.bernstein01Poly C n g = BernsteinSlope.bernstein01Poly C n g := by
  simp [Ripple.BoundedUniversality.BGP.bernstein01Poly, BernsteinSlope.bernstein01Poly,
    Ripple.BoundedUniversality.BGP.bernsteinAffinePhi, BernsteinSlope.bernsteinAffinePhi]

theorem evalR_derivative_root_bernstein01Poly_abs_le
    (C : ℚ) (hC : 0 < C)
    (n : ℕ) (hn : 0 < n)
    (g : Fin (n + 1) → ℚ)
    (hg : ∀ k, g k = 0 ∨ g k = 1)
    {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    |evalR (Polynomial.derivative (Ripple.BoundedUniversality.BGP.bernstein01Poly C n g)) x| ≤
      (n : ℝ) / (2 * (C : ℝ)) := by
  rw [root_bernstein01Poly_eq]
  exact evalR_derivative_bernstein01Poly_abs_le C hC n hn g hg hx

theorem evalR_derivative_rationalBernsteinSeparatorPoly_abs_le
    (C : ℚ) (hC : 0 < C) (eta : ℚ)
    (ones : Finset ℝ) (rho : ℚ) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    |evalR (Polynomial.derivative (rationalBernsteinSeparatorPoly C eta ones rho)) x| ≤
      (rationalBernsteinSeparatorDegree C eta : ℝ) / (2 * (C : ℝ)) := by
  classical
  unfold rationalBernsteinSeparatorPoly
  have hn : 0 < rationalBernsteinSeparatorDegree C eta := by
    simpa [rationalBernsteinSeparatorDegree] using
      Ripple.BoundedUniversality.BGP.bernsteinDegreeAbove_pos (64 * (C : ℝ) ^ 2 / (eta : ℝ))
  apply evalR_derivative_root_bernstein01Poly_abs_le C hC
    (rationalBernsteinSeparatorDegree C eta) hn
  · intro k
    unfold rationalBernsteinSeparatorSample
    by_cases h : ∃ a ∈ ones,
        |(rationalBernsteinSamplePoint C (rationalBernsteinSeparatorDegree C eta) k : ℝ) -
            a| ≤ (rho : ℝ) + 1 / 4
    · right
      rw [if_pos h]
    · left
      rw [if_neg h]
  · exact hx

theorem evalR_derivative_rationalBernsteinOneSidedStepPoly_abs_le
    (C : ℚ) (hC : 0 < C) (θ μ : ℝ)
    (eta : ℚ) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    |evalR (Polynomial.derivative (rationalBernsteinOneSidedStepPoly C θ μ eta)) x| ≤
      (rationalBernsteinOneSidedDegree C μ eta : ℝ) / (2 * (C : ℝ)) := by
  classical
  unfold rationalBernsteinOneSidedStepPoly
  have hn : 0 < rationalBernsteinOneSidedDegree C μ eta := by
    simpa [rationalBernsteinOneSidedDegree] using
      Ripple.BoundedUniversality.BGP.bernsteinDegreeAbove_pos
        (((μ / (2 * (C : ℝ))) ^ 2)⁻¹ * (((eta : ℝ))⁻¹ * 4⁻¹))
  apply evalR_derivative_root_bernstein01Poly_abs_le C hC
    (rationalBernsteinOneSidedDegree C μ eta) hn
  · intro k
    unfold rationalBernsteinOneSidedSample
    by_cases h :
        θ ≤ (rationalBernsteinSamplePoint C
          (rationalBernsteinOneSidedDegree C μ eta) k : ℝ)
    · right
      rw [if_pos h]
    · left
      rw [if_neg h]
  · exact hx

private lemma evalR_derivative_mul_one_sub (P Q : Polynomial ℚ) (x : ℝ) :
    evalR (Polynomial.derivative (P * (1 - Q))) x =
      evalR (Polynomial.derivative P) x * (1 - evalR Q x) -
        evalR P x * evalR (Polynomial.derivative Q) x := by
  simp [evalR, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one]
  ring

theorem evalR_derivative_rationalBernsteinIntervalAtomPoly_abs_le
    (C : ℚ) (hC : 0 < C) (tlo thi μ : ℝ) (hμ : 0 < μ)
    (eta : ℚ) (heta : 0 < eta) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    |evalR (Polynomial.derivative (rationalBernsteinIntervalAtomPoly C tlo thi μ eta)) x| ≤
      (rationalBernsteinOneSidedDegree C μ eta : ℝ) / (C : ℝ) := by
  let L : Polynomial ℚ := rationalBernsteinOneSidedStepPoly C tlo μ eta
  let U : Polynomial ℚ := rationalBernsteinOneSidedStepPoly C thi μ eta
  have hLrange := (rationalBernsteinOneSidedStepPoly_spec C hC tlo μ hμ eta heta).1 x hx
  have hUrange := (rationalBernsteinOneSidedStepPoly_spec C hC thi μ hμ eta heta).1 x hx
  have hLd := evalR_derivative_rationalBernsteinOneSidedStepPoly_abs_le
    C hC tlo μ eta hx
  have hUd := evalR_derivative_rationalBernsteinOneSidedStepPoly_abs_le
    C hC thi μ eta hx
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hden_nonneg :
      0 ≤ (rationalBernsteinOneSidedDegree C μ eta : ℝ) / (2 * (C : ℝ)) := by
    positivity
  unfold rationalBernsteinIntervalAtomPoly
  change |evalR (Polynomial.derivative (L * (1 - U))) x| ≤
    (rationalBernsteinOneSidedDegree C μ eta : ℝ) / (C : ℝ)
  rw [evalR_derivative_mul_one_sub]
  have hOneMinus : |1 - evalR U x| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith [hUrange.2]
  have hLAbs : |evalR L x| ≤ 1 := by
    rw [abs_of_nonneg hLrange.1]
    exact hLrange.2
  calc
    |evalR (Polynomial.derivative L) x * (1 - evalR U x) -
        evalR L x * evalR (Polynomial.derivative U) x|
        ≤ |evalR (Polynomial.derivative L) x * (1 - evalR U x)| +
          |evalR L x * evalR (Polynomial.derivative U) x| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le
            (evalR (Polynomial.derivative L) x * (1 - evalR U x))
            (-(evalR L x * evalR (Polynomial.derivative U) x))
    _ = |evalR (Polynomial.derivative L) x| * |1 - evalR U x| +
          |evalR L x| * |evalR (Polynomial.derivative U) x| := by
          rw [abs_mul, abs_mul]
    _ ≤ ((rationalBernsteinOneSidedDegree C μ eta : ℝ) / (2 * (C : ℝ))) * 1 +
          1 * ((rationalBernsteinOneSidedDegree C μ eta : ℝ) / (2 * (C : ℝ))) := by
          exact add_le_add
            (mul_le_mul hLd hOneMinus (abs_nonneg _) hden_nonneg)
            (mul_le_mul hLAbs hUd (abs_nonneg _) (by norm_num))
    _ = (rationalBernsteinOneSidedDegree C μ eta : ℝ) / (C : ℝ) := by
          field_simp [hCr.ne']
          ring

theorem pderiv_coordinatePolynomial_self {d : ℕ} (coord : Fin d) (H : Polynomial ℚ) :
    MvPolynomial.pderiv coord (coordinatePolynomial coord H) =
      coordinatePolynomial coord (Polynomial.derivative H) := by
  unfold coordinatePolynomial
  induction H using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.derivative_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.derivative_monomial]
      simp [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_self, mul_assoc, mul_comm, mul_left_comm]

theorem pderiv_coordinatePolynomial_of_ne {d : ℕ} (coord i : Fin d) (h : i ≠ coord)
    (H : Polynomial ℚ) :
    MvPolynomial.pderiv i (coordinatePolynomial coord H) = 0 := by
  unfold coordinatePolynomial
  induction H using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_of_ne h.symm]

theorem evalPoly4_pderiv_coordinatePolynomial_abs_le_derivative {d : ℕ}
    (coord i : Fin d) (H : Polynomial ℚ) (Z : Fin d → ℝ) :
    |evalPoly4 Z (MvPolynomial.pderiv i (coordinatePolynomial coord H))| ≤
      |evalR (Polynomial.derivative H) (Z coord)| := by
  by_cases h : i = coord
  · subst i
    rw [pderiv_coordinatePolynomial_self]
    rw [evalPoly4_coordinatePolynomial]
  · rw [pderiv_coordinatePolynomial_of_ne coord i h]
    simp [evalPoly4]

theorem relabel_pderiv_of_image
    {d : ℕ} {A B : Type} (S : CoordAtomData d A)
    (f : A → B) (hf : Function.Injective f) (a : A) (i : Fin d) :
    MvPolynomial.pderiv i (((S.relabel f hf).poly) (f a)) =
      MvPolynomial.pderiv i (S.poly a) := by
  classical
  unfold CoordAtomData.relabel
  simp only
  have hex : ∃ x, f x = f a := ⟨a, rfl⟩
  rw [dif_pos hex]
  have hchoose : Classical.choose hex = a := hf (Classical.choose_spec hex)
  simpa [hchoose]

theorem finiteCoordinateAtoms_pderiv_abs_le_separatorDegree
    {d : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (coord : Fin d) (code : A → ℝ)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |code a - code b|)
    (C : ℚ) (hC : 0 < C)
    (hCbound : ∀ a, |code a| + 1 ≤ (C : ℝ))
    (rho eta : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1 / 4) (heta : 0 < eta)
    (a : A) (Z : Fin d → ℝ) (hZ : |Z coord| ≤ (C : ℝ)) (i : Fin d) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i
        ((finiteCoordinateAtoms coord code hgap C hC hCbound rho eta
          hrho hrho4 heta).poly a))| ≤
      (rationalBernsteinSeparatorDegree C eta : ℝ) / (2 * (C : ℝ)) := by
  have hcoord :=
    evalPoly4_pderiv_coordinatePolynomial_abs_le_derivative coord i
      (rationalBernsteinSeparatorPoly C eta ({code a} : Finset ℝ) rho) Z
  have hderiv :=
    evalR_derivative_rationalBernsteinSeparatorPoly_abs_le
      C hC eta ({code a} : Finset ℝ) rho hZ
  calc
    |evalPoly4 Z
      (MvPolynomial.pderiv i
        ((finiteCoordinateAtoms coord code hgap C hC hCbound rho eta
          hrho hrho4 heta).poly a))|
        =
      |evalPoly4 Z
        (MvPolynomial.pderiv i
          (coordinatePolynomial coord
            (rationalBernsteinSeparatorPoly C eta ({code a} : Finset ℝ) rho)))| := by
          rw [finiteCoordinateAtoms_poly_eq coord code hgap C hC hCbound
            rho eta hrho hrho4 heta a]
    _ ≤
      |evalR
        (Polynomial.derivative
          (rationalBernsteinSeparatorPoly C eta ({code a} : Finset ℝ) rho))
        (Z coord)| := hcoord
    _ ≤ (rationalBernsteinSeparatorDegree C eta : ℝ) / (2 * (C : ℝ)) := hderiv

theorem evalR_derivative_rationalBernsteinIntervalAtomFamilyPoly_abs_le
    (C : ℚ) (hC : 0 < C) {A : Type} (lo hi : A → ℝ)
    (gap : ℝ) (hgap : 0 < gap) (eta : ℚ) (heta : 0 < eta)
    (a : A) {x : ℝ} (hx : |x| ≤ (C : ℝ)) :
    |evalR
      (Polynomial.derivative
        (rationalBernsteinIntervalAtomFamilyPoly C lo hi gap eta a)) x| ≤
      (rationalBernsteinOneSidedDegree C (gap / 2) eta : ℝ) / (C : ℝ) := by
  unfold rationalBernsteinIntervalAtomFamilyPoly
  exact evalR_derivative_rationalBernsteinIntervalAtomPoly_abs_le
    C hC (lo a - gap / 2) (hi a + gap / 2) (gap / 2)
    (by positivity) eta heta hx

theorem intervalAtomSpec_pderiv_abs_le_oneSidedDegree
    {d : ℕ} {A : Type} (S : IntervalAtomSpec d A)
    (a : A) (Z : Fin d → ℝ) (hZ : |Z S.coord| ≤ (S.C : ℝ)) (i : Fin d) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i ((S.toCoordAtomData).poly a))| ≤
      (rationalBernsteinOneSidedDegree S.C (S.gap / 2) S.eta : ℝ) /
        (S.C : ℝ) := by
  have hcoord :=
    evalPoly4_pderiv_coordinatePolynomial_abs_le_derivative S.coord i
      (rationalBernsteinIntervalAtomFamilyPoly S.C S.lo S.hi S.gap S.eta a) Z
  have hderiv :=
    evalR_derivative_rationalBernsteinIntervalAtomFamilyPoly_abs_le
      S.C S.C_pos S.lo S.hi S.gap S.gap_pos S.eta S.eta_pos a hZ
  calc
    |evalPoly4 Z
      (MvPolynomial.pderiv i ((S.toCoordAtomData).poly a))|
        =
      |evalPoly4 Z
        (MvPolynomial.pderiv i
          (coordinatePolynomial S.coord
            (rationalBernsteinIntervalAtomFamilyPoly S.C S.lo S.hi S.gap S.eta a)))| := by
          rw [IntervalAtomSpec.toCoordAtomData_poly_eq S a]
    _ ≤
      |evalR
        (Polynomial.derivative
          (rationalBernsteinIntervalAtomFamilyPoly S.C S.lo S.hi S.gap S.eta a))
        (Z S.coord)| := hcoord
    _ ≤
      (rationalBernsteinOneSidedDegree S.C (S.gap / 2) S.eta : ℝ) /
        (S.C : ℝ) := hderiv

/-! ## Product-rule gradient currency for selector products -/

private theorem evalPoly4_prod_range
    {d : ℕ} {ι : Type*} (Z : Fin d → ℝ) (s : Finset ι)
    (P : ι → Poly4 d)
    (hrange : ∀ k ∈ s, 0 ≤ evalPoly4 Z (P k) ∧ evalPoly4 Z (P k) ≤ 1) :
    0 ≤ evalPoly4 Z (∏ k ∈ s, P k) ∧
      evalPoly4 Z (∏ k ∈ s, P k) ≤ 1 := by
  rw [evalPoly4_prod]
  constructor
  · exact Finset.prod_nonneg fun k hk => (hrange k hk).1
  · exact Finset.prod_le_one
      (fun k hk => (hrange k hk).1)
      (fun k hk => (hrange k hk).2)

/--
Coordinate derivative of a finite product, bounded by the sum of coordinate
derivative bounds for the factors, when every factor is in `[0,1]`.
-/
theorem evalPoly4_pderiv_prod_abs_le
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (Z : Fin d → ℝ) (i : Fin d) (s : Finset ι)
    (P : ι → Poly4 d) (S : ι → ℝ)
    (hS_nonneg : ∀ k ∈ s, 0 ≤ S k)
    (hrange : ∀ k ∈ s, 0 ≤ evalPoly4 Z (P k) ∧ evalPoly4 Z (P k) ≤ 1)
    (hderiv : ∀ k ∈ s,
      |evalPoly4 Z (MvPolynomial.pderiv i (P k))| ≤ S k) :
    |evalPoly4 Z (MvPolynomial.pderiv i (∏ k ∈ s, P k))| ≤
      ∑ k ∈ s, S k := by
  classical
  revert hS_nonneg hrange hderiv
  refine Finset.induction_on s ?base ?step
  · intro _ _ _
    simp [evalPoly4]
  · intro a s ha ih
    intro hS_nonneg hrange hderiv
    have hSa : 0 ≤ S a := hS_nonneg a (Finset.mem_insert_self a s)
    have hS_s : ∀ k ∈ s, 0 ≤ S k := fun k hk =>
      hS_nonneg k (Finset.mem_insert_of_mem hk)
    have hrange_a : 0 ≤ evalPoly4 Z (P a) ∧ evalPoly4 Z (P a) ≤ 1 :=
      hrange a (Finset.mem_insert_self a s)
    have hrange_s : ∀ k ∈ s,
        0 ≤ evalPoly4 Z (P k) ∧ evalPoly4 Z (P k) ≤ 1 := fun k hk =>
      hrange k (Finset.mem_insert_of_mem hk)
    have hderiv_a :
        |evalPoly4 Z (MvPolynomial.pderiv i (P a))| ≤ S a :=
      hderiv a (Finset.mem_insert_self a s)
    have hderiv_s : ∀ k ∈ s,
        |evalPoly4 Z (MvPolynomial.pderiv i (P k))| ≤ S k := fun k hk =>
      hderiv k (Finset.mem_insert_of_mem hk)
    have ih' := ih hS_s hrange_s hderiv_s
    have hprod_range := evalPoly4_prod_range Z s P hrange_s
    have hprod_abs : |evalPoly4 Z (∏ k ∈ s, P k)| ≤ 1 := by
      rw [abs_of_nonneg hprod_range.1]
      exact hprod_range.2
    have ha_abs : |evalPoly4 Z (P a)| ≤ 1 := by
      rw [abs_of_nonneg hrange_a.1]
      exact hrange_a.2
    calc
      |evalPoly4 Z (MvPolynomial.pderiv i (∏ k ∈ insert a s, P k))|
          = |evalPoly4 Z
              (MvPolynomial.pderiv i (P a * ∏ k ∈ s, P k))| := by
              rw [Finset.prod_insert ha]
      _ = |evalPoly4 Z
              (MvPolynomial.pderiv i (P a) * (∏ k ∈ s, P k) +
                P a * MvPolynomial.pderiv i (∏ k ∈ s, P k))| := by
              congr 1
              rw [MvPolynomial.pderiv_mul]
      _ = |evalPoly4 Z (MvPolynomial.pderiv i (P a)) *
              evalPoly4 Z (∏ k ∈ s, P k) +
            evalPoly4 Z (P a) *
              evalPoly4 Z (MvPolynomial.pderiv i (∏ k ∈ s, P k))| := by
              simp [evalPoly4, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul]
      _ ≤ |evalPoly4 Z (MvPolynomial.pderiv i (P a)) *
              evalPoly4 Z (∏ k ∈ s, P k)| +
            |evalPoly4 Z (P a) *
              evalPoly4 Z (MvPolynomial.pderiv i (∏ k ∈ s, P k))| :=
              abs_add_le _ _
      _ = |evalPoly4 Z (MvPolynomial.pderiv i (P a))| *
              |evalPoly4 Z (∏ k ∈ s, P k)| +
            |evalPoly4 Z (P a)| *
              |evalPoly4 Z (MvPolynomial.pderiv i (∏ k ∈ s, P k))| := by
              rw [abs_mul, abs_mul]
      _ ≤ S a * 1 + 1 * (∑ k ∈ s, S k) := by
              exact add_le_add
                (mul_le_mul hderiv_a hprod_abs (abs_nonneg _) hSa)
                (mul_le_mul ha_abs ih'
                  (abs_nonneg _) (by positivity))
      _ = ∑ k ∈ insert a s, S k := by
              rw [Finset.sum_insert ha]
              ring

theorem viewSelectorPolyN_pderiv_abs_le_of_atom_bounds
    {d n : ℕ} {V : Type} (spec : GateViewSpecN V n)
    (atoms : GateSelectorAtomsN d n) (Z : Fin d → ℝ) (v : V)
    (i : Fin d) (S : Fin n → ℝ)
    (hS_nonneg : ∀ k, 0 ≤ S k)
    (hZ : atoms.inWorkingDomain Z)
    (hderiv : ∀ k : Fin n,
      |evalPoly4 Z
        (MvPolynomial.pderiv i ((atoms.atom k).poly (spec.comp k v)))| ≤ S k) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i (viewSelectorPolyN spec atoms v))| ≤
      ∑ k : Fin n, S k := by
  classical
  unfold viewSelectorPolyN
  simpa using
    evalPoly4_pderiv_prod_abs_le Z i Finset.univ
      (fun k : Fin n => (atoms.atom k).poly (spec.comp k v)) S
      (fun k _ => hS_nonneg k)
      (fun k _ => (atoms.atom k).range (spec.comp k v) Z (hZ k))
      (fun k _ => hderiv k)

/-! ## Sidecar slope currency and pGapD adapters -/

/-- The headline selector-atom accuracy used by the Bernstein slope sidecar. -/
def paper3SlopeEta : ℚ :=
  1 / (144 * Fintype.card UniversalLocalView)

theorem paper3SlopeEta_pos : 0 < paper3SlopeEta := by
  have hN : (0 : ℚ) < Fintype.card UniversalLocalView := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
      0 < Fintype.card UniversalLocalView)
  unfold paper3SlopeEta
  exact div_pos zero_lt_one (mul_pos (by norm_num) hN)

private theorem paper3SlopeEta_inv_le_bgpScale_pow_six :
    (paper3SlopeEta : ℝ)⁻¹ ≤ 144 * (bgpScale : ℝ) ^ 6 := by
  have hN_nat : 0 < Fintype.card UniversalLocalView :=
    Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩
  have hN : (0 : ℝ) < Fintype.card UniversalLocalView := by
    exact_mod_cast hN_nat
  have hcard_nat := cardUniversalLocalView_le_bgpScale_pow_six
  have hcard : (Fintype.card UniversalLocalView : ℝ) ≤ (bgpScale : ℝ) ^ 6 := by
    exact_mod_cast hcard_nat
  unfold paper3SlopeEta
  push_cast
  field_simp [hN.ne']
  nlinarith

/-- Coarse per-atom slope slots for the five universal selector factors. -/
noncomputable def paper3UniversalAtomSlope (_k : Fin 5) : ℝ :=
  (10 ^ 30 : ℝ) * (bgpScale : ℝ) ^ 8

/-- Coarse five-factor selector slope constant. -/
noncomputable def paper3HeadlineSelectorSlopeConst : ℝ :=
  ∑ k : Fin 5, paper3UniversalAtomSlope k

theorem paper3UniversalAtomSlope_nonneg (k : Fin 5) :
    0 ≤ paper3UniversalAtomSlope k := by
  unfold paper3UniversalAtomSlope
  positivity

theorem paper3HeadlineSelectorSlopeConst_nonneg :
    0 ≤ paper3HeadlineSelectorSlopeConst := by
  unfold paper3HeadlineSelectorSlopeConst
  exact Finset.sum_nonneg fun k _ => paper3UniversalAtomSlope_nonneg k

theorem paper3HeadlineSelectorSlopeConst_eq :
    paper3HeadlineSelectorSlopeConst =
      (5 : ℝ) * ((10 ^ 30 : ℝ) * (bgpScale : ℝ) ^ 8) := by
  norm_num [paper3HeadlineSelectorSlopeConst, paper3UniversalAtomSlope]

private theorem paper3_control_separator_degree_le_slope :
    (rationalBernsteinSeparatorDegree
      (2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1)
      paper3SlopeEta : ℝ) ≤
      paper3UniversalAtomSlope 0 := by
  let Cq : ℚ := 2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1
  let C : ℝ := (Cq : ℝ)
  let S : ℝ := (bgpScale : ℝ)
  have hS1 : 1 ≤ S := by
    dsimp [S]
    exact bgpScaleR_ge_one
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS1
  have hNle : (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) ≤ S := by
    have hnat : Fintype.card (Option (SuppLabel c_f) × Option Γ') ≤ bgpScale := by
      unfold bgpScale bgpCtrlCard
      exact Nat.le_add_right _ _
    dsimp [S]
    exact_mod_cast hnat
  have hC_le : C ≤ 3 * S := by
    dsimp [C, Cq]
    push_cast
    nlinarith
  have hC0 : 0 ≤ C := by
    dsimp [C, Cq]
    push_cast
    positivity
  have heta_inv := paper3SlopeEta_inv_le_bgpScale_pow_six
  have harg_nonneg : 0 ≤ 64 * C ^ 2 / (paper3SlopeEta : ℝ) := by
    have hetaR : 0 < (paper3SlopeEta : ℝ) := by exact_mod_cast paper3SlopeEta_pos
    positivity
  have hdeg :
      (rationalBernsteinSeparatorDegree Cq paper3SlopeEta : ℝ) ≤
        64 * C ^ 2 / (paper3SlopeEta : ℝ) + 2 := by
    unfold rationalBernsteinSeparatorDegree C
    exact bernsteinDegreeAbove_le_add_two harg_nonneg
  have harg_le :
      64 * C ^ 2 / (paper3SlopeEta : ℝ) ≤ 64 * (3 * S) ^ 2 * (144 * S ^ 6) := by
    rw [div_eq_mul_inv]
    gcongr
    exact inv_nonneg.mpr (by exact_mod_cast paper3SlopeEta_pos.le)
  calc
    (rationalBernsteinSeparatorDegree Cq paper3SlopeEta : ℝ)
        ≤ 64 * C ^ 2 / (paper3SlopeEta : ℝ) + 2 := hdeg
    _ ≤ 64 * (3 * S) ^ 2 * (144 * S ^ 6) + 2 := by linarith
    _ ≤ (10 ^ 30 : ℝ) * S ^ 8 := by
      have hpow : 1 ≤ S ^ 8 := one_le_pow₀ hS1
      nlinarith
    _ = paper3UniversalAtomSlope 0 := by
      simp [paper3UniversalAtomSlope, S]

private theorem paper3_control_separator_degree_div_le_slope :
    (rationalBernsteinSeparatorDegree
      (2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1)
      paper3SlopeEta : ℝ) /
        (2 *
          ((2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1 : ℚ) : ℝ)) ≤
      paper3UniversalAtomSlope 0 := by
  let Cq : ℚ := 2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1
  have hdeg_nonneg :
      0 ≤ (rationalBernsteinSeparatorDegree Cq paper3SlopeEta : ℝ) := by
    positivity
  have hden_pos : 0 < 2 * (Cq : ℝ) := by
    dsimp [Cq]
    push_cast
    positivity
  have hden_ge : 1 ≤ 2 * (Cq : ℝ) := by
    have hcard : (0 : ℝ) ≤ Fintype.card (Option (SuppLabel c_f) × Option Γ') := by
      positivity
    dsimp [Cq]
    push_cast
    nlinarith
  have hdiv :
      (rationalBernsteinSeparatorDegree Cq paper3SlopeEta : ℝ) / (2 * (Cq : ℝ)) ≤
        (rationalBernsteinSeparatorDegree Cq paper3SlopeEta : ℝ) := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  exact le_trans hdiv paper3_control_separator_degree_le_slope

private theorem paper3_oneSided_degree_le_slope_of_mu_ge
    {mu : ℝ} (hmu : (1 / 1000 : ℝ) ≤ mu) (k : Fin 5) :
    (rationalBernsteinOneSidedDegree 1 mu paper3SlopeEta : ℝ) ≤
      paper3UniversalAtomSlope k := by
  let S : ℝ := (bgpScale : ℝ)
  have hS1 : 1 ≤ S := by
    dsimp [S]
    exact bgpScaleR_ge_one
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS1
  have hmu_pos : 0 < mu := by linarith
  have hetaR : 0 < (paper3SlopeEta : ℝ) := by exact_mod_cast paper3SlopeEta_pos
  have harg_nonneg :
      0 ≤ 1 / (4 * (paper3SlopeEta : ℝ) * (mu / (2 * (1 : ℝ))) ^ 2) := by
    positivity
  have hdeg :
      (rationalBernsteinOneSidedDegree 1 mu paper3SlopeEta : ℝ) ≤
        1 / (4 * (paper3SlopeEta : ℝ) * (mu / (2 * (1 : ℝ))) ^ 2) + 2 := by
    simpa [rationalBernsteinOneSidedDegree] using
      bernsteinDegreeAbove_le_add_two harg_nonneg
  have harg_le :
      1 / (4 * (paper3SlopeEta : ℝ) * (mu / (2 * (1 : ℝ))) ^ 2) ≤
        (10 ^ 8 : ℝ) * (paper3SlopeEta : ℝ)⁻¹ := by
    have hden_pos : 0 < 4 * (paper3SlopeEta : ℝ) * (mu / (2 * (1 : ℝ))) ^ 2 := by
      positivity
    rw [div_le_iff₀ hden_pos]
    field_simp [hetaR.ne', hmu_pos.ne']
    nlinarith
  have heta_inv := paper3SlopeEta_inv_le_bgpScale_pow_six
  calc
    (rationalBernsteinOneSidedDegree 1 mu paper3SlopeEta : ℝ)
        ≤ 1 / (4 * (paper3SlopeEta : ℝ) * (mu / (2 * (1 : ℝ))) ^ 2) + 2 := hdeg
    _ ≤ (10 ^ 8 : ℝ) * (paper3SlopeEta : ℝ)⁻¹ + 2 := by linarith
    _ ≤ (10 ^ 8 : ℝ) * (144 * S ^ 6) + 2 := by
      gcongr
    _ ≤ (10 ^ 30 : ℝ) * S ^ 8 := by
      have hpow6 : 1 ≤ S ^ 6 := one_le_pow₀ hS1
      have hS6_le_S8 : S ^ 6 ≤ S ^ 8 := by
        have hS6_nonneg : 0 ≤ S ^ 6 := pow_nonneg hS0 6
        have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS1
        calc
          S ^ 6 = S ^ 6 * 1 := by ring
          _ ≤ S ^ 6 * S ^ 2 := mul_le_mul_of_nonneg_left hS2 hS6_nonneg
          _ = S ^ 8 := by ring
      nlinarith
    _ = paper3UniversalAtomSlope k := by
      simp [paper3UniversalAtomSlope, S]

private theorem paper3_interval_degree_div_le_slope_of_mu_ge
    {mu : ℝ} (hmu : (1 / 1000 : ℝ) ≤ mu) (k : Fin 5) :
    (rationalBernsteinOneSidedDegree 1 mu paper3SlopeEta : ℝ) / (1 : ℝ) ≤
      paper3UniversalAtomSlope k := by
  simpa using paper3_oneSided_degree_le_slope_of_mu_ge hmu k

private theorem controlAtom_pderiv_abs_le_paper3UniversalAtomSlope
    (v : UniversalLocalView) (Z : Fin d_U → ℝ)
    (hZ : |Z ctrlCoordU| ≤
      ((2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1 : ℚ) : ℝ))
    (i : Fin d_U) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i
        ((controlAtom paper3SlopeEta paper3SlopeEta_pos).poly
          (ctrlVarCodeU v.label v.var)))| ≤
      paper3UniversalAtomSlope 0 := by
  let code : Option (SuppLabel c_f) × Option Γ' → ℝ :=
    fun p => (ctrlVarCodeU p.1 p.2 : ℝ)
  let Cq : ℚ := 2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1
  have hbase :
      |evalPoly4 Z
        (MvPolynomial.pderiv i
          (((controlAtomSlab paper3SlopeEta paper3SlopeEta_pos).toCoordAtomData).poly
            (v.label, v.var)))| ≤
        paper3UniversalAtomSlope 0 := by
    have hfinite :=
      finiteCoordinateAtoms_pderiv_abs_le_separatorDegree
        ctrlCoordU code
        (by
          intro a b hab
          apply ctrlVarCodeU_margin
          intro heq
          exact hab (ctrlVarCodeU_injective heq))
        Cq (by positivity)
        (by
          intro p
          have hlt :
              ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (p.1, p.2)).val <
                Fintype.card (Option (SuppLabel c_f) × Option Γ') :=
            (Fintype.equivFin (Option (SuppLabel c_f) × Option Γ') (p.1, p.2)).isLt
          have hnn : (0 : ℝ) ≤ (ctrlVarCodeU p.1 p.2 : ℝ) := by
            unfold ctrlVarCodeU; positivity
          rw [abs_of_nonneg hnn]
          unfold ctrlVarCodeU
          push_cast
          have hle :
              (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ'))
                (p.1, p.2)).val : ℝ) ≤
                (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
            exact_mod_cast hlt.le
          calc
            2 *
                (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ'))
                  (p.1, p.2)).val : ℝ) + 1
                ≤ 2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) + 1 := by
                  nlinarith
            _ = (Cq : ℝ) := by
                  dsimp [Cq]
                  push_cast
                  ring)
        (1 / 4) paper3SlopeEta (by norm_num) (by norm_num) paper3SlopeEta_pos
        (v.label, v.var) Z (by simpa [Cq] using hZ) i
    simpa [SlabAtomicSelectorData.toCoordAtomData, controlAtomSlab,
      finiteCoordinateAtoms, code, Cq] using
      le_trans hfinite paper3_control_separator_degree_div_le_slope
  have hrel :=
    relabel_pderiv_of_image
      ((controlAtomSlab paper3SlopeEta paper3SlopeEta_pos).toCoordAtomData)
      (fun p : Option (SuppLabel c_f) × Option Γ' => ctrlVarCodeU p.1 p.2)
      ctrlVarCodeU_injective (v.label, v.var) i
  simpa [controlAtom] using
    (by
      rw [hrel]
      exact hbase)

private theorem mainPairAtom_pderiv_abs_le_paper3UniversalAtomSlope
    (v : UniversalLocalView) (Z : Fin d_U → ℝ)
    (hZ : |Z mainStackCoordU| ≤ (1 : ℝ)) (i : Fin d_U) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i
        ((mainPairAtom paper3SlopeEta paper3SlopeEta_pos).poly
          (mainPairCodeU v.mainTop v.mainSecond)))| ≤
      paper3UniversalAtomSlope 1 := by
  let S : IntervalAtomSpec d_U (Option Γ' × Option Γ') :=
    mainPairAtomSpec paper3SlopeEta paper3SlopeEta_pos
  have hdom : |Z S.coord| ≤ (S.C : ℝ) := by
    simpa [S, mainPairAtomSpec] using hZ
  have hbase :
      |evalPoly4 Z
        (MvPolynomial.pderiv i ((S.toCoordAtomData).poly (v.mainTop, v.mainSecond)))| ≤
        paper3UniversalAtomSlope 1 := by
    have hraw := intervalAtomSpec_pderiv_abs_le_oneSidedDegree
      S (v.mainTop, v.mainSecond) Z hdom i
    have hraw' :
        |evalPoly4 Z
          (MvPolynomial.pderiv i ((S.toCoordAtomData).poly (v.mainTop, v.mainSecond)))| ≤
          (rationalBernsteinOneSidedDegree 1 (S.gap / 2) paper3SlopeEta : ℝ) /
            (1 : ℝ) := by
      simpa [S, mainPairAtomSpec] using hraw
    have hmu : (1 / 1000 : ℝ) ≤ S.gap / 2 := by
      simp [S, mainPairAtomSpec]
      norm_num [mainPairGapQ, B_U, r_LE_U]
    exact le_trans hraw' (paper3_interval_degree_div_le_slope_of_mu_ge hmu 1)
  have hrel :=
    relabel_pderiv_of_image S.toCoordAtomData
      (fun p : Option Γ' × Option Γ' => mainPairCodeU p.1 p.2)
      mainPairCodeU_injective (v.mainTop, v.mainSecond) i
  simpa [S, mainPairAtom] using
    (by
      rw [hrel]
      exact hbase)

private theorem stackTopAtom_pderiv_abs_le_paper3UniversalAtomSlope
    (coord : Fin d_U) (k : Fin 5) (a : Option Γ') (Z : Fin d_U → ℝ)
    (hZ : |Z coord| ≤ (1 : ℝ)) (i : Fin d_U) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i
        ((stackTopAtom coord paper3SlopeEta paper3SlopeEta_pos).poly
          (topCodeU a)))| ≤
      paper3UniversalAtomSlope k := by
  let S : IntervalAtomSpec d_U (Option Γ') :=
    stackTopAtomSpec coord paper3SlopeEta paper3SlopeEta_pos
  have hdom : |Z S.coord| ≤ (S.C : ℝ) := by
    simpa [S, stackTopAtomSpec] using hZ
  have hbase :
      |evalPoly4 Z
        (MvPolynomial.pderiv i ((S.toCoordAtomData).poly a))| ≤
        paper3UniversalAtomSlope k := by
    have hraw := intervalAtomSpec_pderiv_abs_le_oneSidedDegree S a Z hdom i
    have hraw' :
        |evalPoly4 Z
          (MvPolynomial.pderiv i ((S.toCoordAtomData).poly a))| ≤
          (rationalBernsteinOneSidedDegree 1 (S.gap / 2) paper3SlopeEta : ℝ) /
            (1 : ℝ) := by
      simpa [S, stackTopAtomSpec] using hraw
    have hmu : (1 / 1000 : ℝ) ≤ S.gap / 2 := by
      simp [S, stackTopAtomSpec]
      norm_num [topGapU, B_U, r_LE_U]
    exact le_trans hraw' (paper3_interval_degree_div_le_slope_of_mu_ge hmu k)
  have hrel := relabel_pderiv_of_image S.toCoordAtomData
    topCodeU topCodeU_injective a i
  simpa [S, stackTopAtom] using
    (by
      rw [hrel]
      exact hbase)

theorem universalGateAtoms_pderiv_abs_le_paper3UniversalAtomSlope
    (v : UniversalLocalView) (Z : Fin d_U → ℝ)
    (hZ :
      (gateSelectorAtomsCoordN
        (universalGateAtoms paper3SlopeEta paper3SlopeEta_pos)).inWorkingDomain Z)
    (k : Fin 5) (i : Fin d_U) :
    |evalPoly4 Z
      (MvPolynomial.pderiv i
        (((gateSelectorAtomsCoordN
          (universalGateAtoms paper3SlopeEta paper3SlopeEta_pos)).atom k).poly
          (universalViewSpecN.comp k v)))| ≤
      paper3UniversalAtomSlope k := by
  fin_cases k
  · have hdom :
        |Z ctrlCoordU| ≤
          ((2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1 : ℚ) : ℝ) := by
      simpa [gateSelectorAtomsCoordN, universalGateAtoms, controlAtom,
        CoordAtomData.toAtomicSelectorData, CoordAtomData.relabel,
        SlabAtomicSelectorData.toCoordAtomData, controlAtomSlab, finiteCoordinateAtoms] using
        hZ 0
    simpa [gateSelectorAtomsCoordN, universalGateAtoms, universalViewSpecN,
      CoordAtomData.toAtomicSelectorData] using
      controlAtom_pderiv_abs_le_paper3UniversalAtomSlope v Z hdom i
  · have hdom : |Z mainStackCoordU| ≤ (1 : ℝ) := by
      simpa [gateSelectorAtomsCoordN, universalGateAtoms, mainPairAtom,
        CoordAtomData.toAtomicSelectorData, CoordAtomData.relabel,
        IntervalAtomSpec.toCoordAtomData, mainPairAtomSpec] using hZ 1
    simpa [gateSelectorAtomsCoordN, universalGateAtoms, universalViewSpecN,
      CoordAtomData.toAtomicSelectorData] using
      mainPairAtom_pderiv_abs_le_paper3UniversalAtomSlope v Z hdom i
  · have hdom : |Z revStackCoordU| ≤ (1 : ℝ) := by
      simpa [gateSelectorAtomsCoordN, universalGateAtoms, stackTopAtom,
        CoordAtomData.toAtomicSelectorData, CoordAtomData.relabel,
        IntervalAtomSpec.toCoordAtomData, stackTopAtomSpec] using hZ 2
    simpa [gateSelectorAtomsCoordN, universalGateAtoms, universalViewSpecN,
      CoordAtomData.toAtomicSelectorData] using
      stackTopAtom_pderiv_abs_le_paper3UniversalAtomSlope
        revStackCoordU 2 v.revTop Z hdom i
  · have hdom : |Z auxStackCoordU| ≤ (1 : ℝ) := by
      simpa [gateSelectorAtomsCoordN, universalGateAtoms, stackTopAtom,
        CoordAtomData.toAtomicSelectorData, CoordAtomData.relabel,
        IntervalAtomSpec.toCoordAtomData, stackTopAtomSpec] using hZ 3
    simpa [gateSelectorAtomsCoordN, universalGateAtoms, universalViewSpecN,
      CoordAtomData.toAtomicSelectorData] using
      stackTopAtom_pderiv_abs_le_paper3UniversalAtomSlope
        auxStackCoordU 3 v.auxTop Z hdom i
  · have hdom : |Z dataStackCoordU| ≤ (1 : ℝ) := by
      simpa [gateSelectorAtomsCoordN, universalGateAtoms, stackTopAtom,
        CoordAtomData.toAtomicSelectorData, CoordAtomData.relabel,
        IntervalAtomSpec.toCoordAtomData, stackTopAtomSpec] using hZ 4
    simpa [gateSelectorAtomsCoordN, universalGateAtoms, universalViewSpecN,
      CoordAtomData.toAtomicSelectorData] using
      stackTopAtom_pderiv_abs_le_paper3UniversalAtomSlope
        dataStackCoordU 4 v.dataTop Z hdom i

/--
Direct p-value derivative bound from sidecar atom pderiv bounds.  This is the
selector-product route: the only polynomial-gradient input is the per-factor
coordinate derivative certificate, not a monomial coefficient box bound.
-/
theorem selectorMU_universalPvalDerivRHS_abs_le_selectorSlopeP_of_atom_bounds_card
    {p : DynGateParams}
    (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) {URhs : ℝ}
    (hutube : UTube r_LE_U cfg ((sol w).u t))
    (hatom :
      ∀ k : Fin 5, ∀ i : Fin d_U,
        |evalPoly4 ((sol w).u t)
          (MvPolynomial.pderiv i
            (((gateSelectorAtomsCoordN (universalGateAtoms eta heta)).atom k).poly
              (universalViewSpecN.comp k v)))| ≤
          paper3UniversalAtomSlope k)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤
      ((Fintype.card (Fin d_U) : ℝ) * paper3HeadlineSelectorSlopeConst) * URhs := by
  classical
  have hZ := universalGateAtoms_inWorkingDomain eta heta hutube
  have hgrad : ∀ i : Fin d_U,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
        (MvPolynomial.pderiv i
          (viewSelectorPolyN universalViewSpecN
            (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v))| ≤
        paper3HeadlineSelectorSlopeConst := by
    intro i
    simpa [evalPoly4, paper3HeadlineSelectorSlopeConst] using
      viewSelectorPolyN_pderiv_abs_le_of_atom_bounds
        universalViewSpecN (gateSelectorAtomsCoordN (universalGateAtoms eta heta))
        ((sol w).u t) v i paper3UniversalAtomSlope
        paper3UniversalAtomSlope_nonneg hZ (fun k => hatom k i)
  have h :=
    selectorMU_universalPvalDerivRHS_abs_le_of_coord_boundsP
      eta heta (sol := sol) w v t
      (fun _ : Fin d_U => paper3HeadlineSelectorSlopeConst)
      (fun _ : Fin d_U => URhs)
      (fun _ => paper3HeadlineSelectorSlopeConst_nonneg)
      hgrad huRHS
  calc
    |selectorMU_universalPvalDerivRHSP eta heta sol w v t|
        ≤ ∑ i : Fin d_U, paper3HeadlineSelectorSlopeConst * URhs := h
    _ = ((Fintype.card (Fin d_U) : ℝ) * paper3HeadlineSelectorSlopeConst) * URhs := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring

theorem selectorMU_universalPvalGapDerivRHS_abs_le_selectorSlopeP_of_atom_bounds_card
    {p : DynGateParams}
    (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) {URhs : ℝ}
    (hutube : UTube r_LE_U cfg ((sol w).u t))
    (hatom :
      ∀ x : UniversalLocalView, ∀ k : Fin 5, ∀ i : Fin d_U,
        |evalPoly4 ((sol w).u t)
          (MvPolynomial.pderiv i
            (((gateSelectorAtomsCoordN (universalGateAtoms eta heta)).atom k).poly
              (universalViewSpecN.comp k x)))| ≤
          paper3UniversalAtomSlope k)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w c t -
      selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤
      (2 * ((Fintype.card (Fin d_U) : ℝ) *
        paper3HeadlineSelectorSlopeConst)) * URhs := by
  have hview : ∀ x : UniversalLocalView,
      |selectorMU_universalPvalDerivRHSP eta heta sol w x t| ≤
        ((Fintype.card (Fin d_U) : ℝ) *
          paper3HeadlineSelectorSlopeConst) * URhs := by
    intro x
    exact selectorMU_universalPvalDerivRHS_abs_le_selectorSlopeP_of_atom_bounds_card
      eta heta (sol := sol) w x t cfg hutube (fun k i => hatom x k i) huRHS
  have hgap :=
    selectorMU_universalPvalGapDerivRHS_abs_le_of_view_boundsP
      eta heta (sol := sol) w c v t
      (fun _ : UniversalLocalView =>
        ((Fintype.card (Fin d_U) : ℝ) *
          paper3HeadlineSelectorSlopeConst) * URhs)
      hview
  calc
    |selectorMU_universalPvalDerivRHSP eta heta sol w c t -
      selectorMU_universalPvalDerivRHSP eta heta sol w v t|
        ≤ ((Fintype.card (Fin d_U) : ℝ) *
          paper3HeadlineSelectorSlopeConst) * URhs +
          ((Fintype.card (Fin d_U) : ℝ) *
            paper3HeadlineSelectorSlopeConst) * URhs := hgap
    _ = (2 * ((Fintype.card (Fin d_U) : ℝ) *
        paper3HeadlineSelectorSlopeConst)) * URhs := by ring

theorem selectorMU_universalPvalDerivRHS_abs_le_selectorSlopeP
    {p : DynGateParams}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p paper3SlopeEta paper3SlopeEta_pos Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) {URhs : ℝ}
    (hutube : UTube r_LE_U cfg ((sol w).u t))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP
      paper3SlopeEta paper3SlopeEta_pos sol w v t| ≤
      ((Fintype.card (Fin d_U) : ℝ) * paper3HeadlineSelectorSlopeConst) * URhs := by
  exact selectorMU_universalPvalDerivRHS_abs_le_selectorSlopeP_of_atom_bounds_card
    paper3SlopeEta paper3SlopeEta_pos (sol := sol) w v t cfg hutube
    (fun k i =>
      universalGateAtoms_pderiv_abs_le_paper3UniversalAtomSlope v ((sol w).u t)
        (universalGateAtoms_inWorkingDomain paper3SlopeEta paper3SlopeEta_pos hutube) k i)
    huRHS

theorem selectorMU_universalPvalGapDerivRHS_abs_le_selectorSlopeP
    {p : DynGateParams}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p paper3SlopeEta paper3SlopeEta_pos Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) {URhs : ℝ}
    (hutube : UTube r_LE_U cfg ((sol w).u t))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP paper3SlopeEta paper3SlopeEta_pos sol w c t -
      selectorMU_universalPvalDerivRHSP paper3SlopeEta paper3SlopeEta_pos sol w v t| ≤
      (2 * ((Fintype.card (Fin d_U) : ℝ) *
        paper3HeadlineSelectorSlopeConst)) * URhs := by
  exact selectorMU_universalPvalGapDerivRHS_abs_le_selectorSlopeP_of_atom_bounds_card
    paper3SlopeEta paper3SlopeEta_pos (sol := sol) w c v t cfg hutube
    (fun x k i =>
      universalGateAtoms_pderiv_abs_le_paper3UniversalAtomSlope x ((sol w).u t)
        (universalGateAtoms_inWorkingDomain paper3SlopeEta paper3SlopeEta_pos hutube) k i)
    huRHS

/-- Currency placeholder for downstream S4 leaves. -/
theorem paper3HeadlineSelectorSlopeConst_le_exp_currency_NW (w : ℕ) :
    paper3HeadlineSelectorSlopeConst ≤
      Real.exp (20 * (bgpScaleW w : ℝ) + 200) := by
  rw [paper3HeadlineSelectorSlopeConst_eq]
  let S : ℝ := (bgpScale : ℝ)
  let W : ℝ := (bgpScaleW w : ℝ)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact bgpScaleR_pos.le
  have hSleW : S ≤ W := by
    dsimp [S, W]
    exact bgpScaleR_le_bgpScaleWR w
  have hWexp : W ≤ Real.exp W := by
    have h := Real.add_one_le_exp W
    linarith
  have hS_exp : S ≤ Real.exp W := le_trans hSleW hWexp
  have hS8 : S ^ 8 ≤ Real.exp (8 * W) := by
    have hp := pow_le_pow_left₀ hS_nonneg hS_exp 8
    have hexp_pow : (Real.exp W) ^ 8 = Real.exp (8 * W) := by
      rw [← Real.exp_nat_mul]
      norm_num
    simpa [hexp_pow] using hp
  have hnum : (5 * 10 ^ 30 : ℝ) ≤ Real.exp 200 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h
      exact h
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 200
    have hnum2 : (5 * 10 ^ 30 : ℝ) ≤ (2 : ℝ) ^ 200 := by norm_num
    have hexp : (Real.exp 1) ^ 200 = Real.exp 200 := by
      rw [← Real.exp_nat_mul]
      norm_num
    exact le_trans hnum2 (by simpa [hexp] using hpow)
  calc
    (5 : ℝ) * ((10 ^ 30 : ℝ) * S ^ 8)
        = (5 * 10 ^ 30 : ℝ) * S ^ 8 := by ring
    _ ≤ Real.exp 200 * Real.exp (8 * W) := by
      exact mul_le_mul hnum hS8 (pow_nonneg hS_nonneg 8) (Real.exp_pos _).le
    _ = Real.exp (200 + 8 * W) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (20 * W + 200) := by
      apply Real.exp_le_exp.mpr
      nlinarith [bgpScaleWR_pos w]

end BernsteinSlope

end Ripple.BoundedUniversality.BGP

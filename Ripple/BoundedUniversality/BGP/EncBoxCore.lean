/-
Ripple.BoundedUniversality.BGP.EncBoxCore
---------------------
The encoding-box core for the de-axiom supply residuals `hMix` and `hbox`.

`hMix` (the polynomial target `FP_MU_N i` bounded) is a compact-box polynomial
estimate: once an independent `u`-tube `|u − enc(c_j)| ≤ D` is available, the
renamed target `contractRenameU (PU i)` is bounded by its coefficient box-bound.
This is NON-circular as long as the u-tube is supplied independently of the
finite-horizon existence proof.

Design + proofs cross-checked with the repo-connected channel (pbook R-ENCBOX);
verified here by build.
-/

import Ripple.BoundedUniversality.BGP.FieldPackageMU

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace EncBoxCore

/-- Absolute coefficient box bound for a multivariate polynomial on `|x i| ≤ r i`. -/
def mvPolynomialBoxBound {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (r : Fin n → ℝ) : ℝ :=
  ∑ m ∈ p.support, |((p.coeff m : ℚ) : ℝ)| * ∏ i : Fin n, r i ^ m i

lemma mvPolynomialBoxBound_nonneg {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) {r : Fin n → ℝ} (hr0 : ∀ i, 0 ≤ r i) :
    0 ≤ mvPolynomialBoxBound p r := by
  dsimp [mvPolynomialBoxBound]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _)

lemma mvPolynomialBoxBound_mono {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) {r s : Fin n → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hrs : ∀ i, r i ≤ s i) :
    mvPolynomialBoxBound p r ≤ mvPolynomialBoxBound p s := by
  dsimp [mvPolynomialBoxBound]
  refine Finset.sum_le_sum ?_
  intro m _hm
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine Finset.prod_le_prod (fun i _ => pow_nonneg (hr0 i) _) ?_
  intro i _hi
  exact pow_le_pow_left₀ (hr0 i) (hrs i) _

/-- Compact-box polynomial estimate: `|eval₂ x p| ≤ boxBound p r` when `|x i| ≤ r i`. -/
lemma mvPolynomial_eval₂_abs_le_boxBound {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) {x r : Fin n → ℝ}
    (_hr0 : ∀ i, 0 ≤ r i) (hx : ∀ i, |x i| ≤ r i) :
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p| ≤ mvPolynomialBoxBound p r := by
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ m ∈ p.support, (algebraMap ℚ ℝ) (p.coeff m) * ∏ i : Fin n, x i ^ m i|
        ≤ ∑ m ∈ p.support,
            |(algebraMap ℚ ℝ) (p.coeff m) * ∏ i : Fin n, x i ^ m i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ mvPolynomialBoxBound p r := by
      dsimp [mvPolynomialBoxBound]
      refine Finset.sum_le_sum ?_
      intro m _hm
      rw [abs_mul]
      change |((p.coeff m : ℚ) : ℝ)| * |∏ i : Fin n, x i ^ m i| ≤
        |((p.coeff m : ℚ) : ℝ)| * ∏ i : Fin n, r i ^ m i
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_
      intro i _hi
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _

/-- The compact-box bound after renaming into the contract `u` register
(reuses `Ripple.BoundedUniversality.BGP.contractRenameU`). -/
lemma eval_contractRenameU_abs_le_boxBound {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ)
    {y : Fin (contractDim d) → ℝ} {r : Fin d → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hu : ∀ i, |y (contractU i)| ≤ r i) :
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (contractRenameU p)|
      ≤ mvPolynomialBoxBound p r := by
  rw [contractRenameU, MvPolynomial.eval₂_rename]
  exact mvPolynomial_eval₂_abs_le_boxBound p hr0 hu

/-- A single finite bound for the whole target family. -/
def targetFamilyBoxBound {d : ℕ}
    (PU : Fin d → MvPolynomial (Fin d) ℚ) (r : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, mvPolynomialBoxBound (PU i) r

lemma targetFamilyBoxBound_nonneg {d : ℕ}
    (PU : Fin d → MvPolynomial (Fin d) ℚ) {r : Fin d → ℝ} (hr0 : ∀ i, 0 ≤ r i) :
    0 ≤ targetFamilyBoxBound PU r := by
  dsimp [targetFamilyBoxBound]
  exact Finset.sum_nonneg fun i _ => mvPolynomialBoxBound_nonneg (PU i) hr0

lemma targetFamilyBoxBound_mono {d : ℕ}
    (PU : Fin d → MvPolynomial (Fin d) ℚ) {r s : Fin d → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hrs : ∀ i, r i ≤ s i) :
    targetFamilyBoxBound PU r ≤ targetFamilyBoxBound PU s := by
  dsimp [targetFamilyBoxBound]
  exact Finset.sum_le_sum fun i _ => mvPolynomialBoxBound_mono (PU i) hr0 hrs

/-- **`hMix` from an independent `u`-encoding-tube.**  The non-circular
compact-polynomial bound: with `|u − enc(c_j)| ≤ D` and `|enc(c_j)| ≤ encBd`, the
renamed target `contractRenameU (PU i)` is bounded by `targetFamilyBoxBound PU rU`
for any `rU ≥ D + encBd`. -/
lemma hMix_of_u_encoding_tube
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {E : StackMachineEncoding d nS M}
    (PU : Fin d → MvPolynomial (Fin d) ℚ)
    (c : ℕ → Conf) (y : ℝ → Fin (contractDim d) → ℝ)
    (j : ℕ) (t : ℝ) (D : ℝ)
    (encBd rU : Fin d → ℝ)
    (hrU0 : ∀ i, 0 ≤ rU i)
    (henc : ∀ i, |E.enc (c j) i| ≤ encBd i)
    (hu_tube : ∀ i, |y t (contractU i) - E.enc (c j) i| ≤ D)
    (hrU : ∀ i, D + encBd i ≤ rU i) :
    ∀ i : Fin d,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (contractRenameU (PU i))|
        ≤ targetFamilyBoxBound PU rU := by
  intro i
  have hu_abs : ∀ k, |y t (contractU k)| ≤ rU k := by
    intro k
    calc
      |y t (contractU k)|
          = |(y t (contractU k) - E.enc (c j) k) + E.enc (c j) k| := by ring_nf
      _ ≤ |y t (contractU k) - E.enc (c j) k| + |E.enc (c j) k| := abs_add_le _ _
      _ ≤ D + encBd k := add_le_add (hu_tube k) (henc k)
      _ ≤ rU k := hrU k
  have hpoly := eval_contractRenameU_abs_le_boxBound (PU i) hrU0 hu_abs
  exact hpoly.trans
    (Finset.single_le_sum
      (fun k _ => mvPolynomialBoxBound_nonneg (PU k) hrU0) (Finset.mem_univ i))

end EncBoxCore

end

end Ripple.BoundedUniversality.BGP

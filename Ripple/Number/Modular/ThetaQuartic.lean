import Ripple.Number.Modular.SingularModuli
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin

/-!
# Jacobi quartic theta identity

This file proves the theta-constant identity
`θ₃(τ)^4 = θ₂(τ)^4 + θ₄(τ)^4` on the upper half-plane.

The proof route is the four-dimensional lattice-theta proof.  Expanding the
fourth powers gives theta sums over `ℤ^4`; the Hadamard isometry identifies
the two spinor half-lattice cosets with the odd coset of `ℤ^4`.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Complex
open scoped BigOperators

private abbrev Z4 := Fin 4 → ℤ

private def z4Sum (x : Z4) : ℤ :=
  ∑ i, x i

private abbrev Z4Even := {x : Z4 // Even (z4Sum x)}
private abbrev Z4Odd := {x : Z4 // Odd (z4Sum x)}

private def z4NormSq (x : Z4) : ℤ :=
  ∑ i, x i ^ 2

private def hz0 (x : Z4) : ℤ := x 0 + x 1 + x 2 + x 3
private def hz1 (x : Z4) : ℤ := x 0 + x 1 - x 2 - x 3
private def hz2 (x : Z4) : ℤ := x 0 - x 1 + x 2 - x 3
private def hz3 (x : Z4) : ℤ := x 0 - x 1 - x 2 + x 3

private def hadamardZ4 (x : Z4) : Z4
  | 0 => hz0 x / 2
  | 1 => hz1 x / 2
  | 2 => hz2 x / 2
  | 3 => hz3 x / 2

private def flip0 (x : Z4) : Z4
  | 0 => -x 0 - 1
  | 1 => x 1
  | 2 => x 2
  | 3 => x 3

private def spinorToVector (m : Z4) : Z4
  | 0 => (hz0 m + 2) / 2
  | 1 => hz1 m / 2
  | 2 => hz2 m / 2
  | 3 => hz3 m / 2

private def vectorToSpinor (x : Z4) : Z4
  | 0 => (hz0 x - 1) / 2
  | 1 => (hz1 x - 1) / 2
  | 2 => (hz2 x - 1) / 2
  | 3 => (hz3 x - 1) / 2

private def halfNormSq (m : Z4) : ℂ :=
  ∑ i, ((m i : ℂ) + 1 / 2) ^ 2

private def qTerm (τ : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * τ)

private def qTermHalf (τ : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ)

private def qTermFour (τ : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((n : ℂ) + n ^ 2 * τ))

private def thetaThreeZ4Term (τ : ℂ) (x : Z4) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (z4NormSq x : ℂ) * τ)

private def thetaTwoZ4Term (τ : ℂ) (m : Z4) : ℂ :=
  Complex.exp (Real.pi * Complex.I * halfNormSq m * τ)

private def thetaFourZ4Term (τ : ℂ) (x : Z4) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((z4Sum x : ℂ) + (z4NormSq x : ℂ) * τ))

private def z4ProdEquiv : Z4 ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun x := ((x 0, x 1), (x 2, x 3))
  invFun p
    | 0 => p.1.1
    | 1 => p.1.2
    | 2 => p.2.1
    | 3 => p.2.2
  left_inv x := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

private lemma z4Sum_apply (x : Z4) :
    z4Sum x = x 0 + x 1 + x 2 + x 3 := by
  simp [z4Sum, Fin.sum_univ_four]

private lemma z4NormSq_apply (x : Z4) :
    z4NormSq x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  simp [z4NormSq, Fin.sum_univ_four]

private lemma flip0_involutive (x : Z4) :
    flip0 (flip0 x) = x := by
  ext i
  fin_cases i <;> simp [flip0]

private lemma z4Sum_flip0 (x : Z4) :
    z4Sum (flip0 x) = z4Sum x - 2 * x 0 - 1 := by
  rw [z4Sum_apply, z4Sum_apply]
  simp [flip0]
  ring

private lemma flip0_even_to_odd (x : Z4) (hx : Even (z4Sum x)) :
    Odd (z4Sum (flip0 x)) := by
  rcases hx with ⟨k, hk⟩
  rw [z4Sum_flip0, hk]
  use k - x 0 - 1
  ring

private lemma flip0_odd_to_even (x : Z4) (hx : Odd (z4Sum x)) :
    Even (z4Sum (flip0 x)) := by
  rcases hx with ⟨k, hk⟩
  rw [z4Sum_flip0, hk]
  use k - x 0
  ring

private def flip0EvenOddEquiv : Z4Even ≃ Z4Odd where
  toFun x := ⟨flip0 x.1, flip0_even_to_odd x.1 x.2⟩
  invFun x := ⟨flip0 x.1, flip0_odd_to_even x.1 x.2⟩
  left_inv x := by
    ext i
    exact congr_fun (flip0_involutive x.1) i
  right_inv x := by
    ext i
    exact congr_fun (flip0_involutive x.1) i

private lemma halfNormSq_apply (m : Z4) :
    halfNormSq m =
      ((m 0 : ℂ) + 1 / 2) ^ 2 + ((m 1 : ℂ) + 1 / 2) ^ 2 +
        ((m 2 : ℂ) + 1 / 2) ^ 2 + ((m 3 : ℂ) + 1 / 2) ^ 2 := by
  simp [halfNormSq, Fin.sum_univ_four]

private lemma halfNormSq_flip0 (x : Z4) :
    halfNormSq (flip0 x) = halfNormSq x := by
  rw [halfNormSq_apply, halfNormSq_apply]
  simp [flip0]
  ring

private lemma spinorToVector_odd_of_even (m : Z4) (hm : Even (z4Sum m)) :
    Odd (z4Sum (spinorToVector m)) := by
  rw [z4Sum_apply]
  simp [spinorToVector, hz0, hz1, hz2, hz3]
  rcases hm with ⟨k, hk⟩
  rw [z4Sum_apply] at hk
  use m 0
  omega

private lemma vectorToSpinor_even_of_odd (x : Z4) (hx : Odd (z4Sum x)) :
    Even (z4Sum (vectorToSpinor x)) := by
  rw [z4Sum_apply]
  simp [vectorToSpinor, hz0, hz1, hz2, hz3]
  rcases hx with ⟨k, hk⟩
  rw [z4Sum_apply] at hk
  use x 0 - 1
  omega

private lemma vectorToSpinor_spinorToVector (m : Z4) (hm : Even (z4Sum m)) :
    vectorToSpinor (spinorToVector m) = m := by
  ext i
  rcases hm with ⟨k, hk⟩
  rw [z4Sum_apply] at hk
  fin_cases i <;>
    simp [vectorToSpinor, spinorToVector, hz0, hz1, hz2, hz3] <;> omega

private lemma spinorToVector_vectorToSpinor (x : Z4) (hx : Odd (z4Sum x)) :
    spinorToVector (vectorToSpinor x) = x := by
  ext i
  rcases hx with ⟨k, hk⟩
  rw [z4Sum_apply] at hk
  fin_cases i <;>
    simp [vectorToSpinor, spinorToVector, hz0, hz1, hz2, hz3] <;> omega

private def spinorVectorEquiv : Z4Even ≃ Z4Odd where
  toFun m := ⟨spinorToVector m.1, spinorToVector_odd_of_even m.1 m.2⟩
  invFun x := ⟨vectorToSpinor x.1, vectorToSpinor_even_of_odd x.1 x.2⟩
  left_inv m := by
    ext i
    exact congr_fun (vectorToSpinor_spinorToVector m.1 m.2) i
  right_inv x := by
    ext i
    exact congr_fun (spinorToVector_vectorToSpinor x.1 x.2) i

private def z4ParityEquiv : Z4 ≃ Z4Even ⊕ Z4Odd where
  toFun x :=
    if hx : Even (z4Sum x) then Sum.inl ⟨x, hx⟩
    else Sum.inr ⟨x, Int.not_even_iff_odd.mp hx⟩
  invFun y := y.elim (fun x => x.1) (fun x => x.1)
  left_inv x := by
    by_cases hx : Even (z4Sum x) <;> simp [hx]
  right_inv y := by
    rcases y with x | x
    · simp [x.2]
    · simp [show ¬ Even (z4Sum x.1) from Int.not_even_iff_odd.mpr x.2]

private lemma spinorToVector_norm (m : Z4) (hm : Even (z4Sum m)) :
    ((z4NormSq (spinorToVector m) : ℂ) = halfNormSq m) := by
  rcases hm with ⟨k, hk⟩
  rw [z4Sum_apply] at hk
  rw [z4NormSq_apply, halfNormSq_apply]
  norm_num
  have h0 : ((spinorToVector m 0 : ℤ) : ℂ) =
      ((m 0 : ℂ) + (m 1 : ℂ) + (m 2 : ℂ) + (m 3 : ℂ) + 2) / 2 := by
    unfold spinorToVector hz0
    rw [Int.cast_div_charZero (show (2 : ℤ) ∣ m 0 + m 1 + m 2 + m 3 + 2 by
      use k + 1
      omega
    )]
    norm_num
  have h1 : ((spinorToVector m 1 : ℤ) : ℂ) =
      ((m 0 : ℂ) + (m 1 : ℂ) - (m 2 : ℂ) - (m 3 : ℂ)) / 2 := by
    unfold spinorToVector hz1
    rw [Int.cast_div_charZero (show (2 : ℤ) ∣ m 0 + m 1 - m 2 - m 3 by
      use k - m 2 - m 3
      omega
    )]
    norm_num
  have h2 : ((spinorToVector m 2 : ℤ) : ℂ) =
      ((m 0 : ℂ) - (m 1 : ℂ) + (m 2 : ℂ) - (m 3 : ℂ)) / 2 := by
    unfold spinorToVector hz2
    rw [Int.cast_div_charZero (show (2 : ℤ) ∣ m 0 - m 1 + m 2 - m 3 by
      use k - m 1 - m 3
      omega
    )]
    norm_num
  have h3 : ((spinorToVector m 3 : ℤ) : ℂ) =
      ((m 0 : ℂ) - (m 1 : ℂ) - (m 2 : ℂ) + (m 3 : ℂ)) / 2 := by
    unfold spinorToVector hz3
    rw [Int.cast_div_charZero (show (2 : ℤ) ∣ m 0 - m 1 - m 2 + m 3 by
      use k - m 1 - m 2
      omega
    )]
    norm_num
  rw [h0, h1, h2, h3]
  ring

private lemma exp_int_mul_pi_I_of_even {n : ℤ} (hn : Even n) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ)) = 1 := by
  rcases hn with ⟨k, rfl⟩
  rw [show Real.pi * Complex.I * (((k + k : ℤ) : ℂ)) =
      k * (2 * Real.pi * Complex.I) by
    norm_num
    ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

private lemma exp_int_mul_pi_I_of_odd {n : ℤ} (hn : Odd n) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ)) = -1 := by
  rcases hn with ⟨k, rfl⟩
  rw [show Real.pi * Complex.I * (((2 * k + 1 : ℤ) : ℂ)) =
      k * (2 * Real.pi * Complex.I) + Real.pi * Complex.I by
    norm_num
    ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

private lemma one_sub_exp_int_mul_pi_I (n : ℤ) :
    1 - Complex.exp (Real.pi * Complex.I * (n : ℂ)) =
      if Even n then 0 else 2 := by
  by_cases hn : Even n
  · simp [hn, exp_int_mul_pi_I_of_even hn]
  · have hodd : Odd n := Int.not_even_iff_odd.mp hn
    simp [hn, exp_int_mul_pi_I_of_odd hodd]
    norm_num

private lemma tsum_four_eq_tsum_z4 {f : ℤ → ℂ}
    (hf : Summable fun n => ‖f n‖) :
    (∑' n : ℤ, f n) ^ 4 =
      ∑' x : Z4, (f (x 0) * f (x 1)) * (f (x 2) * f (x 3)) := by
  let g : ℤ × ℤ → ℂ := fun p => f p.1 * f p.2
  have hfg_norm : Summable fun p : ℤ × ℤ => ‖g p‖ := by
    simpa [g] using hf.mul_norm hf
  have hsq :
      (∑' n : ℤ, f n) * (∑' n : ℤ, f n) =
        ∑' p : ℤ × ℤ, g p := by
    simpa [g] using tsum_mul_tsum_of_summable_norm (R := ℂ) hf hf
  calc
    (∑' n : ℤ, f n) ^ 4
        = ((∑' n : ℤ, f n) * (∑' n : ℤ, f n)) *
            ((∑' n : ℤ, f n) * (∑' n : ℤ, f n)) := by ring
    _ = (∑' p : ℤ × ℤ, g p) * (∑' p : ℤ × ℤ, g p) := by rw [hsq]
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), g p.1 * g p.2 := by
      simpa [g] using tsum_mul_tsum_of_summable_norm (R := ℂ) hfg_norm hfg_norm
    _ = ∑' x : Z4, (f (x 0) * f (x 1)) * (f (x 2) * f (x 3)) := by
      rw [← z4ProdEquiv.tsum_eq
        (fun p : (ℤ × ℤ) × (ℤ × ℤ) => g p.1 * g p.2)]
      rfl

private lemma summable_four_z4 {f : ℤ → ℂ}
    (hf : Summable fun n => ‖f n‖) :
    Summable fun x : Z4 => (f (x 0) * f (x 1)) * (f (x 2) * f (x 3)) := by
  let g : ℤ × ℤ → ℂ := fun p => f p.1 * f p.2
  have hfg_norm : Summable fun p : ℤ × ℤ => ‖g p‖ := by
    simpa [g] using hf.mul_norm hf
  have hprod : Summable fun p : (ℤ × ℤ) × (ℤ × ℤ) => g p.1 * g p.2 :=
    summable_mul_of_summable_norm (R := ℂ) hfg_norm hfg_norm
  simpa [g] using! hprod.comp_injective z4ProdEquiv.injective

private lemma qTerm_norm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖qTerm τ n‖ := by
  have hbound := summable_pow_mul_jacobiTheta₂_term_bound 0 hτ 0
  refine hbound.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  simpa [qTerm, jacobiTheta₂_term] using
    (norm_jacobiTheta₂_term_le (S := 0) (T := τ.im) hτ
      (z := 0) (τ := τ) (by norm_num) le_rfl n)

private lemma thetaTwo_base_norm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖jacobiTheta₂_term n (τ / 2) τ‖ := by
  have hbound := summable_pow_mul_jacobiTheta₂_term_bound |(τ / 2).im| hτ 0
  refine hbound.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  simpa using
    (norm_jacobiTheta₂_term_le (S := |(τ / 2).im|) (T := τ.im) hτ
      (z := τ / 2) (τ := τ) le_rfl le_rfl n)

private lemma qTermHalf_norm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖qTermHalf τ n‖ := by
  have hbase := thetaTwo_base_norm_summable hτ
  have hmul :
      Summable fun n : ℤ =>
        ‖Complex.exp (Real.pi * Complex.I * τ / 4)‖ *
          ‖jacobiTheta₂_term n (τ / 2) τ‖ := hbase.mul_left _
  convert hmul using 1
  ext n
  have hterm :
      qTermHalf τ n =
        Complex.exp (Real.pi * Complex.I * τ / 4) *
          jacobiTheta₂_term n (τ / 2) τ := by
    unfold qTermHalf jacobiTheta₂_term
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hterm, norm_mul]

private lemma thetaFour_base_norm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖jacobiTheta₂_term n (1 / 2) τ‖ := by
  have hbound := summable_pow_mul_jacobiTheta₂_term_bound |((1 / 2 : ℂ).im)| hτ 0
  refine hbound.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  simpa using
    (norm_jacobiTheta₂_term_le (S := |((1 / 2 : ℂ).im)|) (T := τ.im) hτ
      (z := 1 / 2) (τ := τ) le_rfl le_rfl n)

private lemma qTermFour_norm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖qTermFour τ n‖ := by
  convert thetaFour_base_norm_summable hτ using 1
  ext n
  unfold qTermFour jacobiTheta₂_term
  congr 1
  ring

private lemma jacobiTheta_pow_four_eq_tsum_z4 {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ ^ 4 = ∑' x : Z4, thetaThreeZ4Term τ x := by
  rw [jacobiTheta]
  change (∑' n : ℤ, qTerm τ n) ^ 4 = ∑' x : Z4, thetaThreeZ4Term τ x
  rw [tsum_four_eq_tsum_z4 (qTerm_norm_summable hτ)]
  apply tsum_congr
  intro x
  unfold qTerm thetaThreeZ4Term
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [z4NormSq_apply]
  norm_num
  ring

private lemma thetaTwoConst_pow_four_eq_tsum_z4 {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwoConst τ ^ 4 = ∑' m : Z4, thetaTwoZ4Term τ m := by
  rw [thetaTwoConst_eq_tsum_shifted]
  change (∑' n : ℤ, qTermHalf τ n) ^ 4 = ∑' m : Z4, thetaTwoZ4Term τ m
  rw [tsum_four_eq_tsum_z4 (qTermHalf_norm_summable hτ)]
  apply tsum_congr
  intro m
  unfold qTermHalf thetaTwoZ4Term
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [halfNormSq_apply]
  ring

private lemma thetaFourConst_pow_four_eq_tsum_z4 {τ : ℂ} (hτ : 0 < τ.im) :
    thetaFourConst τ ^ 4 = ∑' x : Z4, thetaFourZ4Term τ x := by
  rw [thetaFourConst_eq_tsum]
  change (∑' n : ℤ, qTermFour τ n) ^ 4 = ∑' x : Z4, thetaFourZ4Term τ x
  rw [tsum_four_eq_tsum_z4 (qTermFour_norm_summable hτ)]
  apply tsum_congr
  intro x
  unfold qTermFour thetaFourZ4Term
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [z4Sum_apply, z4NormSq_apply]
  norm_num
  ring

private lemma thetaThreeZ4_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun x : Z4 => thetaThreeZ4Term τ x := by
  convert summable_four_z4 (qTerm_norm_summable hτ) using 1
  ext x
  unfold qTerm thetaThreeZ4Term
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [z4NormSq_apply]
  norm_num
  ring

private lemma thetaTwoZ4_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun x : Z4 => thetaTwoZ4Term τ x := by
  convert summable_four_z4 (qTermHalf_norm_summable hτ) using 1
  ext x
  unfold qTermHalf thetaTwoZ4Term
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [halfNormSq_apply]
  ring

private lemma thetaFourZ4_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun x : Z4 => thetaFourZ4Term τ x := by
  convert summable_four_z4 (qTermFour_norm_summable hτ) using 1
  ext x
  unfold qTermFour thetaFourZ4Term
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [z4Sum_apply, z4NormSq_apply]
  norm_num
  ring

private lemma thetaFourZ4Term_eq_exp_mul (τ : ℂ) (x : Z4) :
    thetaFourZ4Term τ x =
      Complex.exp (Real.pi * Complex.I * (z4Sum x : ℂ)) * thetaThreeZ4Term τ x := by
  unfold thetaFourZ4Term thetaThreeZ4Term
  rw [show Real.pi * Complex.I * ((z4Sum x : ℂ) + (z4NormSq x : ℂ) * τ) =
      Real.pi * Complex.I * (z4Sum x : ℂ) +
        Real.pi * Complex.I * (z4NormSq x : ℂ) * τ by ring]
  rw [Complex.exp_add]

private lemma thetaFourZ4Term_eq_of_even (τ : ℂ) {x : Z4} (hx : Even (z4Sum x)) :
    thetaFourZ4Term τ x = thetaThreeZ4Term τ x := by
  rw [thetaFourZ4Term_eq_exp_mul, exp_int_mul_pi_I_of_even hx]
  ring

private lemma thetaThree_sub_thetaFour_eq_zero_of_even
    (τ : ℂ) {x : Z4} (hx : Even (z4Sum x)) :
    thetaThreeZ4Term τ x - thetaFourZ4Term τ x = 0 := by
  rw [thetaFourZ4Term_eq_of_even τ hx]
  ring

private lemma thetaThree_sub_thetaFour_eq_two_mul_of_odd
    (τ : ℂ) {x : Z4} (hx : Odd (z4Sum x)) :
    thetaThreeZ4Term τ x - thetaFourZ4Term τ x = 2 * thetaThreeZ4Term τ x := by
  rw [thetaFourZ4Term_eq_exp_mul, exp_int_mul_pi_I_of_odd hx]
  ring

private lemma thetaTwoZ4Term_flip0 (τ : ℂ) (x : Z4) :
    thetaTwoZ4Term τ (flip0 x) = thetaTwoZ4Term τ x := by
  unfold thetaTwoZ4Term
  rw [halfNormSq_flip0]

private lemma thetaTwoZ4Term_spinorToVector (τ : ℂ) (m : Z4) (hm : Even (z4Sum m)) :
    thetaTwoZ4Term τ m = thetaThreeZ4Term τ (spinorToVector m) := by
  unfold thetaTwoZ4Term thetaThreeZ4Term
  rw [← spinorToVector_norm m hm]

private lemma thetaThree_sub_thetaFour_tsum_eq_two_odd {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' x : Z4, thetaThreeZ4Term τ x) - (∑' x : Z4, thetaFourZ4Term τ x) =
      2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1 := by
  let d : Z4 → ℂ := fun x => thetaThreeZ4Term τ x - thetaFourZ4Term τ x
  have h3s := thetaThreeZ4_summable hτ
  have h4s := thetaFourZ4_summable hτ
  have hds : Summable d := h3s.sub h4s
  rw [(h3s.tsum_sub h4s).symm]
  change (∑' x : Z4, d x) = 2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1
  rw [← z4ParityEquiv.symm.tsum_eq d]
  have hsum : Summable fun y : Z4Even ⊕ Z4Odd => d (z4ParityEquiv.symm y) :=
    hds.comp_injective z4ParityEquiv.symm.injective
  rw [Summable.tsum_sum
    (hsum.comp_injective Sum.inl_injective)
    (hsum.comp_injective Sum.inr_injective)]
  have heven : (∑' x : Z4Even, d (z4ParityEquiv.symm (Sum.inl x))) = 0 := by
    rw [← tsum_zero]
    apply tsum_congr
    intro x
    change d x.1 = 0
    exact thetaThree_sub_thetaFour_eq_zero_of_even τ x.2
  have hodd :
      (∑' x : Z4Odd, d (z4ParityEquiv.symm (Sum.inr x))) =
        2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1 := by
    calc
      (∑' x : Z4Odd, d (z4ParityEquiv.symm (Sum.inr x)))
          = ∑' x : Z4Odd, 2 * thetaThreeZ4Term τ x.1 := by
            apply tsum_congr
            intro x
            change d x.1 = 2 * thetaThreeZ4Term τ x.1
            exact thetaThree_sub_thetaFour_eq_two_mul_of_odd τ x.2
      _ = 2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1 := by
            rw [tsum_mul_left]
  rw [heven, hodd]
  ring

private lemma thetaTwo_tsum_eq_two_odd {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' m : Z4, thetaTwoZ4Term τ m) =
      2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1 := by
  let f : Z4 → ℂ := fun m => thetaTwoZ4Term τ m
  have hfs : Summable f := thetaTwoZ4_summable hτ
  rw [← z4ParityEquiv.symm.tsum_eq f]
  have hsum : Summable fun y : Z4Even ⊕ Z4Odd => f (z4ParityEquiv.symm y) :=
    hfs.comp_injective z4ParityEquiv.symm.injective
  rw [Summable.tsum_sum
    (hsum.comp_injective Sum.inl_injective)
    (hsum.comp_injective Sum.inr_injective)]
  have hflip :
      (∑' x : Z4Odd, f x.1) = (∑' x : Z4Even, f x.1) := by
    rw [← flip0EvenOddEquiv.tsum_eq (fun x : Z4Odd => f x.1)]
    apply tsum_congr
    intro x
    change f (flip0 x.1) = f x.1
    exact thetaTwoZ4Term_flip0 τ x.1
  have heven_to_odd :
      (∑' x : Z4Even, f x.1) =
        ∑' x : Z4Odd, thetaThreeZ4Term τ x.1 := by
    rw [← spinorVectorEquiv.tsum_eq (fun x : Z4Odd => thetaThreeZ4Term τ x.1)]
    apply tsum_congr
    intro x
    change f x.1 = thetaThreeZ4Term τ (spinorToVector x.1)
    exact thetaTwoZ4Term_spinorToVector τ x.1 x.2
  change
      (∑' x : Z4Even, f x.1) + (∑' x : Z4Odd, f x.1) =
        2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1
  rw [hflip, heven_to_odd]
  ring

/-- Jacobi's quartic theta-constant identity.

This is the classical D4 theta identity
`θ₃(τ)^4 = θ₂(τ)^4 + θ₄(τ)^4`.  The intended in-file proof is the
Hadamard/triality lattice-theta argument described above: expand all fourth
powers as absolutely convergent theta sums over `ℤ^4`, split by the parity of
the coordinate sum, and use the normalized Hadamard isometries between the
vector and spinor cosets of the `D₄` lattice.
-/
theorem jacobi_theta_quartic_identity {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ ^ 4 = thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4 := by
  have hsub : jacobiTheta τ ^ 4 - thetaFourConst τ ^ 4 = thetaTwoConst τ ^ 4 := by
    calc
      jacobiTheta τ ^ 4 - thetaFourConst τ ^ 4
          = (∑' x : Z4, thetaThreeZ4Term τ x) -
              (∑' x : Z4, thetaFourZ4Term τ x) := by
                rw [jacobiTheta_pow_four_eq_tsum_z4 hτ,
                  thetaFourConst_pow_four_eq_tsum_z4 hτ]
      _ = 2 * ∑' x : Z4Odd, thetaThreeZ4Term τ x.1 :=
            thetaThree_sub_thetaFour_tsum_eq_two_odd hτ
      _ = ∑' x : Z4, thetaTwoZ4Term τ x :=
            (thetaTwo_tsum_eq_two_odd hτ).symm
      _ = thetaTwoConst τ ^ 4 :=
            (thetaTwoConst_pow_four_eq_tsum_z4 hτ).symm
  calc
    jacobiTheta τ ^ 4 = (jacobiTheta τ ^ 4 - thetaFourConst τ ^ 4) +
        thetaFourConst τ ^ 4 := by ring
    _ = thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4 := by rw [hsub]

theorem jacobiQuarticDefect_eq_zero (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiQuarticDefect τ = 0 := by
  rw [jacobiQuarticDefect_eq_zero_iff]
  exact jacobi_theta_quartic_identity hτ

end Modular
end Number
end Ripple

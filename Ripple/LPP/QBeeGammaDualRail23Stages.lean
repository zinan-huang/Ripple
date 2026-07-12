/-
  Homogeneous quadratic CRN and generic balancing-dilation stage for
  the CRN-safe 23→33 gamma QBee certificate.
-/

import Ripple.LPP.QBeeGammaDualRail23CRN

set_option linter.style.longLine false

namespace Ripple.LPP.QBee.Generated.GammaDualRail23

open Ripple

@[simp] private theorem sum_pair_indicator {n : ℕ} (i j : Fin n)
    (f : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, if a = i ∧ b = j then f a b else 0) = f i j := by
  classical
  calc
    (∑ a, ∑ b, if a = i ∧ b = j then f a b else 0) =
        ∑ a, if a = i then f a j else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hai : a = i
      · subst a
        simp
      · simp [hai]
    _ = f i j := by simp

@[simp] private theorem sum_cast_single_indicator {n : ℕ} (i : Fin n)
    (c : ℚ) (y : Fin n → ℝ) :
    (∑ a, ((if a = i then c else 0 : ℚ) : ℝ) * y a) = (c : ℝ) * y i := by
  classical
  calc
    (∑ a, ((if a = i then c else 0 : ℚ) : ℝ) * y a) =
        ∑ a, if a = i then (c : ℝ) * y a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a = i <;> simp [h]
    _ = (c : ℝ) * y i := by simp

@[simp] private theorem sum_cast_pair_indicator {n : ℕ} (i j : Fin n)
    (c : ℚ) (y : Fin n → ℝ) :
    (∑ a, ∑ b,
      ((if a = i then if b = j then c else 0 else 0 : ℚ) : ℝ) * y a * y b) =
      (c : ℝ) * y i * y j := by
  classical
  calc
    (∑ a, ∑ b,
      ((if a = i then if b = j then c else 0 else 0 : ℚ) : ℝ) * y a * y b) =
        ∑ a, ∑ b, if a = i ∧ b = j then (c : ℝ) * y a * y b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]
    _ = (c : ℝ) * y i * y j := sum_pair_indicator i j
      (fun a b => (c : ℝ) * y a * y b)

@[simp] private theorem vecSnoc_of_val_lt {n : ℕ} {f : Fin n → ℝ} {a : ℝ}
    (i : Fin (n + 1)) (h : i.val < n) :
    vecSnoc f a i = f ⟨i.val, h⟩ := by
  calc
    vecSnoc f a i = vecSnoc f a (Fin.castSucc ⟨i.val, h⟩) := by
      congr 1
    _ = f ⟨i.val, h⟩ := vecSnoc_castSucc

@[simp] private theorem vecSnoc_of_val_eq {n : ℕ} {f : Fin n → ℝ} {a : ℝ}
    (i : Fin (n + 1)) (h : i.val = n) :
    vecSnoc f a i = a := by
  rw [show i = Fin.last n by apply Fin.ext; simpa using h]
  exact vecSnoc_last

noncomputable def homoField (y : Fin 34 → ℝ) : Fin 34 → ℝ :=
  ![(((-68) * y 0 * y 1) + (y 4 * y 33)), (((-68) * y 0 * y 1) + (y 5 * y 33)), (((-68) * y 2 * y 3) + (y 8 * y 14) + (y 8 * y 23) + (y 8 * y 26) + (y 14 * y 33) + (y 9 * y 15) + (y 9 * y 24) + (y 9 * y 25) + (y 23 * y 33) + (y 26 * y 33)), (((-68) * y 2 * y 3) + (y 8 * y 15) + (y 8 * y 24) + (y 8 * y 25) + (y 14 * y 9) + (y 9 * y 23) + (y 9 * y 26) + (y 15 * y 33) + (y 24 * y 33) + (y 25 * y 33)), (((-68) * y 4 * y 5) + (y 6 * y 33) + (y 8 * y 33) + (y 5 * y 33) + (y 33 ^ 2)), (((-68) * y 4 * y 5) + (y 4 * y 33) + (y 7 * y 33) + (y 9 * y 33)), (((-68) * y 6 * y 7) + (y 8 * y 10) + (y 8 * y 33) + (y 10 * y 33) + (y 7 * y 33) + (y 9 * y 11) + (y 33 ^ 2)), (((-68) * y 6 * y 7) + (y 6 * y 33) + (y 8 * y 11) + (y 10 * y 9) + (y 9 * y 33) + (y 11 * y 33)), (((-68) * y 8 * y 9) + (y 9 * y 33)), (((-68) * y 8 * y 9) + (y 8 * y 33) + (y 33 ^ 2)), (((-66) * y 10 * y 11) + (2 * y 11 * y 33)), ((y 10 ^ 2) + ((-68) * y 10 * y 11) + (2 * y 10 * y 33) + (y 11 ^ 2) + (y 33 ^ 2)), ((y 8 * y 12) + (y 8 * y 33) + ((-68) * y 12 * y 13) + (y 12 * y 33) + (y 9 * y 13) + (y 33 ^ 2)), ((y 8 * y 13) + (y 12 * y 9) + ((-68) * y 12 * y 13) + (y 9 * y 33) + (y 13 * y 33)), ((y 8 * y 33) + ((-68) * y 14 * y 15) + (y 15 * y 33) + (y 33 ^ 2)), (((-68) * y 14 * y 15) + (y 14 * y 33) + (y 9 * y 33)), (((-68) * y 16 * y 17) + (y 16 * y 19) + (y 17 * y 33) + (y 33 ^ 2)), (((-68) * y 16 * y 17) + (y 16 * y 33) + (y 17 * y 19) + (y 19 * y 33)), (-(y 18 * y 22) + (y 33 ^ 2)), (-(y 19 * y 33) + (y 33 ^ 2)), ((y 16 * y 20) + -(y 17 * y 20) + -(y 20 * y 33) + (y 33 ^ 2)), (-(y 20 * y 21) + (y 33 ^ 2)), ((y 27 * y 22) + -(y 30 * y 22) + -(y 31 * y 22) + (y 32 * y 22) + -(y 22 * y 33) + (y 33 ^ 2)), ((y 8 * y 23) + ((-68) * y 12 * y 23) + ((-68) * y 14 * y 23) + (y 9 * y 13) + (y 9 * y 15) + (y 9 * y 25) + (y 23 * y 33) + (y 24 * y 33)), ((y 8 * y 13) + (y 8 * y 24) + ((-68) * y 12 * y 24) + (y 14 * y 9) + (y 9 * y 26) + (y 13 * y 33) + ((-68) * y 15 * y 24) + (y 23 * y 33) + (y 24 * y 33)), ((y 8 * y 15) + (y 8 * y 25) + (y 12 * y 9) + ((-68) * y 14 * y 25) + (y 9 * y 23) + ((-68) * y 13 * y 25) + (y 15 * y 33) + (y 25 * y 33) + (y 26 * y 33)), ((y 8 * y 12) + (y 8 * y 14) + (y 8 * y 26) + (y 12 * y 33) + (y 14 * y 33) + (y 9 * y 24) + ((-68) * y 13 * y 26) + ((-68) * y 15 * y 26) + (y 25 * y 33) + (y 26 * y 33)), (((-68) * y 2 * y 27) + (y 14 * y 28) + (y 3 * y 33) + (y 15 * y 29) + (y 15 * y 21) + (y 23 * y 28) + (y 24 * y 29) + (y 24 * y 21) + (y 25 * y 29) + (y 25 * y 21) + (y 26 * y 28) + -(y 27 * y 20)), (((-68) * y 8 * y 28) + (y 9 * y 33) + -(y 28 * y 20) + (y 29 * y 33) + (y 21 * y 33)), ((y 8 * y 33) + ((-68) * y 9 * y 29) + (y 28 * y 33) + -(y 29 * y 20)), ((y 2 * y 33) + (y 14 * y 29) + (y 14 * y 21) + ((-68) * y 3 * y 30) + (y 15 * y 28) + (y 23 * y 29) + (y 23 * y 21) + (y 24 * y 28) + (y 25 * y 28) + (y 26 * y 29) + (y 26 * y 21) + -(y 30 * y 20)), (((-68) * y 0 * y 31) + (y 1 * y 33) + (y 5 * y 21) + -(y 31 * y 20)), ((y 0 * y 33) + (y 4 * y 21) + ((-68) * y 1 * y 32) + -(y 32 * y 20)), 0]

noncomputable def homoAQ (i a b : Fin 34) : ℚ :=
  (![fun a b => (if a = 4 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 5 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 14 then 1 else 0 else 0) + (if a = 8 then if b = 23 then 1 else 0 else 0) + (if a = 8 then if b = 26 then 1 else 0 else 0) + (if a = 9 then if b = 15 then 1 else 0 else 0) + (if a = 9 then if b = 24 then 1 else 0 else 0) + (if a = 9 then if b = 25 then 1 else 0 else 0) + (if a = 14 then if b = 33 then 1 else 0 else 0) + (if a = 23 then if b = 33 then 1 else 0 else 0) + (if a = 26 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 15 then 1 else 0 else 0) + (if a = 8 then if b = 24 then 1 else 0 else 0) + (if a = 8 then if b = 25 then 1 else 0 else 0) + (if a = 9 then if b = 14 then 1 else 0 else 0) + (if a = 9 then if b = 23 then 1 else 0 else 0) + (if a = 9 then if b = 26 then 1 else 0 else 0) + (if a = 15 then if b = 33 then 1 else 0 else 0) + (if a = 24 then if b = 33 then 1 else 0 else 0) + (if a = 25 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 5 then if b = 33 then 1 else 0 else 0) + (if a = 6 then if b = 33 then 1 else 0 else 0) + (if a = 8 then if b = 33 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 4 then if b = 33 then 1 else 0 else 0) + (if a = 7 then if b = 33 then 1 else 0 else 0) + (if a = 9 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 7 then if b = 33 then 1 else 0 else 0) + (if a = 8 then if b = 10 then 1 else 0 else 0) + (if a = 8 then if b = 33 then 1 else 0 else 0) + (if a = 9 then if b = 11 then 1 else 0 else 0) + (if a = 10 then if b = 33 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 6 then if b = 33 then 1 else 0 else 0) + (if a = 8 then if b = 11 then 1 else 0 else 0) + (if a = 9 then if b = 10 then 1 else 0 else 0) + (if a = 9 then if b = 33 then 1 else 0 else 0) + (if a = 11 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 9 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 33 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 11 then if b = 33 then 2 else 0 else 0), fun a b => (if a = 10 then if b = 10 then 1 else 0 else 0) + (if a = 10 then if b = 33 then 2 else 0 else 0) + (if a = 11 then if b = 11 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 12 then 1 else 0 else 0) + (if a = 8 then if b = 33 then 1 else 0 else 0) + (if a = 9 then if b = 13 then 1 else 0 else 0) + (if a = 12 then if b = 33 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 13 then 1 else 0 else 0) + (if a = 9 then if b = 12 then 1 else 0 else 0) + (if a = 9 then if b = 33 then 1 else 0 else 0) + (if a = 13 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 33 then 1 else 0 else 0) + (if a = 15 then if b = 33 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 9 then if b = 33 then 1 else 0 else 0) + (if a = 14 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 16 then if b = 19 then 1 else 0 else 0) + (if a = 17 then if b = 33 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 16 then if b = 33 then 1 else 0 else 0) + (if a = 17 then if b = 19 then 1 else 0 else 0) + (if a = 19 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 16 then if b = 20 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 22 then if b = 27 then 1 else 0 else 0) + (if a = 22 then if b = 32 then 1 else 0 else 0) + (if a = 33 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 23 then 1 else 0 else 0) + (if a = 9 then if b = 13 then 1 else 0 else 0) + (if a = 9 then if b = 15 then 1 else 0 else 0) + (if a = 9 then if b = 25 then 1 else 0 else 0) + (if a = 23 then if b = 33 then 1 else 0 else 0) + (if a = 24 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 13 then 1 else 0 else 0) + (if a = 8 then if b = 24 then 1 else 0 else 0) + (if a = 9 then if b = 14 then 1 else 0 else 0) + (if a = 9 then if b = 26 then 1 else 0 else 0) + (if a = 13 then if b = 33 then 1 else 0 else 0) + (if a = 23 then if b = 33 then 1 else 0 else 0) + (if a = 24 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 15 then 1 else 0 else 0) + (if a = 8 then if b = 25 then 1 else 0 else 0) + (if a = 9 then if b = 12 then 1 else 0 else 0) + (if a = 9 then if b = 23 then 1 else 0 else 0) + (if a = 15 then if b = 33 then 1 else 0 else 0) + (if a = 25 then if b = 33 then 1 else 0 else 0) + (if a = 26 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 12 then 1 else 0 else 0) + (if a = 8 then if b = 14 then 1 else 0 else 0) + (if a = 8 then if b = 26 then 1 else 0 else 0) + (if a = 9 then if b = 24 then 1 else 0 else 0) + (if a = 12 then if b = 33 then 1 else 0 else 0) + (if a = 14 then if b = 33 then 1 else 0 else 0) + (if a = 25 then if b = 33 then 1 else 0 else 0) + (if a = 26 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 3 then if b = 33 then 1 else 0 else 0) + (if a = 14 then if b = 28 then 1 else 0 else 0) + (if a = 15 then if b = 21 then 1 else 0 else 0) + (if a = 15 then if b = 29 then 1 else 0 else 0) + (if a = 21 then if b = 24 then 1 else 0 else 0) + (if a = 21 then if b = 25 then 1 else 0 else 0) + (if a = 23 then if b = 28 then 1 else 0 else 0) + (if a = 24 then if b = 29 then 1 else 0 else 0) + (if a = 25 then if b = 29 then 1 else 0 else 0) + (if a = 26 then if b = 28 then 1 else 0 else 0), fun a b => (if a = 9 then if b = 33 then 1 else 0 else 0) + (if a = 21 then if b = 33 then 1 else 0 else 0) + (if a = 29 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 8 then if b = 33 then 1 else 0 else 0) + (if a = 28 then if b = 33 then 1 else 0 else 0), fun a b => (if a = 2 then if b = 33 then 1 else 0 else 0) + (if a = 14 then if b = 21 then 1 else 0 else 0) + (if a = 14 then if b = 29 then 1 else 0 else 0) + (if a = 15 then if b = 28 then 1 else 0 else 0) + (if a = 21 then if b = 23 then 1 else 0 else 0) + (if a = 21 then if b = 26 then 1 else 0 else 0) + (if a = 23 then if b = 29 then 1 else 0 else 0) + (if a = 24 then if b = 28 then 1 else 0 else 0) + (if a = 25 then if b = 28 then 1 else 0 else 0) + (if a = 26 then if b = 29 then 1 else 0 else 0), fun a b => (if a = 1 then if b = 33 then 1 else 0 else 0) + (if a = 5 then if b = 21 then 1 else 0 else 0), fun a b => (if a = 0 then if b = 33 then 1 else 0 else 0) + (if a = 4 then if b = 21 then 1 else 0 else 0), fun a b => 0]) i a b

noncomputable def homoBQ (i a : Fin 34) : ℚ :=
  (![fun a => (if a = 1 then 68 else 0), fun a => (if a = 0 then 68 else 0), fun a => (if a = 3 then 68 else 0), fun a => (if a = 2 then 68 else 0), fun a => (if a = 5 then 68 else 0), fun a => (if a = 4 then 68 else 0), fun a => (if a = 7 then 68 else 0), fun a => (if a = 6 then 68 else 0), fun a => (if a = 9 then 68 else 0), fun a => (if a = 8 then 68 else 0), fun a => (if a = 11 then 66 else 0), fun a => (if a = 10 then 68 else 0), fun a => (if a = 13 then 68 else 0), fun a => (if a = 12 then 68 else 0), fun a => (if a = 15 then 68 else 0), fun a => (if a = 14 then 68 else 0), fun a => (if a = 17 then 68 else 0), fun a => (if a = 16 then 68 else 0), fun a => (if a = 22 then 1 else 0), fun a => (if a = 33 then 1 else 0), fun a => (if a = 17 then 1 else 0) + (if a = 33 then 1 else 0), fun a => (if a = 20 then 1 else 0), fun a => (if a = 30 then 1 else 0) + (if a = 31 then 1 else 0) + (if a = 33 then 1 else 0), fun a => (if a = 12 then 68 else 0) + (if a = 14 then 68 else 0), fun a => (if a = 12 then 68 else 0) + (if a = 15 then 68 else 0), fun a => (if a = 13 then 68 else 0) + (if a = 14 then 68 else 0), fun a => (if a = 13 then 68 else 0) + (if a = 15 then 68 else 0), fun a => (if a = 2 then 68 else 0) + (if a = 20 then 1 else 0), fun a => (if a = 8 then 68 else 0) + (if a = 20 then 1 else 0), fun a => (if a = 9 then 68 else 0) + (if a = 20 then 1 else 0), fun a => (if a = 3 then 68 else 0) + (if a = 20 then 1 else 0), fun a => (if a = 0 then 68 else 0) + (if a = 20 then 1 else 0), fun a => (if a = 1 then 68 else 0) + (if a = 20 then 1 else 0), fun a => 0]) i a

noncomputable def homoA (i a b : Fin 34) : ℝ := homoAQ i a b

noncomputable def homoB (i a : Fin 34) : ℝ := homoBQ i a

theorem homoAQ_nonneg (i a b : Fin 34) : 0 ≤ homoAQ i a b := by
  fin_cases i <;> simp [homoAQ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] <;> positivity

theorem homoBQ_nonneg (i a : Fin 34) : 0 ≤ homoBQ i a := by
  fin_cases i <;> simp [homoBQ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] <;> positivity

/-- The concrete QBee CRN has no negative self-square monomial. This is the
structural fact that makes every active symmetric-lift input pair distinct. -/
theorem homoBQ_self_zero (i : Fin 34) : homoBQ i i = 0 := by
  fin_cases i <;> simp [homoBQ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

set_option maxHeartbeats 2400000 in
-- Generated finite coefficient normalization.
theorem homoField_form (i : Fin 34) (y : Fin 34 → ℝ) :
    homoField y i = (∑ a, ∑ b, homoA i a b * y a * y b) -
      (∑ a, homoB i a * y a) * y i := by
  fin_cases i <;>
    simp [homoField, homoA, homoAQ, homoB, homoBQ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, add_mul, Finset.sum_add_distrib] <;>
    ring

/-- Adjoin the dummy constant species used to homogenize constant and linear
terms before balancing dilation. -/
noncomputable def homoEmbed (y : Fin 33 → ℝ) : Fin 34 → ℝ :=
  vecSnoc y 1

set_option maxHeartbeats 3200000 in
theorem homoField_on_homoEmbed (y : Fin 33 → ℝ) :
    homoField (homoEmbed y) = vecSnoc (crnQuadField y) 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change homoField (vecSnoc y 1) (Fin.last 33) = 0
    simp [homoField]
  · simp only [homoEmbed, vecSnoc_castSucc]
    fin_cases j <;> simp [homoField, crnQuadField,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

theorem homoField_solution_lift {y : ℝ → Fin 33 → ℝ}
    (hy : ∀ t : ℝ, 0 ≤ t → HasDerivAt y (crnQuadField (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => homoEmbed (y s)) (homoField (homoEmbed (y t))) t := by
  intro t ht
  rw [homoField_on_homoEmbed]
  refine hasDerivAt_pi.mpr (fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [homoEmbed] using (hasDerivAt_const t (1 : ℝ))
  · simpa [homoEmbed] using hasDerivAt_pi.mp (hy t ht) j

theorem homoA_nonneg (i a b : Fin 34) : 0 ≤ homoA i a b := by
  change 0 ≤ (homoAQ i a b : ℝ)
  exact_mod_cast homoAQ_nonneg i a b

theorem homoB_nonneg (i a : Fin 34) : 0 ≤ homoB i a := by
  change 0 ≤ (homoBQ i a : ℝ)
  exact_mod_cast homoBQ_nonneg i a

noncomputable def homoField_crn : IsCRNImplementable 34 homoField where
  prod := fun i y => ∑ a, ∑ b, homoA i a b * y a * y b
  degr := fun i y => ∑ a, homoB i a * y a
  prod_pos := fun i y hy => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (homoA_nonneg i a b) (hy a)) (hy b)
  degr_pos := fun i y hy => Finset.sum_nonneg fun a _ =>
    mul_nonneg (homoB_nonneg i a) (hy a)
  field_eq := fun y i => homoField_form i y

/-! ## Constant dilation, selective lambda scaling, and balancing dilation -/

/-- The journal scaling factor `1/242`. Coordinate 18 is the gamma output
and is the unique unscaled coordinate of the selective lambda trick. -/
def stage2Lambda : ℚ := 1 / 242

def stage2Coeff (j : Fin 34) : ℚ :=
  if j = 18 then 1 else stage2Lambda

/-- Rational quadratic coefficients after constant dilation and selective
lambda scaling. -/
noncomputable def stage2AQ (i a b : Fin 34) : ℚ :=
  stage2Coeff i * homoAQ i a b / (stage2Coeff a * stage2Coeff b)

noncomputable def stage2BQ (i a : Fin 34) : ℚ :=
  homoBQ i a / stage2Coeff a

noncomputable def stage2A (i a b : Fin 34) : ℝ :=
  (if i = 18 then 1 else (1 / 242 : ℝ)) * homoA i a b /
    ((if a = 18 then 1 else (1 / 242 : ℝ)) *
      (if b = 18 then 1 else (1 / 242 : ℝ)))

noncomputable def stage2B (i a : Fin 34) : ℝ :=
  homoB i a / (if a = 18 then 1 else (1 / 242 : ℝ))

theorem stage2AQ_nonneg (i a b : Fin 34) : 0 ≤ stage2AQ i a b := by
  apply div_nonneg
  · exact mul_nonneg (by simp [stage2Coeff, stage2Lambda]; positivity)
      (homoAQ_nonneg i a b)
  · exact mul_nonneg (by simp [stage2Coeff, stage2Lambda]; positivity)
      (by simp [stage2Coeff, stage2Lambda]; positivity)

theorem stage2BQ_nonneg (i a : Fin 34) : 0 ≤ stage2BQ i a := by
  exact div_nonneg (homoBQ_nonneg i a)
    (by simp [stage2Coeff, stage2Lambda]; positivity)

theorem stage2BQ_self_zero (i : Fin 34) : stage2BQ i i = 0 := by
  simp [stage2BQ, homoBQ_self_zero]

theorem stage2AQ_cast (i a b : Fin 34) :
    (stage2AQ i a b : ℝ) = stage2A i a b := by
  simp only [stage2AQ, stage2A, stage2Coeff, stage2Lambda, homoA]
  split_ifs <;> norm_num

theorem stage2BQ_cast (i a : Fin 34) :
    (stage2BQ i a : ℝ) = stage2B i a := by
  simp only [stage2BQ, stage2B, stage2Coeff, stage2Lambda, homoB]
  split_ifs <;> norm_num

theorem stage2A_nonneg (i a b : Fin 34) : 0 ≤ stage2A i a b := by
  rw [← stage2AQ_cast]
  exact (Rat.cast_nonneg (K := ℝ)).2 (stage2AQ_nonneg i a b)

theorem stage2B_nonneg (i a : Fin 34) : 0 ≤ stage2B i a := by
  rw [← stage2BQ_cast]
  exact (Rat.cast_nonneg (K := ℝ)).2 (stage2BQ_nonneg i a)

theorem stage2InnerField_real_form (i : Fin 34) (y : Fin 34 → ℝ) :
    selectiveLambdaTrick 18 (1 / 242 : ℝ) (constantDilation 1 homoField) y i =
      (∑ a, ∑ b, stage2A i a b * y a * y b) -
        (∑ a, stage2B i a * y a) * y i := by
  simpa [stage2A, stage2B] using
    (selectiveLambdaTrick_quadratic_form (o := (18 : Fin 34))
      (c := (1 / 242 : ℝ)) (ε := (1 : ℝ)) (by norm_num)
      homoA homoB homoField_form i y)

theorem stage2InnerField_form (i : Fin 34) (y : Fin 34 → ℝ) :
    selectiveLambdaTrick 18 (1 / 242 : ℝ) (constantDilation 1 homoField) y i =
      (∑ a, ∑ b, (stage2AQ i a b : ℝ) * y a * y b) -
        (∑ a, (stage2BQ i a : ℝ) * y a) * y i := by
  rw [stage2InnerField_real_form]
  simp_rw [stage2AQ_cast, stage2BQ_cast]

/-- The actual Stage-2 order: constant dilation, selective lambda scaling,
then balancing dilation. -/
noncomputable def balancedField : (Fin 35 → ℝ) → Fin 35 → ℝ :=
  stage2_field 18 1 (1 / 242) homoField

noncomputable def balancedField_crn : IsCRNImplementable 35 balancedField :=
  (stage2_field_tpp (o := (18 : Fin 34)) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 242) homoField_crn).toIsCRNImplementable

noncomputable def balancedCubicForm : Stage2CubicForm 35 balancedField :=
  stage2_field_cubicForm (o := (18 : Fin 34))
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 242)
    homoA homoB homoA_nonneg homoB_nonneg homoField_form

#print axioms homoField_form
#print axioms homoField_solution_lift
#print axioms homoField_crn
#print axioms stage2InnerField_form
#print axioms balancedCubicForm

end Ripple.LPP.QBee.Generated.GammaDualRail23

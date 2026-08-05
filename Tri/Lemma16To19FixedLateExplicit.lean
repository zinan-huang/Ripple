/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedLate

/-!
# Explicit late-stage activation parameters

One terminal radius is reused as the target gap and the safety parameter.
Four copies of it supply both the label radius and the incoming late reserve.
-/

namespace Tri

noncomputable section

/-- A terminal natural square bound pays the real label-scale condition for
the fourfold label radius. -/
theorem lemma16To19FixedLate_labelScale
    (n q R : ℕ)
    (hSq : q * n ≤ R ^ 2) :
    lemma16To19FixedErrorScale q * (n : ℝ) ≤
      (((4 * R : ℕ) : ℝ) / 2) ^ 2 := by
  have hNat :
      3 * q * n ≤ (2 * R) ^ 2 := by
    calc
      3 * q * n = 3 * (q * n) := by ring
      _ ≤ 3 * R ^ 2 :=
        Nat.mul_le_mul_left 3 hSq
      _ ≤ 4 * R ^ 2 := by omega
      _ = (2 * R) ^ 2 := by ring
  have hReal :
      (((3 * q * n : ℕ) : ℝ)) ≤
        (((2 * R : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast hNat
  unfold lemma16To19FixedErrorScale
  calc
    3 * (q : ℝ) * (n : ℝ) =
        ((3 * q * n : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (((2 * R : ℕ) : ℝ)) ^ 2 := hReal
    _ = (((4 * R : ℕ) : ℝ) / 2) ^ 2 := by
      push_cast
      ring

/-- The explicit ratio `target : Dlabel : Mlate : Dlate = 1 : 4 : 1 : 4`
reduces every late-stage premise to a terminal square and range bound. -/
theorem lemma16To19FixedLateFacts_explicit
    (n q R : ℕ)
    (hN : 0 < q * n)
    (hRlt : R < n)
    (hSq : q * n ≤ R ^ 2) :
    Lemma16To19FixedLateFacts
      n q (4 * R) (4 * R) R R := by
  have hR : 0 < R := by
    nlinarith
  exact
    lemma16To19FixedLateFacts
      n q (4 * R) (4 * R) R R
      (by omega)
      hR
      hRlt
      (by positivity)
      (lemma16To19FixedLate_labelScale n q R hSq)
      hSq
      (lemma3Quarter_le hR)

end

end Tri

#print axioms Tri.lemma16To19FixedLate_labelScale
#print axioms Tri.lemma16To19FixedLateFacts_explicit

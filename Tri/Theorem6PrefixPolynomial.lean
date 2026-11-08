/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6PrefixFit

/-!
# Polynomial endpoint conditions for the fixed prefix

The floor capacity used by the reaction lower is eliminated from the public
interface.  Each sufficient condition pays one full denominator, so the
rounding loss is retained exactly.
-/

namespace Tri

noncomputable section

/-- Two multiplication-only endpoint conditions imply every indexed reaction
fit in the fixed prefix. -/
theorem lemma17ReactionLower_fit_of_polynomial_endpoint
    (n q cStar a m : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hactive :
      285 * q + 76 * cStar ≤ a)
    (hmean :
      76 * cStar *
          ((2 * lemma17Scale a m) ^ 3 + n ^ 2) ≤
        a * n ^ 2) :
    ∀ j ≤ m,
      76 * cStar *
          lemma17ReactionLower n q cStar
            (lemma17Scale a j) ≤
        lemma17Scale a j := by
  let D := 76 * cStar
  let r := a ⌊/⌋ D
  let X := (2 * lemma17Scale a m) ^ 3
  let N := n ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hcapacity : D ≤ a := by
    dsimp [D]
    omega
  have haUpper : a < D * (r + 1) := by
    have hdiv : a / D < r + 1 := by
      simp [r, Nat.floorDiv_eq_div]
    have h := (Nat.div_lt_iff_lt_mul hD).1 hdiv
    simpa [mul_comm] using h
  have hmeanFit : X ≤ r * N := by
    have hupper :
        a * N < D * (r * N + N) := by
      calc
        a * N < (D * (r + 1)) * N :=
          Nat.mul_lt_mul_of_pos_right haUpper
            (Nat.pow_pos hn)
        _ = D * (r * N + N) := by ring
    have hmean' :
        D * (X + N) ≤ a * N := by
      simpa [D, X, N] using hmean
    have hstrict :
        D * (X + N) < D * (r * N + N) :=
      hmean'.trans_lt hupper
    have hcancel : X + N < r * N + N :=
      Nat.lt_of_mul_lt_mul_left hstrict
    omega
  have hactiveFit : 15 * q ≤ 4 * cStar * r := by
    have h285 : 285 * q < D * r := by
      have : 285 * q + D < D * r + D := by
        calc
          285 * q + D ≤ a := by
            simpa [D] using hactive
          _ < D * (r + 1) := haUpper
          _ = D * r + D := by ring
      omega
    have h19 :
        19 * (15 * q) <
          19 * (4 * cStar * r) := by
      calc
        19 * (15 * q) = 285 * q := by ring
        _ < D * r := h285
        _ = 19 * (4 * cStar * r) := by
          dsimp [D]
          ring
    exact (Nat.lt_of_mul_lt_mul_left h19).le
  apply
    lemma17ReactionLower_fit_of_endpoint
      n q cStar a m hn hcStar
  · simpa [D] using hcapacity
  · simpa [X, N, r] using hmeanFit
  · simpa [r] using hactiveFit

/-- For the paper value `cStar = 1024`, the fixed-square endpoint bracket
supplies the cubic room separately at every dyadic source scale.  This avoids
charging the last source's cubic mean to the initial source capacity. -/
theorem lemma17ReactionLower_fit_of_critical_bracket
    (n q a m : ℕ)
    (hn : 0 < n)
    (hqLarge : 8192 ≤ q)
    (hactive :
      285 * q + 76 * theorem6CStar ≤ a)
    (hbelow :
      theorem6CStarSq *
          lemma17Scale a m < n) :
    ∀ j ≤ m,
      76 * theorem6CStar *
          lemma17ReactionLower n q theorem6CStar
            (lemma17Scale a j) ≤
        lemma17Scale a j := by
  intro j hj
  let x := lemma17Scale a j
  have hxLast :
      x ≤ lemma17Scale a m := by
    exact lemma17Scale_mono a j m hj
  have hax : a ≤ x := by
    simpa [x, lemma17Scale_zero] using
      lemma17Scale_mono a 0 j (Nat.zero_le j)
  have hactiveLocal :
      285 * q + 76 * theorem6CStar ≤ x :=
    hactive.trans hax
  have htwoCapacity :
      2 * (76 * theorem6CStar) ≤ x := by
    have hqRoom :
        76 * theorem6CStar ≤ 285 * q := by
      norm_num [theorem6CStar] at ⊢
      omega
    omega
  have hfixedBelow :
      theorem6CStarSq * x < n := by
    exact
      (Nat.mul_le_mul_left theorem6CStarSq hxLast).trans_lt
        hbelow
  have hfixedSq :
      (theorem6CStarSq * x) ^ 2 ≤ n ^ 2 :=
    Nat.pow_le_pow_left hfixedBelow.le 2
  have hcoefficient :
      16 * (76 * theorem6CStar) ≤
        theorem6CStarSq ^ 2 := by
    norm_num [theorem6CStarSq, theorem6CStar]
  have hcubicDouble :
      2 *
          ((76 * theorem6CStar) * (2 * x) ^ 3) ≤
        x * n ^ 2 := by
    calc
      2 *
            ((76 * theorem6CStar) * (2 * x) ^ 3) =
          (16 * (76 * theorem6CStar)) * x ^ 3 := by
            ring
      _ ≤ theorem6CStarSq ^ 2 * x ^ 3 :=
        Nat.mul_le_mul_right (x ^ 3) hcoefficient
      _ = x * (theorem6CStarSq * x) ^ 2 := by
        ring
      _ ≤ x * n ^ 2 :=
        Nat.mul_le_mul_left x hfixedSq
  have hconstantDouble :
      2 * ((76 * theorem6CStar) * n ^ 2) ≤
        x * n ^ 2 := by
    calc
      2 * ((76 * theorem6CStar) * n ^ 2) =
          (2 * (76 * theorem6CStar)) * n ^ 2 := by
            ring
      _ ≤ x * n ^ 2 :=
        Nat.mul_le_mul_right (n ^ 2) htwoCapacity
  have hmeanLocal :
      76 * theorem6CStar *
          ((2 * x) ^ 3 + n ^ 2) ≤
        x * n ^ 2 := by
    have hdouble :
        2 *
            (76 * theorem6CStar *
              ((2 * x) ^ 3 + n ^ 2)) ≤
          2 * (x * n ^ 2) := by
      calc
        2 *
              (76 * theorem6CStar *
                ((2 * x) ^ 3 + n ^ 2)) =
            2 *
                ((76 * theorem6CStar) *
                  (2 * x) ^ 3) +
              2 *
                ((76 * theorem6CStar) *
                  n ^ 2) := by
                    ring
        _ ≤ x * n ^ 2 + x * n ^ 2 :=
          Nat.add_le_add hcubicDouble hconstantDouble
        _ = 2 * (x * n ^ 2) := by ring
    omega
  have hlocal :=
    lemma17ReactionLower_fit_of_polynomial_endpoint
      n q theorem6CStar x 0 hn
      (by norm_num [theorem6CStar])
      hactiveLocal
      (by
        simpa [lemma17Scale_zero] using hmeanLocal)
  simpa [x, lemma17Scale_zero] using
    hlocal 0 (Nat.zero_le 0)

end

end Tri

#print axioms
  Tri.lemma17ReactionLower_fit_of_polynomial_endpoint
#print axioms
  Tri.lemma17ReactionLower_fit_of_critical_bracket

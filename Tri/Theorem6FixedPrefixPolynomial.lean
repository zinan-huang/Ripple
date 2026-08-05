/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedPrefixFit

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
theorem lemma17FixedReactionLower_fit_of_polynomial_endpoint
    (n q cStar a m : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hactive :
      285 * q + 76 * cStar ≤ a)
    (hmean :
      76 * cStar *
          ((2 * lemma17FixedScale a m) ^ 3 + n ^ 2) ≤
        a * n ^ 2) :
    ∀ j ≤ m,
      76 * cStar *
          lemma17FixedReactionLower n q cStar
            (lemma17FixedScale a j) ≤
        lemma17FixedScale a j := by
  let D := 76 * cStar
  let r := a ⌊/⌋ D
  let X := (2 * lemma17FixedScale a m) ^ 3
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
    lemma17FixedReactionLower_fit_of_endpoint
      n q cStar a m hn hcStar
  · simpa [D] using hcapacity
  · simpa [X, N, r] using hmeanFit
  · simpa [r] using hactiveFit

/-- For the paper value `cStar = 1024`, the fixed-square endpoint bracket
supplies the cubic room separately at every dyadic source scale.  This avoids
charging the last source's cubic mean to the initial source capacity. -/
theorem lemma17FixedReactionLower_fit_of_fixed_bracket
    (n q a m : ℕ)
    (hn : 0 < n)
    (hqLarge : 8192 ≤ q)
    (hactive :
      285 * q + 76 * theorem6FixedCStar ≤ a)
    (hbelow :
      theorem6FixedCStarSq *
          lemma17FixedScale a m < n) :
    ∀ j ≤ m,
      76 * theorem6FixedCStar *
          lemma17FixedReactionLower n q theorem6FixedCStar
            (lemma17FixedScale a j) ≤
        lemma17FixedScale a j := by
  intro j hj
  let x := lemma17FixedScale a j
  have hxLast :
      x ≤ lemma17FixedScale a m := by
    exact lemma17FixedScale_mono a j m hj
  have hax : a ≤ x := by
    simpa [x, lemma17FixedScale_zero] using
      lemma17FixedScale_mono a 0 j (Nat.zero_le j)
  have hactiveLocal :
      285 * q + 76 * theorem6FixedCStar ≤ x :=
    hactive.trans hax
  have htwoCapacity :
      2 * (76 * theorem6FixedCStar) ≤ x := by
    have hqRoom :
        76 * theorem6FixedCStar ≤ 285 * q := by
      norm_num [theorem6FixedCStar] at ⊢
      omega
    omega
  have hfixedBelow :
      theorem6FixedCStarSq * x < n := by
    exact
      (Nat.mul_le_mul_left theorem6FixedCStarSq hxLast).trans_lt
        hbelow
  have hfixedSq :
      (theorem6FixedCStarSq * x) ^ 2 ≤ n ^ 2 :=
    Nat.pow_le_pow_left hfixedBelow.le 2
  have hcoefficient :
      16 * (76 * theorem6FixedCStar) ≤
        theorem6FixedCStarSq ^ 2 := by
    norm_num [theorem6FixedCStarSq, theorem6FixedCStar]
  have hcubicDouble :
      2 *
          ((76 * theorem6FixedCStar) * (2 * x) ^ 3) ≤
        x * n ^ 2 := by
    calc
      2 *
            ((76 * theorem6FixedCStar) * (2 * x) ^ 3) =
          (16 * (76 * theorem6FixedCStar)) * x ^ 3 := by
            ring
      _ ≤ theorem6FixedCStarSq ^ 2 * x ^ 3 :=
        Nat.mul_le_mul_right (x ^ 3) hcoefficient
      _ = x * (theorem6FixedCStarSq * x) ^ 2 := by
        ring
      _ ≤ x * n ^ 2 :=
        Nat.mul_le_mul_left x hfixedSq
  have hconstantDouble :
      2 * ((76 * theorem6FixedCStar) * n ^ 2) ≤
        x * n ^ 2 := by
    calc
      2 * ((76 * theorem6FixedCStar) * n ^ 2) =
          (2 * (76 * theorem6FixedCStar)) * n ^ 2 := by
            ring
      _ ≤ x * n ^ 2 :=
        Nat.mul_le_mul_right (n ^ 2) htwoCapacity
  have hmeanLocal :
      76 * theorem6FixedCStar *
          ((2 * x) ^ 3 + n ^ 2) ≤
        x * n ^ 2 := by
    have hdouble :
        2 *
            (76 * theorem6FixedCStar *
              ((2 * x) ^ 3 + n ^ 2)) ≤
          2 * (x * n ^ 2) := by
      calc
        2 *
              (76 * theorem6FixedCStar *
                ((2 * x) ^ 3 + n ^ 2)) =
            2 *
                ((76 * theorem6FixedCStar) *
                  (2 * x) ^ 3) +
              2 *
                ((76 * theorem6FixedCStar) *
                  n ^ 2) := by
                    ring
        _ ≤ x * n ^ 2 + x * n ^ 2 :=
          Nat.add_le_add hcubicDouble hconstantDouble
        _ = 2 * (x * n ^ 2) := by ring
    omega
  have hlocal :=
    lemma17FixedReactionLower_fit_of_polynomial_endpoint
      n q theorem6FixedCStar x 0 hn
      (by norm_num [theorem6FixedCStar])
      hactiveLocal
      (by
        simpa [lemma17FixedScale_zero] using hmeanLocal)
  simpa [x, lemma17FixedScale_zero] using
    hlocal 0 (Nat.zero_le 0)

end

end Tri

#print axioms
  Tri.lemma17FixedReactionLower_fit_of_polynomial_endpoint
#print axioms
  Tri.lemma17FixedReactionLower_fit_of_fixed_bracket

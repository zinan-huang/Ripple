/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedInitialBias
import Tri.Theorem6FixedTerminalRadius

/-!
# A square-root envelope for the fixed landing radius

The corrected Lemma 17 radii grow like the square root of the dyadic scale.
The last predecessor lies below the population, so the landing radius is a
constant multiple of the paper scale `sqrt (q * n) + 1`.
-/

namespace Tri

noncomputable section

/-- The fixed landing radius is at most eight times the global positive
upper square root. -/
theorem theorem6FixedLandingRho_le_sqrt
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n) :
    lemma17FixedLandingRho
        (theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ))
        (lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive) ≤
      8 * (Nat.sqrt (theorem6Q n γ * n) + 1) := by
  let q := theorem6Q n γ
  let a := theorem6InitialScale n γ
  let m := lemma17FixedStageCount n a S.hpositive
  let p := 2 ^ m
  let rho := theorem6InitialRadius q a
  let x := q * n
  let z := q * (a + 1)
  have hp : 1 ≤ p := by
    dsimp [p]
    exact one_le_pow₀ (by norm_num)
  have hbelow :
      theorem6FixedCStarSq * (p * a) < n := by
    have h :=
      lemma17FixedStageCount_below
        n a S.hpositive (by simpa [a] using S.hbelow)
    simpa [m, p, lemma17FixedScale] using h
  have hC : 1 ≤ theorem6FixedCStarSq := by
    norm_num [theorem6FixedCStarSq, theorem6FixedCStar]
  have hpa : p * a < n := by
    have hscaled :
        p * a ≤ theorem6FixedCStarSq * (p * a) := by
      simpa using Nat.mul_le_mul_right (p * a) hC
    exact hscaled.trans_lt hbelow
  have hp_le_pa : p ≤ p * a := by
    have ha : 1 ≤ a := by
      simpa [a] using S.hpositive
    simpa using Nat.mul_le_mul_left p ha
  have hpaSucc : p * (a + 1) ≤ 2 * n := by
    calc
      p * (a + 1) = p * a + p := by ring
      _ ≤ p * a + p * a :=
        Nat.add_le_add_left hp_le_pa (p * a)
      _ = 2 * (p * a) := by ring
      _ ≤ 2 * n :=
        Nat.mul_le_mul_left 2 hpa.le
  have hzPos : 0 < z := by
    have hq : 0 < q := by
      simpa [q, x] using Nat.pos_of_mul_pos_right hN
    dsimp [z]
    positivity
  have hrhoSq : rho ^ 2 ≤ 4 * z := by
    let r := Nat.sqrt z
    have hr : 1 ≤ r := by
      exact (Nat.sqrt_pos).2 hzPos
    have hrSq : r ^ 2 ≤ z := by
      simpa [r] using Nat.sqrt_le' z
    change (r + 1) ^ 2 ≤ 4 * z
    nlinarith
  have hscaledRho : p * rho ^ 2 ≤ 8 * x := by
    calc
      p * rho ^ 2 ≤ p * (4 * z) :=
        Nat.mul_le_mul_left p hrhoSq
      _ = 4 * q * (p * (a + 1)) := by
        simp [z]
        ring
      _ ≤ 4 * q * (2 * n) :=
        Nat.mul_le_mul_left (4 * q) hpaSucc
      _ = 8 * x := by
        simp [x]
        ring
  have hrhoFamily :
      lemma17FixedRho rho m ≤
        Nat.sqrt (p * rho ^ 2) + 1 := by
    by_cases hm : m = 0
    · rw [show lemma17FixedRho rho m = rho by
          simp [lemma17FixedRho, hm]]
      calc
        rho ≤ rho + 1 := by omega
        _ = Nat.sqrt (p * rho ^ 2) + 1 := by
          simp [p, hm]
    · simp [lemma17FixedRho, hm, p]
  have hsqrtScaled :
      Nat.sqrt (p * rho ^ 2) + 1 ≤
        Nat.sqrt (8 * x) + 1 := by
    exact Nat.add_le_add_right
      (Nat.sqrt_le_sqrt hscaledRho) 1
  have hsqrtEight :
      Nat.sqrt (8 * x) + 1 ≤
        4 * (Nat.sqrt x + 1) := by
    let g := Nat.sqrt x + 1
    have hxUpper : x < g ^ 2 := by
      simpa [g] using Nat.lt_succ_sqrt' x
    have hscaledUpper : 8 * x < (4 * g) ^ 2 := by
      calc
        8 * x < 8 * g ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hxUpper (by norm_num)
        _ ≤ 16 * g ^ 2 := by omega
        _ = (4 * g) ^ 2 := by ring
    have hsqrtLt :
        Nat.sqrt (8 * x) < 4 * g :=
      (Nat.sqrt_lt').2 hscaledUpper
    omega
  calc
    lemma17FixedLandingRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17FixedStageCount n
            (theorem6InitialScale n γ) S.hpositive) =
        2 * lemma17FixedRho rho m := by
      simp [lemma17FixedLandingRho, rho, m, a, q]
    _ ≤ 2 * (Nat.sqrt (p * rho ^ 2) + 1) :=
      Nat.mul_le_mul_left 2 hrhoFamily
    _ ≤ 2 * (Nat.sqrt (8 * x) + 1) :=
      Nat.mul_le_mul_left 2 hsqrtScaled
    _ ≤ 2 * (4 * (Nat.sqrt x + 1)) :=
      Nat.mul_le_mul_left 2 hsqrtEight
    _ = 8 * (Nat.sqrt (theorem6Q n γ * n) + 1) := by
      simp [x, q]
      ring

/-- Both branches of the canonical terminal radius fit below the same
square-root envelope. -/
theorem theorem6FixedTerminalRadius_le_sqrt
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n) :
    theorem6FixedTerminalRadius n γ S.hpositive ≤
      8 * (Nat.sqrt (theorem6Q n γ * n) + 1) := by
  unfold theorem6FixedTerminalRadius
    theorem6CanonicalTerminalRadius
  apply max_le
  · exact theorem6FixedLandingRho_le_sqrt
      S hN
  · have hpos :
        1 ≤ Nat.sqrt (theorem6Q n γ * n) + 1 := by
      omega
    nlinarith

end

end Tri

#print axioms
  Tri.theorem6FixedLandingRho_le_sqrt
#print axioms
  Tri.theorem6FixedTerminalRadius_le_sqrt

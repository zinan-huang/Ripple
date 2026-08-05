/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedGuard
import Tri.Theorem6FixedInitialBias

/-!
# Dominance among the fixed Theorem 6 size conditions

The population bound used for the decisive guard has a much larger
fifth-root cubic coefficient than the earlier fixed-route requirements.  It
therefore also pays the large-window threshold, the initial bias room, and
the active part of the prefix reaction fit.
-/

namespace Tri

noncomputable section

/-- The common logarithmic parameter is at most the square of its binary
fifth-root denominator. -/
theorem theorem6Q_le_fifthRoot_sq
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n) :
    theorem6Q n γ ≤ theorem6FifthRoot n γ ^ 2 := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let a := theorem6InitialScale n γ
  have hd : 0 < d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    positivity
  have hrootLower : q * n < d ^ 5 := by
    simpa [q, d] using
      (theorem6FifthRoot_bounds n γ hN).1
  have hfloor :
      (n ⌊/⌋ d) * d ≤ n := by
    have h :=
      (le_floorDiv_iff_mul_le hd).1
        (le_rfl : n ⌊/⌋ d ≤ n ⌊/⌋ d)
    simpa [mul_comm] using h
  have hqd : q * d ≤ n := by
    calc
      q * d ≤ a * d :=
        Nat.mul_le_mul_right d (by
          simpa [q, a] using S.hq)
      _ ≤ n := by
        unfold a theorem6InitialScale
        exact hfloor
  have hqSqMul : q ^ 2 * d < d ^ 5 := by
    calc
      q ^ 2 * d = q * (q * d) := by ring
      _ ≤ q * n := Nat.mul_le_mul_left q hqd
      _ < d ^ 5 := hrootLower
  by_contra hnot
  have hdq : d ^ 2 < q := Nat.lt_of_not_ge hnot
  have hpow : d ^ 4 < q ^ 2 := by
    nlinarith
  have : d ^ 5 ≤ q ^ 2 * d := by
    calc
      d ^ 5 = d ^ 4 * d := by ring
      _ ≤ q ^ 2 * d :=
        Nat.mul_le_mul_right d hpow.le
  omega

/-- The decisive cube guard alone places the common logarithmic parameter
below the square of the fifth-root denominator. -/
theorem theorem6Q_le_fifthRoot_sq_of_cube_size
    {n γ : ℕ}
    (hN : 0 < theorem6Q n γ * n)
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    theorem6Q n γ ≤ theorem6FifthRoot n γ ^ 2 := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let K := theorem6FixedCStarSq * 4_179_180
  have hd : 0 < d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    positivity
  have hroot : q * n < d ^ 5 := by
    simpa [q, d] using
      (theorem6FifthRoot_bounds n γ hN).1
  have hKd : K * d ^ 3 ≤ n := by
    calc
      K * d ^ 3 =
          theorem6FixedCStarSq *
            (4_179_180 * d ^ 3) := by
        simp [K]
        ring
      _ ≤ theorem6FixedCStarSq *
            (4_179_180 * d ^ 3 + 1_020) :=
        Nat.mul_le_mul_left _
          (Nat.le_add_right _ _)
      _ ≤ n := by
        simpa [d] using hcube
  have hcancel :
      (q * K) * d ^ 3 <
        d ^ 2 * d ^ 3 := by
    calc
      (q * K) * d ^ 3 =
          q * (K * d ^ 3) := by ring
      _ ≤ q * n := Nat.mul_le_mul_left q hKd
      _ < d ^ 5 := hroot
      _ = d ^ 2 * d ^ 3 := by ring
  have hqK : q * K < d ^ 2 := by
    nlinarith [hcancel, pow_pos hd 3]
  have hK : 1 ≤ K := by
    norm_num [K, theorem6FixedCStarSq,
      theorem6FixedCStar]
  calc
    q = q * 1 := by simp
    _ ≤ q * K := Nat.mul_le_mul_left q hK
    _ ≤ d ^ 2 := hqK.le

/-- The decisive cube guard implies the fourth-power seed separation. -/
theorem theorem6FixedSeed_of_cube_size
    {n γ : ℕ}
    (hN : 0 < theorem6Q n γ * n)
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    32 * theorem6Q n γ ^ 6 ≤ n ^ 4 := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let K := theorem6FixedCStarSq * 4_179_180
  have hqd : q ≤ d ^ 2 := by
    simpa [q, d] using
      theorem6Q_le_fifthRoot_sq_of_cube_size
        hN hcube
  have hKd : K * d ^ 3 ≤ n := by
    calc
      K * d ^ 3 =
          theorem6FixedCStarSq *
            (4_179_180 * d ^ 3) := by
        simp [K]
        ring
      _ ≤ theorem6FixedCStarSq *
            (4_179_180 * d ^ 3 + 1_020) :=
        Nat.mul_le_mul_left _
          (Nat.le_add_right _ _)
      _ ≤ n := by
        simpa [d] using hcube
  have hqPow :
      q ^ 6 ≤ d ^ 12 := by
    calc
      q ^ 6 ≤ (d ^ 2) ^ 6 :=
        Nat.pow_le_pow_left hqd 6
      _ = d ^ 12 := by ring
  have hK32 : 32 ≤ K ^ 4 := by
    norm_num [K, theorem6FixedCStarSq,
      theorem6FixedCStar]
  have hpopulation :
      (K * d ^ 3) ^ 4 ≤ n ^ 4 :=
    Nat.pow_le_pow_left hKd 4
  calc
    32 * theorem6Q n γ ^ 6 =
        32 * q ^ 6 := by simp [q]
    _ ≤ 32 * d ^ 12 :=
      Nat.mul_le_mul_left 32 hqPow
    _ ≤ K ^ 4 * d ^ 12 :=
      Nat.mul_le_mul_right (d ^ 12) hK32
    _ = (K * d ^ 3) ^ 4 := by ring
    _ ≤ n ^ 4 := hpopulation

/-- The decisive cube guard and the fixed lower bound on `q` place the
fifth-root denominator strictly above twice the critical multiplier, which
implies the critical-scale separation. -/
theorem theorem6FixedCriticalSeparation_of_cube_size
    {n γ : ℕ}
    (hN : 0 < theorem6Q n γ * n)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    theorem6FixedCStarSq ^ 5 <
      theorem6Q n γ * n := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let C := theorem6FixedCStarSq
  let K := C * 4_179_180
  have hqK : q * K < d ^ 2 := by
    have hd : 0 < d := by
      unfold d theorem6FifthRoot binaryFifthRoot
      positivity
    have hroot : q * n < d ^ 5 := by
      simpa [q, d] using
        (theorem6FifthRoot_bounds n γ hN).1
    have hKd : K * d ^ 3 ≤ n := by
      calc
        K * d ^ 3 =
            theorem6FixedCStarSq *
              (4_179_180 * d ^ 3) := by
          simp [K, C]
          ring
        _ ≤ theorem6FixedCStarSq *
              (4_179_180 * d ^ 3 + 1_020) :=
          Nat.mul_le_mul_left _
            (Nat.le_add_right _ _)
        _ ≤ n := by
          simpa [d] using hcube
    have hcancel :
        (q * K) * d ^ 3 <
          d ^ 2 * d ^ 3 := by
      calc
        (q * K) * d ^ 3 =
            q * (K * d ^ 3) := by ring
        _ ≤ q * n := Nat.mul_le_mul_left q hKd
        _ < d ^ 5 := hroot
        _ = d ^ 2 * d ^ 3 := by ring
    nlinarith [hcancel, pow_pos hd 3]
  have hconstant :
      (2 * C) ^ 2 ≤ 8192 * K := by
    norm_num [C, K, theorem6FixedCStarSq,
      theorem6FixedCStar]
  have hconstantQ :
      (2 * C) ^ 2 ≤ q * K := by
    exact hconstant.trans
      (Nat.mul_le_mul_right K (by
        simpa [q] using hqLarge))
  have hCd : 2 * C < d := by
    nlinarith [hconstantQ, hqK]
  have hpow :
      (2 * C) ^ 5 < d ^ 5 :=
    Nat.pow_lt_pow_left hCd (by norm_num)
  have hrootUpper :
      d ^ 5 ≤ 32 * (q * n) := by
    simpa [q, d] using
      (theorem6FifthRoot_bounds n γ hN).2
  have hscaled :
      32 * C ^ 5 < 32 * (q * n) := by
    calc
      32 * C ^ 5 = (2 * C) ^ 5 := by ring
      _ < d ^ 5 := hpow
      _ ≤ 32 * (q * n) := hrootUpper
  have hfinal : C ^ 5 < q * n := by
    omega
  simpa [C, q] using hfinal

/-- The decisive cube guard implies the fixed large-window threshold. -/
theorem theorem6FixedLarge_of_cube_size
    {n γ : ℕ}
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    theorem6FixedCStarSq *
        (theorem6FixedCStarSq + 6) ≤
      n := by
  apply hcube.trans'
  apply Nat.mul_le_mul_left
  have hd :
      1 ≤ theorem6FifthRoot n γ ^ 3 := by
    apply one_le_pow₀
    unfold theorem6FifthRoot binaryFifthRoot
    exact one_le_pow₀ (by norm_num)
  norm_num [theorem6FixedCStarSq,
    theorem6FixedCStar] at ⊢
  nlinarith

/-- The decisive cube guard also pays the initial-radius bias condition. -/
theorem theorem6FixedInitialBiasSize_of_cube_size
    {n γ : ℕ}
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    38 * theorem6FixedCStar *
        theorem6FifthRoot n γ *
          (theorem6FifthRoot n γ ^ 2 + 2) ≤
      n := by
  let d := theorem6FifthRoot n γ
  have hd : 1 ≤ d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    exact one_le_pow₀ (by norm_num)
  have hdCube : d ≤ d ^ 3 := by
    calc
      d = d * 1 := by simp
      _ ≤ d * d ^ 2 :=
        Nat.mul_le_mul_left d (one_le_pow₀ hd)
      _ = d ^ 3 := by ring
  apply hcube.trans'
  norm_num [theorem6FixedCStarSq,
    theorem6FixedCStar]
  nlinarith

/-- The decisive cube guard pays the active part of the prefix reaction fit
after exact floor-division rounding. -/
theorem theorem6FixedPrefixActive_of_cube_size
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n)
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    285 * theorem6Q n γ +
        76 * theorem6FixedCStar ≤
      theorem6InitialScale n γ := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  have hd : 0 < d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    positivity
  have hd1 : 1 ≤ d := hd
  have hqd : q ≤ d ^ 2 := by
    simpa [q, d] using
      theorem6Q_le_fifthRoot_sq S hN
  unfold theorem6InitialScale
  apply (le_floorDiv_iff_mul_le hd).2
  have hdom :
      d * (285 * q + 76 * theorem6FixedCStar) ≤
        theorem6FixedCStarSq *
          (4_179_180 * d ^ 3 + 1_020) := by
    norm_num [theorem6FixedCStarSq,
      theorem6FixedCStar]
    nlinarith
  exact hdom.trans (by simpa [d] using hcube)

/-- The decisive cube guard pays the active numerator in the critical
reaction capacity. -/
theorem theorem6FixedDecisiveActive_of_cube_size
    {n γ : ℕ}
    (hN : 0 < theorem6Q n γ * n)
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    4500 * theorem6Q n γ +
        1200 * theorem6FixedCStar ≤
      7 * theorem6FixedCriticalScale n := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let T := 4_179_180 * d ^ 3 + 1_020
  have hd : 1 ≤ d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    exact one_le_pow₀ (by norm_num)
  have hq : q ≤ d ^ 2 := by
    simpa [q, d] using
      theorem6Q_le_fifthRoot_sq_of_cube_size
        hN hcube
  have hsqCube : d ^ 2 ≤ d ^ 3 := by
    calc
      d ^ 2 = d ^ 2 * 1 := by ring
      _ ≤ d ^ 2 * d :=
        Nat.mul_le_mul_left (d ^ 2) hd
      _ = d ^ 3 := by ring
  have hT :
      T ≤ theorem6FixedCriticalScale n := by
    apply theorem6FixedCriticalScale_lower n T
    simpa [T, d] using hcube
  calc
    4500 * theorem6Q n γ +
          1200 * theorem6FixedCStar =
        4500 * q + 1200 * theorem6FixedCStar := by
          simp [q]
    _ ≤ 4500 * d ^ 2 +
          1200 * theorem6FixedCStar :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left 4500 hq) _
    _ ≤ 4500 * d ^ 3 +
          1200 * theorem6FixedCStar :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left 4500 hsqCube) _
    _ ≤ 7 * T := by
      have hnumeric :
          4500 * d ^ 3 + 1200 * 1024 ≤
            7 * (4_179_180 * d ^ 3 + 1_020) := by
        nlinarith
      simpa [T, theorem6FixedCStar] using hnumeric
    _ ≤ 7 * theorem6FixedCriticalScale n :=
      Nat.mul_le_mul_left 7 hT

/-- The same cube guard supplies the cubic mean numerator at the least
fixed-square critical scale. -/
theorem theorem6FixedDecisiveMean_of_cube_size
    {n γ : ℕ}
    (hn : 0 < n)
    (hcube :
      theorem6FixedCStarSq *
          (4_179_180 *
              theorem6FifthRoot n γ ^ 3 +
            1_020) ≤
        n) :
    1200 * theorem6FixedCStar *
          ((2 * theorem6FixedCriticalScale n) ^ 3 +
            n ^ 2) ≤
      (7 * theorem6FixedCriticalScale n) * n ^ 2 := by
  let d := theorem6FifthRoot n γ
  let A := theorem6FixedCriticalScale n
  let B := 1200 * theorem6FixedCStar
  let T := 4_179_180 * d ^ 3 + 1_020
  have hd : 1 ≤ d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    exact one_le_pow₀ (by norm_num)
  have hdCube : 1 ≤ d ^ 3 :=
    one_le_pow₀ hd
  have hT : T ≤ A := by
    apply theorem6FixedCriticalScale_lower n T
    simpa [T, d] using hcube
  have hBA : B ≤ A := by
    calc
      B ≤ T := by
        dsimp [B, T]
        norm_num [theorem6FixedCStar] at ⊢
        omega
      _ ≤ A := hT
  obtain ⟨aPred, e, haPred, he, hexcess⟩ :=
    theorem6FixedCriticalScale_additive_ceiling n hn
  have haPredA : aPred + 1 = A := by
    simpa [A] using haPred
  have haPredPos : 1 ≤ aPred := by
    omega
  have hpredBelow :
      theorem6FixedCStarSq * aPred < n := by
    rw [← haPred] at he
    rw [theorem6FixedCStar_sq] at he hexcess ⊢
    omega
  have hscale : 2048 * A ≤ n := by
    rw [theorem6FixedCStar_sq] at hpredBelow
    rw [← haPredA]
    omega
  have hscaleSq :
      (2048 * A) ^ 2 ≤ n ^ 2 :=
    Nat.pow_le_pow_left hscale 2
  have hcubic :
      B * (2 * A) ^ 3 ≤
        (6 * A) * n ^ 2 := by
    calc
      B * (2 * A) ^ 3 =
          (8 * B) * A ^ 3 := by ring
      _ ≤ (6 * 2048 ^ 2) * A ^ 3 := by
        apply Nat.mul_le_mul_right
        dsimp [B]
        norm_num [theorem6FixedCStar]
      _ = (6 * A) * (2048 * A) ^ 2 := by
        ring
      _ ≤ (6 * A) * n ^ 2 :=
        Nat.mul_le_mul_left (6 * A) hscaleSq
  have hconstant :
      B * n ^ 2 ≤ A * n ^ 2 :=
    Nat.mul_le_mul_right (n ^ 2) hBA
  calc
    1200 * theorem6FixedCStar *
          ((2 * theorem6FixedCriticalScale n) ^ 3 +
            n ^ 2) =
        B * ((2 * A) ^ 3 + n ^ 2) := by
          simp [A, B]
    _ = B * (2 * A) ^ 3 + B * n ^ 2 := by
      ring
    _ ≤ (6 * A) * n ^ 2 + A * n ^ 2 :=
      Nat.add_le_add hcubic hconstant
    _ = (7 * theorem6FixedCriticalScale n) * n ^ 2 := by
      simp [A]
      ring

end

end Tri

#print axioms Tri.theorem6Q_le_fifthRoot_sq
#print axioms
  Tri.theorem6Q_le_fifthRoot_sq_of_cube_size
#print axioms Tri.theorem6FixedSeed_of_cube_size
#print axioms
  Tri.theorem6FixedCriticalSeparation_of_cube_size
#print axioms Tri.theorem6FixedLarge_of_cube_size
#print axioms
  Tri.theorem6FixedInitialBiasSize_of_cube_size
#print axioms
  Tri.theorem6FixedPrefixActive_of_cube_size
#print axioms
  Tri.theorem6FixedDecisiveActive_of_cube_size
#print axioms
  Tri.theorem6FixedDecisiveMean_of_cube_size

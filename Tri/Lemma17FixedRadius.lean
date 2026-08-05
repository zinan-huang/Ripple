/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedScale

/-!
# Square-root label radii for the dyadic Lemma 17 prefix

At every positive rung the radius is the positive upper square root of the
dyadically scaled initial square.  This retains the paper's square-root
growth instead of doubling the radius at every stage.
-/

namespace Tri

noncomputable section

/-- Square-root label radii for the ordinary Lemma 17 prefix.  The zeroth
radius is kept exact so that it agrees with the Lemma 16 endpoint. -/
def lemma17FixedRho (rho j : ℕ) : ℕ :=
  if j = 0 then rho
  else Nat.sqrt (2 ^ j * rho ^ 2) + 1

/-- Label radius at the custom fixed-target landing. -/
def lemma17FixedLandingRho (rho m : ℕ) : ℕ :=
  2 * lemma17FixedRho rho m

@[simp] theorem lemma17FixedRho_zero
    (rho : ℕ) :
    lemma17FixedRho rho 0 = rho := by
  simp [lemma17FixedRho]

@[simp] theorem lemma17FixedRho_succ
    (rho j : ℕ) :
    lemma17FixedRho rho (j + 1) =
      Nat.sqrt (2 ^ (j + 1) * rho ^ 2) + 1 := by
  simp [lemma17FixedRho]

private theorem nineteen_upperSqrt_le_fourteen_double
    (X : ℕ)
    (hX : 23 ^ 2 ≤ X) :
    19 * (Nat.sqrt X + 1) ≤
      14 * (Nat.sqrt (2 * X) + 1) := by
  let r := Nat.sqrt X
  let s := Nat.sqrt (2 * X)
  have hr : 23 ≤ r := by
    apply (Nat.le_sqrt').2
    simpa [r] using hX
  have hrSq : r ^ 2 ≤ X := by
    simpa [r] using Nat.sqrt_le' X
  have hsUpper : 2 * X < (s + 1) ^ 2 := by
    simpa [s, Nat.succ_eq_add_one] using
      Nat.lt_succ_sqrt' (2 * X)
  by_contra hnot
  have hbad :
      14 * (s + 1) < 19 * (r + 1) :=
    Nat.lt_of_not_ge hnot
  have hlinear :
      14 * (s + 1) ≤ 19 * r + 18 := by
    omega
  have hsquare :
      (14 * (s + 1)) ^ 2 ≤
        (19 * r + 18) ^ 2 :=
    Nat.pow_le_pow_left hlinear 2
  have hlower :
      392 * r ^ 2 <
        (14 * (s + 1)) ^ 2 := by
    calc
      392 * r ^ 2 =
          196 * (2 * r ^ 2) := by ring
      _ ≤ 196 * (2 * X) :=
        Nat.mul_le_mul_left 196
          (Nat.mul_le_mul_left 2 hrSq)
      _ < 196 * (s + 1) ^ 2 :=
        Nat.mul_lt_mul_of_pos_left hsUpper
          (by norm_num)
      _ = (14 * (s + 1)) ^ 2 := by ring
  nlinarith

theorem lemma17FixedRho_pos
    (rho j : ℕ) (hrho : 1 ≤ rho) :
    1 ≤ lemma17FixedRho rho j := by
  by_cases hj : j = 0
  · simp [lemma17FixedRho, hj, hrho]
  · have hp : 0 < 2 ^ j := by positivity
    have hrad : 0 < 2 ^ j * rho ^ 2 := by
      positivity
    have hsqrt :
        0 < Nat.sqrt (2 ^ j * rho ^ 2) :=
      (Nat.sqrt_pos).2 hrad
    simp [lemma17FixedRho, hj]

theorem lemma17FixedRho_growth
    (rho j : ℕ)
    (hrho : 23 ≤ rho) :
    19 * lemma17FixedRho rho j ≤
      14 * lemma17FixedRho rho (j + 1) := by
  let X := 2 ^ j * rho ^ 2
  have hp : 1 ≤ 2 ^ j :=
    one_le_pow₀ (by norm_num)
  have hX : 23 ^ 2 ≤ X := by
    calc
      23 ^ 2 ≤ rho ^ 2 :=
        Nat.pow_le_pow_left hrho 2
      _ ≤ 2 ^ j * rho ^ 2 := by
        simpa using
          Nat.mul_le_mul_right (rho ^ 2) hp
      _ = X := rfl
  have hgrowth :=
    nineteen_upperSqrt_le_fourteen_double X hX
  have hnext :
      lemma17FixedRho rho (j + 1) =
        Nat.sqrt (2 * X) + 1 := by
    rw [lemma17FixedRho_succ]
    congr 2
    dsimp [X]
    rw [pow_succ]
    ring
  rw [hnext]
  by_cases hj : j = 0
  · subst j
    simp only [lemma17FixedRho_zero]
    have hsqrt :
        Nat.sqrt X = rho := by
      dsimp [X]
      simp
    rw [← hsqrt]
    exact
      (Nat.mul_le_mul_left 19
        (Nat.le_add_right (Nat.sqrt X) 1)).trans
        hgrowth
  · rw [show lemma17FixedRho rho j =
        Nat.sqrt X + 1 by
          simp [lemma17FixedRho, hj, X]]
    exact hgrowth

theorem lemma17FixedRho_bias
    (a cStar rho j : ℕ)
    (hrho : 1 ≤ rho)
    (hbias : 38 * cStar * rho ≤ a) :
    38 * cStar * lemma17FixedRho rho j ≤
      lemma17FixedScale a j := by
  by_cases hj : j = 0
  · subst j
    simpa using hbias
  let p := 2 ^ j
  have hp : 2 ≤ p := by
    have hjPos : 0 < j := Nat.pos_of_ne_zero hj
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by norm_num) hjPos
      _ = p := rfl
  have hrad :
      p * rho ^ 2 < (p * rho) ^ 2 := by
    have hpSq : p < p ^ 2 := by
      nlinarith
    calc
      p * rho ^ 2 < p ^ 2 * rho ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hpSq
          (Nat.pow_pos (by omega))
      _ = (p * rho) ^ 2 := by ring
  have hsqrt :
      Nat.sqrt (p * rho ^ 2) + 1 ≤ p * rho := by
    have hlt := (Nat.sqrt_lt').2 hrad
    omega
  calc
    38 * cStar * lemma17FixedRho rho j =
        38 * cStar *
          (Nat.sqrt (p * rho ^ 2) + 1) := by
            simp [lemma17FixedRho, hj, p]
    _ ≤ 38 * cStar * (p * rho) :=
      Nat.mul_le_mul_left (38 * cStar) hsqrt
    _ = p * (38 * cStar * rho) := by ring
    _ ≤ p * a :=
      Nat.mul_le_mul_left p hbias
    _ = lemma17FixedScale a j := by
      simp [lemma17FixedScale, p]

/-- The initial square-radius inequality propagates along the dyadic scales
and radii. -/
theorem lemma17FixedRho_sq
    (q a rho j : ℕ)
    (hrho : 1 ≤ rho)
    (hroot : q * (a + 1) ≤ rho ^ 2) :
    q * (lemma17FixedScale a j + 1) ≤
      (lemma17FixedRho rho j) ^ 2 := by
  by_cases hj : j = 0
  · subst j
    simpa using hroot
  let p := 2 ^ j
  have hp : 1 ≤ p := by
    dsimp [p]
    exact one_le_pow₀ (by norm_num)
  have hscale :
      lemma17FixedScale a j + 1 ≤
        p * (a + 1) := by
    dsimp [lemma17FixedScale, p]
    rw [mul_add]
    omega
  have hfirst :
      q * (lemma17FixedScale a j + 1) ≤
        p * rho ^ 2 := by
    calc
      q * (lemma17FixedScale a j + 1)
          ≤ q * (p * (a + 1)) :=
        Nat.mul_le_mul_left q hscale
      _ = p * (q * (a + 1)) := by ring
      _ ≤ p * rho ^ 2 :=
        Nat.mul_le_mul_left p hroot
  have hradPos : 0 < p * rho ^ 2 := by
    positivity
  have hsqrtPos :
      1 ≤ Nat.sqrt (p * rho ^ 2) := by
    exact (Nat.sqrt_pos).2 hradPos
  have hcover :
      p * rho ^ 2 ≤
        (Nat.sqrt (p * rho ^ 2) + 1) ^ 2 :=
    (Nat.lt_succ_sqrt' (p * rho ^ 2)).le
  calc
    q * (lemma17FixedScale a j + 1)
        ≤ p * rho ^ 2 := hfirst
    _ ≤ (Nat.sqrt (p * rho ^ 2) + 1) ^ 2 :=
      hcover
    _ = (lemma17FixedRho rho j) ^ 2 := by
      simp [lemma17FixedRho, hj, p]

theorem lemma17FixedLandingRho_growth
    (rho m : ℕ) :
    19 * lemma17FixedRho rho m ≤
      14 * lemma17FixedLandingRho rho m := by
  unfold lemma17FixedLandingRho
  omega

/-- All fixed-radius hypotheses for the ordinary prefix and custom landing. -/
structure Lemma17FixedRadiusFacts
    (q a cStar rho m : ℕ) : Prop where
  hrho0 :
    lemma17FixedRho rho 0 = rho
  hgrowth :
    ∀ j < m,
      19 * lemma17FixedRho rho j ≤
        14 * lemma17FixedRho rho (j + 1)
  hpositive :
    ∀ j ≤ m, 1 ≤ lemma17FixedRho rho j
  hbias :
    ∀ j ≤ m,
      38 * cStar * lemma17FixedRho rho j ≤
        lemma17FixedScale a j
  hroot :
    ∀ j ≤ m,
      q * (lemma17FixedScale a j + 1) ≤
        (lemma17FixedRho rho j) ^ 2
  hlandingGrowth :
    19 * lemma17FixedRho rho m ≤
      14 * lemma17FixedLandingRho rho m

/-- Two scalar premises at the initial rung supply the complete fixed radius
family. -/
theorem lemma17FixedRadiusFacts
    (q a cStar rho m : ℕ)
    (hrho : 23 ≤ rho)
    (hbias : 38 * cStar * rho ≤ a)
    (hroot : q * (a + 1) ≤ rho ^ 2) :
    Lemma17FixedRadiusFacts q a cStar rho m :=
  { hrho0 := lemma17FixedRho_zero rho
    hgrowth := fun j _ => lemma17FixedRho_growth rho j hrho
    hpositive := fun j _ =>
      lemma17FixedRho_pos rho j (by omega)
    hbias := fun j _ =>
      lemma17FixedRho_bias a cStar rho j (by omega) hbias
    hroot := fun j _ =>
      lemma17FixedRho_sq q a rho j (by omega) hroot
    hlandingGrowth :=
      lemma17FixedLandingRho_growth rho m }

end

end Tri

#print axioms Tri.lemma17FixedRho_pos
#print axioms Tri.lemma17FixedRho_growth
#print axioms Tri.lemma17FixedRho_bias
#print axioms Tri.lemma17FixedRho_sq
#print axioms Tri.lemma17FixedLandingRho_growth
#print axioms Tri.lemma17FixedRadiusFacts

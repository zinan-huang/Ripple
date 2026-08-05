/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16Exponent
import Tri.InfectionRevealUrn

/-!
# Lemma 16 activation-label urn tail

This file instantiates the maximal without-replacement window bound at the
Lemma 16 radius and discharges its exponent with the sharp `3/16` floor.
-/

namespace Tri

open scoped ENNReal

/-- The signed activation-label deviation event used by Lemma 16. -/
noncomputable def Lemma16UrnWindowBad
    (rho : ℕ) (u k R B : ℕ) : ℕ × ℕ → Prop :=
  UrnWindowBad
    ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
    ((rho : ℝ) / (2 * ((R : ℝ) + (B : ℝ))))
    (4 * ((rho : ℝ) / (2 * ((R : ℝ) + (B : ℝ)))) /
      (2 * (k : ℝ) /
        (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ)))))
    u

noncomputable instance (rho u k R B : ℕ) :
    DecidablePred (Lemma16UrnWindowBad rho u k R B) :=
  Classical.decPred _

/-- Negative-tilt form when adverse `Y` is the second urn coordinate.  Here
`R` is the initial `Y` count and `B` the initial `X` count, so the count state
starts at `(B, R)`. -/
noncomputable def Lemma16UrnWindowBadY
    (rho : ℕ) (u k R B : ℕ) : ℕ × ℕ → Prop :=
  UrnWindowBad
    ((B : ℝ) / ((B : ℝ) + (R : ℝ)))
    ((rho : ℝ) / (2 * ((B : ℝ) + (R : ℝ))))
    (- (4 * ((rho : ℝ) / (2 * ((B : ℝ) + (R : ℝ)))) /
      (2 * (k : ℝ) /
        (((u : ℝ) + 1) * ((B : ℝ) + (R : ℝ))))))
    u

noncomputable instance (rho u k R B : ℕ) :
    DecidablePred (Lemma16UrnWindowBadY rho u k R B) :=
  Classical.decPred _

/-- The maximal activation-label urn failure has the normalized Lemma 16
error. All asymptotic side conditions remain explicit. -/
theorem lemma16_urn_window_tail
    (q rho n a k u nu R B : ℕ)
    (hqa : q * a ≤ rho ^ 2)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ n)
    (hk0 : 0 < k) :
    ⨆ T : ℕ,
        hitProb (Lemma16UrnWindowBad rho u k R B)
          urnStopped T (R, B)
      ≤ lemma16UrnError q := by
  have hsum : u + k + 1 = R + B := huk.trans hRB.symm
  have htail :=
    urn_window_tail_telescope
      ((rho : ℝ) / (2 * ((R : ℝ) + (B : ℝ))))
      u k R B (by positivity) hsum hk0
  refine htail.trans ?_
  unfold lemma16UrnError
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hRBReal :
      (R : ℝ) + (B : ℝ) = (nu : ℝ) := by
    exact_mod_cast hRB
  have hkReal : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk0
  have hnu0 : 0 < nu := by omega
  have hnuReal : (0 : ℝ) < (nu : ℝ) := by
    exact_mod_cast hnu0
  have hexp :
      2 * ((rho : ℝ) / (2 * ((R : ℝ) + (B : ℝ)))) ^ 2 /
          (2 * (k : ℝ) /
            (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ)))) =
        ((rho : ℝ) / (2 * (nu : ℝ))) ^ 2 *
          (nu : ℝ) * ((u : ℝ) + 1) / (k : ℝ) := by
    rw [hRBReal]
    field_simp
  rw [hexp]
  have hfloor :=
    lemma16_exponent_floor
      (q : ℝ) (rho : ℝ) n a k u nu
      (by positivity)
      (by exact_mod_cast hqa)
      hnu hk huk hquarter hk0
  linarith

/-- The same activation-prefix tail with adverse `Y` in the second count
coordinate. -/
theorem lemma16_urn_window_tail_Y
    (q rho n a k u nu R B : ℕ)
    (hqa : q * a ≤ rho ^ 2)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ n)
    (hk0 : 0 < k) :
    ⨆ T : ℕ,
        hitProb (Lemma16UrnWindowBadY rho u k R B)
          urnStopped T (B, R)
      ≤ lemma16UrnError q := by
  have hsum : u + k + 1 = B + R := by omega
  have htail :=
    urn_window_tail_telescope_neg
      ((rho : ℝ) / (2 * ((B : ℝ) + (R : ℝ))))
      u k B R (by positivity) hsum hk0
  refine htail.trans ?_
  unfold lemma16UrnError
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hBRReal :
      (B : ℝ) + (R : ℝ) = (nu : ℝ) := by
    have h : B + R = nu := by omega
    exact_mod_cast h
  have hkReal : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk0
  have hnu0 : 0 < nu := by omega
  have hnuReal : (0 : ℝ) < (nu : ℝ) := by
    exact_mod_cast hnu0
  have hexp :
      2 * ((rho : ℝ) / (2 * ((B : ℝ) + (R : ℝ)))) ^ 2 /
          (2 * (k : ℝ) /
            (((u : ℝ) + 1) * ((B : ℝ) + (R : ℝ)))) =
        ((rho : ℝ) / (2 * (nu : ℝ))) ^ 2 *
          (nu : ℝ) * ((u : ℝ) + 1) / (k : ℝ) := by
    rw [hBRReal]
    field_simp
  rw [hexp]
  have hfloor :=
    lemma16_exponent_floor
      (q : ℝ) (rho : ℝ) n a k u nu
      (by positivity)
      (by exact_mod_cast hqa)
      hnu hk huk hquarter hk0
  linarith

end Tri

#print axioms Tri.lemma16_urn_window_tail
#print axioms Tri.lemma16_urn_window_tail_Y

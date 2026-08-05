/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Inhabit

/-!
# The strict phase-2 band contraction

This module discharges the one-step contraction used by
`Phase2BandBridge.hcontract`.  On the phase-2 live band, the productive
direction has success probability at least `3 / 4`, while the productive mass
is at least `3 / 2^(s+2)`.  At geometric base two these facts give the strict
whole-step factor

    phase2DecayENN s = 1 - 3 / 2^(s+5).

The band form at the end has exactly the quantifier shape needed for the
`hcontract` field once the chosen open band is shown to lie in `Phase2Live`.
-/

namespace Tri

open scoped ENNReal

/-- The phase-2 contraction factor is strictly below one at every stage. -/
theorem phase2_contract_phi_lt_one (s : ℕ) : phase2DecayENN s < 1 := by
  rw [phase2DecayENN, ENNReal.ofReal_lt_one]
  unfold phase2Decay
  have hloss : (0 : ℝ) < 3 / (2 : ℝ) ^ (s + 5) := by positivity
  linarith

/-- At one phase-2 live state, the exact three-atom base-two moment contracts
by `phase2DecayENN s`.

The weak inequality used to transfer from `ℝ≥0∞` to `ℝ` is supplied by
`three_term_drift_ennreal`.  Strict slack then comes from the phase-2
direction comparison and `phase2_productive_lower`, whose lower bound is
proved from `xy_ge_phase2`. -/
theorem phase2_hcontract_of_live (a b n s : ℕ)
    (hlocal : 3 ≤ (a + 1) + (b + 1)) (hpop : a + b + 2 = n)
    (hlive : Phase2Live n s (a + 1)) :
    triStep (a + 1) (b + 1) hlocal a +
          triStep (a + 1) (b + 1) hlocal (a + 1) *
            ((1 : ℝ≥0∞) / 2) +
          triStep (a + 1) (b + 1) hlocal (a + 2) *
            ((1 : ℝ≥0∞) / 2) ^ 2 ≤
        phase2DecayENN s * ((1 : ℝ≥0∞) / 2) := by
  have h3 : 3 ≤ n := by omega
  obtain ⟨hsmall, hstage⟩ := phase2_live_bounds hpop hlive
  have hab : b ≤ a := by omega
  have hquarter : 3 * n ≤ 4 * (a + 1) := by omega

  -- Route the phase-2 guard through the paper's direction comparison
  -- `(x - 1)/(n - 2) ≥ x/n`.
  have hdirection := direction_ge_cross (a := a) (b := b) hab
  rw [hpop] at hdirection
  have hscaledDirection : n * (3 * (a + b)) ≤ n * (4 * a) := by
    calc
      n * (3 * (a + b)) = (3 * n) * (a + b) := by ring
      _ ≤ (4 * (a + 1)) * (a + b) :=
        Nat.mul_le_mul_right (a + b) hquarter
      _ ≤ 4 * (n * a) := by
        calc
          (4 * (a + 1)) * (a + b) =
              4 * ((a + 1) * (a + b)) := by ring
          _ ≤ 4 * (n * a) := Nat.mul_le_mul_left 4 hdirection
      _ = n * (4 * a) := by ring
  have habDirection : 3 * (a + b) ≤ 4 * a :=
    Nat.le_of_mul_le_mul_left hscaledDirection (by omega)

  -- Convert the conditional direction bound into the corresponding bound on
  -- the two productive reaction counts.
  have hcross := direction_cross_mul a b
  have hscaledCounts :
      (3 * (upCount a b + downCount a b)) * (a + b) ≤
        (4 * upCount a b) * (a + b) := by
    calc
      (3 * (upCount a b + downCount a b)) * (a + b) =
          (3 * (a + b)) * (upCount a b + downCount a b) := by ring
      _ ≤ (4 * a) * (upCount a b + downCount a b) :=
        Nat.mul_le_mul_right (upCount a b + downCount a b) habDirection
      _ = 4 * (a * (upCount a b + downCount a b)) := by ring
      _ = 4 * (upCount a b * (a + b)) := by rw [hcross]
      _ = (4 * upCount a b) * (a + b) := by ring
  have hdirectionCounts :
      3 * (upCount a b + downCount a b) ≤ 4 * upCount a b :=
    Nat.le_of_mul_le_mul_right hscaledCounts (by omega)
  have hdownUp : 3 * downCount a b ≤ upCount a b := by omega
  have hcountsE :
      (3 : ℝ≥0∞) * (downCount a b : ℝ≥0∞) ≤
        (upCount a b : ℝ≥0∞) := by
    exact_mod_cast hdownUp
  push_cast at hcountsE
  have hdirectionE :
      (3 : ℝ≥0∞) * triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) := by
    rw [triStep_down, triStep_up]
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_left hcountsE
        (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞)⁻¹
  have htwoDown :
      (2 : ℝ≥0∞) * triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) := by
    calc
      (2 : ℝ≥0∞) * triStep (a + 1) (b + 1) hlocal a ≤
          3 * triStep (a + 1) (b + 1) hlocal a := by gcongr; norm_num
      _ ≤ triStep (a + 1) (b + 1) hlocal (a + 2) := hdirectionE
  have hdrift :
      triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) *
          ((1 : ℝ≥0∞) / 2) := by
    have hhalf : triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) / 2 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
        (Or.inl (by norm_num))]
      simpa [mul_comm] using htwoDown
    simpa only [div_eq_mul_inv, one_mul] using hhalf

  have hsum := triStep_masses_sum a (b + 1) hlocal
  have hweak := three_term_drift_ennreal hsum (by norm_num) hdrift
  have fhalf : ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by norm_num
  have fleft :
      triStep (a + 1) (b + 1) hlocal a +
            triStep (a + 1) (b + 1) hlocal (a + 1) *
              ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) hlocal (a + 2) *
              ((1 : ℝ≥0∞) / 2) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top fhalf hweak
  have fright : phase2DecayENN s * ((1 : ℝ≥0∞) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top fhalf

  let p0 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) hlocal a)
  let p1 : ℝ := ENNReal.toReal
    (triStep (a + 1) (b + 1) hlocal (a + 1))
  let p2 : ℝ := ENNReal.toReal
    (triStep (a + 1) (b + 1) hlocal (a + 2))
  have f0 : triStep (a + 1) (b + 1) hlocal a ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f1 : triStep (a + 1) (b + 1) hlocal (a + 1) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f2 : triStep (a + 1) (b + 1) hlocal (a + 2) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have hsumR : p0 + p1 + p2 = 1 := by
    have hreal := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f0, f1⟩) f2,
      ENNReal.toReal_add f0 f1, ENNReal.toReal_one] at hreal
    simpa [p0, p1, p2] using hreal
  have hdirectionR : 3 * p0 ≤ p2 := by
    have hreal := ENNReal.toReal_mono f2 hdirectionE
    rw [ENNReal.toReal_mul] at hreal
    simpa [p0, p2] using hreal
  have hmajor : 2 * (a + 1) ≥ n := by omega
  have hproductiveR :
      (3 : ℝ) / (2 : ℝ) ^ (s + 2) ≤ p0 + p2 := by
    simpa [p0, p2] using
      phase2_productive_lower a b n s h3 hpop hstage hmajor
  have hbracket :
      2 * p0 + p1 + p2 / 2 ≤
        1 - (1 / 8 : ℝ) * (p0 + p2) := by
    nlinarith
  have hrate :
      1 - (1 / 8 : ℝ) * (p0 + p2) ≤
        1 - 3 / (2 : ℝ) ^ (s + 5) := by
    have hscaled := mul_le_mul_of_nonneg_left hproductiveR
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    calc
      1 - (1 / 8 : ℝ) * (p0 + p2) ≤
          1 - (1 / 8 : ℝ) * (3 / (2 : ℝ) ^ (s + 2)) :=
        sub_le_sub_left hscaled 1
      _ = 1 - 3 / (2 : ℝ) ^ (s + 5) := by
        rw [phase2_loss_check]

  rw [← ENNReal.toReal_le_toReal fleft fright,
    ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨f0, ENNReal.mul_ne_top f1 fhalf⟩)
      (ENNReal.mul_ne_top f2 (ENNReal.pow_ne_top fhalf)),
    ENNReal.toReal_add f0 (ENNReal.mul_ne_top f1 fhalf)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, phase2DecayENN,
    ENNReal.toReal_ofReal (phase2Decay_nonneg s)]
  norm_num only [ENNReal.toReal_ofNat]
  change p0 + p1 * (1 / 2 : ℝ) + p2 * (1 / 4 : ℝ) ≤
    phase2Decay s * (1 / 2 : ℝ)
  calc
    p0 + p1 * (1 / 2 : ℝ) + p2 * (1 / 4 : ℝ) =
        (1 / 2 : ℝ) * (2 * p0 + p1 + p2 / 2) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 - (1 / 8 : ℝ) * (p0 + p2)) :=
      mul_le_mul_of_nonneg_left hbracket (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (1 - 3 / (2 : ℝ) ^ (s + 5)) :=
      mul_le_mul_of_nonneg_left hrate (by norm_num)
    _ = phase2Decay s * (1 / 2 : ℝ) := by
      unfold phase2Decay
      ring

/-- The phase-2 live-band contraction in the exact quantifier shape of
`Phase2BandBridge.hcontract`.  Thus a bridge using
`φ = phase2DecayENN s` fills `hcontract` by applying this lemma to a proof
that its selected open band lies in `Phase2Live n s`. -/
theorem phase2_hcontract (n s bandLo bandHi : ℕ)
    (hlive : ∀ z, bandLo < z → z < bandHi → Phase2Live n s z) :
    ∀ (a b : ℕ) (hlocal : 3 ≤ (a + 1) + (b + 1)),
      a + b + 2 = n →
      bandLo < a + 1 → a + 1 < bandHi →
      triStep (a + 1) (b + 1) hlocal a +
            triStep (a + 1) (b + 1) hlocal (a + 1) *
              ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) hlocal (a + 2) *
              ((1 : ℝ≥0∞) / 2) ^ 2 ≤
          phase2DecayENN s * ((1 : ℝ≥0∞) / 2) := by
  intro a b hlocal hpop hlo hhi
  exact phase2_hcontract_of_live a b n s hlocal hpop
    (hlive (a + 1) hlo hhi)

#print axioms phase2_contract_phi_lt_one
#print axioms phase2_hcontract_of_live
#print axioms phase2_hcontract

end Tri

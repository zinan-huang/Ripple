/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBBandReturn

/-!
# Concrete parameters for Double-B band phases

This file discharges two recurring analytic interfaces of a Double-B band:

* the event-indexed direction multiplier `η`, chosen from a harmonic ratio
  `u < w < 1`;
* a uniform productive-pair mass obtained from the lower gap and upper
  co-level of the band.
-/

namespace Tri

open scoped ENNReal

/-- The reciprocal resolution-event contraction associated with geometric
base `w` and down/up ratio bound `u`. -/
noncomputable def doubleDirectionEta (u w : ℝ≥0∞) : ℝ≥0∞ :=
  w * (u + 1) / (u + w ^ 2)

/-- The concrete `η` satisfies every scalar side condition of
`doubleState_band_phase_reaches_mono` whenever `0 < u < w < 1`. -/
theorem doubleDirectionEta_spec
    {u w : ℝ≥0∞} (hu0 : 0 < u) (huw : u < w) (hw1 : w < 1) :
    doubleDirectionEta u w * (u + w ^ 2) = w * (u + 1) ∧
      w ≤ doubleDirectionEta u w ∧
      1 ≤ doubleDirectionEta u w ∧
      doubleDirectionEta u w ≠ ⊤ := by
  have huT : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (huw.trans hw1).le
  have hwT : w ≠ ⊤ := ne_top_of_lt (hw1.trans_le le_top)
  have hd0 : u + w ^ 2 ≠ 0 := by
    intro h
    exact hu0.ne' (add_eq_zero.mp h).1
  have hdT : u + w ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨huT, ENNReal.pow_ne_top hwT⟩
  have hnT : w * (u + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top hwT
      (ENNReal.add_ne_top.mpr ⟨huT, ENNReal.one_ne_top⟩)
  have hw0 : w ≠ 0 := (hu0.trans huw).ne'
  constructor
  · unfold doubleDirectionEta
    exact ENNReal.div_mul_cancel hd0 hdT
  constructor
  · unfold doubleDirectionEta
    apply (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdT)).2
    simpa only [add_comm] using
      (mul_le_mul_left'
        (add_le_add_left (pow_le_one₀ bot_le hw1.le) u) w)
  constructor
  · unfold doubleDirectionEta
    apply (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdT)).2
    rw [one_mul]
    apply (ENNReal.toReal_le_toReal hdT hnT).1
    rw [ENNReal.toReal_add huT (ENNReal.pow_ne_top hwT),
      ENNReal.toReal_pow, ENNReal.toReal_mul,
      ENNReal.toReal_add huT ENNReal.one_ne_top, ENNReal.toReal_one]
    have huwR : u.toReal ≤ w.toReal := by
      exact (ENNReal.toReal_le_toReal huT hwT).2 huw.le
    have hwR : w.toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal hwT ENNReal.one_ne_top).2 hw1.le
    have hprod : 0 ≤ (w.toReal - u.toReal) * (1 - w.toReal) :=
      mul_nonneg (sub_nonneg.mpr huwR) (sub_nonneg.mpr hwR)
    nlinarith
  · unfold doubleDirectionEta
    exact ENNReal.div_ne_top hnT hd0

/-- The productive mass assigned to the open level band
`aLo < level < hi`. -/
noncomputable def doubleBandProductivity
    (n aLo hi : ℕ) : ℝ≥0∞ :=
  ((((aLo + 1 - n) * (2 * n - (hi - 1)) : ℕ) : ℝ≥0∞) /
    ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞))

/-- The level-based productive floor is uniform on the whole open band. -/
theorem doubleBandProductivity_le
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ aLo + 1) (hhi : hi ≤ 2 * n)
    (s : DoubleState n)
    (hs : ¬ (s.1.doubleLevel ≤ aLo ∨ hi ≤ s.1.doubleLevel)) :
    doubleBandProductivity n aLo hi ≤
      dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xy
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xb
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2
          simp only [BiCfg.DoubleInv] at this
          omega) .yb := by
  have hlive : aLo < s.1.doubleLevel ∧ s.1.doubleLevel < hi := by
    omega
  have hgap :
      aLo + 1 - n ≤ s.1.doubleLevel - n := by omega
  have hco :
      2 * n - (hi - 1) ≤ 2 * n - s.1.doubleLevel := by omega
  have hprod :
      (aLo + 1 - n) * (2 * n - (hi - 1)) ≤
        (s.1.doubleLevel - n) * (2 * n - s.1.doubleLevel) :=
    Nat.mul_le_mul hgap hco
  calc
    doubleBandProductivity n aLo hi ≤
        (((s.1.doubleLevel - n) * (2 * n - s.1.doubleLevel) : ℕ) : ℝ≥0∞) /
          ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) := by
      unfold doubleBandProductivity
      exact ENNReal.div_le_div_right (by exact_mod_cast hprod) _
    _ ≤ dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xy
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xb
        + dbPairPMF s.1.x s.1.y s.1.b (by
          have := s.2
          simp only [BiCfg.DoubleInv] at this
          omega) .yb :=
      by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          productive_mass_level_floor n hn s

/-- The band productivity parameter is a probability. -/
theorem doubleBandProductivity_le_one
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ aLo + 1) (hwidth : aLo + 2 ≤ hi)
    (hhi : hi ≤ 2 * n) :
    doubleBandProductivity n aLo hi ≤ 1 := by
  let A := aLo + 1 - n
  let B := 2 * n - (hi - 1)
  have hAB : A + B ≤ n := by
    dsimp [A, B]
    omega
  have hmul : A * B ≤ n * (n - 1) := by
    by_cases hA : A = 0
    · simp [hA]
    · have hApos : 0 < A := Nat.pos_of_ne_zero hA
      have hAle : A ≤ n := by omega
      have hBle : B ≤ n - 1 := by omega
      exact Nat.mul_le_mul hAle hBle
  have hchoose : 2 * Nat.choose n 2 = n * (n - 1) := by
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hden0 : ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast
      (Nat.mul_ne_zero (by norm_num) (Nat.choose_pos hn).ne')
  have hdenT : ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    doubleBandProductivity n aLo hi ≤
        ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) /
          ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) := by
      unfold doubleBandProductivity
      apply ENNReal.div_le_div_right
      rw [hchoose]
      exact_mod_cast hmul
    _ = 1 := ENNReal.div_self hden0 hdenT

/-- Complementing the productive floor supplies the Bernoulli split required
by the productivity supermartingale. -/
theorem doubleBandProductivity_add_compl
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ aLo + 1) (hwidth : aLo + 2 ≤ hi)
    (hhi : hi ≤ 2 * n) :
    doubleBandProductivity n aLo hi +
        (1 - doubleBandProductivity n aLo hi) = 1 := by
  rw [add_comm]
  exact tsub_add_cancel_of_le
    (doubleBandProductivity_le_one n hn aLo hi hnLo hwidth hhi)

end Tri

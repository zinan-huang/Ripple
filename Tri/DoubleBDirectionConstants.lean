/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockConstants

/-!
# Scalar constants for Double-B resolution direction

At a symmetric effective lower boundary

```
aLo = n+g,  bHiD = n-g,
```

the concrete harmonic base and reciprocal resolution multiplier simplify to

```
w = n/(n+g),
η⁻¹ = ((n-g)(n+g)+n²)/(2n²).
```

This makes the direction error an elementary product of two natural-number
ratios.  A resolution budget of at least `4n`, together with an upward band
width at most `g`, pays an `exp(-g²/n)` envelope.
-/

namespace Tri

open scoped ENNReal

/-- The midpoint harmonic base at the symmetric lower boundary is `n/(n+g)`.
-/
theorem phase1RungBase_symmetric
    (n g : ℕ) (hn : 0 < n) (hg : g ≤ n) :
    phase1RungBase (n + g) (n - g) =
      (n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞) := by
  unfold phase1RungBase
  have hsum : n + g + (n - g) = 2 * n := by omega
  rw [hsum]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hngR : (n + g : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Exact natural-ratio form of the reciprocal direction multiplier at a
symmetric lower boundary. -/
theorem doubleDirectionEta_inv_symmetric
    (n g : ℕ) (hn : 0 < n) (hg : g ≤ n) :
    (doubleDirectionEta
        (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
        (phase1RungBase (n + g) (n - g)))⁻¹ =
      ((((n - g) * (n + g) + n ^ 2 : ℕ) : ℝ≥0∞) /
        ((2 * n ^ 2 : ℕ) : ℝ≥0∞)) := by
  rw [phase1RungBase_symmetric n g hn hg]
  let u : ℝ≥0∞ :=
    ((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)
  let w : ℝ≥0∞ :=
    (n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)
  have huT : u ≠ ⊤ := by
    dsimp [u]
    finiteness
  have hwT : w ≠ ⊤ := by
    dsimp [w]
    finiteness
  have hw0 : w ≠ 0 := by
    dsimp [w]
    exact ENNReal.div_ne_zero.mpr ⟨(by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega), ENNReal.natCast_ne_top _⟩
  have hdenT : u + w ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨huT, ENNReal.pow_ne_top hwT⟩
  have hη0 : doubleDirectionEta u w ≠ 0 := by
    unfold doubleDirectionEta
    exact ENNReal.div_ne_zero.mpr
      ⟨mul_ne_zero hw0 (by simp), hdenT⟩
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.inv_ne_top.mpr hη0) (by finiteness)).mp
  unfold doubleDirectionEta
  rw [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_add huT ENNReal.one_ne_top,
    ENNReal.toReal_add huT (ENNReal.pow_ne_top hwT),
    ENNReal.toReal_pow, ENNReal.toReal_div]
  dsimp [u, w]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hngR : (n + g : ℝ) ≠ 0 := by positivity
  norm_num only [Nat.cast_sub hg, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hnR, hngR]
  ring

/-- Exponential decay of the reciprocal direction multiplier over `M`
resolution events. -/
theorem doubleDirectionEta_inv_pow_le_exp
    (n g M : ℕ) (hn : 0 < n) (hg : g ≤ n) :
    1 /
        doubleDirectionEta
            (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
            (phase1RungBase (n + g) (n - g)) ^ M ≤
      ENNReal.ofReal
        (Real.exp
          (-((M : ℝ) * (g : ℝ) ^ 2 /
            (2 * (n : ℝ) ^ 2)))) := by
  rw [one_div, ENNReal.inv_pow,
    doubleDirectionEta_inv_symmetric n g hn hg]
  have hraw :=
    ratio_pow_le_exp
      (2 * n ^ 2) ((n - g) * (n + g) + n ^ 2) M
      (by positivity) (by
        have hprod :
            (n - g) * (n + g) = n ^ 2 - g ^ 2 := by
          simpa only [pow_two, Nat.mul_comm] using
            (Nat.mul_self_sub_mul_self_eq n g).symm
        rw [hprod]
        calc
          n ^ 2 - g ^ 2 + n ^ 2 ≤ n ^ 2 + n ^ 2 :=
            Nat.add_le_add_right (Nat.sub_le _ _) _
          _ = 2 * n ^ 2 := by ring)
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : g ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hg 2
  have hprod :
      (n - g) * (n + g) = n ^ 2 - g ^ 2 := by
    simpa only [pow_two, Nat.mul_comm] using
      (Nat.mul_self_sub_mul_self_eq n g).symm
  rw [hprod]
  norm_num only [Nat.cast_sub hsq, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring_nf
  exact le_refl (-((M : ℝ) * (g : ℝ) ^ 2))

/-- Exact exponential envelope for the direction term: potential growth
across the band minus contraction over resolution events. -/
theorem doubleDirectionError_le_exp
    (n g start hi M : ℕ)
    (hn : 0 < n) (hg : g ≤ n) (hstart : start ≤ hi - 1) :
    phase1RungBase (n + g) (n - g) ^ start /
        (phase1RungBase (n + g) (n - g) ^ (hi - 1) *
          doubleDirectionEta
            (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
            (phase1RungBase (n + g) (n - g)) ^ M) ≤
      ENNReal.ofReal
        (Real.exp (
          ((((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
              Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) -
            (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2)))) := by
  rw [phase1RungBase_symmetric n g hn hg]
  have hratio :=
    base_pow_ratio_le_ofReal_exp n (n + g) start (hi - 1)
      hn (by omega) hstart
  have heta := doubleDirectionEta_inv_pow_le_exp n g M hn hg
  rw [phase1RungBase_symmetric n g hn hg] at heta
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hnT : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit :
      ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ start /
          (((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ (hi - 1) *
            doubleDirectionEta
              (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
              ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ M) =
        (((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ start /
          ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ (hi - 1)) *
        (1 /
          doubleDirectionEta
            (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
            ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ M) := by
    have hbase0 :
        (n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨hn0, ENNReal.natCast_ne_top _⟩
    have hbaseT :
        (n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top hnT (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
    simpa using
      (ENNReal.mul_div_mul_comm
        (a := ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ start)
        (b := 1)
        (c := ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ (hi - 1))
        (d := doubleDirectionEta
          (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
          ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ M)
        (Or.inl (pow_ne_zero _ hbase0))
        (Or.inl (ENNReal.pow_ne_top hbaseT)))
  rw [hsplit]
  calc
    (((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ start /
          ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ (hi - 1)) *
        (1 /
          doubleDirectionEta
            (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
            ((n : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ M)
        ≤ ENNReal.ofReal
              (Real.exp
                ((((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
                  Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)))) *
            ENNReal.ofReal
              (Real.exp
                (-((M : ℝ) * (g : ℝ) ^ 2 /
                  (2 * (n : ℝ) ^ 2)))) :=
      mul_le_mul hratio heta bot_le bot_le
    _ = ENNReal.ofReal
          (Real.exp
            ((((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
                Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) -
              (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3

/-- A width-`g` band and at least `4n` resolution events give the desired
Gaussian-scale direction error. -/
theorem doubleDirectionError_le_exp_neg
    (n g start hi M : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi - 1) (hwidth : hi - 1 ≤ start + g)
    (hM : 4 * n ≤ M) :
    phase1RungBase (n + g) (n - g) ^ start /
        (phase1RungBase (n + g) (n - g) ^ (hi - 1) *
          doubleDirectionEta
            (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
            (phase1RungBase (n + g) (n - g)) ^ M) ≤
      ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) := by
  refine (doubleDirectionError_le_exp
    n g start hi M hn hg hstart).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgR : (0 : ℝ) ≤ g := by positivity
  have hratio :
      (0 : ℝ) < ((n + g : ℕ) : ℝ) / (n : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hratioSub :
      ((n + g : ℕ) : ℝ) / (n : ℝ) - 1 =
        (g : ℝ) / (n : ℝ) := by
    push_cast
    field_simp
    ring
  rw [hratioSub] at hlog
  have hratioOne :
      (1 : ℝ) ≤ ((n + g : ℕ) : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    push_cast
    linarith
  have hlog0 :
      0 ≤ Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) :=
    Real.log_nonneg hratioOne
  have hwidthR :
      (((hi - 1 : ℕ) : ℝ) - (start : ℝ)) ≤ g := by
    have hcast : ((hi - 1 : ℕ) : ℝ) ≤ start + g := by
      exact_mod_cast hwidth
    push_cast at hcast
    linarith
  have hgrowth :
      (((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
          Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) ≤
        (g : ℝ) ^ 2 / (n : ℝ) := by
    calc
      (((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
            Real.log (((n + g : ℕ) : ℝ) / (n : ℝ))
          ≤ g * Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hwidthR hlog0
      _ ≤ g * (g / n) :=
        mul_le_mul_of_nonneg_left hlog hgR
      _ = g ^ 2 / n := by ring
  have hMR : (4 : ℝ) * n ≤ M := by exact_mod_cast hM
  have hdecay :
      2 * (g : ℝ) ^ 2 / (n : ℝ) ≤
        (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2) := by
    have hscaled :=
      mul_le_mul_of_nonneg_right hMR (sq_nonneg (g : ℝ))
    field_simp [hnR.ne']
    nlinarith
  have htwo :
      2 * (g : ℝ) ^ 2 / (n : ℝ) =
        2 * ((g : ℝ) ^ 2 / (n : ℝ)) := by ring
  rw [htwo] at hdecay
  linarith

/-- Once the resolution budget is at least `2n`, the normal-clock geometric
term is also below the Gaussian rung envelope. -/
theorem doubleNormalEnvelope_le_exp_neg
    (n g M : ℕ) (hn : 0 < n) (hg : g ≤ n) (hM : 2 * n ≤ M) :
    ((3 : ℝ≥0∞) / 4) ^ doubleClockBudget n M ≤
      ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) := by
  apply ratio_pow_le_ofReal_exp
    4 3 (doubleClockBudget n M) ((g : ℝ) ^ 2 / (n : ℝ))
    (by norm_num) (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgSq : (g : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hg 2
  have hMR : (2 : ℝ) * n ≤ M := by exact_mod_cast hM
  unfold doubleClockBudget
  push_cast
  field_simp [hnR.ne']
  nlinarith

/-- With the same budget, the two occupation-clock terms together cost at
most two copies of the Gaussian rung envelope. -/
theorem doubleJointClockEnvelope_le_two_exp_neg
    (n g M : ℕ) (hn : 0 < n) (hg : g ≤ n) (hM : 2 * n ≤ M) :
    doubleJointClockEnvelope n g M ≤
      2 * ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) := by
  unfold doubleJointClockEnvelope
  calc
    ((3 : ℝ≥0∞) / 4) ^ doubleClockBudget n M +
          ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ))))
        ≤ ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) +
          ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) :=
      add_le_add (doubleNormalEnvelope_le_exp_neg n g M hn hg hM) le_rfl
    _ = 2 * ENNReal.ofReal
          (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) := by ring

/-- One symmetric early-rung envelope.  The safety and upper-return terms stay
exact; direction and both clock branches cost three Gaussian terms. -/
noncomputable def doubleBandSymmetricRungError
    (n g bHiR k returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  ((bHiR : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ k +
      3 * ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ)))) +
    ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet

/-- The clocked concrete-rung error at the symmetric lower boundary and
`M=4n` is below the symmetric early-rung envelope. -/
theorem doubleBandJointRungClockedError_le_symmetric
    (n g bHiR hi k returnLo bHiRet kRet : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : n + g + k ≤ hi - 1)
    (hwidth : hi - 1 ≤ n + g + k + g) :
    doubleBandJointRungClockedError
        n g (n + g) bHiR (n - g) hi k (4 * n)
          returnLo bHiRet kRet ≤
      doubleBandSymmetricRungError
        n g bHiR k returnLo bHiRet kRet := by
  let E : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ))))
  have hdir :=
    doubleDirectionError_le_exp_neg
      n g (n + g + k) hi (4 * n) hn hg hstart hwidth le_rfl
  have hclock :
      doubleJointClockEnvelope n g (4 * n) ≤ 2 * E := by
    exact doubleJointClockEnvelope_le_two_exp_neg
      n g (4 * n) hn hg (by omega)
  unfold doubleBandJointRungClockedError doubleBandSymmetricRungError
  dsimp only
  change
    (((bHiR : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ k +
        phase1RungBase (n + g) (n - g) ^ (n + g + k) /
          (phase1RungBase (n + g) (n - g) ^ (hi - 1) *
            doubleDirectionEta
              (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
              (phase1RungBase (n + g) (n - g)) ^ (4 * n)) +
        doubleJointClockEnvelope n g (4 * n)) +
      ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet ≤
    ((bHiR : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ k +
        3 * E +
      ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet
  apply add_le_add
  · calc
      ((bHiR : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ k +
            phase1RungBase (n + g) (n - g) ^ (n + g + k) /
              (phase1RungBase (n + g) (n - g) ^ (hi - 1) *
                doubleDirectionEta
                  (((n - g : ℕ) : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞))
                  (phase1RungBase (n + g) (n - g)) ^ (4 * n)) +
            doubleJointClockEnvelope n g (4 * n)
          ≤ ((bHiR : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ k +
              E + 2 * E :=
        add_le_add (add_le_add le_rfl hdir) hclock
      _ = ((bHiR : ℝ≥0∞) / ((n + g : ℕ) : ℝ≥0∞)) ^ k +
            3 * E := by ring
  · exact le_rfl

/-- A fully symmetric early Double-B rung.  All directional and clock
parameters are fixed; only the band geometry and the two exact Feller buffers
remain. -/
theorem doubleBand_symmetric_rung
    (n : ℕ) (hn : 2 ≤ n)
    (g bHiR hi k : ℕ)
    (hg0 : 0 < g) (hg : g ≤ n)
    (hsmall : 8 * hi ≤ 9 * n)
    (hpopR : n + g + bHiR + 2 = 2 * n)
    (hbHiR : 0 < bHiR) (hmajR : bHiR ≤ n + g)
    (hstart : n + g + k ≤ hi - 1)
    (hwidth : hi ≤ n + g + k + g)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : n + g < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (doubleStateStep n hn) (doubleClockHorizon n (4 * n))
      (fun s => n + g + k ≤ s.1.doubleLevel)
      (fun s => returnLo + 1 ≤ s.1.doubleLevel)
      (doubleBandSymmetricRungError
        n g bHiR k returnLo bHiRet kRet) := by
  have hsum : n + g + (n - g) = 2 * n := by omega
  have hstartHi : n + g + k ≤ hi := hstart.trans (Nat.sub_le _ _)
  have hr :=
    doubleBandJointRung_clocked
      n hn g (n + g) bHiR (n - g) hi k (4 * n)
      (by omega) hsmall (by omega) hpopR (by omega) hbHiR hmajR
      hsum (by omega) (by omega) hstartHi hwidth hg
      returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
      hlowerTarget htargetHi hreturnGap
  exact hr.mono_error
    (doubleBandJointRungClockedError_le_symmetric
      n g bHiR hi k returnLo bHiRet kRet
      (by omega) hg hstart (by omega))

end Tri

#print axioms Tri.phase1RungBase_symmetric
#print axioms Tri.doubleDirectionEta_inv_symmetric
#print axioms Tri.doubleDirectionError_le_exp
#print axioms Tri.doubleDirectionError_le_exp_neg
#print axioms Tri.doubleJointClockEnvelope_le_two_exp_neg
#print axioms Tri.doubleBand_symmetric_rung

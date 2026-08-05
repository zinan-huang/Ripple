/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBClockNormal
import Tri.SingleBWindowTail
import Tri.HeavyBClockBlank

/-!
# The blank-heavy branch of the Single-B occupation clock

The level potential runs on the CORRECTED doubled level, carried
subtraction-free as `w^(2x+b+CY) · v^CX` with `w·v = 1` — this is
`singleTheta w v 1`, so creations are Λ-inert and the blank-branch algebra is
unchanged from Double-B.

Because the corrected level is doubled, the honest geometric base is
`w = 2n/(2n+g)` with slack `r = g/(2n+g)` and drift quantum `d = g/(2n)`;
then `r = w·d` holds exactly and the Heavy-B quadratic-slack scalar lemma
applies verbatim at scale `2n`, giving `η = 1 + r²/2`.

Blank-heaviness on complementary live ticks needs an upper bound on the
`X`-oriented creation count, which the four-way freeze does not supply.  The
potential is therefore masked by `CX < cxCap`; the mask is absorbing because
`CX` is monotone, and the corrected-`Y` identity `y + CX = y₀ + RY` turns the
mask back on at every few-resolution endpoint.
-/

namespace Tri

open scoped ENNReal

/-! ### Blank-branch parameters at doubled scale -/

/-- Geometric base for the Single-B blank-heavy corrected-level potential:
`2n/(2n+g)`. -/
noncomputable def singleBlankW (n g : ℕ) : ℝ≥0∞ := heavyBlankW (2 * n) g

/-- The complementary rational slack `g/(2n+g)`, with `w+r=1`. -/
noncomputable def singleBlankR (n g : ℕ) : ℝ≥0∞ := heavyBlankR (2 * n) g

/-- Per-blank-tick multiplier `1 + r²/2`. -/
noncomputable def singleBlankEta (n g : ℕ) : ℝ≥0∞ := heavyBlankEta (2 * n) g

/-- The uniform resolution-drift quantum `g/(2n)` on the doubled level. -/
noncomputable def singleBlankDrift (n g : ℕ) : ℝ≥0∞ :=
  heavyBlankDrift (2 * n) g

/-- The reciprocal base `(2n+g)/(2n)`, used as the `v` of the corrected
potential. -/
noncomputable def singleBlankV (n g : ℕ) : ℝ≥0∞ :=
  ((2 * n + g : ℕ) : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)

theorem singleBlankW_add_R (n g : ℕ) (hn : 0 < n) :
    singleBlankW n g + singleBlankR n g = 1 :=
  heavyBlankW_add_R (2 * n) g (by omega)

theorem singleBlank_R_eq_W_mul_drift (n g : ℕ) (hn : 0 < n) :
    singleBlankR n g = singleBlankW n g * singleBlankDrift n g :=
  heavyBlank_R_eq_W_mul_drift (2 * n) g (by omega)

theorem singleBlankW_le_one (n g : ℕ) (hn : 0 < n) :
    singleBlankW n g ≤ 1 :=
  heavyBlankW_le_one (2 * n) g (by omega)

/-- The doubled base and its reciprocal cancel. -/
theorem singleBlankW_mul_V (n g : ℕ) (hn : 0 < n) :
    singleBlankW n g * singleBlankV n g = 1 := by
  have ha0 : ((2 * n : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n ≠ 0)
  have hb0 : ((2 * n + g : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n + g ≠ 0)
  have haT : ((2 * n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hbT : ((2 * n + g : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold singleBlankW singleBlankV heavyBlankW
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    ((2 * n : ℕ) : ℝ≥0∞) * (((2 * n + g : ℕ) : ℝ≥0∞))⁻¹ *
          (((2 * n + g : ℕ) : ℝ≥0∞) * (((2 * n : ℕ) : ℝ≥0∞))⁻¹)
        = ((2 * n : ℕ) : ℝ≥0∞) * (((2 * n : ℕ) : ℝ≥0∞))⁻¹ *
            (((2 * n + g : ℕ) : ℝ≥0∞) * (((2 * n + g : ℕ) : ℝ≥0∞))⁻¹) := by
          ring
    _ = 1 := by
          rw [ENNReal.mul_inv_cancel ha0 haT, ENNReal.mul_inv_cancel hb0 hbT,
            one_mul]

/-! ### Split arithmetic on the live band -/

/-- A live state of the repaired stopped band has physical gap at least `g`
whenever the corrected floor carries `n + D + g`. -/
theorem singleB_live_gap {n aLoΛ hiΛ D H g : ℕ} (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hgap : n + D + g ≤ aLoΛ + 1) :
    q.cfg.1.y + g ≤ q.cfg.1.x := by
  have hnotLow : ¬ (q.cfg.1.doubleLevel + q.cy ≤ aLoΛ + q.cx) :=
    fun h => hlive (Or.inl h)
  have hnotBad : ¬ CreationBadY D H q :=
    fun h => hlive (Or.inr (Or.inr (Or.inl h)))
  have hnotBoundary : ¬ singleCreationBoundary H q :=
    fun h => hlive (Or.inr (Or.inr (Or.inr h)))
  have hbudget : q.cx + q.cy ≤ H := by
    unfold singleCreationBoundary at hnotBoundary
    omega
  have hbal : q.cy ≤ q.cx + D := by
    by_contra hbal
    exact hnotBad ⟨hbudget, by omega⟩
  have hinv := q.cfg.2
  simp only [BiCfg.doubleLevel] at hnotLow
  simp only [BiCfg.DoubleInv] at hinv
  omega

/-- A complementary live unmasked tick of the small Single-B band is
blank-heavy: the live upper corrected edge plus the `CX` cap bound the
physical level, and `16y < n` leaves the blanks. -/
theorem singleB_blankHeavy_of_notNormal_live_masked
    {n aLoΛ hiΛ D H cxCap : ℕ} (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hnormal : ¬ q.NormalTick)
    (hcx : q.cx < cxCap)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n) :
    3 * n ≤ 8 * q.cfg.1.b := by
  have hnotHigh : ¬ (hiΛ + q.cx ≤ q.cfg.1.doubleLevel + q.cy) :=
    fun h => hlive (Or.inr (Or.inl h))
  unfold SingleLedger.NormalTick at hnormal
  have hinv := q.cfg.2
  simp only [BiCfg.doubleLevel] at hnotHigh
  simp only [BiCfg.DoubleInv] at hinv
  omega

/-! ### Drift inequalities -/

/-- Doubled-scale direction cross bound: gap `g` and `y ≤ n` give
`(2n+g)·y ≤ 2n·x`. -/
theorem singleB_blank_direction_guard {n g : ℕ} (q : SingleLedger n)
    (hgap : q.cfg.1.y + g ≤ q.cfg.1.x) :
    (2 * n + g) * q.cfg.1.y ≤ (2 * n) * q.cfg.1.x := by
  have hy : q.cfg.1.y ≤ n := by
    have hinv := q.cfg.2
    simp only [BiCfg.DoubleInv] at hinv
    omega
  nlinarith [Nat.mul_le_mul_left (2 * n) hgap, Nat.mul_le_mul_left g hy]

/-- The direction ratio on every Single-B state with gap at least `g`. -/
theorem singleResolveDown_le_up_mul_blankW {n g : ℕ} (q : SingleLedger n)
    (hn : 0 < n) (hgap : q.cfg.1.y + g ≤ q.cfg.1.x) :
    singleResolveDown q ≤ singleResolveUp q * singleBlankW n g := by
  have hguard := singleB_blank_direction_guard (g := g) q hgap
  have h := single_dir_guard_ratio (p := 2 * n) (qRat := 2 * n + g) q
    (by omega) hguard
  simpa [singleBlankW, heavyBlankW] using h

/-- Blank-heavy drift cross bound over the ambient denominator. -/
theorem singleB_blank_drift_cross {n x y b g : ℕ}
    (hinv : x + y + b = n)
    (hgap : y + g ≤ x)
    (hblank : 3 * n ≤ 8 * b) :
    Nat.choose n 2 * g + 2 * n * (y * b) ≤ 2 * n * (x * b) := by
  have hchoose := two_mul_choose_two n
  have h1 : n - 1 ≤ 4 * b := by omega
  have h2 : n * (n - 1) ≤ n * (4 * b) := Nat.mul_le_mul_left n h1
  have hCb : Nat.choose n 2 ≤ 2 * (n * b) := by nlinarith
  have hCg : Nat.choose n 2 * g ≤ 2 * (n * b) * g :=
    Nat.mul_le_mul_right g hCb
  calc
    Nat.choose n 2 * g + 2 * n * (y * b)
        ≤ 2 * (n * b) * g + 2 * n * (y * b) :=
      Nat.add_le_add_right hCg _
    _ = 2 * n * (b * (y + g)) := by ring
    _ ≤ 2 * n * (b * x) :=
      Nat.mul_le_mul_left (2 * n) (Nat.mul_le_mul_left b hgap)
    _ = 2 * n * (x * b) := by ring

/-- Single-B blank-heavy resolution drift, without `ℝ≥0∞` subtraction. -/
theorem singleResolve_blank_drift {n g : ℕ} (hn : 2 ≤ n)
    (q : SingleLedger n)
    (hgap : q.cfg.1.y + g ≤ q.cfg.1.x)
    (hblank : 3 * n ≤ 8 * q.cfg.1.b) :
    singleResolveDown q + singleBlankDrift n g ≤ singleResolveUp q := by
  have hcross := singleB_blank_drift_cross q.cfg.2 hgap hblank
  have hchoose : 0 < Nat.choose n 2 := Nat.choose_pos hn
  have hchooseR : 0 < (Nat.choose n 2 : ℝ) := by exact_mod_cast hchoose
  have h2nR : 0 < ((2 * n : ℕ) : ℝ) := by
    have : 0 < 2 * n := by omega
    exact_mod_cast this
  have hcrossR :
      ((2 * n : ℕ) : ℝ) * (q.cfg.1.y * q.cfg.1.b) +
          (Nat.choose n 2 : ℝ) * g ≤
        ((2 * n : ℕ) : ℝ) * (q.cfg.1.x * q.cfg.1.b) := by
    have h : (Nat.choose n 2 : ℝ) * g +
        ((2 * n : ℕ) : ℝ) * (q.cfg.1.y * q.cfg.1.b) ≤
        ((2 * n : ℕ) : ℝ) * (q.cfg.1.x * q.cfg.1.b) := by
      exact_mod_cast hcross
    linarith
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  have h2n0 : ((2 * n : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n ≠ 0)
  have hdownTop : singleResolveDown q ≠ ⊤ := by
    unfold singleResolveDown
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hupTop : singleResolveUp q ≠ ⊤ := by
    unfold singleResolveUp
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hdTop : singleBlankDrift n g ≠ ⊤ := by
    unfold singleBlankDrift heavyBlankDrift
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h2n0
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨hdownTop, hdTop⟩) hupTop]
  unfold singleResolveDown singleResolveUp singleBlankDrift heavyBlankDrift
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hCR : ((Nat.choose n 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2nR' : ((2 * n : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    (↑(q.cfg.1.y * q.cfg.1.b) : ℝ) / ↑(Nat.choose n 2) + ↑g / ↑(2 * n)
        = (↑(2 * n) * ↑(q.cfg.1.y * q.cfg.1.b) +
            ↑(Nat.choose n 2) * ↑g) /
            (↑(2 * n) * ↑(Nat.choose n 2)) := by
          field_simp
    _ ≤ (↑(2 * n) * ↑(q.cfg.1.x * q.cfg.1.b)) /
          (↑(2 * n) * ↑(Nat.choose n 2)) := by
      apply (div_le_div_iff_of_pos_right (mul_pos h2nR hchooseR)).2
      push_cast at hcrossR ⊢
      linarith
    _ = (↑(q.cfg.1.x * q.cfg.1.b) : ℝ) / ↑(Nat.choose n 2) := by
      rw [mul_div_mul_left _ _ h2nR']

/-! ### The masked corrected-level potential -/

/-- Corrected-level/blank-occupation potential, masked by the `CX` cap.  The
level part is `singleTheta w v 1 = w^(2x+b+CY) · v^CX`, which represents
`w^Λ` subtraction-free whenever `w·v = 1`. -/
noncomputable def singleBlankMaskedV {n : ℕ} (cxCap : ℕ) (w v η : ℝ≥0∞)
    (q : SingleClockTrace n) : ℝ≥0∞ :=
  if cxCap ≤ q.core.cx then 0
  else singleTheta w v 1 q.core * η ^ q.blankTicks

/-- Exact three-mass expansion of the raw corrected-level blank potential at a
live tick. -/
theorem singleClockBandStep_expect_blankRaw
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (q : SingleClockTrace n) (w v η : ℝ≥0∞) (a : ℕ)
    (h2 : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q.core)
    (hL : q.core.CorrectedLevel (a + 1))
    (hwv : w * v = 1) :
    expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
        (fun z => singleTheta w v 1 z.core * η ^ z.blankTicks)
      = (if q.core.NormalTick then 1 else η) *
          (singleResolveDown q.core * w ^ a
            + singleNeutralMass q.core h2 * w ^ (a + 1)
            + singleResolveUp q.core * w ^ (a + 2)) * η ^ q.blankTicks := by
  have key : ∀ k ∈ (Finset.univ : Finset SingleComp),
      singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
          (singleTheta w v 1 (SingleComp.nextSingleClockTrace q k).core *
            η ^ (SingleComp.nextSingleClockTrace q k).blankTicks)
        = ((if q.core.NormalTick then 1 else η) * η ^ q.blankTicks) *
            (singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
              singleTheta w v 1 (SingleComp.nextSingleLedger q.core k)) := by
    intro k _
    by_cases hw :
        SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleClockTrace
      rw [dif_neg hw]
      by_cases hnormal : q.core.NormalTick
      · simp only [hnormal, if_true, add_zero]
        ring
      · simp only [hnormal, if_false]
        rw [pow_succ]
        ring
  have hexp :
      expect (singleLedgerStep n hn q.core) (singleTheta w v 1)
        = singleResolveDown q.core *
            (w ^ a * (1 : ℝ≥0∞) ^ (q.core.rx + q.core.ry + 1))
          + singleNeutralMass q.core h2 *
            (w ^ (a + 1) * (1 : ℝ≥0∞) ^ (q.core.rx + q.core.ry))
          + singleResolveUp q.core *
            (w ^ (a + 2) * (1 : ℝ≥0∞) ^ (q.core.rx + q.core.ry + 1)) :=
    singleLedgerStep_theta_expect n hn q.core a hL w v 1 hwv
  have hstep :
      expect (singleLedgerStep n hn q.core) (singleTheta w v 1)
        = ∑ k : SingleComp,
            singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
              singleTheta w v 1 (SingleComp.nextSingleLedger q.core k) := by
    unfold singleLedgerStep
    rw [expect_map, expect_fintype]
  rw [expect_singleClockBandStep_live n hn aLoΛ hiΛ D H q hlive _ h2]
  calc
    (∑ k : SingleComp,
        singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
          (singleTheta w v 1 (SingleComp.nextSingleClockTrace q k).core *
            η ^ (SingleComp.nextSingleClockTrace q k).blankTicks))
        = ∑ k : SingleComp,
            ((if q.core.NormalTick then 1 else η) * η ^ q.blankTicks) *
              (singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b
                  h2 k *
                singleTheta w v 1 (SingleComp.nextSingleLedger q.core k)) :=
      Finset.sum_congr rfl key
    _ = ((if q.core.NormalTick then 1 else η) * η ^ q.blankTicks) *
          ∑ k : SingleComp,
            singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
              singleTheta w v 1 (SingleComp.nextSingleLedger q.core k) :=
      (Finset.mul_sum _ _ _).symm
    _ = ((if q.core.NormalTick then 1 else η) * η ^ q.blankTicks) *
          (singleResolveDown q.core *
              (w ^ a * (1 : ℝ≥0∞) ^ (q.core.rx + q.core.ry + 1))
            + singleNeutralMass q.core h2 *
              (w ^ (a + 1) * (1 : ℝ≥0∞) ^ (q.core.rx + q.core.ry))
            + singleResolveUp q.core *
              (w ^ (a + 2) * (1 : ℝ≥0∞) ^ (q.core.rx + q.core.ry + 1))) := by
      rw [← hstep, hexp]
    _ = (if q.core.NormalTick then 1 else η) *
          (singleResolveDown q.core * w ^ a
            + singleNeutralMass q.core h2 * w ^ (a + 1)
            + singleResolveUp q.core * w ^ (a + 2)) * η ^ q.blankTicks := by
      simp only [one_pow, mul_one]
      ring

/-- The masked corrected-level blank potential is a one-step supermartingale
on the repaired stopped Single-B band. -/
theorem singleClockBandStep_blank_super
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n) :
    ∀ q : SingleClockTrace n,
      expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
          (singleBlankMaskedV cxCap
            (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g)) ≤
        singleBlankMaskedV cxCap
          (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) q := by
  intro q
  have hn0 : 0 < n := by omega
  have hwv : singleBlankW n g * singleBlankV n g = 1 :=
    singleBlankW_mul_V n g hn0
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q.core
  · unfold singleClockBandStep
    rw [if_pos hB, expect_pure]
  · by_cases hmask : cxCap ≤ q.core.cx
    · have hzero :
          expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
            (singleBlankMaskedV cxCap
              (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g))
            = 0 := by
        unfold expect
        rw [ENNReal.tsum_eq_zero]
        intro z
        by_cases hz : singleClockBandStep n hn aLoΛ hiΛ D H q z = 0
        · simp [hz]
        · have hmono :=
            singleClockBandStep_cx_mono_of_apply_ne_zero hn aLoΛ hiΛ D H
              q z hz
          have hzmask : cxCap ≤ z.core.cx := le_trans hmask hmono
          simp [singleBlankMaskedV, hzmask]
      rw [hzero]
      exact bot_le
    · have hcx : q.core.cx < cxCap := Nat.lt_of_not_ge hmask
      have h2 := single_two_entities hn q.core
      have hnotLow :
          ¬ (q.core.cfg.1.doubleLevel + q.core.cy ≤ aLoΛ + q.core.cx) :=
        fun h => hB (Or.inl h)
      obtain ⟨a, ha⟩ :
          ∃ a, q.core.cfg.1.doubleLevel + q.core.cy = (a + 1) + q.core.cx :=
        ⟨q.core.cfg.1.doubleLevel + q.core.cy - q.core.cx - 1, by omega⟩
      have hL : q.core.CorrectedLevel (a + 1) := ha
      have hVle : ∀ z : SingleClockTrace n,
          singleBlankMaskedV cxCap
              (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) z ≤
            singleTheta (singleBlankW n g) (singleBlankV n g) 1 z.core *
              singleBlankEta n g ^ z.blankTicks := by
        intro z
        unfold singleBlankMaskedV
        split_ifs
        · exact bot_le
        · exact le_rfl
      have hEle :
          expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
              (singleBlankMaskedV cxCap
                (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g)) ≤
            expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
              (fun z =>
                singleTheta (singleBlankW n g) (singleBlankV n g) 1 z.core *
                  singleBlankEta n g ^ z.blankTicks) := by
        unfold expect
        refine ENNReal.tsum_le_tsum fun z => ?_
        gcongr
        exact hVle z
      have hbridge := singleClockBandStep_expect_blankRaw n hn aLoΛ hiΛ D H
        q (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) a
        h2 hB hL hwv
      -- scalar facts
      have hsum := single_mass_sum q.core h2
      have hgapPhys : q.core.cfg.1.y + g ≤ q.core.cfg.1.x :=
        singleB_live_gap q.core hB hgap
      have hchoose : 0 < Nat.choose n 2 := Nat.choose_pos hn
      have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast hchoose.ne'
      have hdt : singleResolveDown q.core ≠ ⊤ := by
        unfold singleResolveDown
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
      have hut : singleResolveUp q.core ≠ ⊤ := by
        unfold singleResolveUp
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
      have hnt : singleNeutralMass q.core h2 ≠ ⊤ := by
        intro ht
        rw [ht] at hsum
        simp at hsum
      have hwt : singleBlankW n g ≠ ⊤ := by
        unfold singleBlankW heavyBlankW
        finiteness
      have hrt : singleBlankR n g ≠ ⊤ := by
        unfold singleBlankR heavyBlankR
        finiteness
      have hddt : singleBlankDrift n g ≠ ⊤ := by
        unfold singleBlankDrift heavyBlankDrift
        finiteness
      have hwr := singleBlankW_add_R n g hn0
      have hrd : singleBlankR n g ≤
          singleBlankW n g * singleBlankDrift n g :=
        (singleBlank_R_eq_W_mul_drift n g hn0).le
      have hw1 : singleBlankW n g ≤ 1 := singleBlankW_le_one n g hn0
      have hfactor :
          (if q.core.NormalTick then 1 else singleBlankEta n g) *
              (singleResolveDown q.core +
                singleNeutralMass q.core h2 * singleBlankW n g +
                singleResolveUp q.core * singleBlankW n g ^ 2) ≤
            singleBlankW n g := by
        by_cases hnormal : q.core.NormalTick
        · rw [if_pos hnormal, one_mul]
          exact feller_reduced
            (singleResolveDown q.core)
            (singleNeutralMass q.core h2)
            (singleResolveUp q.core)
            (singleBlankW n g)
            hsum
            (singleResolveDown_le_up_mul_blankW q.core hn0 hgapPhys)
            hw1 hdt hnt hut
        · rw [if_neg hnormal]
          have hblank : 3 * n ≤ 8 * q.core.cfg.1.b :=
            singleB_blankHeavy_of_notNormal_live_masked q.core hB hnormal
              hcx hsmall
          have hdrift :=
            singleResolve_blank_drift hn q.core hgapPhys hblank
          have hEta :
              singleBlankEta n g = 1 + singleBlankR n g ^ 2 / 2 := rfl
          rw [hEta]
          exact heavy_blank_three_term_eta hsum hdrift hwr hrd
            hdt hnt hut hddt hwt hrt
      refine le_trans hEle ?_
      rw [hbridge]
      have hVq :
          singleBlankMaskedV cxCap
              (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) q
            = singleBlankW n g ^ (a + 1) *
                singleBlankEta n g ^ q.blankTicks := by
        unfold singleBlankMaskedV
        rw [if_neg hmask,
          singleTheta_of_correctedLevel (singleBlankW n g)
            (singleBlankV n g) 1 q.core hL hwv]
        simp
      rw [hVq]
      calc
        (if q.core.NormalTick then 1 else singleBlankEta n g) *
              (singleResolveDown q.core * singleBlankW n g ^ a
                + singleNeutralMass q.core h2 * singleBlankW n g ^ (a + 1)
                + singleResolveUp q.core * singleBlankW n g ^ (a + 2)) *
              singleBlankEta n g ^ q.blankTicks
            = (singleBlankW n g ^ a *
                singleBlankEta n g ^ q.blankTicks) *
                ((if q.core.NormalTick then 1 else singleBlankEta n g) *
                  (singleResolveDown q.core +
                    singleNeutralMass q.core h2 * singleBlankW n g +
                    singleResolveUp q.core * singleBlankW n g ^ 2)) := by
              rw [pow_succ (singleBlankW n g) a,
                show a + 2 = (a + 1) + 1 by omega,
                pow_succ (singleBlankW n g) (a + 1),
                pow_succ (singleBlankW n g) a]
              ring
        _ ≤ (singleBlankW n g ^ a *
                singleBlankEta n g ^ q.blankTicks) * singleBlankW n g := by
          gcongr
        _ = singleBlankW n g ^ (a + 1) *
              singleBlankEta n g ^ q.blankTicks := by
          rw [pow_succ]
          ring

/-- Finite-horizon upper tail for blank-heavy occupation on live unmasked
endpoints of the stopped Single-B band. -/
theorem singleClock_blank_tail
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n)
    (T Hocc : ℕ) (q₀ : SingleClockTrace n) :
    ∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
          Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
      singleBlankMaskedV cxCap
          (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) q₀ /
        (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc) := by
  have hn0 : 0 < n := by omega
  have hwv := singleBlankW_mul_V n g hn0
  have hw1 : singleBlankW n g ≤ 1 := singleBlankW_le_one n g hn0
  have hw0 : singleBlankW n g ≠ 0 := by
    unfold singleBlankW heavyBlankW
    exact ne_of_gt (ENNReal.div_pos
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
      (ENNReal.natCast_ne_top _))
  have hwt : singleBlankW n g ≠ ⊤ := by
    unfold singleBlankW heavyBlankW
    finiteness
  have hη1 : 1 ≤ singleBlankEta n g := by
    unfold singleBlankEta heavyBlankEta
    exact le_add_right le_rfl
  have hη0 : singleBlankEta n g ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hη1)
  have hηt : singleBlankEta n g ≠ ⊤ := by
    unfold singleBlankEta heavyBlankEta heavyBlankR
    finiteness
  have hθ0 :
      singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hη0)
  have hθt :
      singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top hηt)
  have hsub : ∀ z : SingleClockTrace n,
      (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
        (if singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc ≤
              singleBlankMaskedV cxCap
                (singleBlankW n g) (singleBlankV n g)
                (singleBlankEta n g) z then
            iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) := by
    intro z
    by_cases hz : (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
        Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap
    · have hnotHigh :
          ¬ (hiΛ + z.core.cx ≤ z.core.cfg.1.doubleLevel + z.core.cy) :=
        fun h => hz.1 (Or.inr (Or.inl h))
      have hcorr :
          z.core.cfg.1.doubleLevel + z.core.cy ≤ hiΛ + z.core.cx := by
        omega
      have hwPow :
          singleBlankW n g ^ hiΛ ≤
            singleTheta (singleBlankW n g) (singleBlankV n g) 1 z.core := by
        have h := singleTheta_lower_of_corrected_le
          (thr := hiΛ) (M := 0)
          (singleBlankW n g) (singleBlankV n g) 1 hwv hw1 le_rfl
          z.core hcorr (Nat.zero_le _)
        simpa using h
      have hηPow :
          singleBlankEta n g ^ Hocc ≤
            singleBlankEta n g ^ z.blankTicks :=
        pow_le_pow_right₀ hη1 hz.2.1
      have hpot :
          singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc ≤
            singleBlankMaskedV cxCap
              (singleBlankW n g) (singleBlankV n g)
              (singleBlankEta n g) z := by
        unfold singleBlankMaskedV
        rw [if_neg (Nat.not_le.mpr hz.2.2)]
        exact mul_le_mul hwPow hηPow bot_le bot_le
      simp only [hz, if_true, hpot]
      simp
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀)
      (singleBlankMaskedV cxCap
        (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g))
      (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc)
      hθ0 hθt) ?_
  exact ENNReal.div_le_div_right
    (by
      simpa using
        (expect_iter_le
          (singleClockBandStep n hn aLoΛ hiΛ D H)
          (singleBlankMaskedV cxCap
            (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g))
          1
          (by
            simpa using
              singleClockBandStep_blank_super n hn aLoΛ hiΛ D H g cxCap
                hgap hsmall)
          T q₀))
    (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc)

section Inhabitation

example :
    3 * 160 ≤ 8 *
      (⟨⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
          SingleLedger 160).cfg.1.b := by
  apply singleB_blankHeavy_of_notNormal_live_masked
      (aLoΛ := 166) (hiΛ := 168) (D := 5) (H := 20737) (cxCap := 12)
  · norm_num [SingleBandFrozen, BiCfg.doubleLevel, CreationBadY,
      singleCreationBoundary]
  · norm_num [SingleLedger.NormalTick]
  · norm_num
  · norm_num

example :
    singleResolveDown
        (⟨⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
          SingleLedger 160) +
        singleBlankDrift 160 2 ≤
      singleResolveUp
        (⟨⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
          SingleLedger 160) := by
  apply singleResolve_blank_drift
  · norm_num
  · norm_num
  · norm_num

example :
    ∀ q : SingleClockTrace 160,
      expect (singleClockBandStep 160 (by norm_num) 166 168 5 20737 q)
          (singleBlankMaskedV 12
            (singleBlankW 160 2) (singleBlankV 160 2)
            (singleBlankEta 160 2)) ≤
        singleBlankMaskedV 12
          (singleBlankW 160 2) (singleBlankV 160 2)
          (singleBlankEta 160 2) q := by
  apply singleClockBandStep_blank_super
  · norm_num
  · norm_num

end Inhabitation

end Tri

#print axioms Tri.singleBlankW_mul_V
#print axioms Tri.singleB_live_gap
#print axioms Tri.singleB_blankHeavy_of_notNormal_live_masked
#print axioms Tri.singleB_blank_direction_guard
#print axioms Tri.singleResolveDown_le_up_mul_blankW
#print axioms Tri.singleB_blank_drift_cross
#print axioms Tri.singleResolve_blank_drift
#print axioms Tri.singleClockBandStep_expect_blankRaw
#print axioms Tri.singleClockBandStep_blank_super
#print axioms Tri.singleClock_blank_tail

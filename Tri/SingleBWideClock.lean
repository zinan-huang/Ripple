/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBClockConstants

/-!
# The wide blank branch of the Single-B occupation clock

The narrow blank branch (`Tri/SingleBClockBlank.lean`) certifies
blank-heaviness `3n ≤ 8b` from `8·(hiΛ + cxCap) ≤ 9n`.  With the `CX` cap
anchored at the entry `Y` count, that smallness constraint forces
`y₀ ≲ n/8`, which fails for every early-phase state (`y₀ ≈ n/2`).

This file widens the branch: the mask constraint is relaxed to
`4·(hiΛ + cxCap) ≤ 7n`, which certifies only `n ≤ 8b`; the drift then runs
at the doubled-again scale — geometric base `singleBlankW (2n) g`, drift
quantum `g/(4n)`, multiplier `singleBlankEta (2n) g` — because
`C(n,2) ≤ 4nb` needs only `n-1 ≤ 8b`.  The blank occupation envelope
becomes `exp(-g²/(4n))`, at the price of a doubled half-horizon
`128·(n+2M)`.  Since `y₀ ≤ (n-G)/2 ≤ n/2` holds on every gap-form
checkpoint, the wide mask constraint is satisfiable with `cxCap = n/2 + M`
whenever `G/2 + g + M ≤ n/4` — the whole early and middle gap range.
-/

namespace Tri

open scoped ENNReal

/-! ## Wide blank-heaviness -/

/-- A complementary live unmasked tick of the WIDE Single-B band is still
one-eighth blank. -/
theorem singleB_blankHeavy_wide
    {n aLoΛ hiΛ D H cxCap : ℕ} (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hnormal : ¬ q.NormalTick)
    (hcx : q.cx < cxCap)
    (hsmall : 4 * (hiΛ + cxCap) ≤ 7 * n) :
    n ≤ 8 * q.cfg.1.b := by
  have hnotHigh : ¬ (hiΛ + q.cx ≤ q.cfg.1.doubleLevel + q.cy) :=
    fun h => hlive (Or.inr (Or.inl h))
  unfold SingleLedger.NormalTick at hnormal
  have hinv := q.cfg.2
  simp only [BiCfg.doubleLevel] at hnotHigh
  simp only [BiCfg.DoubleInv] at hinv
  omega

/-! ## Wide drift inequalities -/

/-- Doubled-again direction cross bound. -/
theorem singleB_blank_direction_guard_wide {n g : ℕ} (q : SingleLedger n)
    (hgap : q.cfg.1.y + g ≤ q.cfg.1.x) :
    (2 * (2 * n) + g) * q.cfg.1.y ≤ (2 * (2 * n)) * q.cfg.1.x := by
  have hy : q.cfg.1.y ≤ n := by
    have hinv := q.cfg.2
    simp only [BiCfg.DoubleInv] at hinv
    omega
  nlinarith [Nat.mul_le_mul_left (2 * (2 * n)) hgap,
    Nat.mul_le_mul_left g hy]

/-- The direction ratio at the doubled-again base. -/
theorem singleResolveDown_le_up_mul_wideW {n g : ℕ} (q : SingleLedger n)
    (hn : 0 < n) (hgap : q.cfg.1.y + g ≤ q.cfg.1.x) :
    singleResolveDown q ≤ singleResolveUp q * singleBlankW (2 * n) g := by
  have hguard := singleB_blank_direction_guard_wide (g := g) q hgap
  have h := single_dir_guard_ratio (p := 2 * (2 * n))
    (qRat := 2 * (2 * n) + g) q (by omega) hguard
  simpa [singleBlankW, heavyBlankW] using h

/-- Wide blank drift cross bound: an eighth of blank suffices at quantum
`g/(4n)`. -/
theorem singleB_blank_drift_cross_wide {n x y b g : ℕ}
    (hinv : x + y + b = n)
    (hgap : y + g ≤ x)
    (hblank : n ≤ 8 * b) :
    Nat.choose n 2 * g + 2 * (2 * n) * (y * b) ≤
      2 * (2 * n) * (x * b) := by
  have hchoose := two_mul_choose_two n
  have h1 : n - 1 ≤ 8 * b := by omega
  have h2 : n * (n - 1) ≤ n * (8 * b) := Nat.mul_le_mul_left n h1
  have hCb : Nat.choose n 2 ≤ 4 * (n * b) := by nlinarith
  have hCg : Nat.choose n 2 * g ≤ 4 * (n * b) * g :=
    Nat.mul_le_mul_right g hCb
  calc
    Nat.choose n 2 * g + 2 * (2 * n) * (y * b)
        ≤ 4 * (n * b) * g + 2 * (2 * n) * (y * b) :=
      Nat.add_le_add_right hCg _
    _ = 2 * (2 * n) * (b * (y + g)) := by ring
    _ ≤ 2 * (2 * n) * (b * x) :=
      Nat.mul_le_mul_left (2 * (2 * n)) (Nat.mul_le_mul_left b hgap)
    _ = 2 * (2 * n) * (x * b) := by ring

/-- Wide Single-B blank-heavy resolution drift. -/
theorem singleResolve_blank_drift_wide {n g : ℕ} (hn : 2 ≤ n)
    (q : SingleLedger n)
    (hgap : q.cfg.1.y + g ≤ q.cfg.1.x)
    (hblank : n ≤ 8 * q.cfg.1.b) :
    singleResolveDown q + singleBlankDrift (2 * n) g ≤
      singleResolveUp q := by
  have hcross := singleB_blank_drift_cross_wide q.cfg.2 hgap hblank
  have hchoose : 0 < Nat.choose n 2 := Nat.choose_pos hn
  have hchooseR : 0 < (Nat.choose n 2 : ℝ) := by exact_mod_cast hchoose
  have h4nR : 0 < ((2 * (2 * n) : ℕ) : ℝ) := by
    have : 0 < 2 * (2 * n) := by omega
    exact_mod_cast this
  have hcrossR :
      ((2 * (2 * n) : ℕ) : ℝ) * (q.cfg.1.y * q.cfg.1.b) +
          (Nat.choose n 2 : ℝ) * g ≤
        ((2 * (2 * n) : ℕ) : ℝ) * (q.cfg.1.x * q.cfg.1.b) := by
    have h : (Nat.choose n 2 : ℝ) * g +
        ((2 * (2 * n) : ℕ) : ℝ) * (q.cfg.1.y * q.cfg.1.b) ≤
        ((2 * (2 * n) : ℕ) : ℝ) * (q.cfg.1.x * q.cfg.1.b) := by
      exact_mod_cast hcross
    linarith
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  have h4n0 : ((2 * (2 * n) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : 2 * (2 * n) ≠ 0)
  have hdownTop : singleResolveDown q ≠ ⊤ := by
    unfold singleResolveDown
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hupTop : singleResolveUp q ≠ ⊤ := by
    unfold singleResolveUp
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hdTop : singleBlankDrift (2 * n) g ≠ ⊤ := by
    unfold singleBlankDrift heavyBlankDrift
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h4n0
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨hdownTop, hdTop⟩) hupTop]
  unfold singleResolveDown singleResolveUp singleBlankDrift heavyBlankDrift
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  calc
    (↑(q.cfg.1.y * q.cfg.1.b) : ℝ) / ↑(Nat.choose n 2) +
          ↑g / ↑(2 * (2 * n))
        = (↑(2 * (2 * n)) * ↑(q.cfg.1.y * q.cfg.1.b) +
            ↑(Nat.choose n 2) * ↑g) /
            (↑(2 * (2 * n)) * ↑(Nat.choose n 2)) := by
          field_simp
    _ ≤ (↑(2 * (2 * n)) * ↑(q.cfg.1.x * q.cfg.1.b)) /
          (↑(2 * (2 * n)) * ↑(Nat.choose n 2)) := by
      apply (div_le_div_iff_of_pos_right (mul_pos h4nR hchooseR)).2
      push_cast at hcrossR ⊢
      linarith
    _ = (↑(q.cfg.1.x * q.cfg.1.b) : ℝ) / ↑(Nat.choose n 2) := by
      rw [mul_div_mul_left _ _ (by positivity : ((2 * (2 * n) : ℕ) : ℝ) ≠ 0)]

/-! ## The wide masked supermartingale and tail -/

/-- The wide masked corrected-level blank potential is a one-step
supermartingale on the repaired stopped Single-B band. -/
theorem singleClockBandStep_blank_super_wide
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 4 * (hiΛ + cxCap) ≤ 7 * n) :
    ∀ q : SingleClockTrace n,
      expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
          (singleBlankMaskedV cxCap
            (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
            (singleBlankEta (2 * n) g)) ≤
        singleBlankMaskedV cxCap
          (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
          (singleBlankEta (2 * n) g) q := by
  intro q
  have hn0 : 0 < n := by omega
  have h2n0 : 0 < 2 * n := by omega
  have hwv : singleBlankW (2 * n) g * singleBlankV (2 * n) g = 1 :=
    singleBlankW_mul_V (2 * n) g h2n0
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q.core
  · unfold singleClockBandStep
    rw [if_pos hB, expect_pure]
  · by_cases hmask : cxCap ≤ q.core.cx
    · have hzero :
          expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
            (singleBlankMaskedV cxCap
              (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
              (singleBlankEta (2 * n) g))
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
              (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
              (singleBlankEta (2 * n) g) z ≤
            singleTheta (singleBlankW (2 * n) g)
                (singleBlankV (2 * n) g) 1 z.core *
              singleBlankEta (2 * n) g ^ z.blankTicks := by
        intro z
        unfold singleBlankMaskedV
        split_ifs
        · exact bot_le
        · exact le_rfl
      have hEle :
          expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
              (singleBlankMaskedV cxCap
                (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
                (singleBlankEta (2 * n) g)) ≤
            expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
              (fun z =>
                singleTheta (singleBlankW (2 * n) g)
                    (singleBlankV (2 * n) g) 1 z.core *
                  singleBlankEta (2 * n) g ^ z.blankTicks) := by
        unfold expect
        refine ENNReal.tsum_le_tsum fun z => ?_
        gcongr
        exact hVle z
      have hbridge := singleClockBandStep_expect_blankRaw n hn aLoΛ hiΛ D H
        q (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
        (singleBlankEta (2 * n) g) a h2 hB hL hwv
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
      have hwt : singleBlankW (2 * n) g ≠ ⊤ := by
        unfold singleBlankW heavyBlankW
        finiteness
      have hrt : singleBlankR (2 * n) g ≠ ⊤ := by
        unfold singleBlankR heavyBlankR
        finiteness
      have hddt : singleBlankDrift (2 * n) g ≠ ⊤ := by
        unfold singleBlankDrift heavyBlankDrift
        finiteness
      have hwr := singleBlankW_add_R (2 * n) g h2n0
      have hrd : singleBlankR (2 * n) g ≤
          singleBlankW (2 * n) g * singleBlankDrift (2 * n) g :=
        (singleBlank_R_eq_W_mul_drift (2 * n) g h2n0).le
      have hw1 : singleBlankW (2 * n) g ≤ 1 :=
        singleBlankW_le_one (2 * n) g h2n0
      have hfactor :
          (if q.core.NormalTick then 1 else singleBlankEta (2 * n) g) *
              (singleResolveDown q.core +
                singleNeutralMass q.core h2 * singleBlankW (2 * n) g +
                singleResolveUp q.core * singleBlankW (2 * n) g ^ 2) ≤
            singleBlankW (2 * n) g := by
        by_cases hnormal : q.core.NormalTick
        · rw [if_pos hnormal, one_mul]
          exact feller_reduced
            (singleResolveDown q.core)
            (singleNeutralMass q.core h2)
            (singleResolveUp q.core)
            (singleBlankW (2 * n) g)
            hsum
            (singleResolveDown_le_up_mul_wideW q.core hn0 hgapPhys)
            hw1 hdt hnt hut
        · rw [if_neg hnormal]
          have hblank : n ≤ 8 * q.core.cfg.1.b :=
            singleB_blankHeavy_wide q.core hB hnormal hcx hsmall
          have hdrift :=
            singleResolve_blank_drift_wide hn q.core hgapPhys hblank
          have hEta :
              singleBlankEta (2 * n) g =
                1 + singleBlankR (2 * n) g ^ 2 / 2 := rfl
          rw [hEta]
          exact heavy_blank_three_term_eta hsum hdrift hwr hrd
            hdt hnt hut hddt hwt hrt
      refine le_trans hEle ?_
      rw [hbridge]
      have hVq :
          singleBlankMaskedV cxCap
              (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
              (singleBlankEta (2 * n) g) q
            = singleBlankW (2 * n) g ^ (a + 1) *
                singleBlankEta (2 * n) g ^ q.blankTicks := by
        unfold singleBlankMaskedV
        rw [if_neg hmask,
          singleTheta_of_correctedLevel (singleBlankW (2 * n) g)
            (singleBlankV (2 * n) g) 1 q.core hL hwv]
        simp
      rw [hVq]
      calc
        (if q.core.NormalTick then 1 else singleBlankEta (2 * n) g) *
              (singleResolveDown q.core * singleBlankW (2 * n) g ^ a
                + singleNeutralMass q.core h2 *
                    singleBlankW (2 * n) g ^ (a + 1)
                + singleResolveUp q.core *
                    singleBlankW (2 * n) g ^ (a + 2)) *
              singleBlankEta (2 * n) g ^ q.blankTicks
            = (singleBlankW (2 * n) g ^ a *
                singleBlankEta (2 * n) g ^ q.blankTicks) *
                ((if q.core.NormalTick then 1
                    else singleBlankEta (2 * n) g) *
                  (singleResolveDown q.core +
                    singleNeutralMass q.core h2 *
                      singleBlankW (2 * n) g +
                    singleResolveUp q.core *
                      singleBlankW (2 * n) g ^ 2)) := by
              rw [pow_succ (singleBlankW (2 * n) g) a,
                show a + 2 = (a + 1) + 1 by omega,
                pow_succ (singleBlankW (2 * n) g) (a + 1),
                pow_succ (singleBlankW (2 * n) g) a]
              ring
        _ ≤ (singleBlankW (2 * n) g ^ a *
                singleBlankEta (2 * n) g ^ q.blankTicks) *
              singleBlankW (2 * n) g := by
          gcongr
        _ = singleBlankW (2 * n) g ^ (a + 1) *
              singleBlankEta (2 * n) g ^ q.blankTicks := by
          rw [pow_succ]
          ring

/-- Finite-horizon upper tail for wide blank-heavy occupation. -/
theorem singleClock_blank_tail_wide
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 4 * (hiΛ + cxCap) ≤ 7 * n)
    (T Hocc : ℕ) (q₀ : SingleClockTrace n) :
    ∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
          Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
      singleBlankMaskedV cxCap
          (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
          (singleBlankEta (2 * n) g) q₀ /
        (singleBlankW (2 * n) g ^ hiΛ *
          singleBlankEta (2 * n) g ^ Hocc) := by
  have h2n0 : 0 < 2 * n := by omega
  have hwv := singleBlankW_mul_V (2 * n) g h2n0
  have hw1 : singleBlankW (2 * n) g ≤ 1 :=
    singleBlankW_le_one (2 * n) g h2n0
  have hw0 : singleBlankW (2 * n) g ≠ 0 := by
    unfold singleBlankW heavyBlankW
    exact ne_of_gt (ENNReal.div_pos
      (by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega)
      (ENNReal.natCast_ne_top _))
  have hwt : singleBlankW (2 * n) g ≠ ⊤ := by
    unfold singleBlankW heavyBlankW
    finiteness
  have hη1 : 1 ≤ singleBlankEta (2 * n) g := by
    unfold singleBlankEta heavyBlankEta
    exact le_add_right le_rfl
  have hη0 : singleBlankEta (2 * n) g ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hη1)
  have hηt : singleBlankEta (2 * n) g ≠ ⊤ := by
    unfold singleBlankEta heavyBlankEta heavyBlankR
    finiteness
  have hθ0 :
      singleBlankW (2 * n) g ^ hiΛ *
          singleBlankEta (2 * n) g ^ Hocc ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hη0)
  have hθt :
      singleBlankW (2 * n) g ^ hiΛ *
          singleBlankEta (2 * n) g ^ Hocc ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top hηt)
  have hsub : ∀ z : SingleClockTrace n,
      (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
        (if singleBlankW (2 * n) g ^ hiΛ *
              singleBlankEta (2 * n) g ^ Hocc ≤
              singleBlankMaskedV cxCap
                (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
                (singleBlankEta (2 * n) g) z then
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
          singleBlankW (2 * n) g ^ hiΛ ≤
            singleTheta (singleBlankW (2 * n) g)
              (singleBlankV (2 * n) g) 1 z.core := by
        have h := singleTheta_lower_of_corrected_le
          (thr := hiΛ) (M := 0)
          (singleBlankW (2 * n) g) (singleBlankV (2 * n) g) 1 hwv hw1 le_rfl
          z.core hcorr (Nat.zero_le _)
        simpa using h
      have hηPow :
          singleBlankEta (2 * n) g ^ Hocc ≤
            singleBlankEta (2 * n) g ^ z.blankTicks :=
        pow_le_pow_right₀ hη1 hz.2.1
      have hpot :
          singleBlankW (2 * n) g ^ hiΛ *
              singleBlankEta (2 * n) g ^ Hocc ≤
            singleBlankMaskedV cxCap
              (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
              (singleBlankEta (2 * n) g) z := by
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
        (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
        (singleBlankEta (2 * n) g))
      (singleBlankW (2 * n) g ^ hiΛ * singleBlankEta (2 * n) g ^ Hocc)
      hθ0 hθt) ?_
  exact ENNReal.div_le_div_right
    (by
      simpa using
        (expect_iter_le
          (singleClockBandStep n hn aLoΛ hiΛ D H)
          (singleBlankMaskedV cxCap
            (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
            (singleBlankEta (2 * n) g))
          1
          (by
            simpa using
              singleClockBandStep_blank_super_wide n hn aLoΛ hiΛ D H g cxCap
                hgap hsmall)
          T q₀))
    (singleBlankW (2 * n) g ^ hiΛ * singleBlankEta (2 * n) g ^ Hocc)

/-! ## The wide two-branch tail -/

/-- Fixed-horizon wide two-branch Single-B clock. -/
theorem singleClock_twoBranch_tail_wide
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 4 * (hiΛ + cxCap) ≤ 7 * n)
    (T Hocc M K b₀ y₀ : ℕ)
    (hHT : 2 * Hocc ≤ T) (hK : n + 2 * M ≤ K)
    (hcxCap : y₀ + M ≤ cxCap)
    (q₀ : SingleClockTrace n)
    (hq₀ : q₀.FuelClockInv b₀ y₀)
    (hnt0 : q₀.normalTicks = 0) (hbt0 : q₀.blankTicks = 0) :
    ∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
          z.core.rx + z.core.ry < M then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
      maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
        (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
      singleBlankMaskedV cxCap
          (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
          (singleBlankEta (2 * n) g) q₀ /
        (singleBlankW (2 * n) g ^ hiΛ *
          singleBlankEta (2 * n) g ^ Hocc) := by
  have hpoint : ∀ z : SingleClockTrace n,
      (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            z.core.rx + z.core.ry < M then
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
        (if Hocc ≤ z.normalTicks ∧ z.normalFuel ≤ K then
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) +
        (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) := by
    intro z
    by_cases hbad : (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
        z.core.rx + z.core.ry < M
    · by_cases hp : iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z = 0
      · simp [hbad, hp]
      · have hInv :=
          singleClockBand_iter_fuelClockInv hn aLoΛ hiΛ D H q₀ z hq₀ hp
        obtain ⟨hbl, hcy, hfuel⟩ := hInv
        have hticks :=
          singleClockBand_iter_tick_sum_of_final_live hn aLoΛ hiΛ D H
            T q₀ z hp hbad.1
        have hticks' : z.normalTicks + z.blankTicks = T := by
          rw [hnt0, hbt0] at hticks
          simpa using hticks
        have hbl' : z.core.cx + z.core.cy + b₀ =
            z.core.cfg.1.b + z.core.rx + z.core.ry := hbl
        have hcy' : z.core.cfg.1.y + z.core.cx = y₀ + z.core.ry := hcy
        by_cases hblank : Hocc ≤ z.blankTicks
        · have hcxlt : z.core.cx < cxCap := by
            have hres := hbad.2
            omega
          simp [hbad, hblank, hcxlt]
        · have hnormal : Hocc ≤ z.normalTicks := by omega
          have hb : z.core.cfg.1.b ≤ n := by
            have hinv := z.core.cfg.2
            simp only [BiCfg.DoubleInv] at hinv
            omega
          have hfuelK : z.normalFuel ≤ K := by
            have hres := hbad.2
            omega
          simp [hbad, hnormal, hfuelK]
    · simp [hbad]
  calc
    ∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
          z.core.rx + z.core.ry < M then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0)
        ≤ ∑' z,
            ((if Hocc ≤ z.normalTicks ∧ z.normalFuel ≤ K then
                iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) +
              (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
                  Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
                iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z
                  else 0)) :=
      ENNReal.tsum_le_tsum hpoint
    _ =
        (∑' z, (if Hocc ≤ z.normalTicks ∧ z.normalFuel ≤ K then
            iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0)) +
        (∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then
            iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0)) :=
      ENNReal.tsum_add
    _ ≤
        maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
          (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
        singleBlankMaskedV cxCap
            (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
            (singleBlankEta (2 * n) g) q₀ /
          (singleBlankW (2 * n) g ^ hiΛ *
            singleBlankEta (2 * n) g ^ Hocc) := by
      exact add_le_add
        (singleClock_normal_tail_half n hn aLoΛ hiΛ D H
          (by omega) T Hocc K q₀)
        (singleClock_blank_tail_wide n hn aLoΛ hiΛ D H g cxCap
          hgap hsmall T Hocc q₀)

/-- The wide two-branch clock on the repaired stopped Single-B band,
started from a fresh ledger. -/
theorem singleBand_joint_clock_tail_wide
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 4 * (hiΛ + cxCap) ≤ 7 * n)
    (T Hocc M K : ℕ)
    (hHT : 2 * Hocc ≤ T) (hK : n + 2 * M ≤ K)
    (s₀ : SingleState n) (hcxCap : s₀.1.y + M ≤ cxCap) :
    ∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
          q.rx + q.ry < M then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) ≤
      1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
      singleBlankW (2 * n) g ^ s₀.1.doubleLevel /
        (singleBlankW (2 * n) g ^ hiΛ *
          singleBlankEta (2 * n) g ^ Hocc) := by
  let qClock := SingleClockTrace.initial (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
  have hclock :=
    singleClock_twoBranch_tail_wide n hn aLoΛ hiΛ D H g cxCap hgap hsmall
      T Hocc M K s₀.1.b s₀.1.y hHT hK hcxCap qClock
      (SingleClockTrace.initial_fuelClockInv s₀) rfl rfl
  have hproj :
      (∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
            q.rx + q.ry < M then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)) =
        ∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            z.core.rx + z.core.ry < M then
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T qClock z else 0) := by
    simpa [qClock, SingleClockTrace.initial] using
      (singleBand_indicator_eq_clock n hn aLoΛ hiΛ D H T qClock
        (fun q => (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧ q.rx + q.ry < M))
  have hnormPot :
      maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) qClock
        = 1 := by
    simp [maskedCountPotential, qClock, SingleClockTrace.initial]
  have hblankPot :
      singleBlankMaskedV cxCap
          (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
          (singleBlankEta (2 * n) g) qClock
        ≤ singleBlankW (2 * n) g ^ s₀.1.doubleLevel := by
    unfold singleBlankMaskedV
    split_ifs
    · exact bot_le
    · simp [qClock, SingleClockTrace.initial, singleTheta]
  calc
    (∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
          q.rx + q.ry < M then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        =
          ∑' z, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
              z.core.rx + z.core.ry < M then
            iter (singleClockBandStep n hn aLoΛ hiΛ D H) T qClock z else 0) :=
      hproj
    _ ≤
        maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) qClock /
          (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
        singleBlankMaskedV cxCap
            (singleBlankW (2 * n) g) (singleBlankV (2 * n) g)
            (singleBlankEta (2 * n) g)
            qClock /
          (singleBlankW (2 * n) g ^ hiΛ *
            singleBlankEta (2 * n) g ^ Hocc) := hclock
    _ ≤
        1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
        singleBlankW (2 * n) g ^ s₀.1.doubleLevel /
          (singleBlankW (2 * n) g ^ hiΛ *
            singleBlankEta (2 * n) g ^ Hocc) := by
      exact add_le_add
        (ENNReal.div_le_div_right hnormPot.le _)
        (ENNReal.div_le_div_right hblankPot _)

/-! ## Wide horizons and scalar envelopes -/

/-- Wide half-horizon: `128·(n+2M)` occupation ticks per branch. -/
def singleWideHalfHorizon (n M : ℕ) : ℕ :=
  128 * singleClockBudget n M

/-- Wide raw-interaction horizon of one Single-B rung: `256·(n+2M)`. -/
def singleWideHorizon (n M : ℕ) : ℕ :=
  256 * singleClockBudget n M

theorem two_singleWideHalfHorizon (n M : ℕ) :
    2 * singleWideHalfHorizon n M = singleWideHorizon n M := by
  simp only [singleWideHalfHorizon, singleWideHorizon, singleClockBudget]
  ring

/-- The wide horizon is γ-free and linear: `256n + 512M`. -/
theorem singleWideHorizon_linear (n M : ℕ) :
    singleWideHorizon n M = 256 * n + 512 * M := by
  simp only [singleWideHorizon, singleClockBudget]
  ring

/-- The wide normal-branch error is still below `(3/4)^K`. -/
theorem singleWideNormalClockError_le (K : ℕ) :
    1 / (((32 : ℝ≥0∞) / 31) ^ (128 * K) * (1 / 2) ^ K) ≤
      ((3 : ℝ≥0∞) / 4) ^ K := by
  have hbase : (1 : ℝ≥0∞) ≤ (32 : ℝ≥0∞) / 31 := by
    rw [← ENNReal.toReal_le_toReal ENNReal.one_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  have hmono :
      ((32 : ℝ≥0∞) / 31) ^ (64 * K) ≤ ((32 : ℝ≥0∞) / 31) ^ (128 * K) :=
    pow_le_pow_right' hbase (by omega)
  calc
    1 / (((32 : ℝ≥0∞) / 31) ^ (128 * K) * (1 / 2) ^ K)
        ≤ 1 / (((32 : ℝ≥0∞) / 31) ^ (64 * K) * (1 / 2) ^ K) :=
      ENNReal.div_le_div_left (mul_le_mul' hmono le_rfl) 1
    _ ≤ ((3 : ℝ≥0∞) / 4) ^ K := by
      simpa using singleNormalClockError_le K

/-- Uniform envelope for the two wide occupation-clock errors. -/
noncomputable def singleWideClockEnvelope (n g M : ℕ) : ℝ≥0∞ :=
  ((3 : ℝ≥0∞) / 4) ^ singleClockBudget n M +
    ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (4 * (n : ℝ)))))

/-- At the wide half-horizon, the two occupation-clock errors are bounded by
the wide envelope. -/
theorem singleWideClockError_le
    (n g start hi M : ℕ)
    (hn : 0 < n) (hg : g ≤ 4 * n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g) :
    1 / (((32 : ℝ≥0∞) / 31) ^ singleWideHalfHorizon n M *
          (1 / 2) ^ singleClockBudget n M) +
        singleBlankW (2 * n) g ^ start /
          (singleBlankW (2 * n) g ^ hi *
            singleBlankEta (2 * n) g ^ singleWideHalfHorizon n M) ≤
      singleWideClockEnvelope n g M := by
  unfold singleWideClockEnvelope
  apply add_le_add
  · simpa [singleWideHalfHorizon] using
      singleWideNormalClockError_le (singleClockBudget n M)
  · have h := singleBlankClockError_le_exp_neg (2 * n) g start hi
      (singleWideHalfHorizon n M) (by omega) (by omega) hstart hwidth
      (by
        simp only [singleWideHalfHorizon, singleClockBudget]
        omega)
    have hcast : (2 * ((2 * n : ℕ) : ℝ)) = 4 * (n : ℝ) := by
      push_cast
      ring
    rw [hcast] at h
    exact h

section Inhabitation

example :
    (⟨⟨⟨40, 30, 30⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
        SingleLedger 100).NormalTick := by
  norm_num [SingleLedger.NormalTick]

example : singleWideHorizon 100 12 = 2 * singleWideHalfHorizon 100 12 :=
  (two_singleWideHalfHorizon 100 12).symm

end Inhabitation

end Tri

#print axioms Tri.singleB_blankHeavy_wide
#print axioms Tri.singleResolveDown_le_up_mul_wideW
#print axioms Tri.singleResolve_blank_drift_wide
#print axioms Tri.singleClockBandStep_blank_super_wide
#print axioms Tri.singleClock_blank_tail_wide
#print axioms Tri.singleClock_twoBranch_tail_wide
#print axioms Tri.singleBand_joint_clock_tail_wide
#print axioms Tri.singleWideNormalClockError_le
#print axioms Tri.singleWideClockError_le

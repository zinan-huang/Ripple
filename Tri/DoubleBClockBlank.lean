/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockNormal
import Tri.DoubleBDirection

/-!
# The blank-heavy branch of the Double-B occupation clock

In a blank-heavy state with majority gap at least `g`, the exact resolution
drift satisfies

`down + g / n ≤ up`.

The rational parameters

`w = 2n / (2n+g)`, `r = g / (2n+g)`, `η = 1 + r²/2`

obey `w+r=1` and `2r=w(g/n)`.  They turn the geometric level potential,
augmented by `η^blankTicks`, into a supermartingale without invoking a real
exponential or an independence premise.
-/

namespace Tri

open scoped ENNReal

/-- The uniform resolution-drift quantum on the blank-heavy branch. -/
noncomputable def doubleBlankDrift (n g : ℕ) : ℝ≥0∞ :=
  (g : ℝ≥0∞) / (n : ℝ≥0∞)

/-- Geometric base for the blank-heavy level potential. -/
noncomputable def doubleBlankW (n g : ℕ) : ℝ≥0∞ :=
  (2 * n : ℕ) / (2 * n + g : ℕ)

/-- The complementary rational slack, with `w+r=1`. -/
noncomputable def doubleBlankR (n g : ℕ) : ℝ≥0∞ :=
  (g : ℝ≥0∞) / (2 * n + g : ℕ)

/-- Per-blank-tick multiplier paid for by the quadratic drift slack. -/
noncomputable def doubleBlankEta (n g : ℕ) : ℝ≥0∞ :=
  1 + doubleBlankR n g ^ 2 / 2

/-- The geometric base and its rational slack partition one. -/
theorem doubleBlankW_add_R
    (n g : ℕ) (hn : 0 < n) :
    doubleBlankW n g + doubleBlankR n g = 1 := by
  unfold doubleBlankW doubleBlankR
  rw [ENNReal.div_add_div_same]
  have hnum :
      ((2 * n : ℕ) : ℝ≥0∞) + (g : ℝ≥0∞) =
        ((2 * n + g : ℕ) : ℝ≥0∞) := by norm_cast
  rw [hnum]
  exact ENNReal.div_self
    (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
    (ENNReal.natCast_ne_top _)

/-- The slack is exactly half of `w` times the drift quantum. -/
theorem doubleBlank_two_R
    (n g : ℕ) (hn : 0 < n) :
    2 * doubleBlankR n g =
      doubleBlankW n g * doubleBlankDrift n g := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by unfold doubleBlankR; finiteness)
    (by unfold doubleBlankW doubleBlankDrift; finiteness)).mp
  unfold doubleBlankR doubleBlankW doubleBlankDrift
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  rw [show ENNReal.toReal 2 = 2 by norm_num]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdenR : (2 * n + g : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- The blank-heavy direction base is at most one. -/
theorem doubleBlankW_le_one
    (n g : ℕ) (hn : 0 < n) :
    doubleBlankW n g ≤ 1 := by
  rw [← doubleBlankW_add_R n g hn]
  exact le_add_right le_rfl

/-- The direction ratio on every state with gap at least `g`. -/
theorem doubleResolveDown_le_up_mul_blankW
    {n g : ℕ} (hn : 2 ≤ n) (s : DoubleState n)
    (hgap : s.1.y + g ≤ s.1.x) :
    doubleResolveDown s ≤
      doubleResolveUp s * doubleBlankW n g := by
  have hcross := doubleB_gap_direction_cross s.2 hgap
  have hchoose : 0 < Nat.choose n 2 := Nat.choose_pos hn
  have hchooseR : 0 < (Nat.choose n 2 : ℝ) := by exact_mod_cast hchoose
  have hdenR : 0 < (2 * n + g : ℝ) := by positivity
  have hcrossR :
      (2 * n + g : ℝ) * (s.1.y * s.1.b) ≤
        (2 * n : ℝ) * (s.1.x * s.1.b) := by
    exact_mod_cast hcross
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  have hdownTop : doubleResolveDown s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hupTop : doubleResolveUp s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hwTop : doubleBlankW n g ≠ ⊤ := by
    unfold doubleBlankW
    finiteness
  rw [← ENNReal.toReal_le_toReal hdownTop
    (ENNReal.mul_ne_top hupTop hwTop)]
  unfold doubleResolveDown doubleResolveUp doubleBlankW
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  calc
    (↑(s.1.y * s.1.b) : ℝ) / ↑(Nat.choose n 2)
        = ((2 * ↑n + ↑g) * ↑(s.1.y * s.1.b)) /
            (↑(Nat.choose n 2) * (2 * ↑n + ↑g)) := by
              field_simp
    _ ≤ ((2 * ↑n) * ↑(s.1.x * s.1.b)) /
          (↑(Nat.choose n 2) * (2 * ↑n + ↑g)) := by
      exact (div_le_div_iff_of_pos_right
        (mul_pos hchooseR hdenR)).2 (by simpa using hcrossR)
    _ = (↑(s.1.x * s.1.b) : ℝ) / ↑(Nat.choose n 2) *
          ((↑(2 * n) : ℝ) / ↑(2 * n + g)) := by
      field_simp
      push_cast
      ring

/-- Blank-heavy resolution drift, stated without `ℝ≥0∞` subtraction. -/
theorem doubleResolve_blank_drift
    {n g : ℕ} (hn : 2 ≤ n) (s : DoubleState n)
    (hgap : s.1.y + g ≤ s.1.x)
    (hblank : 3 * n ≤ 4 * s.1.b) :
    doubleResolveDown s + doubleBlankDrift n g ≤
      doubleResolveUp s := by
  have hcross := doubleB_blank_drift_cross hn s.2 hgap hblank
  have hnR : 0 < (n : ℝ) := by positivity
  have hchoose : 0 < Nat.choose n 2 := Nat.choose_pos hn
  have hchooseR : 0 < (Nat.choose n 2 : ℝ) := by exact_mod_cast hchoose
  have hcrossR :
      (Nat.choose n 2 : ℝ) * g +
          n * (s.1.y * s.1.b) ≤
        n * (s.1.x * s.1.b) := by
    exact_mod_cast hcross
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hdownTop : doubleResolveDown s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hupTop : doubleResolveUp s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hdTop : doubleBlankDrift n g ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn0
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨hdownTop, hdTop⟩) hupTop]
  unfold doubleResolveDown doubleResolveUp doubleBlankDrift
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  calc
    (↑(s.1.y * s.1.b) : ℝ) / ↑(Nat.choose n 2) + ↑g / ↑n
        = (↑n * ↑(s.1.y * s.1.b) +
            ↑(Nat.choose n 2) * ↑g) /
            (↑n * ↑(Nat.choose n 2)) := by
              field_simp
    _ ≤ (↑n * ↑(s.1.x * s.1.b)) /
          (↑n * ↑(Nat.choose n 2)) := by
      exact (div_le_div_iff_of_pos_right (mul_pos hnR hchooseR)).2
        (by simpa [add_comm] using hcrossR)
    _ = (↑(s.1.x * s.1.b) : ℝ) / ↑(Nat.choose n 2) := by
      field_simp

/-- Scalar quadratic-slack inequality for a three-outcome `-1,0,+1` step.
The explicit slack `r²` is what later pays for one blank occupation tick. -/
theorem blank_three_term_slack
    {down neutral up d w r : ℝ≥0∞}
    (hsum : down + neutral + up = 1)
    (hdrift : down + d ≤ up)
    (hwr : w + r = 1)
    (h2r : 2 * r ≤ w * d)
    (hdt : down ≠ ⊤) (hnt : neutral ≠ ⊤) (hut : up ≠ ⊤)
    (hddt : d ≠ ⊤) (hwt : w ≠ ⊤) (hrt : r ≠ ⊤) :
    down + neutral * w + up * w ^ 2 + r ^ 2 ≤ w := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) hwt]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add hdt (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow]
  have hsumR :
      down.toReal + neutral.toReal + up.toReal = 1 := by
    have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add (by finiteness) hut,
      ENNReal.toReal_add hdt hnt, ENNReal.toReal_one] at this
  have hdriftR : down.toReal + d.toReal ≤ up.toReal := by
    have := (ENNReal.toReal_le_toReal (by finiteness) hut).mpr hdrift
    rwa [ENNReal.toReal_add hdt hddt] at this
  have hwrR : w.toReal + r.toReal = 1 := by
    have := congrArg ENNReal.toReal hwr
    rwa [ENNReal.toReal_add hwt hrt, ENNReal.toReal_one] at this
  have h2rR : 2 * r.toReal ≤ w.toReal * d.toReal := by
    have := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h2r
    simpa using this
  have hdown1 : down.toReal ≤ 1 := by
    have hn0 : 0 ≤ neutral.toReal := by positivity
    have hu0 : 0 ≤ up.toReal := by positivity
    linarith
  have hwdiff :
      w.toReal * d.toReal ≤
        w.toReal * (up.toReal - down.toReal) := by
    exact mul_le_mul_of_nonneg_left (by linarith)
      (by positivity)
  have hrdown : r.toReal * down.toReal ≤ r.toReal := by
    simpa using mul_le_mul_of_nonneg_left hdown1
      (by positivity)
  have hinner : r.toReal ≤ w.toReal * up.toReal - down.toReal := by
    have hwrMul := congrArg
      (fun z : ℝ => z * down.toReal) hwrR
    have hid :
        w.toReal * up.toReal - down.toReal =
          w.toReal * (up.toReal - down.toReal) -
            r.toReal * down.toReal := by
      nlinarith
    rw [hid]
    linarith
  have hmul :
      r.toReal ^ 2 ≤
        r.toReal * (w.toReal * up.toReal - down.toReal) := by
    simpa [pow_two] using
      mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ r.toReal)
  have hneutralR :
      neutral.toReal = 1 - down.toReal - up.toReal := by
    linarith
  have hid :
      w.toReal -
          (down.toReal + neutral.toReal * w.toReal +
            up.toReal * w.toReal ^ 2) =
        r.toReal * (w.toReal * up.toReal - down.toReal) := by
    rw [hneutralR]
    calc
      w.toReal -
            (down.toReal +
              (1 - down.toReal - up.toReal) * w.toReal +
              up.toReal * w.toReal ^ 2)
          = (1 - w.toReal) *
              (w.toReal * up.toReal - down.toReal) := by ring
      _ = r.toReal * (w.toReal * up.toReal - down.toReal) := by
        congr 1
        linarith
  linarith

/-- The quadratic slack pays the multiplier `1+r²/2`. -/
theorem blank_three_term_eta
    {down neutral up d w r : ℝ≥0∞}
    (hsum : down + neutral + up = 1)
    (hdrift : down + d ≤ up)
    (hwr : w + r = 1)
    (h2r : 2 * r ≤ w * d)
    (hdt : down ≠ ⊤) (hnt : neutral ≠ ⊤) (hut : up ≠ ⊤)
    (hddt : d ≠ ⊤) (hwt : w ≠ ⊤) (hrt : r ≠ ⊤) :
    (1 + r ^ 2 / 2) *
        (down + neutral * w + up * w ^ 2) ≤ w := by
  have hslack := blank_three_term_slack hsum hdrift hwr h2r
    hdt hnt hut hddt hwt hrt
  have hF :
      down + neutral * w + up * w ^ 2 ≤ w := by
    exact (le_add_right le_rfl).trans hslack
  have hw1 : w ≤ 1 := by
    rw [← hwr]
    exact le_add_right le_rfl
  calc
    (1 + r ^ 2 / 2) *
          (down + neutral * w + up * w ^ 2)
        = (down + neutral * w + up * w ^ 2) +
            r ^ 2 / 2 *
              (down + neutral * w + up * w ^ 2) := by ring
    _ ≤ (down + neutral * w + up * w ^ 2) + r ^ 2 / 2 := by
      have hm :
          r ^ 2 / 2 * (down + neutral * w + up * w ^ 2) ≤
            r ^ 2 / 2 := by
        simpa using
          mul_le_mul_right (hF.trans hw1) (r ^ 2 / 2)
      exact add_le_add_right hm _
    _ ≤ (down + neutral * w + up * w ^ 2) + r ^ 2 := by
      have hhalf : r ^ 2 / 2 ≤ r ^ 2 := by
        apply ENNReal.div_le_of_le_mul
        calc
          r ^ 2 ≤ r ^ 2 + r ^ 2 := le_add_right le_rfl
          _ = r ^ 2 * 2 := by ring
      exact add_le_add_right hhalf _
    _ ≤ w := hslack

/-- Level/blank-occupation potential. -/
noncomputable def doubleBlankPotential
    (w η : ℝ≥0∞) {n : ℕ} (q : DoubleClockTrace n) : ℝ≥0∞ :=
  w ^ q.core.cfg.1.doubleLevel * η ^ q.blankTicks

/-- On a live tick, forgetting the clock counters reduces the potential
expectation to the counted core step.  The extra factor is `η` exactly on a
complementary tick. -/
theorem doubleClockBandStep_expect_blank_bridge
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (q : DoubleClockTrace n) (w η : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi) :
    expect (doubleClockBandStep n hn aLo hi q)
        (doubleBlankPotential w η) =
      (if q.core.NormalTick then 1 else η) *
        expect (doubleTraceStep n hn q.core)
          (fun z => w ^ z.cfg.1.doubleLevel * η ^ q.blankTicks) := by
  have hh : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b := by
    have := q.core.cfg.2
    simp only [BiCfg.DoubleInv] at this
    omega
  unfold doubleClockBandStep
  rw [if_pos hlive, expect_map]
  unfold doubleTraceStep
  rw [expect_map]
  unfold expect
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Function.comp_apply]
  by_cases hw :
      PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
  · rw [dbPairPMF_zero_of_weight_zero hw]
    simp
  · unfold doubleBlankPotential PairComp.nextDoubleClockTrace
    rw [dif_neg hw]
    by_cases hnormal : q.core.NormalTick
    · simp only [hnormal, if_pos, add_zero, one_mul]
    · simp only [hnormal, if_false]
      rw [pow_succ]
      ring

/-- Exact three-mass expansion of the blank-occupation potential. -/
theorem doubleClockBandStep_expect_blank
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (q : DoubleClockTrace n) (a : ℕ)
    (ha : q.core.cfg.1.doubleLevel = a + 1)
    (w η : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi) :
    expect (doubleClockBandStep n hn aLo hi q)
        (doubleBlankPotential w η) =
      (if q.core.NormalTick then 1 else η) *
        (doubleResolveDown q.core.cfg * w ^ a +
          doubleNeutralMass hn q.core.cfg * w ^ (a + 1) +
          doubleResolveUp q.core.cfg * w ^ (a + 2)) *
        η ^ q.blankTicks := by
  rw [doubleClockBandStep_expect_blank_bridge n hn aLo hi q w η hlive]
  have hexp := doubleTraceStep_expect n hn q.core a ha
    (fun L _ => w ^ L * η ^ q.blankTicks)
  rw [hexp]
  ring

/-- The blank-occupation potential is a one-step supermartingale on an early
small-gap band.  Normal ticks use only the directional ratio; complementary
ticks are blank-heavy and pay one factor of `η`. -/
theorem doubleClockBandStep_blank_super
    (n : ℕ) (hn : 2 ≤ n) (g aLo hi : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n) :
    ∀ q : DoubleClockTrace n,
      expect (doubleClockBandStep n hn aLo hi q)
          (doubleBlankPotential
            (doubleBlankW n g) (doubleBlankEta n g)) ≤
        doubleBlankPotential
          (doubleBlankW n g) (doubleBlankEta n g) q := by
  intro q
  by_cases hlive : q.core.BandLive aLo hi
  · obtain ⟨a, ha⟩ :
        ∃ a, q.core.cfg.1.doubleLevel = a + 1 := by
      refine ⟨q.core.cfg.1.doubleLevel - 1, ?_⟩
      unfold DoubleTrace.BandLive at hlive
      omega
    have hgap : q.core.cfg.1.y + g ≤ q.core.cfg.1.x := by
      have hinv := q.core.cfg.2
      unfold DoubleTrace.BandLive at hlive
      simp only [BiCfg.DoubleInv, BiCfg.doubleLevel] at hinv hlive
      omega
    have hgapUpper :
        8 * q.core.cfg.1.x ≤ 8 * q.core.cfg.1.y + n := by
      have hinv := q.core.cfg.2
      unfold DoubleTrace.BandLive at hlive
      simp only [BiCfg.DoubleInv, BiCfg.doubleLevel] at hinv hlive
      omega
    have hsum := double_mass_sum n hn q.core.cfg
    have hchoose : 0 < Nat.choose n 2 := Nat.choose_pos hn
    have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hchoose.ne'
    have hdt : doubleResolveDown q.core.cfg ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
    have hut : doubleResolveUp q.core.cfg ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
    have hnt : doubleNeutralMass hn q.core.cfg ≠ ⊤ := by
      intro h
      rw [h] at hsum
      simp at hsum
    have hwt : doubleBlankW n g ≠ ⊤ := by
      unfold doubleBlankW
      finiteness
    have hrt : doubleBlankR n g ≠ ⊤ := by
      unfold doubleBlankR
      finiteness
    have hddt : doubleBlankDrift n g ≠ ⊤ := by
      unfold doubleBlankDrift
      finiteness
    have hwr :
        doubleBlankW n g + doubleBlankR n g = 1 :=
      doubleBlankW_add_R n g (by omega)
    have h2r :
        2 * doubleBlankR n g ≤
          doubleBlankW n g * doubleBlankDrift n g := by
      exact (doubleBlank_two_R n g (by omega)).le
    have hw1 : doubleBlankW n g ≤ 1 :=
      doubleBlankW_le_one n g (by omega)
    have hfactor :
        (if q.core.NormalTick then 1 else doubleBlankEta n g) *
            (doubleResolveDown q.core.cfg +
              doubleNeutralMass hn q.core.cfg * doubleBlankW n g +
              doubleResolveUp q.core.cfg * doubleBlankW n g ^ 2) ≤
          doubleBlankW n g := by
      by_cases hnormal : q.core.NormalTick
      · rw [if_pos hnormal, one_mul]
        exact feller_reduced
          (doubleResolveDown q.core.cfg)
          (doubleNeutralMass hn q.core.cfg)
          (doubleResolveUp q.core.cfg)
          (doubleBlankW n g)
          hsum
          (doubleResolveDown_le_up_mul_blankW hn q.core.cfg hgap)
          hw1 hdt hnt hut
      · rw [if_neg hnormal]
        have hblank : 3 * n ≤ 4 * q.core.cfg.1.b := by
          rcases doubleState_freeY_or_blankHeavy q.core.cfg hgapUpper with
            hnormal' | hblank
          · exact absurd hnormal' hnormal
          · exact hblank
        unfold doubleBlankEta
        exact blank_three_term_eta hsum
          (doubleResolve_blank_drift hn q.core.cfg hgap hblank)
          hwr h2r hdt hnt hut hddt hwt hrt
    rw [doubleClockBandStep_expect_blank
      n hn aLo hi q a ha (doubleBlankW n g)
      (doubleBlankEta n g) hlive]
    calc
      (if q.core.NormalTick then 1 else doubleBlankEta n g) *
            (doubleResolveDown q.core.cfg * doubleBlankW n g ^ a +
              doubleNeutralMass hn q.core.cfg *
                doubleBlankW n g ^ (a + 1) +
              doubleResolveUp q.core.cfg *
                doubleBlankW n g ^ (a + 2)) *
            doubleBlankEta n g ^ q.blankTicks
          =
            (doubleBlankW n g ^ a *
              doubleBlankEta n g ^ q.blankTicks) *
              ((if q.core.NormalTick then 1 else doubleBlankEta n g) *
                (doubleResolveDown q.core.cfg +
                  doubleNeutralMass hn q.core.cfg * doubleBlankW n g +
                  doubleResolveUp q.core.cfg * doubleBlankW n g ^ 2)) := by
            rw [pow_succ (doubleBlankW n g) a,
              show a + 2 = (a + 1) + 1 by omega,
              pow_succ (doubleBlankW n g) (a + 1)]
            ring
      _ ≤ (doubleBlankW n g ^ a *
              doubleBlankEta n g ^ q.blankTicks) *
            doubleBlankW n g := by
        gcongr
      _ = doubleBlankPotential
            (doubleBlankW n g) (doubleBlankEta n g) q := by
        unfold doubleBlankPotential
        rw [ha, pow_succ]
        ring
  · unfold doubleClockBandStep
    rw [if_neg hlive, expect_pure]

/-- Finite-horizon upper tail for blank-heavy occupation while the stopped
chain remains inside the band. -/
theorem doubleClock_blank_tail
    (n : ℕ) (hn : 2 ≤ n) (g aLo hi : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (T H : ℕ) (q₀ : DoubleClockTrace n) :
    ∑' z, (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
        iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) ≤
      doubleBlankPotential
          (doubleBlankW n g) (doubleBlankEta n g) q₀ /
        (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) := by
  have hw1 : doubleBlankW n g ≤ 1 :=
    doubleBlankW_le_one n g (by omega)
  have hw0 : doubleBlankW n g ≠ 0 := by
    unfold doubleBlankW
    exact ne_of_gt (ENNReal.div_pos
      (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
      (ENNReal.natCast_ne_top _))
  have hwt : doubleBlankW n g ≠ ⊤ := by
    unfold doubleBlankW
    finiteness
  have hη1 : 1 ≤ doubleBlankEta n g := by
    unfold doubleBlankEta
    exact le_add_right le_rfl
  have hη0 : doubleBlankEta n g ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hη1)
  have hηt : doubleBlankEta n g ≠ ⊤ := by
    unfold doubleBlankEta doubleBlankR
    finiteness
  have hθ0 :
      doubleBlankW n g ^ hi * doubleBlankEta n g ^ H ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hη0)
  have hθt :
      doubleBlankW n g ^ hi * doubleBlankEta n g ^ H ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt)
      (ENNReal.pow_ne_top hηt)
  have hsub : ∀ z : DoubleClockTrace n,
      (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
          iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) ≤
        (if doubleBlankW n g ^ hi * doubleBlankEta n g ^ H ≤
              doubleBlankPotential
                (doubleBlankW n g) (doubleBlankEta n g) z then
            iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) := by
    intro z
    by_cases hz : z.core.BandLive aLo hi ∧ H ≤ z.blankTicks
    · have hlevel : z.core.cfg.1.doubleLevel ≤ hi := by
        unfold DoubleTrace.BandLive at hz
        omega
      have hwPow :
          doubleBlankW n g ^ hi ≤
            doubleBlankW n g ^ z.core.cfg.1.doubleLevel :=
        pow_le_pow_right_of_le_one' hw1 hlevel
      have hηPow :
          doubleBlankEta n g ^ H ≤
            doubleBlankEta n g ^ z.blankTicks :=
        pow_le_pow_right₀ hη1 hz.2
      have hpot :
          doubleBlankW n g ^ hi * doubleBlankEta n g ^ H ≤
            doubleBlankPotential
              (doubleBlankW n g) (doubleBlankEta n g) z := by
        unfold doubleBlankPotential
        exact mul_le_mul hwPow hηPow bot_le bot_le
      simp [hz, hpot]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (doubleClockBandStep n hn aLo hi) T q₀)
      (doubleBlankPotential
        (doubleBlankW n g) (doubleBlankEta n g))
      (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H)
      hθ0 hθt) ?_
  exact ENNReal.div_le_div_right
    (by
      simpa using
        (expect_iter_le
          (doubleClockBandStep n hn aLo hi)
          (doubleBlankPotential
            (doubleBlankW n g) (doubleBlankEta n g))
          1
          (by simpa using
            doubleClockBandStep_blank_super n hn g aLo hi hnLo hsmall)
          T q₀))
    (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H)

/-- Fixed-horizon two-branch clock.  A live endpoint with too few resolutions
must lie in either the normal-fuel lower tail or the blank-occupation upper
tail.  The theorem keeps both exact finite error terms exposed for later
constant optimization. -/
theorem doubleClock_twoBranch_tail
    (n : ℕ) (hn : 2 ≤ n) (g aLo hi : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (T H M y₀ : ℕ) (hH : 2 * H ≤ T)
    (q₀ : DoubleClockTrace n)
    (hqInv : q₀.FuelClockInv y₀)
    (hy₀ : y₀ ≤ n)
    (hnormal0 : q₀.normalTicks = 0)
    (hblank0 : q₀.blankTicks = 0) :
    ∑' z, (if z.core.BandLive aLo hi ∧ z.core.resolve < M then
        iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) ≤
      maskedCountPotential DoubleClockTrace.normalTicks
          DoubleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
        (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ (n + 2 * M)) +
      doubleBlankPotential
          (doubleBlankW n g) (doubleBlankEta n g) q₀ /
        (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) := by
  let K := doubleClockBandStep n hn aLo hi
  let p := iter K T q₀
  have hpoint : ∀ z : DoubleClockTrace n,
      (if z.core.BandLive aLo hi ∧ z.core.resolve < M then p z else 0) ≤
        (if H ≤ z.normalTicks ∧ z.normalFuel ≤ n + 2 * M then p z else 0) +
        (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then p z else 0) := by
    intro z
    by_cases hbad : z.core.BandLive aLo hi ∧ z.core.resolve < M
    · by_cases hp : p z = 0
      · simp [hbad, hp]
      · have hticks :=
          doubleClockBand_iter_tick_sum_of_final_live
            hn aLo hi T q₀ z hp hbad.1
        have hticks' :
            z.normalTicks + z.blankTicks = T := by
          rw [hnormal0, hblank0] at hticks
          simpa using hticks
        by_cases hblank : H ≤ z.blankTicks
        · simp [hbad, hblank]
        · have hnormal : H ≤ z.normalTicks := by omega
          have hzInv :=
            doubleClockBand_iter_fuelClockInv
              hn aLo hi q₀ z hqInv hp
          have hfuel : z.normalFuel ≤ n + 2 * M := by
            unfold DoubleClockTrace.FuelClockInv DoubleTrace.FuelInv at hzInv
            omega
          simp [hbad, hnormal, hfuel]
    · simp [hbad]
  calc
    ∑' z, (if z.core.BandLive aLo hi ∧ z.core.resolve < M then
          iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0)
        ≤ ∑' z,
            ((if H ≤ z.normalTicks ∧ z.normalFuel ≤ n + 2 * M then
                iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) +
              (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
                iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0)) := by
          exact ENNReal.tsum_le_tsum hpoint
    _ =
        (∑' z, (if H ≤ z.normalTicks ∧ z.normalFuel ≤ n + 2 * M then
            iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0)) +
        (∑' z, (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
            iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0)) :=
      ENNReal.tsum_add
    _ ≤
        maskedCountPotential DoubleClockTrace.normalTicks
            DoubleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
          (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ (n + 2 * M)) +
        doubleBlankPotential
            (doubleBlankW n g) (doubleBlankEta n g) q₀ /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) := by
      exact add_le_add
        (doubleClock_normal_tail_half n hn aLo hi
          (by omega) T H (n + 2 * M) q₀)
        (doubleClock_blank_tail n hn g aLo hi
          hnLo hsmall T H q₀)

end Tri

#print axioms Tri.doubleResolve_blank_drift
#print axioms Tri.blank_three_term_eta
#print axioms Tri.doubleClockBandStep_expect_blank
#print axioms Tri.doubleClockBandStep_blank_super
#print axioms Tri.doubleClock_blank_tail
#print axioms Tri.doubleClock_twoBranch_tail

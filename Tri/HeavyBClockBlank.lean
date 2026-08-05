/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBClockNormal
import Tri.HeavyBResolution

/-!
# The blank-heavy branch of the Heavy-B occupation clock

The Heavy-B blank branch uses the half-scale level `heavyLevel = x + b` and the
state-dependent entity denominator `C(x+y+b,2)`.  In the early band,
complementary ticks are blank-heavy, and the resolution drift is spent by the
geometric level potential with

`w = n/(n+g)`, `r = g/(n+g)`, `η = 1 + r²/2`.
-/

namespace Tri

open scoped ENNReal

/-! ### Split arithmetic -/

/-- A complementary live Heavy-B tick in the early band is blank-heavy. -/
theorem heavyB_blankHeavy_of_notNormal_live_small
    {n aLo hi : ℕ} (q : HeavyTrace n)
    (hlive : q.BandLive aLo hi)
    (hnormal : ¬q.NormalTick)
    (hsmall : 16 * hi ≤ 9 * n) :
    3 * n ≤ 8 * q.cfg.1.b := by
  have hinv := q.cfg.2
  unfold HeavyTrace.BandLive BiCfg.heavyLevel at hlive
  unfold HeavyTrace.NormalTick at hnormal
  simp only [BiCfg.HeavyInv] at hinv
  omega

/-- The live lower edge gives the Heavy-B majority gap `x-y ≥ g`. -/
theorem heavyB_live_gap
    {n g aLo hi : ℕ} (s : HeavyState n)
    (hlive : (⟨s, 0, 0, 0⟩ : HeavyTrace n).BandLive aLo hi)
    (hfloor : n + g ≤ 2 * (aLo + 1)) :
    s.1.y + g ≤ s.1.x := by
  have hinv := s.2
  change aLo + 1 ≤ BiCfg.heavyLevel s.1 ∧
      BiCfg.heavyLevel s.1 + 1 ≤ hi at hlive
  unfold BiCfg.heavyLevel at hlive
  simp only [BiCfg.HeavyInv] at hinv
  omega

/-- Pointwise form of `heavyB_live_gap` for an existing trace. -/
theorem HeavyTrace.live_gap
    {n g aLo hi : ℕ} (q : HeavyTrace n)
    (hlive : q.BandLive aLo hi)
    (hfloor : n + g ≤ 2 * (aLo + 1)) :
    q.cfg.1.y + g ≤ q.cfg.1.x := by
  have hinv := q.cfg.2
  unfold HeavyTrace.BandLive BiCfg.heavyLevel at hlive
  simp only [BiCfg.HeavyInv] at hinv
  omega

/-- Heavy-B direction cross bound for `w = n/(n+g)`. -/
theorem heavyB_gap_direction_cross
    {n x y b g : ℕ}
    (hinv : x + y + 2 * b = n)
    (hgap : y + g ≤ x) :
    (n + g) * PairComp.weight x y b .yb ≤
      n * PairComp.weight x y b .xb := by
  have hy : y ≤ n := by omega
  have hgy : g * y ≤ n * g := by
    have := Nat.mul_le_mul_left g hy
    nlinarith
  have hgyb := Nat.mul_le_mul_right b hgy
  have hgapb := Nat.mul_le_mul_left (n * b) hgap
  calc
    (n + g) * PairComp.weight x y b .yb
        = n * b * y + g * y * b := by
          simp only [PairComp.weight]
          ring
    _ ≤ n * b * y + n * g * b :=
      Nat.add_le_add_left hgyb _
    _ = n * b * (y + g) := by ring
    _ ≤ n * b * x := hgapb
    _ = n * PairComp.weight x y b .xb := by
      simp only [PairComp.weight]
      ring

/-- In a blank-heavy Heavy-B state, the unnormalized drift dominates
`C(entities,2) * g / n`. -/
theorem heavyB_blank_drift_cross
    {n x y b g : ℕ}
    (hinv : x + y + 2 * b = n)
    (hgap : y + g ≤ x)
    (hblank : 3 * n ≤ 8 * b) :
    Nat.choose (x + y + b) 2 * g +
        n * PairComp.weight x y b .yb ≤
      n * PairComp.weight x y b .xb := by
  have hmleN : x + y + b ≤ n := by omega
  have hmle2b : x + y + b ≤ 2 * b := by omega
  have hsub : (x + y + b) * (x + y + b - 1) ≤
      (x + y + b) * (x + y + b) :=
    Nat.mul_le_mul_left (x + y + b) (Nat.sub_le _ _)
  have hmul2b : (x + y + b) * (x + y + b) ≤
      (x + y + b) * (2 * b) :=
    Nat.mul_le_mul_left (x + y + b) hmle2b
  have hmn : (x + y + b) * b ≤ n * b :=
    Nat.mul_le_mul_right b hmleN
  have hchoose := two_mul_choose_two (x + y + b)
  have hCb : Nat.choose (x + y + b) 2 ≤ n * b := by
    nlinarith
  have hCg : Nat.choose (x + y + b) 2 * g ≤ n * b * g :=
    Nat.mul_le_mul_right g hCb
  calc
    Nat.choose (x + y + b) 2 * g +
          n * PairComp.weight x y b .yb
        ≤ n * b * g + n * PairComp.weight x y b .yb :=
      Nat.add_le_add_right hCg _
    _ = n * b * (y + g) := by
      simp only [PairComp.weight]
      ring
    _ ≤ n * b * x := Nat.mul_le_mul_left (n * b) hgap
    _ = n * PairComp.weight x y b .xb := by
      simp only [PairComp.weight]
      ring

/-! ### Blank-branch parameters -/

/-- The uniform resolution-drift quantum on the Heavy-B blank branch. -/
noncomputable def heavyBlankDrift (n g : ℕ) : ℝ≥0∞ :=
  (g : ℝ≥0∞) / (n : ℝ≥0∞)

/-- Geometric base for the Heavy-B blank-heavy level potential. -/
noncomputable def heavyBlankW (n g : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞) / (n + g : ℕ)

/-- The complementary rational slack, with `w+r=1`. -/
noncomputable def heavyBlankR (n g : ℕ) : ℝ≥0∞ :=
  (g : ℝ≥0∞) / (n + g : ℕ)

/-- Per-blank-tick multiplier paid for by the quadratic drift slack. -/
noncomputable def heavyBlankEta (n g : ℕ) : ℝ≥0∞ :=
  1 + heavyBlankR n g ^ 2 / 2

/-- The geometric base and its rational slack partition one. -/
theorem heavyBlankW_add_R
    (n g : ℕ) (hn : 0 < n) :
    heavyBlankW n g + heavyBlankR n g = 1 := by
  unfold heavyBlankW heavyBlankR
  rw [ENNReal.div_add_div_same]
  have hnum :
      (n : ℝ≥0∞) + (g : ℝ≥0∞) =
        ((n + g : ℕ) : ℝ≥0∞) := by norm_cast
  rw [hnum]
  exact ENNReal.div_self
    (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
    (ENNReal.natCast_ne_top _)

/-- At Heavy-B scale the slack is exactly `w` times the drift quantum. -/
theorem heavyBlank_R_eq_W_mul_drift
    (n g : ℕ) (hn : 0 < n) :
    heavyBlankR n g =
      heavyBlankW n g * heavyBlankDrift n g := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by unfold heavyBlankR; finiteness)
    (by unfold heavyBlankW heavyBlankDrift; finiteness)).mp
  unfold heavyBlankR heavyBlankW heavyBlankDrift
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdenR : (n + g : ℝ) ≠ 0 := by positivity
  field_simp

/-- The blank-heavy direction base is at most one. -/
theorem heavyBlankW_le_one
    (n g : ℕ) (hn : 0 < n) :
    heavyBlankW n g ≤ 1 := by
  rw [← heavyBlankW_add_R n g hn]
  exact le_add_right le_rfl

/-! ### Drift inequalities -/

/-- The direction ratio on every Heavy-B state with gap at least `g`. -/
theorem heavyResolveDown_le_up_mul_blankW
    {n g : ℕ} (hn : 3 ≤ n) (s : HeavyState n)
    (hgap : s.1.y + g ≤ s.1.x) :
    heavyResolveDown s ≤
      heavyResolveUp s * heavyBlankW n g := by
  have hcross := heavyB_gap_direction_cross s.2 hgap
  have hchoose : 0 < Nat.choose (heavyEntities s) 2 :=
    Nat.choose_pos (heavy_two_entities hn s)
  have hchooseR : 0 < (Nat.choose (heavyEntities s) 2 : ℝ) := by
    exact_mod_cast hchoose
  have hdenR : 0 < (n + g : ℝ) := by positivity
  have hcrossR :
      (n + g : ℝ) * (s.1.y * s.1.b) ≤
        (n : ℝ) * (s.1.x * s.1.b) := by
    exact_mod_cast hcross
  have hden0 : ((Nat.choose (heavyEntities s) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  have hdownTop : heavyResolveDown s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hupTop : heavyResolveUp s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hwTop : heavyBlankW n g ≠ ⊤ := by
    unfold heavyBlankW
    finiteness
  rw [← ENNReal.toReal_le_toReal hdownTop
    (ENNReal.mul_ne_top hupTop hwTop)]
  unfold heavyResolveDown heavyResolveUp heavyBlankW
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  calc
    (↑(s.1.y * s.1.b) : ℝ) / ↑(Nat.choose (heavyEntities s) 2)
        = ((↑n + ↑g) * ↑(s.1.y * s.1.b)) /
            (↑(Nat.choose (heavyEntities s) 2) * (↑n + ↑g)) := by
              field_simp
    _ ≤ (↑n * ↑(s.1.x * s.1.b)) /
          (↑(Nat.choose (heavyEntities s) 2) * (↑n + ↑g)) := by
      exact (div_le_div_iff_of_pos_right
        (mul_pos hchooseR hdenR)).2 (by simpa using hcrossR)
    _ = (↑(s.1.x * s.1.b) : ℝ) /
          ↑(Nat.choose (heavyEntities s) 2) *
          ((↑n : ℝ) / ↑(n + g)) := by
      field_simp
      push_cast
      ring

/-- Heavy-B blank-heavy resolution drift, without `ℝ≥0∞` subtraction. -/
theorem heavyResolve_blank_drift
    {n g : ℕ} (hn : 3 ≤ n) (s : HeavyState n)
    (hgap : s.1.y + g ≤ s.1.x)
    (hblank : 3 * n ≤ 8 * s.1.b) :
    heavyResolveDown s + heavyBlankDrift n g ≤
      heavyResolveUp s := by
  have hcross := heavyB_blank_drift_cross s.2 hgap hblank
  have hnR : 0 < (n : ℝ) := by positivity
  have hchoose : 0 < Nat.choose (heavyEntities s) 2 :=
    Nat.choose_pos (heavy_two_entities hn s)
  have hchooseR : 0 < (Nat.choose (heavyEntities s) 2 : ℝ) := by
    exact_mod_cast hchoose
  have hcrossR :
      (Nat.choose (heavyEntities s) 2 : ℝ) * g +
          n * (s.1.y * s.1.b) ≤
        n * (s.1.x * s.1.b) := by
    simpa [heavyEntities] using (show
      (Nat.choose (s.1.x + s.1.y + s.1.b) 2 : ℝ) * g +
          n * (s.1.y * s.1.b) ≤
        n * (s.1.x * s.1.b) by
      exact_mod_cast hcross)
  have hden0 : ((Nat.choose (heavyEntities s) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hdownTop : heavyResolveDown s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hupTop : heavyResolveUp s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
  have hdTop : heavyBlankDrift n g ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn0
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨hdownTop, hdTop⟩) hupTop]
  unfold heavyResolveDown heavyResolveUp heavyBlankDrift
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  calc
    (↑(s.1.y * s.1.b) : ℝ) / ↑(Nat.choose (heavyEntities s) 2) + ↑g / ↑n
        = (↑n * ↑(s.1.y * s.1.b) +
            ↑(Nat.choose (heavyEntities s) 2) * ↑g) /
            (↑n * ↑(Nat.choose (heavyEntities s) 2)) := by
              field_simp
    _ ≤ (↑n * ↑(s.1.x * s.1.b)) /
          (↑n * ↑(Nat.choose (heavyEntities s) 2)) := by
      exact (div_le_div_iff_of_pos_right (mul_pos hnR hchooseR)).2
        (by simpa [add_comm] using hcrossR)
    _ = (↑(s.1.x * s.1.b) : ℝ) / ↑(Nat.choose (heavyEntities s) 2) := by
      field_simp

/-! ### Scalar slack and potential -/

/-- Scalar quadratic-slack inequality for the Heavy-B `w = n/(n+g)` regime. -/
theorem heavy_blank_three_term_slack
    {down neutral up d w r : ℝ≥0∞}
    (hsum : down + neutral + up = 1)
    (hdrift : down + d ≤ up)
    (hwr : w + r = 1)
    (hrd : r ≤ w * d)
    (hdt : down ≠ ⊤) (hnt : neutral ≠ ⊤) (hut : up ≠ ⊤)
    (hddt : d ≠ ⊤) (hwt : w ≠ ⊤) (hrt : r ≠ ⊤) :
    down + neutral * w + up * w ^ 2 + r ^ 2 / 2 ≤ w := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) hwt]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add hdt (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_pow]
  rw [show ENNReal.toReal 2 = 2 by norm_num]
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
  have hrdR : r.toReal ≤ w.toReal * d.toReal := by
    have := (ENNReal.toReal_le_toReal hrt (by finiteness)).mpr hrd
    rwa [ENNReal.toReal_mul] at this
  have hdownHalf : down.toReal ≤ 1 / 2 := by
    have hdu : down.toReal ≤ up.toReal := by
      have hd0 : 0 ≤ d.toReal := ENNReal.toReal_nonneg
      linarith
    have hn0 : 0 ≤ neutral.toReal := ENNReal.toReal_nonneg
    nlinarith
  have hwdiff :
      w.toReal * d.toReal ≤
        w.toReal * (up.toReal - down.toReal) := by
    exact mul_le_mul_of_nonneg_left (by linarith)
      (ENNReal.toReal_nonneg)
  have hinner0 : r.toReal ≤
      w.toReal * (up.toReal - down.toReal) :=
    hrdR.trans hwdiff
  have hrdhalf : r.toReal * down.toReal ≤ r.toReal / 2 := by
    calc
      r.toReal * down.toReal ≤ r.toReal * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left hdownHalf ENNReal.toReal_nonneg
      _ = r.toReal / 2 := by ring
  have hinner : r.toReal / 2 ≤
      w.toReal * up.toReal - down.toReal := by
    have hid :
        w.toReal * up.toReal - down.toReal =
          w.toReal * (up.toReal - down.toReal) -
            r.toReal * down.toReal := by
      nlinarith
    rw [hid]
    linarith
  have hmul :
      r.toReal ^ 2 / 2 ≤
        r.toReal * (w.toReal * up.toReal - down.toReal) := by
    have hr0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    have := mul_le_mul_of_nonneg_left hinner hr0
    nlinarith
  have hneutralR :
      neutral.toReal = 1 - down.toReal - up.toReal := by
    linarith
  have hdiff :
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
  nlinarith

/-- The quadratic slack pays the multiplier `1+r²/2` at Heavy-B scale. -/
theorem heavy_blank_three_term_eta
    {down neutral up d w r : ℝ≥0∞}
    (hsum : down + neutral + up = 1)
    (hdrift : down + d ≤ up)
    (hwr : w + r = 1)
    (hrd : r ≤ w * d)
    (hdt : down ≠ ⊤) (hnt : neutral ≠ ⊤) (hut : up ≠ ⊤)
    (hddt : d ≠ ⊤) (hwt : w ≠ ⊤) (hrt : r ≠ ⊤) :
    (1 + r ^ 2 / 2) *
        (down + neutral * w + up * w ^ 2) ≤ w := by
  have hslack := heavy_blank_three_term_slack hsum hdrift hwr hrd
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
    _ ≤ w := hslack

/-- Level/blank-occupation potential. -/
noncomputable def heavyBlankPotential
    (w η : ℝ≥0∞) {n : ℕ} (q : HeavyClockTrace n) : ℝ≥0∞ :=
  w ^ BiCfg.heavyLevel q.core.cfg.1 * η ^ q.blankTicks

/-- On a live tick, forgetting the clock counters reduces the potential
expectation to the counted core step. -/
theorem heavyClockBandStep_expect_blank_bridge
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (q : HeavyClockTrace n) (w η : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi) :
    expect (heavyClockBandStep n aLo hi q)
        (heavyBlankPotential w η) =
      (if q.core.NormalTick then 1 else η) *
        expect (heavyTraceStep n q.core)
          (fun z => w ^ BiCfg.heavyLevel z.cfg.1 * η ^ q.blankTicks) := by
  have hh := heavy_two_entities hn q.core.cfg
  unfold heavyClockBandStep
  rw [if_pos hlive, dif_pos hh, expect_map]
  unfold heavyTraceStep
  rw [dif_pos hh, expect_map]
  unfold expect
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change (dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh) k *
      heavyBlankPotential w η (PairComp.nextHeavyClockTrace q k) =
    (if q.core.NormalTick then 1 else η) *
      ((dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh) k *
        (w ^ BiCfg.heavyLevel (PairComp.nextHeavyTrace q.core k).cfg.1 *
          η ^ q.blankTicks))
  by_cases hw :
      PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
  · rw [dbPairPMF_zero_of_weight_zero hw]
    simp
  · unfold heavyBlankPotential PairComp.nextHeavyClockTrace
    rw [dif_neg hw]
    by_cases hnormal : q.core.NormalTick
    · simp only [hnormal, if_pos, add_zero, one_mul]
    · simp only [hnormal, if_false]
      rw [pow_succ]
      ring

/-- Exact three-mass expansion of the blank-occupation potential. -/
theorem heavyClockBandStep_expect_blank
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (q : HeavyClockTrace n) (a : ℕ)
    (ha : BiCfg.heavyLevel q.core.cfg.1 = a + 1)
    (w η : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi) :
    expect (heavyClockBandStep n aLo hi q)
        (heavyBlankPotential w η) =
      (if q.core.NormalTick then 1 else η) *
        (heavyResolveDown q.core.cfg * w ^ a +
          heavyNeutralMass (heavy_two_entities hn q.core.cfg) * w ^ (a + 1) +
          heavyResolveUp q.core.cfg * w ^ (a + 2)) *
        η ^ q.blankTicks := by
  rw [heavyClockBandStep_expect_blank_bridge n hn aLo hi q w η hlive]
  have htrace :
      expect (heavyTraceStep n q.core)
          (fun z => w ^ BiCfg.heavyLevel z.cfg.1 * η ^ q.blankTicks) =
        expect (heavyStateStep n q.core.cfg)
    (fun z => w ^ BiCfg.heavyLevel z.1 * η ^ q.blankTicks) := by
    calc
      expect (heavyTraceStep n q.core)
          (fun z => w ^ BiCfg.heavyLevel z.cfg.1 * η ^ q.blankTicks)
        = expect ((heavyTraceStep n q.core).map HeavyTrace.cfg)
            (fun z => w ^ BiCfg.heavyLevel z.1 * η ^ q.blankTicks) := by
          rw [expect_map]
      _ = expect (heavyStateStep n q.core.cfg)
            (fun z => w ^ BiCfg.heavyLevel z.1 * η ^ q.blankTicks) := by
          rw [heavyTraceStep_map_cfg hn q.core]
  rw [htrace]
  have hexp := heavyStateStep_expect_level hn q.core.cfg a ha
    (fun L => w ^ L * η ^ q.blankTicks)
  rw [hexp]
  ring

/-- The blank-occupation potential is a one-step supermartingale on an early
small-gap Heavy-B band. -/
theorem heavyClockBandStep_blank_super
    (n : ℕ) (hn : 3 ≤ n) (g aLo hi : ℕ)
    (hfloor : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n) :
    ∀ q : HeavyClockTrace n,
      expect (heavyClockBandStep n aLo hi q)
          (heavyBlankPotential
            (heavyBlankW n g) (heavyBlankEta n g)) ≤
        heavyBlankPotential
          (heavyBlankW n g) (heavyBlankEta n g) q := by
  intro q
  by_cases hlive : q.core.BandLive aLo hi
  · obtain ⟨a, ha⟩ :
        ∃ a, BiCfg.heavyLevel q.core.cfg.1 = a + 1 := by
      refine ⟨BiCfg.heavyLevel q.core.cfg.1 - 1, ?_⟩
      unfold HeavyTrace.BandLive at hlive
      omega
    have hgap : q.core.cfg.1.y + g ≤ q.core.cfg.1.x :=
      q.core.live_gap hlive hfloor
    have hsum := heavy_mass_sum q.core.cfg (heavy_two_entities hn q.core.cfg)
    have hchoose : 0 < Nat.choose (heavyEntities q.core.cfg) 2 :=
      Nat.choose_pos (heavy_two_entities hn q.core.cfg)
    have hden0 : ((Nat.choose (heavyEntities q.core.cfg) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hchoose.ne'
    have hdt : heavyResolveDown q.core.cfg ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
    have hut : heavyResolveUp q.core.cfg ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden0
    have hnt : heavyNeutralMass (heavy_two_entities hn q.core.cfg) ≠ ⊤ := by
      intro h
      rw [h] at hsum
      simp at hsum
    have hwt : heavyBlankW n g ≠ ⊤ := by
      unfold heavyBlankW
      finiteness
    have hrt : heavyBlankR n g ≠ ⊤ := by
      unfold heavyBlankR
      finiteness
    have hddt : heavyBlankDrift n g ≠ ⊤ := by
      unfold heavyBlankDrift
      finiteness
    have hwr :
        heavyBlankW n g + heavyBlankR n g = 1 :=
      heavyBlankW_add_R n g (by omega)
    have hrd :
        heavyBlankR n g ≤
          heavyBlankW n g * heavyBlankDrift n g := by
      exact (heavyBlank_R_eq_W_mul_drift n g (by omega)).le
    have hw1 : heavyBlankW n g ≤ 1 :=
      heavyBlankW_le_one n g (by omega)
    have hfactor :
        (if q.core.NormalTick then 1 else heavyBlankEta n g) *
            (heavyResolveDown q.core.cfg +
              heavyNeutralMass (heavy_two_entities hn q.core.cfg) * heavyBlankW n g +
              heavyResolveUp q.core.cfg * heavyBlankW n g ^ 2) ≤
          heavyBlankW n g := by
      by_cases hnormal : q.core.NormalTick
      · rw [if_pos hnormal, one_mul]
        exact feller_reduced
          (heavyResolveDown q.core.cfg)
          (heavyNeutralMass (heavy_two_entities hn q.core.cfg))
          (heavyResolveUp q.core.cfg)
          (heavyBlankW n g)
          hsum
          (heavyResolveDown_le_up_mul_blankW hn q.core.cfg hgap)
          hw1 hdt hnt hut
      · rw [if_neg hnormal]
        have hblank : 3 * n ≤ 8 * q.core.cfg.1.b :=
          heavyB_blankHeavy_of_notNormal_live_small
            q.core hlive hnormal hsmall
        unfold heavyBlankEta
        exact heavy_blank_three_term_eta hsum
          (heavyResolve_blank_drift hn q.core.cfg hgap hblank)
          hwr hrd hdt hnt hut hddt hwt hrt
    rw [heavyClockBandStep_expect_blank
      n hn aLo hi q a ha (heavyBlankW n g)
      (heavyBlankEta n g) hlive]
    calc
      (if q.core.NormalTick then 1 else heavyBlankEta n g) *
            (heavyResolveDown q.core.cfg * heavyBlankW n g ^ a +
              heavyNeutralMass (heavy_two_entities hn q.core.cfg) *
                heavyBlankW n g ^ (a + 1) +
              heavyResolveUp q.core.cfg *
                heavyBlankW n g ^ (a + 2)) *
            heavyBlankEta n g ^ q.blankTicks
          =
            (heavyBlankW n g ^ a *
              heavyBlankEta n g ^ q.blankTicks) *
              ((if q.core.NormalTick then 1 else heavyBlankEta n g) *
                (heavyResolveDown q.core.cfg +
                  heavyNeutralMass (heavy_two_entities hn q.core.cfg) * heavyBlankW n g +
                  heavyResolveUp q.core.cfg * heavyBlankW n g ^ 2)) := by
            rw [pow_succ (heavyBlankW n g) a,
              show a + 2 = (a + 1) + 1 by omega,
              pow_succ (heavyBlankW n g) (a + 1)]
            ring
      _ ≤ (heavyBlankW n g ^ a *
              heavyBlankEta n g ^ q.blankTicks) *
            heavyBlankW n g := by
        gcongr
      _ = heavyBlankPotential
            (heavyBlankW n g) (heavyBlankEta n g) q := by
        unfold heavyBlankPotential
        rw [ha, pow_succ]
        ring
  · unfold heavyClockBandStep
    rw [if_neg hlive, expect_pure]

/-- Finite-horizon upper tail for blank-heavy occupation while the stopped
chain remains inside the band. -/
theorem heavyClock_blank_tail
    (n : ℕ) (hn : 3 ≤ n) (g aLo hi : ℕ)
    (hfloor : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (T H : ℕ) (q₀ : HeavyClockTrace n) :
    ∑' z, (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
        iter (heavyClockBandStep n aLo hi) T q₀ z else 0) ≤
      heavyBlankPotential
          (heavyBlankW n g) (heavyBlankEta n g) q₀ /
        (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) := by
  have hw1 : heavyBlankW n g ≤ 1 :=
    heavyBlankW_le_one n g (by omega)
  have hw0 : heavyBlankW n g ≠ 0 := by
    unfold heavyBlankW
    exact ne_of_gt (ENNReal.div_pos
      (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
      (ENNReal.natCast_ne_top _))
  have hwt : heavyBlankW n g ≠ ⊤ := by
    unfold heavyBlankW
    finiteness
  have hη1 : 1 ≤ heavyBlankEta n g := by
    unfold heavyBlankEta
    exact le_add_right le_rfl
  have hη0 : heavyBlankEta n g ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hη1)
  have hηt : heavyBlankEta n g ≠ ⊤ := by
    unfold heavyBlankEta heavyBlankR
    finiteness
  have hθ0 :
      heavyBlankW n g ^ hi * heavyBlankEta n g ^ H ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hη0)
  have hθt :
      heavyBlankW n g ^ hi * heavyBlankEta n g ^ H ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt)
      (ENNReal.pow_ne_top hηt)
  have hsub : ∀ z : HeavyClockTrace n,
      (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
          iter (heavyClockBandStep n aLo hi) T q₀ z else 0) ≤
        (if heavyBlankW n g ^ hi * heavyBlankEta n g ^ H ≤
              heavyBlankPotential
                (heavyBlankW n g) (heavyBlankEta n g) z then
            iter (heavyClockBandStep n aLo hi) T q₀ z else 0) := by
    intro z
    by_cases hz : z.core.BandLive aLo hi ∧ H ≤ z.blankTicks
    · have hlevel : BiCfg.heavyLevel z.core.cfg.1 ≤ hi := by
        unfold HeavyTrace.BandLive at hz
        omega
      have hwPow :
          heavyBlankW n g ^ hi ≤
            heavyBlankW n g ^ BiCfg.heavyLevel z.core.cfg.1 :=
        pow_le_pow_right_of_le_one' hw1 hlevel
      have hηPow :
          heavyBlankEta n g ^ H ≤
            heavyBlankEta n g ^ z.blankTicks :=
        pow_le_pow_right₀ hη1 hz.2
      have hpot :
          heavyBlankW n g ^ hi * heavyBlankEta n g ^ H ≤
            heavyBlankPotential
              (heavyBlankW n g) (heavyBlankEta n g) z := by
        unfold heavyBlankPotential
        exact mul_le_mul hwPow hηPow bot_le bot_le
      simp [hz, hpot]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (heavyClockBandStep n aLo hi) T q₀)
      (heavyBlankPotential
        (heavyBlankW n g) (heavyBlankEta n g))
      (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H)
      hθ0 hθt) ?_
  exact ENNReal.div_le_div_right
    (by
      simpa using
        (expect_iter_le
          (heavyClockBandStep n aLo hi)
          (heavyBlankPotential
            (heavyBlankW n g) (heavyBlankEta n g))
          1
          (by simpa using
            heavyClockBandStep_blank_super n hn g aLo hi hfloor hsmall)
          T q₀))
    (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H)

example :
    3 * 160 ≤ 8 *
      (⟨⟨⟨21, 9, 65⟩, by norm_num [BiCfg.HeavyInv]⟩, 0, 0, 0⟩ :
        HeavyTrace 160).cfg.1.b := by
  apply heavyB_blankHeavy_of_notNormal_live_small
      (aLo := 85) (hi := 88)
  · norm_num [HeavyTrace.BandLive, BiCfg.heavyLevel]
  · norm_num [HeavyTrace.NormalTick]
  · norm_num

example :
    heavyResolveDown (⟨⟨21, 9, 65⟩, by norm_num [BiCfg.HeavyInv]⟩ :
        HeavyState 160) +
        heavyBlankDrift 160 10 ≤
      heavyResolveUp (⟨⟨21, 9, 65⟩, by norm_num [BiCfg.HeavyInv]⟩ :
        HeavyState 160) := by
  apply heavyResolve_blank_drift
  · norm_num
  · norm_num
  · norm_num

example :
    ∀ q : HeavyClockTrace 160,
      expect (heavyClockBandStep 160 85 88 q)
          (heavyBlankPotential
            (heavyBlankW 160 10) (heavyBlankEta 160 10)) ≤
        heavyBlankPotential
          (heavyBlankW 160 10) (heavyBlankEta 160 10) q := by
  apply heavyClockBandStep_blank_super
  · norm_num
  · norm_num
  · norm_num

end Tri

#print axioms Tri.heavyB_blankHeavy_of_notNormal_live_small
#print axioms Tri.heavyB_gap_direction_cross
#print axioms Tri.heavyB_blank_drift_cross
#print axioms Tri.heavyResolve_blank_drift
#print axioms Tri.heavy_blank_three_term_eta
#print axioms Tri.heavyClockBandStep_expect_blank
#print axioms Tri.heavyClockBandStep_blank_super
#print axioms Tri.heavyClock_blank_tail

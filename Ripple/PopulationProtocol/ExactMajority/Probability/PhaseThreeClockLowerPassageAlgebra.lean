-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockLowerPassageAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockOpportunityProcess

/-!
A polynomial supersolution for P7.  It replaces the eight-block sum by a
larger explicit envelope below 0.092 at the same horizon.  The clock
discount and the existing eight-block exponential comparison are unchanged.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageAlgebra

open PhaseThreeScalar

def passagePhi (z : ℝ) : ℝ :=
  11 / 1000 + z / 25 + 3 * z ^ 2 / 20 + z ^ 3 / 2 + 3 * z ^ 4 / 10

def passageSlope (z : ℝ) : ℝ :=
  1 / 25 + 3 * z / 10 + 3 * z ^ 2 / 2 + 6 * z ^ 3 / 5

theorem passagePhi_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ passagePhi z := by
  unfold passagePhi
  positivity

theorem passagePhi_mono {z v : ℝ} (hz : 0 ≤ z) (hzv : z ≤ v) :
    passagePhi z ≤ passagePhi v := by
  unfold passagePhi
  gcongr

theorem passagePhi_upper {z : ℝ} (hz : 0 ≤ z) (hu : z ≤ 401 / 1000) :
    passagePhi z ≤ 23 / 250 := by
  apply (passagePhi_mono hz hu).trans
  norm_num [passagePhi]

theorem passageSlope_upper {z : ℝ} (hz : 0 ≤ z) (hu : z ≤ 1 / 2) :
    passageSlope z ≤ 1 := by
  have h : passageSlope z ≤ passageSlope (1 / 2) := by
    unfold passageSlope
    gcongr
  norm_num [passageSlope] at h
  unfold passageSlope
  linarith

theorem passageSlope_margin {z : ℝ} (hz : 0 ≤ z) (hu : z ≤ 1 / 2) :
    (1 / 10 + z) ^ 2 + 2 * passagePhi z + 1 / 125 ≤ passageSlope z := by
  have hsq : z ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hz hu 2
  have hp : 0 ≤ z ^ 2 * (1 / 5 - 3 * z ^ 2 / 5) :=
    mul_nonneg (sq_nonneg _) (by nlinarith only [hsq])
  have hzpow : 0 ≤ z ^ 3 := pow_nonneg hz _
  dsimp only [passagePhi, passageSlope]
  nlinarith only [hp, hzpow, hz]

theorem passagePhi_increment {z δ : ℝ} (hz : 0 ≤ z) (hd : 0 ≤ δ) :
    δ * passageSlope z ≤ passagePhi (z + δ) - passagePhi z := by
  have h : 0 ≤ δ ^ 2 *
      (3 / 20 + 3 * z / 2 + 9 * z ^ 2 / 5 +
        δ * (1 / 2 + 6 * z / 5) + 3 * δ ^ 2 / 10) := by positivity
  dsimp only [passagePhi, passageSlope]
  nlinarith only [h]

theorem passagePhi_discrete {z δ : ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ 1 / 2)
    (hd : 0 ≤ δ) (hdu : δ ≤ 1 / 1000000) :
    δ * ((1 / 10 + z + δ) ^ 2 + 2 * passagePhi z) ≤
      (1 - δ) * (passagePhi (z + δ) - passagePhi z) := by
  have hinc := passagePhi_increment hz hd
  have hmargin := passageSlope_margin hz hzu
  have hslope := passageSlope_upper hz hzu
  have hround : (1 / 10 + z + δ) ^ 2 ≤ (1 / 10 + z) ^ 2 + 2 * δ := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 / 5 + 2 * z + δ ≤ (2 : ℝ) by linarith) hd
    nlinarith only [h]
  have hds := mul_le_mul_of_nonneg_left hslope hd
  have hinner :
      (1 / 10 + z + δ) ^ 2 + 2 * passagePhi z ≤
        (1 - δ) * passageSlope z := by
    nlinarith only [hmargin, hround, hds, hdu]
  have hmul := mul_le_mul_of_nonneg_left hinner hd
  have hincmul := mul_le_mul_of_nonneg_left hinc
    (show 0 ≤ 1 - δ by linarith)
  nlinarith only [hmul, hincmul]

def lowerHorizon (C : ℕ) : ℕ := 8 * Nat.ceil ((C : ℝ) / 20)
def lowerBase (C : ℕ) : ℝ := 1 + 2 / ((C : ℝ) - 1)
def lowerDiscount (C j : ℕ) : ℝ := 1 / lowerBase C ^ j
def lowerEnvelope (C j : ℕ) : ℝ := (C : ℝ) * passagePhi ((j : ℝ) / (C : ℝ))
def lowerSource (C j : ℕ) : ℝ :=
  ((StageEventSpec.bulkThreshold C : ℝ) + (j : ℝ)) ^ 2 /
    ((C : ℝ) * ((C : ℝ) - 1))
def lowerRate (C j : ℕ) (Y : ℝ) : ℝ :=
  2 * Y / ((C : ℝ) - 1) + lowerSource C j

theorem lowerBase_one_le (C : ℕ) (hC : 1000000 ≤ C) : 1 ≤ lowerBase C := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  unfold lowerBase
  have h : 0 ≤ 2 / ((C : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
  linarith

theorem lowerDiscount_bounds (C j : ℕ) (hC : 1000000 ≤ C) :
    0 < lowerDiscount C j ∧ lowerDiscount C j ≤ 1 := by
  have ha := lowerBase_one_le C hC
  have hp : 1 ≤ lowerBase C ^ j := one_le_pow₀ ha
  unfold lowerDiscount
  exact ⟨div_pos (by norm_num) (by linarith), (div_le_one (by linarith)).2 hp⟩

theorem lowerHorizon_bounds (C : ℕ) (hC : 1000000 ≤ C) :
    (2 / 5 : ℝ) * C ≤ (lowerHorizon C : ℝ) ∧
      (lowerHorizon C : ℝ) ≤ (401 / 1000 : ℝ) * C ∧
      (lowerHorizon C : ℝ) ≤ (C : ℝ) / 2 := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hb := eight_block_calibration hCR
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ (C : ℝ) / 20)
  simp only [lowerHorizon, Nat.cast_mul, Nat.cast_ofNat]
  exact ⟨hb.2.2.2.2.1, by linarith, hb.2.2.2.2.2⟩

theorem lowerIndex_ratio (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) :
    0 ≤ (j : ℝ) / (C : ℝ) ∧ (j : ℝ) / (C : ℝ) ≤ 401 / 1000 := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hjR : (j : ℝ) ≤ lowerHorizon C := by exact_mod_cast hj
  refine ⟨by positivity, (div_le_iff₀ (by linarith)).2 ?_⟩
  linarith [(lowerHorizon_bounds C hC).2.1]

theorem lowerEnvelope_nonneg (C j : ℕ) : 0 ≤ lowerEnvelope C j :=
  mul_nonneg (Nat.cast_nonneg C) (passagePhi_nonneg (by positivity))

theorem lowerEnvelope_upper (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) :
    lowerEnvelope C j ≤ (23 / 250 : ℝ) * C := by
  have hz := lowerIndex_ratio C j hC hj
  have h := mul_le_mul_of_nonneg_left (passagePhi_upper hz.1 hz.2) (Nat.cast_nonneg C)
  simpa only [lowerEnvelope, mul_comm] using h

theorem lowerSource_bounds (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) : 0 ≤ lowerSource C j ∧ lowerSource C j ≤ 1 / 2 := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hpos : 0 < (C : ℝ) := by linarith
  have hm : 0 < (C : ℝ) - 1 := by linarith
  have hb : (StageEventSpec.bulkThreshold C : ℝ) ≤ (C : ℝ) / 10 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (C : ℝ) / 10)).le
  have hjR : (j : ℝ) ≤ lowerHorizon C := by exact_mod_cast hj
  have hsum : (StageEventSpec.bulkThreshold C : ℝ) + j ≤ (3 / 5 : ℝ) * C := by
    linarith [(lowerHorizon_bounds C hC).2.1]
  have hsquare := pow_le_pow_left₀
    (show 0 ≤ (StageEventSpec.bulkThreshold C : ℝ) + j by positivity) hsum 2
  refine ⟨div_nonneg (sq_nonneg _) (mul_pos hpos hm).le, ?_⟩
  apply (div_le_iff₀ (mul_pos hpos hm)).2
  have hlarge := mul_nonneg hpos.le (show 0 ≤ (C : ℝ) - 10 by linarith)
  nlinarith only [hsquare, hlarge]

theorem lowerRate_bounds (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) (Y : ℝ) (hY : 0 ≤ Y) (hYC : Y ≤ C) :
    0 ≤ lowerRate C j Y ∧ lowerRate C j Y ≤ 3 := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hs := lowerSource_bounds C j hC hj
  have hlinear : 2 * Y / ((C : ℝ) - 1) ≤ 5 / 2 := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  refine ⟨add_nonneg (div_nonneg (by positivity) (by linarith)) hs.1, ?_⟩
  dsimp only [lowerRate]
  linarith only [hlinear, hs.2]

/-- A discrete supersolution for every tick before the unchanged P7 horizon. -/
theorem lowerEnvelope_step (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j < lowerHorizon C) :
    lowerBase C * lowerEnvelope C j + lowerSource C j ≤ lowerEnvelope C (j + 1) := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hpos : 0 < (C : ℝ) := by linarith
  have hm : 0 < (C : ℝ) - 1 := by linarith
  have hz := lowerIndex_ratio C j hC hj.le
  have hd : (0 : ℝ) ≤ 1 / (C : ℝ) := by positivity
  have hdu : (1 : ℝ) / C ≤ 1 / 1000000 := by
    exact one_div_le_one_div_of_le (by norm_num) hCR
  have hpoly := passagePhi_discrete hz.1 (by linarith [hz.2]) hd hdu
  have hb : (StageEventSpec.bulkThreshold C : ℝ) ≤ (C : ℝ) / 10 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (C : ℝ) / 10)).le
  have hratio :
      ((StageEventSpec.bulkThreshold C : ℝ) + j) / (C : ℝ) ≤
        1 / 10 + (j : ℝ) / C + 1 / C := by
    apply (div_le_iff₀ hpos).2
    have he :
        (1 / 10 + (j : ℝ) / C + 1 / C) * (C : ℝ) =
          (C : ℝ) / 10 + j + 1 := by field_simp [hpos.ne'] <;> ring
    rw [he]
    linarith
  have hsquare := pow_le_pow_left₀ (by positivity) hratio 2
  have hsqscaled := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ (C : ℝ) / ((C : ℝ) - 1) by positivity)
  have hsource :
      lowerSource C j ≤ (C : ℝ) / ((C : ℝ) - 1) *
        (1 / 10 + (j : ℝ) / C + 1 / C) ^ 2 := by
    convert hsqscaled using 1 <;>
      dsimp only [lowerSource] <;> field_simp [hpos.ne', hm.ne'] <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ (C : ℝ) ^ 2 / ((C : ℝ) - 1) by positivity)
  have hdiff :
      (C : ℝ) ^ 2 / ((C : ℝ) - 1) *
        ((1 - 1 / C) *
          (passagePhi ((j : ℝ) / C + 1 / C) - passagePhi ((j : ℝ) / C)) -
          (1 / C) * ((1 / 10 + (j : ℝ) / C + 1 / C) ^ 2 +
            2 * passagePhi ((j : ℝ) / C))) =
        lowerEnvelope C (j + 1) - lowerBase C * lowerEnvelope C j -
          (C : ℝ) / ((C : ℝ) - 1) *
            (1 / 10 + (j : ℝ) / C + 1 / C) ^ 2 := by
    have he : ((j + 1 : ℕ) : ℝ) / (C : ℝ) = (j : ℝ) / C + 1 / C := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    unfold lowerEnvelope lowerBase
    rw [he]
    field_simp [hpos.ne', hm.ne']
    <;> ring
  have hnonneg : 0 ≤ lowerEnvelope C (j + 1) -
      lowerBase C * lowerEnvelope C j -
        (C : ℝ) / ((C : ℝ) - 1) *
          (1 / 10 + (j : ℝ) / C + 1 / C) ^ 2 := by
    rw [← hdiff]
    nlinarith only [hscaled]
  linarith only [hnonneg, hsource]

theorem lowerBase_power_lt (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) : lowerBase C ^ j < 3 := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hc := eight_block_calibration hCR
  have hblock : lowerBase C ^ Nat.ceil ((C : ℝ) / 20) ≤ (10 / 9 : ℝ) :=
    hc.2.1.trans hc.2.2.1.le
  calc
    _ ≤ lowerBase C ^ (Nat.ceil ((C : ℝ) / 20) * 8) :=
      pow_le_pow_right₀ (lowerBase_one_le C hC) (by simpa only [lowerHorizon, Nat.mul_comm] using hj)
    _ = (lowerBase C ^ Nat.ceil ((C : ℝ) / 20)) ^ 8 := pow_mul _ _ _
    _ ≤ (10 / 9 : ℝ) ^ 8 := pow_le_pow_left₀
      (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (lowerBase_one_le C hC)) _) hblock _
    _ < 3 := hc.2.2.2.1

theorem lower_initial_gap (C : ℕ) (hC : 1000000 ≤ C) (Y : ℝ)
    (hY : Y ≤ (StageEventSpec.bulkThreshold C : ℝ) ^ 2 / (C : ℝ)) :
    Y ≤ lowerEnvelope C 0 := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hp : 0 < (C : ℝ) := by linarith
  have hs := eight_block_initial_ceiling_square hCR
  have hmul := mul_le_mul_of_nonneg_left hs hp.le
  have hid : (C : ℝ) * ((StageEventSpec.bulkThreshold C : ℝ) / C) ^ 2 =
      (StageEventSpec.bulkThreshold C : ℝ) ^ 2 / C := by
    field_simp [hp.ne'] <;> ring
  change (C : ℝ) * ((StageEventSpec.bulkThreshold C : ℝ) / C) ^ 2 ≤ _ at hmul
  rw [hid] at hmul
  norm_num [lowerEnvelope, passagePhi]
  linarith only [hY, hmul, hp]

def lowerExponent (C j : ℕ) (Y : ℝ) : ℝ :=
  (1 / 1000 : ℝ) * lowerDiscount C j * (Y - lowerEnvelope C j) -
    (3 / 1000000 : ℝ) * j

theorem lowerExponent_upper (C j : ℕ) (hC : 1000000 ≤ C)
    (Y : ℝ) (hY : Y ≤ C) :
    lowerExponent C j Y ≤ (C : ℝ) / 1000 := by
  have hd := lowerDiscount_bounds C j hC
  have henv := lowerEnvelope_nonneg C j
  have hprod := mul_le_mul_of_nonneg_left
    (show Y - lowerEnvelope C j ≤ (C : ℝ) by linarith) hd.1.le
  have hcap := mul_le_mul_of_nonneg_right hd.2 (Nat.cast_nonneg C)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold lowerExponent
  nlinarith only [hprod, hcap, hj]

theorem lowerExponent_at_hit (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) (Y : ℝ)
    (hhit : (StageEventSpec.bulkThreshold C : ℝ) ≤ Y) :
    (C : ℝ) / 1000000 ≤ lowerExponent C j Y := by
  have hCR : (1000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hb : (C : ℝ) / 10 ≤ (StageEventSpec.bulkThreshold C : ℝ) := Nat.le_ceil _
  have he := lowerEnvelope_upper C j hC hj
  have hpow := lowerBase_power_lt C j hC hj
  have hp : 0 < lowerBase C ^ j :=
    pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (lowerBase_one_le C hC)) _
  have hdisc : (C : ℝ) / 400 ≤ lowerDiscount C j * (Y - lowerEnvelope C j) := by
    rw [lowerDiscount, one_div_mul_eq_div]
    apply (le_div_iff₀ hp).2
    have hm := mul_le_mul_of_nonneg_left hpow.le
      (show 0 ≤ (C : ℝ) / 400 by positivity)
    nlinarith only [hm, hb, hhit, he, hCR]
  have hjR : (j : ℝ) ≤ lowerHorizon C := by exact_mod_cast hj
  have hhalf := (lowerHorizon_bounds C hC).2.2
  unfold lowerExponent
  nlinarith only [hdisc, hjR, hhalf]

theorem exp_small_increment (z : ℝ) (hz : 0 ≤ z) (hu : z ≤ 1) :
    0 ≤ Real.exp z - 1 ∧ Real.exp z - 1 ≤ z + z ^ 2 := by
  have he := Real.abs_exp_sub_one_sub_id_le (show |z| ≤ 1 by simpa [abs_of_nonneg hz] using hu)
  exact ⟨sub_nonneg.mpr (Real.one_le_exp hz), by linarith [(abs_le.mp he).2]⟩

theorem lower_exponential_rate (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j ≤ lowerHorizon C) (Y p q : ℝ)
    (hY : 0 ≤ Y) (hYC : Y ≤ C) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrate : p ≤ q * lowerRate C j Y) :
    (Real.exp ((1 / 1000 : ℝ) * lowerDiscount C (j + 1)) - 1) * p ≤
      q * ((1 / 1000 : ℝ) * lowerDiscount C (j + 1) * lowerRate C j Y +
        3 / 1000000) := by
  have hd := lowerDiscount_bounds C (j + 1) hC
  let z := (1 / 1000 : ℝ) * lowerDiscount C (j + 1)
  have hz : 0 ≤ z := mul_nonneg (by norm_num) hd.1.le
  have hzu : z ≤ 1 / 1000 := by dsimp only [z]; linarith [hd.2]
  have he := exp_small_increment z hz (by linarith)
  have hk := lowerRate_bounds C j hC hj Y hY hYC
  have hsq : z ^ 2 ≤ (1 / 1000000 : ℝ) :=
    (pow_le_pow_left₀ hz hzu 2).trans_eq (by norm_num)
  have hterm : z ^ 2 * lowerRate C j Y ≤ 3 / 1000000 := by
    calc
      _ ≤ (1 / 1000000 : ℝ) * 3 := mul_le_mul hsq hk.2 hk.1 (by norm_num)
      _ = _ := by norm_num
  have hfirst := mul_le_mul_of_nonneg_right he.2 hp
  have hsecond := mul_le_mul_of_nonneg_left hrate (by positivity : 0 ≤ z + z ^ 2)
  have hlast := mul_le_mul_of_nonneg_left hterm hq
  change (Real.exp z - 1) * p ≤ _
  dsimp only [z] at hfirst hsecond hlast ⊢
  nlinarith only [hfirst, hsecond, hlast]


theorem lowerDiscount_succ (C j : ℕ) (hC : 1000000 ≤ C) :
    lowerDiscount C j = lowerBase C * lowerDiscount C (j + 1) := by
  have ha : lowerBase C ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (lowerBase_one_le C hC))
  unfold lowerDiscount
  rw [pow_succ]
  field_simp [ha]
  <;> ring

theorem lowerExponent_tick (C j : ℕ) (hC : 1000000 ≤ C)
    (hj : j < lowerHorizon C) (Y P : ℝ) :
    lowerExponent C (j + 1) (Y + P) ≤ lowerExponent C j Y +
      (1 / 1000 : ℝ) * lowerDiscount C (j + 1) * P -
        ((1 / 1000 : ℝ) * lowerDiscount C (j + 1) * lowerRate C j Y +
          3 / 1000000) := by
  have he := lowerEnvelope_step C j hC hj
  have hd := lowerDiscount_bounds C (j + 1) hC
  have hm := mul_le_mul_of_nonneg_left he
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 1000) hd.1.le)
  unfold lowerExponent
  rw [lowerDiscount_succ C j hC]
  simp only [Nat.cast_add, Nat.cast_one]
  dsimp only [lowerRate, lowerBase] at hm ⊢
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem exp_bernoulli_factor (x θ D P : ℝ) (hP : P = 0 ∨ P = 1) :
    Real.exp (x + θ * P - D) =
      Real.exp x * (Real.exp (-D) * (1 + (Real.exp θ - 1) * P)) := by
  rcases hP with rfl | rfl
  · simp only [mul_zero, add_zero, mul_one]
    rw [← Real.exp_add]
    congr 1
  · simp only [mul_one]
    rw [show 1 + (Real.exp θ - 1) = Real.exp θ by ring,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageAlgebra

end

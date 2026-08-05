/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBClockTrace
import Tri.MaskedCounting

/-!
# The normal/free-Y branch of the Heavy-B occupation clock

On a normal tick, the masked fuel labels are the same pair labels used by the
Double-B normal branch, `xy` and `yb`.  At Heavy-B scale their unnormalized mass
is `y * heavyLevel`; the state-dependent pair denominator is bounded by the
ambient `C(n,2)`.
-/

namespace Tri

open scoped ENNReal

/-- The four non-fuel pair classes for the normal mask. -/
noncomputable def heavyNormalIdleMass {n : ℕ}
    (hn : 3 ≤ n) (q : HeavyClockTrace n) : ℝ≥0∞ :=
  let h := heavy_two_entities hn q.core.cfg
  dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .xx +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .yy +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .xb +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .bb

/-- The two masked-fuel pair classes, `xy` and `yb`. -/
noncomputable def heavyNormalFuelMass {n : ℕ}
    (hn : 3 ≤ n) (q : HeavyClockTrace n) : ℝ≥0∞ :=
  let h := heavy_two_entities hn q.core.cfg
  dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .xy +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .yb

/-- Exact mass of a Heavy-B normal masked-fuel event (`xy` or `yb`). -/
theorem heavyPairPMF_normalFuel_mass
    (x y b : ℕ) (h : 2 ≤ x + y + b) :
    dbPairPMF x y b h .xy + dbPairPMF x y b h .yb =
      (y * (x + b) : ℝ≥0∞) /
        (Nat.choose (x + y + b) 2 : ℝ≥0∞) := by
  simp only [dbPairPMF_apply, PairComp.weight]
  rw [ENNReal.div_add_div_same]
  congr 1
  exact_mod_cast (by ring : x * y + y * b = y * (x + b))

/-- Heavy-B normal-fuel cross bound over the ambient denominator. -/
theorem heavyB_normalFuel_cross
    {n : ℕ} (s : HeavyState n)
    (hlevel : n ≤ 2 * BiCfg.heavyLevel s.1)
    (hnormal : n ≤ 16 * s.1.y) :
    Nat.choose n 2 ≤
      16 * (s.1.y * BiCfg.heavyLevel s.1) := by
  have hmul : n * n ≤
      (16 * s.1.y) * (2 * BiCfg.heavyLevel s.1) :=
    Nat.mul_le_mul hnormal hlevel
  have hchoose := two_mul_choose_two n
  have hsub : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith

/-- On a normal/free-`Y` Heavy-B tick, masked fuel has mass at least `1/16`. -/
theorem heavyNormalFuelMass_ge_sixteenth
    {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n)
    (hlevel : n ≤ 2 * BiCfg.heavyLevel s.1)
    (hnormal : n ≤ 16 * s.1.y) :
    (1 : ℝ≥0∞) / 16 ≤
      dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xy +
        dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .yb := by
  rw [heavyPairPMF_normalFuel_mass]
  have hcrossN := heavyB_normalFuel_cross s hlevel hnormal
  have hent : heavyEntities s ≤ n := by
    have := s.2
    simp only [BiCfg.HeavyInv, heavyEntities] at this ⊢
    omega
  have hcross :
      Nat.choose (s.1.x + s.1.y + s.1.b) 2 ≤
        16 * (s.1.y * (s.1.x + s.1.b)) := by
    have h := (Nat.choose_le_choose 2 hent).trans hcrossN
    simpa [heavyEntities, BiCfg.heavyLevel] using h
  have hden0 :
      ((Nat.choose (s.1.x + s.1.y + s.1.b) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (heavy_two_entities hn s)).ne'
  have hdenTop :
      ((Nat.choose (s.1.x + s.1.y + s.1.b) 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)).2
  calc
    (1 : ℝ≥0∞) / 16 *
          (Nat.choose (s.1.x + s.1.y + s.1.b) 2 : ℝ≥0∞)
        = (Nat.choose (s.1.x + s.1.y + s.1.b) 2 : ℝ≥0∞) / 16 := by
            simp only [div_eq_mul_inv]
            ac_rfl
    _ ≤ (s.1.y * (s.1.x + s.1.b) : ℝ≥0∞) := by
          apply ENNReal.div_le_of_le_mul
          exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)

/-- Fuel and non-fuel masses partition the six pair labels. -/
theorem heavyNormal_masses
    {n : ℕ} (hn : 3 ≤ n) (q : HeavyClockTrace n) :
    heavyNormalFuelMass hn q + heavyNormalIdleMass hn q = 1 := by
  have hh := heavy_two_entities hn q.core.cfg
  have hsum := (dbPairPMF q.core.cfg.1.x q.core.cfg.1.y
    q.core.cfg.1.b hh).tsum_coe
  rw [tsum_fintype, show (Finset.univ : Finset PairComp) =
      {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
        PairComp.yb, PairComp.bb} from rfl] at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  unfold heavyNormalFuelMass heavyNormalIdleMass
  rw [← hsum]
  ring

/-- Exact masked-potential expansion at a live normal tick. -/
theorem heavyClockBandStep_expect_normal
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (q : HeavyClockTrace n) (η w : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi)
    (hnormal : q.core.NormalTick) :
    expect (heavyClockBandStep n aLo hi q)
        (maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel η w) =
      heavyNormalIdleMass hn q *
          (η ^ (q.normalTicks + 1) * w ^ q.normalFuel) +
        heavyNormalFuelMass hn q *
          (η ^ (q.normalTicks + 1) * w ^ (q.normalFuel + 1)) := by
  have hh := heavy_two_entities hn q.core.cfg
  have key : ∀ k : PairComp,
      dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          maskedCountPotential HeavyClockTrace.normalTicks
            HeavyClockTrace.normalFuel η w
            (PairComp.nextHeavyClockTrace q k) =
        dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          (η ^ (q.normalTicks + 1) *
            w ^ (q.normalFuel + k.heavyNormalFuelInc)) := by
    intro k
    by_cases hw :
        PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]
      simp
    · unfold PairComp.nextHeavyClockTrace
      rw [dif_neg hw]
      simp only [maskedCountPotential, hnormal, if_pos]
  unfold heavyClockBandStep
  rw [if_pos hlive, dif_pos hh, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
      {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
        PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [key .xx, key .xy, key .yy, key .xb, key .yb, key .bb]
  simp only [PairComp.heavyNormalFuelInc]
  unfold heavyNormalIdleMass heavyNormalFuelMass
  ring

/-- At a live complementary tick the normal masked potential is unchanged in
expectation. -/
theorem heavyClockBandStep_expect_not_normal
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (q : HeavyClockTrace n) (η w : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi)
    (hnormal : ¬q.core.NormalTick) :
    expect (heavyClockBandStep n aLo hi q)
        (maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel η w) =
      maskedCountPotential HeavyClockTrace.normalTicks
        HeavyClockTrace.normalFuel η w q := by
  have hh := heavy_two_entities hn q.core.cfg
  have key : ∀ k : PairComp,
      dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          maskedCountPotential HeavyClockTrace.normalTicks
            HeavyClockTrace.normalFuel η w
            (PairComp.nextHeavyClockTrace q k) =
        dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          maskedCountPotential HeavyClockTrace.normalTicks
            HeavyClockTrace.normalFuel η w q := by
    intro k
    by_cases hw :
        PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]
      simp
    · unfold PairComp.nextHeavyClockTrace
      rw [dif_neg hw]
      simp only [maskedCountPotential, hnormal, if_false, add_zero]
  unfold heavyClockBandStep
  rw [if_pos hlive, dif_pos hh, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
      {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
        PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [key .xx, key .xy, key .yy, key .xb, key .yb, key .bb]
  have hsum := (dbPairPMF q.core.cfg.1.x q.core.cfg.1.y
    q.core.cfg.1.b hh).tsum_coe
  rw [tsum_fintype, show (Finset.univ : Finset PairComp) =
      {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
        PairComp.yb, PairComp.bb} from rfl] at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  conv_rhs =>
    rw [← one_mul
      (maskedCountPotential HeavyClockTrace.normalTicks
        HeavyClockTrace.normalFuel η w q), ← hsum]
  ring

/-- The normal masked potential is a one-step supermartingale throughout a
majority-side Heavy-B band. -/
theorem heavyClockBandStep_normal_super
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ 2 * (aLo + 1)) (η w : ℝ≥0∞)
    (hw1 : w ≤ 1)
    (hfactor :
      η * ((15 : ℝ≥0∞) / 16 + (1 / 16) * w) ≤ 1) :
    ∀ q : HeavyClockTrace n,
      expect (heavyClockBandStep n aLo hi q)
          (maskedCountPotential HeavyClockTrace.normalTicks
            HeavyClockTrace.normalFuel η w) ≤
        maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel η w q := by
  intro q
  by_cases hlive : q.core.BandLive aLo hi
  · by_cases hnormal : q.core.NormalTick
    · rw [heavyClockBandStep_expect_normal n hn aLo hi q η w hlive hnormal]
      have hlevel : n ≤ 2 * BiCfg.heavyLevel q.core.cfg.1 := by
        unfold HeavyTrace.BandLive at hlive
        omega
      have hq :
          (1 : ℝ≥0∞) / 16 ≤ heavyNormalFuelMass hn q := by
        unfold heavyNormalFuelMass
        exact heavyNormalFuelMass_ge_sixteenth hn q.core.cfg hlevel hnormal
      have hp : (1 : ℝ≥0∞) / 16 + 15 / 16 = 1 := by
        rw [ENNReal.div_add_div_same]
        have hnum : (1 : ℝ≥0∞) + 15 = 16 := by norm_num
        rw [hnum]
        exact ENNReal.div_self
          (by norm_num : (16 : ℝ≥0∞) ≠ 0)
          (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
      have hm := heavyNormal_masses hn q
      have hscalar :
          heavyNormalIdleMass hn q + heavyNormalFuelMass hn q * w ≤
            15 / 16 + (1 / 16 : ℝ≥0∞) * w :=
        step_factor_antitone_ennreal hp hm hw1 hq
      calc
        heavyNormalIdleMass hn q *
              (η ^ (q.normalTicks + 1) * w ^ q.normalFuel) +
            heavyNormalFuelMass hn q *
              (η ^ (q.normalTicks + 1) * w ^ (q.normalFuel + 1))
            = η *
                (heavyNormalIdleMass hn q + heavyNormalFuelMass hn q * w) *
                maskedCountPotential HeavyClockTrace.normalTicks
                  HeavyClockTrace.normalFuel η w q := by
                    unfold maskedCountPotential
                    rw [pow_succ η q.normalTicks, pow_succ w q.normalFuel]
                    ring
        _ ≤ η * (15 / 16 + (1 / 16 : ℝ≥0∞) * w) *
              maskedCountPotential HeavyClockTrace.normalTicks
                HeavyClockTrace.normalFuel η w q := by
          gcongr
        _ ≤ 1 * maskedCountPotential HeavyClockTrace.normalTicks
              HeavyClockTrace.normalFuel η w q := by
          gcongr
        _ = maskedCountPotential HeavyClockTrace.normalTicks
              HeavyClockTrace.normalFuel η w q := one_mul _
    · rw [heavyClockBandStep_expect_not_normal n hn aLo hi q η w hlive hnormal]
  · unfold heavyClockBandStep
    rw [if_neg hlive, expect_pure]

/-- Finite-horizon lower tail for the number of masked-fuel labels observed on
normal ticks. -/
theorem heavyClock_normal_tail
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ 2 * (aLo + 1)) (η w : ℝ≥0∞)
    (hη1 : 1 ≤ η) (hηtop : η ≠ ⊤)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hfactor :
      η * ((15 : ℝ≥0∞) / 16 + (1 / 16) * w) ≤ 1)
    (T H m : ℕ) (q₀ : HeavyClockTrace n) :
    ∑' z, (if H ≤ z.normalTicks ∧ z.normalFuel ≤ m then
        iter (heavyClockBandStep n aLo hi) T q₀ z else 0) ≤
      maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel η w q₀ /
        (η ^ H * w ^ m) := by
  exact masked_count_tail
    (heavyClockBandStep n aLo hi)
    HeavyClockTrace.normalTicks HeavyClockTrace.normalFuel
    η w hη1 hηtop hw1 hw0
    (heavyClockBandStep_normal_super n hn aLo hi hnLo η w hw1 hfactor)
    T H m q₀

/-- The concrete `w = 1/2`, `η = 32/31` normal-tail specialization. -/
theorem heavyClock_normal_tail_half
    (n : ℕ) (hn : 3 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ 2 * (aLo + 1))
    (T H m : ℕ) (q₀ : HeavyClockTrace n) :
    ∑' z, (if H ≤ z.normalTicks ∧ z.normalFuel ≤ m then
        iter (heavyClockBandStep n aLo hi) T q₀ z else 0) ≤
      maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
        (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ m) := by
  apply heavyClock_normal_tail n hn aLo hi hnLo
      ((32 : ℝ≥0∞) / 31) (1 / 2)
  · rw [← ENNReal.toReal_le_toReal (by norm_num)
        (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  · exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  · rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num

example :
    ∀ q : HeavyClockTrace 160,
      expect (heavyClockBandStep 160 85 88 q)
          (maskedCountPotential HeavyClockTrace.normalTicks
            HeavyClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2)) ≤
        maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q := by
  apply heavyClockBandStep_normal_super
  · norm_num
  · norm_num
  · norm_num
  · rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num

end Tri

#print axioms Tri.heavyPairPMF_normalFuel_mass
#print axioms Tri.heavyB_normalFuel_cross
#print axioms Tri.heavyNormalFuelMass_ge_sixteenth
#print axioms Tri.heavyClockBandStep_normal_super
#print axioms Tri.heavyClock_normal_tail_half

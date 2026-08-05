/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockTrace
import Tri.MaskedCounting

/-!
# The normal/free-Y branch of the Double-B occupation clock

On a normal tick, `xy` and `yb` are the masked successes and have conditional
mass at least `1/16`.  The potential
`η^normalTicks * w^normalFuel` is therefore a supermartingale for every
`η * (15/16 + (1/16)w) ≤ 1`.
-/

namespace Tri

open scoped ENNReal

/-- The four non-fuel pair classes. -/
noncomputable def doubleNormalIdleMass {n : ℕ}
    (hn : 2 ≤ n) (q : DoubleClockTrace n) : ℝ≥0∞ :=
  let h : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b := by
    have := q.core.cfg.2
    simp only [BiCfg.DoubleInv] at this
    omega
  dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .xx +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .yy +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .xb +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .bb

/-- The two fuel pair classes. -/
noncomputable def doubleNormalFuelMass {n : ℕ}
    (hn : 2 ≤ n) (q : DoubleClockTrace n) : ℝ≥0∞ :=
  let h : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b := by
    have := q.core.cfg.2
    simp only [BiCfg.DoubleInv] at this
    omega
  dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .xy +
    dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h .yb

/-- Fuel and non-fuel masses partition the six pair labels. -/
theorem doubleNormal_masses
    {n : ℕ} (hn : 2 ≤ n) (q : DoubleClockTrace n) :
    doubleNormalFuelMass hn q + doubleNormalIdleMass hn q = 1 := by
  have hh : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b := by
    have := q.core.cfg.2
    simp only [BiCfg.DoubleInv] at this
    omega
  have hsum := (dbPairPMF q.core.cfg.1.x q.core.cfg.1.y
    q.core.cfg.1.b hh).tsum_coe
  rw [tsum_fintype, show (Finset.univ : Finset PairComp) =
      {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
        PairComp.yb, PairComp.bb} from rfl] at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  unfold doubleNormalFuelMass doubleNormalIdleMass
  rw [← hsum]
  ring

/-- Exact masked-potential expansion at a live normal tick. -/
theorem doubleClockBandStep_expect_normal
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (q : DoubleClockTrace n) (η w : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi)
    (hnormal : q.core.NormalTick) :
    expect (doubleClockBandStep n hn aLo hi q)
        (maskedCountPotential DoubleClockTrace.normalTicks
          DoubleClockTrace.normalFuel η w) =
      doubleNormalIdleMass hn q *
          (η ^ (q.normalTicks + 1) * w ^ q.normalFuel) +
        doubleNormalFuelMass hn q *
          (η ^ (q.normalTicks + 1) * w ^ (q.normalFuel + 1)) := by
  have hh : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b := by
    have := q.core.cfg.2
    simp only [BiCfg.DoubleInv] at this
    omega
  have key : ∀ k : PairComp,
      dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          maskedCountPotential DoubleClockTrace.normalTicks
            DoubleClockTrace.normalFuel η w
            (PairComp.nextDoubleClockTrace q k) =
        dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          (η ^ (q.normalTicks + 1) *
            w ^ (q.normalFuel + k.fuelInc)) := by
    intro k
    by_cases hw :
        PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]
      simp
    · unfold PairComp.nextDoubleClockTrace
      rw [dif_neg hw]
      simp only [maskedCountPotential, hnormal, if_pos]
  unfold doubleClockBandStep
  rw [if_pos hlive, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
      {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
        PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [key .xx, key .xy, key .yy, key .xb, key .yb, key .bb]
  simp only [PairComp.fuelInc]
  unfold doubleNormalIdleMass doubleNormalFuelMass
  ring

/-- At a live complementary tick the masked potential is unchanged in
expectation. -/
theorem doubleClockBandStep_expect_not_normal
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (q : DoubleClockTrace n) (η w : ℝ≥0∞)
    (hlive : q.core.BandLive aLo hi)
    (hnormal : ¬q.core.NormalTick) :
    expect (doubleClockBandStep n hn aLo hi q)
        (maskedCountPotential DoubleClockTrace.normalTicks
          DoubleClockTrace.normalFuel η w) =
      maskedCountPotential DoubleClockTrace.normalTicks
        DoubleClockTrace.normalFuel η w q := by
  have hh : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b := by
    have := q.core.cfg.2
    simp only [BiCfg.DoubleInv] at this
    omega
  have key : ∀ k : PairComp,
      dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          maskedCountPotential DoubleClockTrace.normalTicks
            DoubleClockTrace.normalFuel η w
            (PairComp.nextDoubleClockTrace q k) =
        dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b hh k *
          maskedCountPotential DoubleClockTrace.normalTicks
            DoubleClockTrace.normalFuel η w q := by
    intro k
    by_cases hw :
        PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]
      simp
    · unfold PairComp.nextDoubleClockTrace
      rw [dif_neg hw]
      simp only [maskedCountPotential, hnormal, if_false, add_zero]
  unfold doubleClockBandStep
  rw [if_pos hlive, expect_map]
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
      (maskedCountPotential DoubleClockTrace.normalTicks
        DoubleClockTrace.normalFuel η w q), ← hsum]
  ring

/-- The normal masked potential is a one-step supermartingale throughout a
majority-side band. -/
theorem doubleClockBandStep_normal_super
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ aLo) (η w : ℝ≥0∞)
    (hw1 : w ≤ 1)
    (hfactor :
      η * ((15 : ℝ≥0∞) / 16 + (1 / 16) * w) ≤ 1) :
    ∀ q : DoubleClockTrace n,
      expect (doubleClockBandStep n hn aLo hi q)
          (maskedCountPotential DoubleClockTrace.normalTicks
            DoubleClockTrace.normalFuel η w) ≤
        maskedCountPotential DoubleClockTrace.normalTicks
          DoubleClockTrace.normalFuel η w q := by
  intro q
  by_cases hlive : q.core.BandLive aLo hi
  · by_cases hnormal : q.core.NormalTick
    · rw [doubleClockBandStep_expect_normal n hn aLo hi q η w hlive hnormal]
      have hmaj : q.core.cfg.1.y ≤ q.core.cfg.1.x := by
        have hinv := q.core.cfg.2
        unfold DoubleTrace.BandLive BiCfg.doubleLevel at hlive
        simp only [BiCfg.DoubleInv] at hinv
        omega
      have hq :
          (1 : ℝ≥0∞) / 16 ≤ doubleNormalFuelMass hn q := by
        unfold doubleNormalFuelMass
        exact dbPairPMF_fuel_mass_ge_sixteenth hn q.core.cfg.2 hmaj hnormal
      have hp : (1 : ℝ≥0∞) / 16 + 15 / 16 = 1 := by
        rw [ENNReal.div_add_div_same]
        have hnum : (1 : ℝ≥0∞) + 15 = 16 := by norm_num
        rw [hnum]
        exact ENNReal.div_self
          (by norm_num : (16 : ℝ≥0∞) ≠ 0)
          (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
      have hm := doubleNormal_masses hn q
      have hscalar :
          doubleNormalIdleMass hn q + doubleNormalFuelMass hn q * w ≤
            15 / 16 + (1 / 16 : ℝ≥0∞) * w :=
        step_factor_antitone_ennreal hp hm hw1 hq
      calc
        doubleNormalIdleMass hn q *
              (η ^ (q.normalTicks + 1) * w ^ q.normalFuel) +
            doubleNormalFuelMass hn q *
              (η ^ (q.normalTicks + 1) * w ^ (q.normalFuel + 1))
            = η *
                (doubleNormalIdleMass hn q + doubleNormalFuelMass hn q * w) *
                maskedCountPotential DoubleClockTrace.normalTicks
                  DoubleClockTrace.normalFuel η w q := by
                    unfold maskedCountPotential
                    rw [pow_succ η q.normalTicks, pow_succ w q.normalFuel]
                    ring
        _ ≤ η * (15 / 16 + (1 / 16 : ℝ≥0∞) * w) *
              maskedCountPotential DoubleClockTrace.normalTicks
                DoubleClockTrace.normalFuel η w q := by
          gcongr
        _ ≤ 1 * maskedCountPotential DoubleClockTrace.normalTicks
              DoubleClockTrace.normalFuel η w q := by
          gcongr
        _ = maskedCountPotential DoubleClockTrace.normalTicks
              DoubleClockTrace.normalFuel η w q := one_mul _
    · rw [doubleClockBandStep_expect_not_normal n hn aLo hi q η w hlive hnormal]
  · unfold doubleClockBandStep
    rw [if_neg hlive, expect_pure]

/-- Finite-horizon lower tail for the number of fuel labels observed on normal
ticks.  The bound is uniform in the interleaved complementary ticks. -/
theorem doubleClock_normal_tail
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ aLo) (η w : ℝ≥0∞)
    (hη1 : 1 ≤ η) (hηtop : η ≠ ⊤)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hfactor :
      η * ((15 : ℝ≥0∞) / 16 + (1 / 16) * w) ≤ 1)
    (T H m : ℕ) (q₀ : DoubleClockTrace n) :
    ∑' z, (if H ≤ z.normalTicks ∧ z.normalFuel ≤ m then
        iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) ≤
      maskedCountPotential DoubleClockTrace.normalTicks
          DoubleClockTrace.normalFuel η w q₀ /
        (η ^ H * w ^ m) := by
  exact masked_count_tail
    (doubleClockBandStep n hn aLo hi)
    DoubleClockTrace.normalTicks DoubleClockTrace.normalFuel
    η w hη1 hηtop hw1 hw0
    (doubleClockBandStep_normal_super n hn aLo hi hnLo η w hw1 hfactor)
    T H m q₀

/-- A concrete specialization: each normal tick exposes a fuel label with
conditional mass at least `1/16`.  The choice `w = 1/2`, `η = 32/31` makes the
one-step factor exactly one. -/
theorem doubleClock_normal_tail_half
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (hnLo : n ≤ aLo)
    (T H m : ℕ) (q₀ : DoubleClockTrace n) :
    ∑' z, (if H ≤ z.normalTicks ∧ z.normalFuel ≤ m then
        iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0) ≤
      maskedCountPotential DoubleClockTrace.normalTicks
          DoubleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
        (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ m) := by
  apply doubleClock_normal_tail n hn aLo hi hnLo
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

end Tri

#print axioms Tri.doubleClockBandStep_normal_super
#print axioms Tri.doubleClock_normal_tail_half

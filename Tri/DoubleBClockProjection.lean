/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockBlank
import Tri.DoubleBBandReturn

/-!
# Projecting the Double-B occupation clock to the counted band chain

The occupation counters are proof instrumentation only.  Forgetting them
intertwines `doubleClockBandStep` with the existing `doubleBandStop`, so the
two-branch raw-clock estimate transfers without duplicating its probability
argument.
-/

namespace Tri

open scoped ENNReal

/-- A counted trace with fresh occupation counters. -/
def DoubleClockTrace.initial {n : ℕ}
    (q : DoubleTrace n) : DoubleClockTrace n :=
  { core := q
    normalTicks := 0
    blankTicks := 0
    normalFuel := 0 }

/-- Fresh occupation counters satisfy the joint fuel-clock invariant whenever
the underlying trace satisfies the fuel ledger. -/
theorem DoubleClockTrace.initial_fuelClockInv
    {n y₀ : ℕ} (q : DoubleTrace n) (hq : q.FuelInv y₀) :
    (DoubleClockTrace.initial q).FuelClockInv y₀ := by
  exact ⟨hq, by simp [DoubleClockTrace.initial]⟩

/-- Forgetting occupation counters in one stopped clock step gives the
existing stopped counted-trace step. -/
theorem doubleClockBandStep_map_core_stop
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (q : DoubleClockTrace n) :
    (doubleClockBandStep n hn aLo hi q).map DoubleClockTrace.core =
      doubleBandStop n hn aLo hi q.core := by
  rw [doubleClockBandStep_map_core]
  rfl

/-- The stopped counted-trace iterate is the pushforward of the occupation
iterate. -/
theorem iter_doubleBandStop_eq_clock_map
    (n : ℕ) (hn : 2 ≤ n) (aLo hi T : ℕ)
    (q : DoubleClockTrace n) :
    iter (doubleBandStop n hn aLo hi) T q.core =
      (iter (doubleClockBandStep n hn aLo hi) T q).map
        DoubleClockTrace.core :=
  iter_map_equivariant
    (doubleClockBandStep n hn aLo hi)
    (doubleBandStop n hn aLo hi)
    DoubleClockTrace.core
    (doubleClockBandStep_map_core_stop n hn aLo hi)
    T q

/-- Indicator mass for a core predicate is unchanged by forgetting occupation
counters. -/
theorem doubleBand_indicator_eq_clock
    (n : ℕ) (hn : 2 ≤ n) (aLo hi T : ℕ)
    (q₀ : DoubleClockTrace n)
    (A : DoubleTrace n → Prop) [DecidablePred A] :
    (∑' q, if A q then
        iter (doubleBandStop n hn aLo hi) T q₀.core q else 0) =
      ∑' z, if A z.core then
        iter (doubleClockBandStep n hn aLo hi) T q₀ z else 0 := by
  rw [iter_doubleBandStop_eq_clock_map n hn aLo hi T q₀]
  set p := iter (doubleClockBandStep n hn aLo hi) T q₀
  let V : DoubleTrace n → ℝ≥0∞ := fun q => if A q then 1 else 0
  calc
    (∑' q, if A q then (p.map DoubleClockTrace.core) q else 0)
        = expect (p.map DoubleClockTrace.core) V := by
          unfold expect V
          apply tsum_congr
          intro q
          by_cases hq : A q <;> simp [hq]
    _ = expect p (fun z => V z.core) := by rw [expect_map]
    _ = ∑' z, if A z.core then p z else 0 := by
      unfold expect V
      apply tsum_congr
      intro z
      by_cases hz : A z.core <;> simp [hz]

/-- The two-branch clock on the existing counted band chain, started with
fresh occupation counters. -/
theorem doubleBand_joint_clock_tail
    (n : ℕ) (hn : 2 ≤ n) (g aLo hi : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (T H M y₀ : ℕ) (hH : 2 * H ≤ T)
    (q₀ : DoubleTrace n)
    (hqInv : q₀.FuelInv y₀)
    (hy₀ : y₀ ≤ n) :
    ∑' q, (if q.BandLive aLo hi ∧ q.resolve < M then
        iter (doubleBandStop n hn aLo hi) T q₀ q else 0) ≤
      1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ (n + 2 * M)) +
      doubleBlankW n g ^ q₀.cfg.1.doubleLevel /
        (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) := by
  let qClock := DoubleClockTrace.initial q₀
  have hclock :=
    doubleClock_twoBranch_tail
      n hn g aLo hi hnLo hsmall T H M y₀ hH qClock
      (DoubleClockTrace.initial_fuelClockInv q₀ hqInv)
      hy₀ (by rfl) (by rfl)
  calc
    (∑' q, (if q.BandLive aLo hi ∧ q.resolve < M then
          iter (doubleBandStop n hn aLo hi) T q₀ q else 0))
        =
          ∑' z, (if z.core.BandLive aLo hi ∧ z.core.resolve < M then
            iter (doubleClockBandStep n hn aLo hi) T qClock z else 0) := by
              simpa [qClock, DoubleClockTrace.initial] using
                (doubleBand_indicator_eq_clock
                  n hn aLo hi T qClock
                  (fun q => q.BandLive aLo hi ∧ q.resolve < M))
    _ ≤
        1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ (n + 2 * M)) +
        doubleBlankW n g ^ q₀.cfg.1.doubleLevel /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) := by
      simpa [qClock, DoubleClockTrace.initial, maskedCountPotential,
        doubleBlankPotential] using hclock

/-- Per-phase stopped-band failure bound with the old level-only productivity
term replaced by the two-branch raw clock. -/
theorem band_phase_fail_joint_clock
    (n : ℕ) (hn : 2 ≤ n)
    (g aLo bHiD hi M T H : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLo : 0 < aLo) (hmajD : bHiD ≤ aLo)
    (heqD : aLo + bHiD = 2 * n) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : DoubleState n) :
    ∑' q, (if q.cfg.1.doubleLevel + 1 ≤ hi then
        iter (doubleBandStop n hn aLo hi) T
          (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0) ≤
      (∑' q, (if q.cfg.1.doubleLevel ≤ aLo then
          iter (doubleBandStop n hn aLo hi) T
            (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0)) +
      w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M) +
      (1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ (n + 2 * M)) +
        doubleBlankW n g ^ s₀.1.doubleLevel /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H)) := by
  let q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩
  refine le_trans (band_split n hn aLo hi M T q₀) ?_
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · have hdir :=
      doubleBandStop_tail n hn aLo bHiD hi (hi - 1) M T
        haLo hmajD heqD hhi w η u hu hrel hwη
        hw1 hw0 hη1 hηt q₀ (by rfl)
    simpa [q₀] using hdir
  · have hclock :=
      doubleBand_joint_clock_tail
        n hn g aLo hi hnLo hsmall T H M s₀.1.y hH q₀
        (DoubleTrace.initial_fuelInv s₀ (le_refl _))
        (by
          have := s₀.2
          simp only [BiCfg.DoubleInv] at this
          omega)
    simpa [q₀, DoubleTrace.BandLive, and_assoc] using hclock

/-- Complete explicit stopped-band phase bound using the joint raw clock. -/
theorem band_phase_fail_joint_clock_full
    (n : ℕ) (hn : 2 ≤ n)
    (g aLo bHiR bHiD hi k M T H : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n)
    (hmajD : bHiD ≤ aLo) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : DoubleState n)
    (hstart : s₀.1.doubleLevel = aLo + k) :
    ∑' q, (if q.cfg.1.doubleLevel + 1 ≤ hi then
        iter (doubleBandStop n hn aLo hi) T
          (⟨s₀, 0, 0⟩ : DoubleTrace n) q else 0) ≤
      ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
      w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M) +
      (1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ (n + 2 * M)) +
        doubleBlankW n g ^ s₀.1.doubleLevel /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H)) := by
  refine le_trans
    (band_phase_fail_joint_clock
      n hn g aLo bHiD hi M T H hnLo hsmall hH
      haLo hmajD heqD hhi w η u hu hrel hwη
      hw1 hw0 hη1 hηt s₀) ?_
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  exact band_ruin_term_le
    n hn aLo bHiR hi k T haLohi hpopR haLo hbHiR hmajR
    (⟨s₀, 0, 0⟩ : DoubleTrace n) (by simpa using hstart)

/-- Explicit error of a joint-clock band phase after transferring back to the
original state chain. -/
noncomputable def doubleBandJointClockError
    (n g aLo bHiR hi k M H : ℕ)
    (w η : ℝ≥0∞)
    (returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  (((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
      w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M) +
      (1 / (((32 : ℝ≥0∞) / 31) ^ H *
          (1 / 2) ^ (n + 2 * M)) +
        doubleBlankW n g ^ (aLo + k) /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H))) +
    ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet

/-- Joint-clock phase failure transferred from the stopped counted chain to an
exact-time checkpoint of the original `DoubleState` chain. -/
theorem doubleState_band_phase_fail_joint_clock
    (n : ℕ) (hn : 2 ≤ n)
    (g aLo bHiR bHiD hi k M T H : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n)
    (hmajD : bHiD ≤ aLo) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi)
    (s₀ : DoubleState n)
    (hstart : s₀.1.doubleLevel = aLo + k) :
    (∑' s, if returnLo + 1 ≤ s.1.doubleLevel then 0
        else iter (doubleStateStep n hn) T s₀ s) ≤
      doubleBandJointClockError
        n g aLo bHiR hi k M H w η returnLo bHiRet kRet := by
  let A : DoubleState n → Prop :=
    fun s => returnLo + 1 ≤ s.1.doubleLevel
  let q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩
  have htransfer :
      (∑' s, if A s then 0 else iter (doubleStateStep n hn) T s₀ s)
        ≤ (∑' q, if A q.cfg then 0 else
            iter (doubleBandStop n hn aLo hi) T q₀ q) +
          ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet := by
    exact doubleBand_transfer_upper
      n aLo hi returnLo bHiRet kRet T hn
      hpopRet hreturnLo hbHiRet hmajRet hreturnGap q₀ A
      (by
        intro s hs
        change returnLo + 1 ≤ s.1.doubleLevel at hs
        omega)
      (by
        intro s hs
        change ¬returnLo + 1 ≤ s.1.doubleLevel at hs
        omega)
  have hphase :
      (∑' q, (if q.cfg.1.doubleLevel + 1 ≤ hi then
          iter (doubleBandStop n hn aLo hi) T q₀ q else 0)) ≤
        ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M) +
        (1 / (((32 : ℝ≥0∞) / 31) ^ H *
            (1 / 2) ^ (n + 2 * M)) +
          doubleBlankW n g ^ s₀.1.doubleLevel /
            (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H)) := by
    simpa [q₀] using
      (band_phase_fail_joint_clock_full
        n hn g aLo bHiR bHiD hi k M T H
        hnLo hsmall hH haLohi hpopR haLo hbHiR hmajR
        heqD hmajD hhi w η u hu hrel hwη hw1 hw0 hη1 hηt
        s₀ hstart)
  have hstopped :
      (∑' q, if A q.cfg then 0 else
          iter (doubleBandStop n hn aLo hi) T q₀ q) ≤
        ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M) +
        (1 / (((32 : ℝ≥0∞) / 31) ^ H *
            (1 / 2) ^ (n + 2 * M)) +
          doubleBlankW n g ^ s₀.1.doubleLevel /
            (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H)) := by
    refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) hphase
    by_cases hA : A q.cfg
    · simp [hA]
    · have hqLo : q.cfg.1.doubleLevel ≤ returnLo := by
        change ¬returnLo + 1 ≤ q.cfg.1.doubleLevel at hA
        omega
      have hqHi : q.cfg.1.doubleLevel + 1 ≤ hi := by omega
      simp [hA, hqHi]
  change (∑' s, if A s then 0 else
      iter (doubleStateStep n hn) T s₀ s) ≤ _
  unfold doubleBandJointClockError
  rw [hstart] at hstopped
  exact htransfer.trans (add_le_add hstopped le_rfl)

/-- Predicate and monotone-start form of the transferred joint-clock phase. -/
theorem doubleState_band_phase_reaches_joint_clock_mono
    (n : ℕ) (hn : 2 ≤ n)
    (g aLo bHiR bHiD hi k M T H : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n)
    (hmajD : bHiD ≤ aLo) (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (doubleStateStep n hn) T
      (fun s => aLo + k ≤ s.1.doubleLevel)
      (fun s => returnLo + 1 ≤ s.1.doubleLevel)
      (doubleBandJointClockError
        n g aLo bHiR hi k M H w η returnLo bHiRet kRet) := by
  intro s hs
  obtain ⟨d, hd⟩ : ∃ d, s.1.doubleLevel = aLo + d :=
    ⟨s.1.doubleLevel - aLo, by omega⟩
  have hkd : k ≤ d := by omega
  have hbaseR :
      (bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ 1 := by
    have haLo0 : (aLo : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have haLoT : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc
      (bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤
          (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmajR) _
      _ = 1 := ENNReal.div_self haLo0 haLoT
  have hraw :=
    doubleState_band_phase_fail_joint_clock
      n hn g aLo bHiR bHiD hi d M T H
      hnLo hsmall hH haLohi hpopR haLo hbHiR hmajR
      heqD hmajD hhi w η u hu hrel hwη hw1 hw0 hη1 hηt
      returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
      hlowerTarget htargetHi hreturnGap s hd
  have hruin :
      ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ d ≤
        ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
    pow_le_pow_right_of_le_one' hbaseR hkd
  have hdir :
      w ^ (aLo + d) / (w ^ (hi - 1) * η ^ M) ≤
        w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M) :=
    ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hw1 (by omega)) _
  have hblankBase : doubleBlankW n g ≤ 1 :=
    doubleBlankW_le_one n g (by omega)
  have hblank :
      doubleBlankW n g ^ (aLo + d) /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) ≤
        doubleBlankW n g ^ (aLo + k) /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) :=
    ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hblankBase (by omega)) _
  unfold doubleBandJointClockError at hraw ⊢
  exact hraw.trans
    (add_le_add
      (add_le_add
        (add_le_add hruin hdir)
        (add_le_add le_rfl hblank))
      le_rfl)

end Tri

#print axioms Tri.doubleClockBandStep_map_core_stop
#print axioms Tri.doubleBand_joint_clock_tail
#print axioms Tri.band_phase_fail_joint_clock_full
#print axioms Tri.doubleState_band_phase_reaches_joint_clock_mono

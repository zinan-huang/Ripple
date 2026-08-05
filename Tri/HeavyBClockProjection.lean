/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBClockBlank
import Tri.HeavyBStaged

/-!
# Projecting the Heavy-B occupation clock to the counted band chain

The Heavy-B occupation counters are proof instrumentation.  Forgetting them
intertwines the stopped clock kernel with the stopped counted-trace kernel, and
the two occupation tails combine into a raw-resolution clock for one band.
-/

namespace Tri

open scoped ENNReal

/-- A counted Heavy-B trace with fresh occupation counters. -/
def HeavyClockTrace.initial {n : ℕ}
    (q : HeavyTrace n) : HeavyClockTrace n :=
  { core := q
    normalTicks := 0
    blankTicks := 0
    normalFuel := 0 }

/-- Fresh occupation counters satisfy the Heavy-B joint fuel-clock invariant
whenever the underlying trace satisfies the `Y` ledger. -/
theorem HeavyClockTrace.initial_fuelClockInv
    {n y₀ : ℕ} (q : HeavyTrace n) (hq : q.YLedger y₀) :
    (HeavyClockTrace.initial q).FuelClockInv y₀ := by
  exact ⟨hq, by simp [HeavyClockTrace.initial]⟩

/-- Forgetting occupation counters in one stopped Heavy-B clock step gives the
existing stopped counted-trace step. -/
theorem heavyClockBandStep_map_core_stop
    (n : ℕ) (aLo hi : ℕ) (q : HeavyClockTrace n) :
    (heavyClockBandStep n aLo hi q).map HeavyClockTrace.core =
      heavyBandStop n aLo hi q.core := by
  exact heavyClockBandStep_map_core n aLo hi q

/-- The stopped counted-trace iterate is the pushforward of the occupation
iterate. -/
theorem iter_heavyBandStop_eq_clock_map
    (n : ℕ) (aLo hi T : ℕ) (q : HeavyClockTrace n) :
    iter (heavyBandStop n aLo hi) T q.core =
      (iter (heavyClockBandStep n aLo hi) T q).map
        HeavyClockTrace.core :=
  iter_map_equivariant
    (heavyClockBandStep n aLo hi)
    (heavyBandStop n aLo hi)
    HeavyClockTrace.core
    (heavyClockBandStep_map_core_stop n aLo hi)
    T q

/-- Indicator mass for a core predicate is unchanged by forgetting occupation
counters. -/
theorem heavyBand_indicator_eq_clock
    (n : ℕ) (aLo hi T : ℕ)
    (q₀ : HeavyClockTrace n)
    (A : HeavyTrace n → Prop) [DecidablePred A] :
    (∑' q, if A q then
        iter (heavyBandStop n aLo hi) T q₀.core q else 0) =
      ∑' z, if A z.core then
        iter (heavyClockBandStep n aLo hi) T q₀ z else 0 := by
  rw [iter_heavyBandStop_eq_clock_map n aLo hi T q₀]
  set p := iter (heavyClockBandStep n aLo hi) T q₀
  let V : HeavyTrace n → ℝ≥0∞ := fun q => if A q then 1 else 0
  calc
    (∑' q, if A q then (p.map HeavyClockTrace.core) q else 0)
        = expect (p.map HeavyClockTrace.core) V := by
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

/-- Fixed-horizon two-branch Heavy-B clock.  A live endpoint with too few
resolutions must lie in either the normal-fuel lower tail or the blank
occupation upper tail. -/
theorem heavyClock_twoBranch_tail
    (n : ℕ) (hn : 3 ≤ n) (g aLo hi : ℕ)
    (hfloor : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (T H M K y₀ : ℕ) (hH : 2 * H ≤ T)
    (q₀ : HeavyClockTrace n)
    (hqInv : q₀.FuelClockInv y₀)
    (hyK : y₀ + 3 * M ≤ K)
    (hnormal0 : q₀.normalTicks = 0)
    (hblank0 : q₀.blankTicks = 0) :
    ∑' z, (if z.core.BandLive aLo hi ∧ z.core.up + z.core.down < M then
        iter (heavyClockBandStep n aLo hi) T q₀ z else 0) ≤
      maskedCountPotential HeavyClockTrace.normalTicks
          HeavyClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
        (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) +
      heavyBlankPotential
          (heavyBlankW n g) (heavyBlankEta n g) q₀ /
        (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) := by
  let Kstep := heavyClockBandStep n aLo hi
  let p := iter Kstep T q₀
  have hpoint : ∀ z : HeavyClockTrace n,
      (if z.core.BandLive aLo hi ∧ z.core.up + z.core.down < M then
          p z else 0) ≤
        (if H ≤ z.normalTicks ∧ z.normalFuel ≤ K then p z else 0) +
        (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then p z else 0) := by
    intro z
    by_cases hbad : z.core.BandLive aLo hi ∧ z.core.up + z.core.down < M
    · by_cases hp : p z = 0
      · simp [hbad, hp]
      · have hticks :=
          heavyClockBand_iter_tick_sum_of_final_live
            hn aLo hi T q₀ z (by simpa [p, Kstep] using hp) hbad.1
        have hticks' :
            z.normalTicks + z.blankTicks = T := by
          rw [hnormal0, hblank0] at hticks
          simpa using hticks
        by_cases hblank : H ≤ z.blankTicks
        · simp [hbad, hblank]
        · have hnormal : H ≤ z.normalTicks := by omega
          have hzInv :=
            heavyClockBand_iter_fuelClockInv
              aLo hi q₀ z hqInv (by simpa [p, Kstep] using hp)
          have hfuel : z.normalFuel ≤ K := by
            unfold HeavyClockTrace.FuelClockInv HeavyTrace.YLedger at hzInv
            omega
          simp [hbad, hnormal, hfuel]
    · simp [hbad]
  calc
    ∑' z, (if z.core.BandLive aLo hi ∧ z.core.up + z.core.down < M then
          iter (heavyClockBandStep n aLo hi) T q₀ z else 0)
        ≤ ∑' z,
            ((if H ≤ z.normalTicks ∧ z.normalFuel ≤ K then
                iter (heavyClockBandStep n aLo hi) T q₀ z else 0) +
              (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
                iter (heavyClockBandStep n aLo hi) T q₀ z else 0)) := by
          simpa [p, Kstep] using ENNReal.tsum_le_tsum hpoint
    _ =
        (∑' z, (if H ≤ z.normalTicks ∧ z.normalFuel ≤ K then
            iter (heavyClockBandStep n aLo hi) T q₀ z else 0)) +
        (∑' z, (if z.core.BandLive aLo hi ∧ H ≤ z.blankTicks then
            iter (heavyClockBandStep n aLo hi) T q₀ z else 0)) :=
      ENNReal.tsum_add
    _ ≤
        maskedCountPotential HeavyClockTrace.normalTicks
            HeavyClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
          (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) +
        heavyBlankPotential
            (heavyBlankW n g) (heavyBlankEta n g) q₀ /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) := by
      exact add_le_add
        (heavyClock_normal_tail_half n hn aLo hi
          (by omega) T H K q₀)
        (heavyClock_blank_tail n hn g aLo hi
          hfloor hsmall T H q₀)

/-- The two-branch clock on the existing counted Heavy-B band chain, started
with fresh occupation counters. -/
theorem heavyBand_joint_clock_tail
    (n : ℕ) (hn : 3 ≤ n) (g aLo hi : ℕ)
    (hfloor : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (T H M K y₀ : ℕ) (hH : 2 * H ≤ T)
    (q₀ : HeavyTrace n)
    (hqInv : q₀.YLedger y₀)
    (hyK : y₀ + 3 * M ≤ K) :
    ∑' q, (if q.BandLive aLo hi ∧ q.up + q.down < M then
        iter (heavyBandStop n aLo hi) T q₀ q else 0) ≤
      1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) +
      heavyBlankW n g ^ BiCfg.heavyLevel q₀.cfg.1 /
        (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) := by
  let qClock := HeavyClockTrace.initial q₀
  have hclock :=
    heavyClock_twoBranch_tail
      n hn g aLo hi hfloor hsmall T H M K y₀ hH qClock
      (HeavyClockTrace.initial_fuelClockInv q₀ hqInv)
      hyK (by rfl) (by rfl)
  calc
    (∑' q, (if q.BandLive aLo hi ∧ q.up + q.down < M then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
        =
          ∑' z, (if z.core.BandLive aLo hi ∧
              z.core.up + z.core.down < M then
            iter (heavyClockBandStep n aLo hi) T qClock z else 0) := by
              simpa [qClock, HeavyClockTrace.initial] using
                (heavyBand_indicator_eq_clock
                  n aLo hi T qClock
                  (fun q => q.BandLive aLo hi ∧ q.up + q.down < M))
    _ ≤
        1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) +
        heavyBlankW n g ^ BiCfg.heavyLevel q₀.cfg.1 /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) := by
      simpa [qClock, HeavyClockTrace.initial, maskedCountPotential,
        heavyBlankPotential] using hclock

/-- Stopped-band event split with the resolution clock separated from the
direction-deadline term. -/
theorem heavyBand_split_resolutions
    (n aLo hi thr M T : ℕ)
    (hthr : thr + 1 = hi)
    (q₀ : HeavyTrace n) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
        iter (heavyBandStop n aLo hi) T q₀ q else 0)
      ≤ (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
            iter (heavyBandStop n aLo hi) T q₀ q else 0))
        + (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ thr ∧ M ≤ q.up + q.down then
            iter (heavyBandStop n aLo hi) T q₀ q else 0))
        + (∑' q, (if q.BandLive aLo hi ∧ q.up + q.down < M then
            iter (heavyBandStop n aLo hi) T q₀ q else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set p := iter (heavyBandStop n aLo hi) T q₀ q with hp
  by_cases hfail : BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi
  · rw [if_pos hfail]
    by_cases hlow : BiCfg.heavyLevel q.cfg.1 ≤ aLo
    · rw [if_pos hlow]
      exact le_trans (self_le_add_right _ _) (self_le_add_right _ _)
    · rw [if_neg hlow]
      by_cases hres : M ≤ q.up + q.down
      · have hlevThr : BiCfg.heavyLevel q.cfg.1 ≤ thr := by omega
        rw [if_pos ⟨hlevThr, hres⟩, zero_add]
        exact self_le_add_right _ _
      · rw [if_neg (by intro h; exact hres h.2)]
        have hlive : q.BandLive aLo hi := by
          unfold HeavyTrace.BandLive
          omega
        have hresLt : q.up + q.down < M := by omega
        rw [if_pos ⟨hlive, hresLt⟩, zero_add, zero_add]
  · rw [if_neg hfail]
    positivity

/-- Per-phase stopped-band failure bound with the old productive-clock term
replaced by the two-branch raw clock. -/
theorem heavyBand_phase_fail_joint_clock
    (n : ℕ) (hn : 3 ≤ n)
    (g aLo hi thr M K T H : ℕ)
    (hfloorClock : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (hthr : thr + 1 = hi)
    (p q : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : HeavyState n)
    (hyK : s₀.1.y + 3 * M ≤ K) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
        iter (heavyBandStop n aLo hi) T
          (⟨s₀, 0, 0, 0⟩ : HeavyTrace n) q else 0) ≤
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
          iter (heavyBandStop n aLo hi) T
            (⟨s₀, 0, 0, 0⟩ : HeavyTrace n) q else 0)) +
      w ^ BiCfg.heavyLevel s₀.1 / (w ^ thr * η ^ M) +
      (1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) +
        heavyBlankW n g ^ BiCfg.heavyLevel s₀.1 /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H)) := by
  let q₀ : HeavyTrace n := ⟨s₀, 0, 0, 0⟩
  refine le_trans (heavyBand_split_resolutions n aLo hi thr M T hthr q₀) ?_
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · have hdir :=
      heavyBandWindowStop_tail_of_guard hn aLo hi p q thr M T hq
        hguard w η u hu hrel hwη
        hw1 hw0 hη1 hηt q₀ (by simp [q₀])
    simpa [q₀] using hdir
  · have hclock :=
      heavyBand_joint_clock_tail
        n hn g aLo hi hfloorClock hsmall T H M K s₀.1.y hH q₀
        (HeavyTrace.initial_yLedger s₀)
        (by simpa [q₀] using hyK)
    simpa [q₀, HeavyTrace.BandLive, and_assoc] using hclock

/-- Complete explicit stopped-band phase bound using the joint raw clock. -/
theorem heavyBand_phase_fail_joint_clock_full
    (n : ℕ) (hn : 3 ≤ n)
    (g aLo bHiR hi thr k M K T H : ℕ)
    (hfloorClock : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hthr : thr + 1 = hi)
    (hpopR : aLo + bHiR + 2 = n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (p q : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : HeavyState n)
    (hstart : BiCfg.heavyLevel s₀.1 = aLo + k)
    (hyK : s₀.1.y + 3 * M ≤ K) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
        iter (heavyBandStop n aLo hi) T
          (⟨s₀, 0, 0, 0⟩ : HeavyTrace n) q else 0) ≤
      ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
      w ^ (aLo + k) / (w ^ thr * η ^ M) +
      (1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) +
        heavyBlankW n g ^ (aLo + k) /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H)) := by
  refine le_trans
    (heavyBand_phase_fail_joint_clock
      n hn g aLo hi thr M K T H hfloorClock hsmall hH hthr
      p q hq hguard w η u hu hrel hwη hw1 hw0 hη1 hηt
      s₀ hyK) ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact heavyBand_ruin_term_le hn aLo bHiR hi k T haLohi hpopR
      haLo hbHiR hmajR (⟨s₀, 0, 0, 0⟩ : HeavyTrace n)
      (by simpa using hstart)
  · simp [hstart]
  · simp [hstart]

/-- Explicit error of a joint-clock Heavy-B band phase after transferring back
to the original state chain. -/
noncomputable def heavyBandJointClockError
    (n g aLo bHiR hi thr k M K H : ℕ)
    (w η : ℝ≥0∞)
    (returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  (((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
      w ^ (aLo + k) / (w ^ thr * η ^ M) +
      (1 / (((32 : ℝ≥0∞) / 31) ^ H *
          (1 / 2) ^ K) +
        heavyBlankW n g ^ (aLo + k) /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H))) +
    ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet

/-- Joint-clock phase failure transferred from the stopped counted chain to an
exact-time checkpoint of the original `HeavyState` chain. -/
theorem heavyState_band_phase_fail_joint_clock
    (n : ℕ) (hn : 3 ≤ n)
    (g aLo bHiR hi thr k M K T H : ℕ)
    (hfloorClock : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hthr : thr + 1 = hi)
    (hpopR : aLo + bHiR + 2 = n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (p q : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi)
    (s₀ : HeavyState n)
    (hstart : BiCfg.heavyLevel s₀.1 = aLo + k)
    (hyK : s₀.1.y + 3 * M ≤ K) :
    (∑' s, if returnLo + 1 ≤ BiCfg.heavyLevel s.1 then 0
        else iter (heavyStateStep n) T s₀ s) ≤
      heavyBandJointClockError
        n g aLo bHiR hi thr k M K H w η returnLo bHiRet kRet := by
  let A : HeavyState n → Prop :=
    fun s => returnLo + 1 ≤ BiCfg.heavyLevel s.1
  let q₀ : HeavyTrace n := ⟨s₀, 0, 0, 0⟩
  have htransfer :
      (∑' s, if A s then 0 else iter (heavyStateStep n) T s₀ s)
        ≤ (∑' q, if A q.cfg then 0 else
            iter (heavyBandStop n aLo hi) T q₀ q) +
          ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet := by
    exact heavyBand_transfer_upper
      aLo hi returnLo bHiRet kRet T hn
      hpopRet hreturnLo hbHiRet hmajRet hreturnGap q₀ A
      (by
        intro s hs
        change returnLo + 1 ≤ BiCfg.heavyLevel s.1 at hs
        omega)
      (by
        intro s hs
        change ¬returnLo + 1 ≤ BiCfg.heavyLevel s.1 at hs
        omega)
  have hphase :
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
          iter (heavyBandStop n aLo hi) T q₀ q else 0)) ≤
        ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        w ^ (aLo + k) / (w ^ thr * η ^ M) +
        (1 / (((32 : ℝ≥0∞) / 31) ^ H *
            (1 / 2) ^ K) +
          heavyBlankW n g ^ (aLo + k) /
            (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H)) := by
    simpa [q₀] using
      (heavyBand_phase_fail_joint_clock_full
        n hn g aLo bHiR hi thr k M K T H
        hfloorClock hsmall hH haLohi hthr hpopR
        haLo hbHiR hmajR p q hq hguard w η u hu hrel hwη
        hw1 hw0 hη1 hηt s₀ hstart hyK)
  have hstopped :
      (∑' q, if A q.cfg then 0 else
          iter (heavyBandStop n aLo hi) T q₀ q) ≤
        ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        w ^ (aLo + k) / (w ^ thr * η ^ M) +
        (1 / (((32 : ℝ≥0∞) / 31) ^ H *
            (1 / 2) ^ K) +
          heavyBlankW n g ^ (aLo + k) /
            (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H)) := by
    refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) hphase
    by_cases hA : A q.cfg
    · simp [hA]
    · have hqHi : BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi := by
        dsimp [A] at hA
        omega
      simp [hA, hqHi]
  change (∑' s, if A s then 0 else
      iter (heavyStateStep n) T s₀ s) ≤ _
  unfold heavyBandJointClockError
  exact htransfer.trans (add_le_add hstopped le_rfl)

/-- Predicate and monotone-start form of the transferred joint-clock Heavy-B
phase. -/
theorem heavyState_band_phase_reaches_joint_clock_mono
    (n : ℕ) (hn : 3 ≤ n)
    (g aLo bHiR hi thr k M K T H cL : ℕ)
    (hfloorClock : n + g ≤ 2 * (aLo + 1))
    (hsmall : 16 * hi ≤ 9 * n)
    (hH : 2 * H ≤ T)
    (haLohi : aLo < hi)
    (hthr : thr + 1 = hi)
    (hstartCo : aLo + k + cL = n)
    (hK : cL + 3 * M ≤ K)
    (hpopR : aLo + bHiR + 2 = n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (p q : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (heavyStateStep n) T
      (fun s => aLo + k ≤ BiCfg.heavyLevel s.1)
      (fun s => returnLo + 1 ≤ BiCfg.heavyLevel s.1)
      (heavyBandJointClockError
        n g aLo bHiR hi thr k M K H w η returnLo bHiRet kRet) := by
  intro s hs
  obtain ⟨d, hd⟩ : ∃ d, BiCfg.heavyLevel s.1 = aLo + d :=
    ⟨BiCfg.heavyLevel s.1 - aLo, by omega⟩
  have hkd : k ≤ d := by omega
  have hyK : s.1.y + 3 * M ≤ K := by
    have hco := BiCfg.heavyLevel_add_coLevel s.2
    omega
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
    heavyState_band_phase_fail_joint_clock
      n hn g aLo bHiR hi thr d M K T H
      hfloorClock hsmall hH haLohi hthr hpopR
      haLo hbHiR hmajR p q hq hguard w η u hu hrel hwη hw1 hw0
      hη1 hηt returnLo bHiRet kRet hpopRet hreturnLo hbHiRet
      hmajRet hlowerTarget htargetHi hreturnGap s hd hyK
  have hruin :
      ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ d ≤
        ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
    pow_le_pow_right_of_le_one' hbaseR hkd
  have hdir :
      w ^ (aLo + d) / (w ^ thr * η ^ M) ≤
        w ^ (aLo + k) / (w ^ thr * η ^ M) :=
    ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hw1 (by omega)) _
  have hblankBase : heavyBlankW n g ≤ 1 :=
    heavyBlankW_le_one n g (by omega)
  have hblank :
      heavyBlankW n g ^ (aLo + d) /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) ≤
        heavyBlankW n g ^ (aLo + k) /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) :=
    ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hblankBase (by omega)) _
  unfold heavyBandJointClockError at hraw ⊢
  exact hraw.trans
    (add_le_add
      (add_le_add
        (add_le_add hruin hdir)
        (add_le_add le_rfl hblank))
      le_rfl)

end Tri

#print axioms Tri.HeavyClockTrace.initial_fuelClockInv
#print axioms Tri.heavyClockBandStep_map_core_stop
#print axioms Tri.iter_heavyBandStop_eq_clock_map
#print axioms Tri.heavyBand_indicator_eq_clock
#print axioms Tri.heavyClock_twoBranch_tail
#print axioms Tri.heavyBand_joint_clock_tail
#print axioms Tri.heavyBand_split_resolutions
#print axioms Tri.heavyBand_phase_fail_joint_clock
#print axioms Tri.heavyBand_phase_fail_joint_clock_full
#print axioms Tri.heavyState_band_phase_fail_joint_clock
#print axioms Tri.heavyState_band_phase_reaches_joint_clock_mono

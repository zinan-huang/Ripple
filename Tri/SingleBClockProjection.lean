/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBClockBlank
import Tri.DoubleBAssembly

/-!
# Projecting the Single-B occupation clock to the stopped ledger band

The occupation counters are proof instrumentation: forgetting them intertwines
the stopped clock kernel with the repaired `singleBandStop`.  The two-branch
pigeonhole then bounds the few-resolution live endpoints: with `2H ≤ T` every
live time-`T` endpoint has `H` normal ticks or `H` blank ticks; the aggregate
blank ledger converts few resolutions into a normal-fuel cap, and the
corrected-`Y` identity converts them into the `CX` cap that keeps the blank
mask off.
-/

namespace Tri

open scoped ENNReal

/-- A Single-B ledger with fresh occupation counters. -/
def SingleClockTrace.initial {n : ℕ} (q : SingleLedger n) :
    SingleClockTrace n :=
  { core := q
    normalTicks := 0
    blankTicks := 0
    normalFuel := 0 }

/-- Fresh occupation counters over a fresh ledger satisfy the joint fuel-clock
invariant at the physical initial blank and `Y` counts. -/
theorem SingleClockTrace.initial_fuelClockInv {n : ℕ} (s : SingleState n) :
    (SingleClockTrace.initial (⟨s, 0, 0, 0, 0⟩ : SingleLedger n)).FuelClockInv
      s.1.b s.1.y := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [SingleClockTrace.initial, SingleLedger.BlankLedger,
      SingleLedger.CorrectedY]

/-- The stopped ledger iterate is the pushforward of the occupation iterate. -/
theorem iter_singleBandStop_eq_clock_map
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H T : ℕ) (q : SingleClockTrace n) :
    iter (singleBandStop n hn aLoΛ hiΛ D H) T q.core =
      (iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q).map
        SingleClockTrace.core :=
  iter_map_equivariant
    (singleClockBandStep n hn aLoΛ hiΛ D H)
    (singleBandStop n hn aLoΛ hiΛ D H)
    SingleClockTrace.core
    (singleClockBandStep_map_core n hn aLoΛ hiΛ D H)
    T q

/-- Indicator mass for a ledger predicate is unchanged by forgetting the
occupation counters. -/
theorem singleBand_indicator_eq_clock
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H T : ℕ)
    (q₀ : SingleClockTrace n)
    (A : SingleLedger n → Prop) [DecidablePred A] :
    (∑' q, if A q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T q₀.core q else 0) =
      ∑' z, if A z.core then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0 := by
  rw [iter_singleBandStop_eq_clock_map n hn aLoΛ hiΛ D H T q₀]
  set p := iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀
  let V : SingleLedger n → ℝ≥0∞ := fun q => if A q then 1 else 0
  calc
    (∑' q, if A q then (p.map SingleClockTrace.core) q else 0)
        = expect (p.map SingleClockTrace.core) V := by
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

/-- Fixed-horizon two-branch Single-B clock.  A live endpoint with too few
resolutions must lie in either the normal-fuel lower tail or the masked blank
occupation upper tail. -/
theorem singleClock_twoBranch_tail
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n)
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
          (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) q₀ /
        (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc) := by
  let Kstep := singleClockBandStep n hn aLoΛ hiΛ D H
  let p := iter Kstep T q₀
  have hpoint : ∀ z : SingleClockTrace n,
      (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            z.core.rx + z.core.ry < M then p z else 0) ≤
        (if Hocc ≤ z.normalTicks ∧ z.normalFuel ≤ K then p z else 0) +
        (if (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
            Hocc ≤ z.blankTicks ∧ z.core.cx < cxCap then p z else 0) := by
    intro z
    by_cases hbad : (¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) ∧
        z.core.rx + z.core.ry < M
    · by_cases hp : p z = 0
      · simp [hbad, hp]
      · have hInv :=
          singleClockBand_iter_fuelClockInv hn aLoΛ hiΛ D H q₀ z hq₀
            (by simpa [p, Kstep] using hp)
        obtain ⟨hbl, hcy, hfuel⟩ := hInv
        have hticks :=
          singleClockBand_iter_tick_sum_of_final_live hn aLoΛ hiΛ D H
            T q₀ z (by simpa [p, Kstep] using hp) hbad.1
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
                iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0)) := by
          simpa [p, Kstep] using ENNReal.tsum_le_tsum hpoint
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
            (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) q₀ /
          (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc) := by
      exact add_le_add
        (singleClock_normal_tail_half n hn aLoΛ hiΛ D H
          (by omega) T Hocc K q₀)
        (singleClock_blank_tail n hn aLoΛ hiΛ D H g cxCap
          hgap hsmall T Hocc q₀)

/-- The two-branch clock on the repaired stopped Single-B ledger band, started
from a fresh ledger. -/
theorem singleBand_joint_clock_tail
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H g cxCap : ℕ)
    (hgap : n + D + g ≤ aLoΛ + 1)
    (hsmall : 8 * (hiΛ + cxCap) ≤ 9 * n)
    (T Hocc M K : ℕ)
    (hHT : 2 * Hocc ≤ T) (hK : n + 2 * M ≤ K)
    (s₀ : SingleState n) (hcxCap : s₀.1.y + M ≤ cxCap) :
    ∑' q, (if (¬ SingleBandFrozen n aLoΛ hiΛ D H q) ∧
          q.rx + q.ry < M then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) ≤
      1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
      singleBlankW n g ^ s₀.1.doubleLevel /
        (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc) := by
  let qClock := SingleClockTrace.initial (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
  have hclock :=
    singleClock_twoBranch_tail n hn aLoΛ hiΛ D H g cxCap hgap hsmall
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
          (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g) qClock
        ≤ singleBlankW n g ^ s₀.1.doubleLevel := by
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
            (singleBlankW n g) (singleBlankV n g) (singleBlankEta n g)
            qClock /
          (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc) := hclock
    _ ≤
        1 / (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ K) +
        singleBlankW n g ^ s₀.1.doubleLevel /
          (singleBlankW n g ^ hiΛ * singleBlankEta n g ^ Hocc) := by
      exact add_le_add
        (ENNReal.div_le_div_right hnormPot.le _)
        (ENNReal.div_le_div_right hblankPot _)

section Inhabitation

example :
    (SingleClockTrace.initial
        (⟨⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
          SingleLedger 160)).FuelClockInv 137 8 :=
  SingleClockTrace.initial_fuelClockInv
    (⟨⟨15, 8, 137⟩, by norm_num [BiCfg.DoubleInv]⟩ : SingleState 160)

end Inhabitation

end Tri

#print axioms Tri.SingleClockTrace.initial_fuelClockInv
#print axioms Tri.iter_singleBandStop_eq_clock_map
#print axioms Tri.singleBand_indicator_eq_clock
#print axioms Tri.singleClock_twoBranch_tail
#print axioms Tri.singleBand_joint_clock_tail

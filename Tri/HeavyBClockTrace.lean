/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBBandReturn

/-!
# Occupation trace for the two-branch Heavy-B clock

This is the Heavy-B analogue of `DoubleBClockTrace`.  The normal tick mask is
the same free-`Y` condition, but the core ledger is Heavy-B's exact `YLedger`.
The masked normal-fuel counter counts the same pair labels as Double-B's normal
branch (`xy` and `yb`), while the Heavy core's `fuel` counter still counts only
creations (`xy`).
-/

namespace Tri

/-- The counted Heavy-B trace augmented by occupation and masked-fuel counters. -/
structure HeavyClockTrace (n : ℕ) where
  core : HeavyTrace n
  normalTicks : ℕ
  blankTicks : ℕ
  normalFuel : ℕ

/-- The strict interior of a Heavy-B level band. -/
def HeavyTrace.BandLive {n : ℕ} (aLo hi : ℕ) (q : HeavyTrace n) : Prop :=
  aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
    BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi

/-- The free-`Y` branch of the occupation split. -/
def HeavyTrace.NormalTick {n : ℕ} (q : HeavyTrace n) : Prop :=
  n ≤ 16 * q.cfg.1.y

instance HeavyTrace.instDecidableBandLive {n : ℕ} (aLo hi : ℕ) (q : HeavyTrace n) :
    Decidable (q.BandLive aLo hi) := by
  unfold HeavyTrace.BandLive
  infer_instance

instance HeavyTrace.instDecidableNormalTick {n : ℕ} (q : HeavyTrace n) :
    Decidable q.NormalTick := by
  unfold HeavyTrace.NormalTick
  infer_instance

namespace PairComp

/-- The normal-branch masked fuel labels, matching Double-B: `xy` and `yb`. -/
def heavyNormalFuelInc : PairComp → ℕ
  | .xy | .yb => 1
  | _ => 0

/-- Advance the Heavy-B core and occupation counters on a supported pair label.
A zero-weight label leaves the whole trace fixed.  The branch classification is
made from the pre-state. -/
noncomputable def nextHeavyClockTrace {n : ℕ}
    (q : HeavyClockTrace n) (k : PairComp) : HeavyClockTrace n :=
  if _hk : PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0 then
    q
  else
    { core := PairComp.nextHeavyTrace q.core k
      normalTicks :=
        q.normalTicks + if q.core.NormalTick then 1 else 0
      blankTicks :=
        q.blankTicks + if q.core.NormalTick then 0 else 1
      normalFuel :=
        q.normalFuel + if q.core.NormalTick then k.heavyNormalFuelInc else 0 }

end PairComp

/-- One raw Heavy-B interaction while the core is inside the band, frozen
outside.  At populations with fewer than two entities the underlying Heavy-B
trace step is totalized as a self-loop. -/
noncomputable def heavyClockBandStep
    (n : ℕ) (aLo hi : ℕ)
    (q : HeavyClockTrace n) : PMF (HeavyClockTrace n) :=
  if q.core.BandLive aLo hi then
    if h : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b then
      (dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h).map
        (PairComp.nextHeavyClockTrace q)
    else
      PMF.pure q
  else
    PMF.pure q

/-- Forgetting the occupation counters recovers the corresponding stopped core
step. -/
theorem heavyClockBandStep_map_core
    (n : ℕ) (aLo hi : ℕ) (q : HeavyClockTrace n) :
    (heavyClockBandStep n aLo hi q).map HeavyClockTrace.core =
      heavyBandStop n aLo hi q.core := by
  unfold heavyClockBandStep heavyBandStop heavyTraceStep
  by_cases hlive : q.core.BandLive aLo hi
  · rw [if_pos hlive]
    unfold HeavyTrace.BandLive at hlive
    rw [if_pos hlive]
    by_cases h : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b
    · rw [dif_pos h, dif_pos h]
      rw [PMF.map_comp]
      congr 1
      funext k
      unfold Function.comp PairComp.nextHeavyClockTrace
      by_cases hk :
          PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
      · rw [dif_pos hk, PairComp.nextHeavyTrace, dif_pos hk]
      · rw [dif_neg hk]
    · rw [dif_neg h, dif_neg h]
      exact PMF.pure_map HeavyClockTrace.core q
  · rw [if_neg hlive]
    have hstop : ¬(aLo + 1 ≤ BiCfg.heavyLevel q.core.cfg.1 ∧
        BiCfg.heavyLevel q.core.cfg.1 + 1 ≤ hi) := by
      simpa [HeavyTrace.BandLive] using hlive
    rw [if_neg hstop]
    exact PMF.pure_map HeavyClockTrace.core q

/-- Exactly one of the two occupation counters advances on each live supported
raw interaction. -/
theorem PairComp.nextHeavyClockTrace_tick_sum {n : ℕ}
    (q : HeavyClockTrace n) (k : PairComp)
    (hk : PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k ≠ 0) :
    (PairComp.nextHeavyClockTrace q k).normalTicks +
        (PairComp.nextHeavyClockTrace q k).blankTicks =
      q.normalTicks + q.blankTicks + 1 := by
  unfold PairComp.nextHeavyClockTrace
  rw [dif_neg hk]
  by_cases hnormal : q.core.NormalTick <;> simp [hnormal] <;> omega

/-- The masked normal-fuel counter never exceeds the sum of Heavy creations and
`Y`-resolutions if this was true before the step. -/
theorem PairComp.nextHeavyClockTrace_normalFuel_le {n : ℕ}
    (q : HeavyClockTrace n) (k : PairComp)
    (hq : q.normalFuel ≤ q.core.fuel + q.core.down)
    (hk : PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k ≠ 0) :
    (PairComp.nextHeavyClockTrace q k).normalFuel ≤
      (PairComp.nextHeavyClockTrace q k).core.fuel +
        (PairComp.nextHeavyClockTrace q k).core.down := by
  unfold PairComp.nextHeavyClockTrace
  rw [dif_neg hk]
  rw [PairComp.nextHeavyTrace, dif_neg hk]
  cases k <;>
    simp only [PairComp.heavyNormalFuelInc, PairComp.heavyFuelInc,
      PairComp.heavyDownInc] <;>
    split_ifs <;> omega

/-- The Heavy-B `Y` ledger together with the fact that masked normal fuel is a
subcounter of creations plus `Y`-resolutions. -/
def HeavyClockTrace.FuelClockInv {n : ℕ}
    (y₀ : ℕ) (q : HeavyClockTrace n) : Prop :=
  q.core.YLedger y₀ ∧ q.normalFuel ≤ q.core.fuel + q.core.down

/-- A supported stopped-clock step preserves the joint fuel-clock invariant. -/
theorem heavyClockBandStep_fuelClockInv_of_apply_ne_zero
    {n y₀ : ℕ} (aLo hi : ℕ)
    (a : HeavyClockTrace n) (ha : a.FuelClockInv y₀)
    (z : HeavyClockTrace n)
    (haz : heavyClockBandStep n aLo hi a z ≠ 0) :
    z.FuelClockInv y₀ := by
  unfold heavyClockBandStep at haz
  split_ifs at haz with hlive hent
  · rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
    push Not at haz
    obtain ⟨k, hk⟩ := haz
    split_ifs at hk with hzk
    · have hwk :
          PairComp.weight a.core.cfg.1.x a.core.cfg.1.y a.core.cfg.1.b k ≠ 0 :=
        fun hw => hk (dbPairPMF_zero_of_weight_zero hw)
      rw [hzk]
      constructor
      · unfold PairComp.nextHeavyClockTrace
        rw [dif_neg hwk]
        exact PairComp.nextHeavyTrace_yLedger a.core k ha.1 hwk
      · exact PairComp.nextHeavyClockTrace_normalFuel_le a k ha.2 hwk
    · exact absurd rfl hk
  · simp only [PMF.pure_apply] at haz
    by_cases hza : z = a
    · rwa [hza]
    · simp [hza] at haz
  · simp only [PMF.pure_apply] at haz
    by_cases hza : z = a
    · rwa [hza]
    · simp [hza] at haz

/-- The joint fuel-clock invariant holds throughout every finite stopped
occupation trace. -/
theorem heavyClockBand_iter_fuelClockInv
    {n y₀ T : ℕ} (aLo hi : ℕ)
    (q z : HeavyClockTrace n) (hq : q.FuelClockInv y₀)
    (hz : iter (heavyClockBandStep n aLo hi) T q z ≠ 0) :
    z.FuelClockInv y₀ :=
  iter_support_closed
    (heavyClockBandStep n aLo hi) (HeavyClockTrace.FuelClockInv y₀)
    (fun a ha z haz =>
      heavyClockBandStep_fuelClockInv_of_apply_ne_zero aLo hi a ha z haz)
    T q z hq hz

/-- A supported step ending in the live band started live and advanced exactly
one of the two occupation counters.  The population hypothesis rules out the
Heavy-B totalized no-entity self-loop. -/
theorem heavyClockBandStep_tick_sum_of_live_target
    {n : ℕ} (hn : 3 ≤ n) (aLo hi : ℕ)
    (a z : HeavyClockTrace n)
    (hzlive : z.core.BandLive aLo hi)
    (haz : heavyClockBandStep n aLo hi a z ≠ 0) :
    a.core.BandLive aLo hi ∧
      z.normalTicks + z.blankTicks =
        a.normalTicks + a.blankTicks + 1 := by
  have halive : a.core.BandLive aLo hi := by
    by_contra halive
    unfold heavyClockBandStep at haz
    rw [if_neg halive, PMF.pure_apply] at haz
    by_cases hza : z = a
    · rw [hza] at hzlive
      exact halive hzlive
    · simp [hza] at haz
  refine ⟨halive, ?_⟩
  unfold heavyClockBandStep at haz
  rw [if_pos halive] at haz
  have hent : 2 ≤ a.core.cfg.1.x + a.core.cfg.1.y + a.core.cfg.1.b :=
    heavy_two_entities hn a.core.cfg
  rw [dif_pos hent, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
  push Not at haz
  obtain ⟨k, hk⟩ := haz
  split_ifs at hk with hzk
  · have hwk :
        PairComp.weight a.core.cfg.1.x a.core.cfg.1.y a.core.cfg.1.b k ≠ 0 :=
      fun hw => hk (dbPairPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact PairComp.nextHeavyClockTrace_tick_sum a k hwk
  · exact absurd rfl hk

/-- Once the stopped occupation chain is outside the band, every supported next
state is outside as well. -/
theorem heavyClockBandStep_not_live_of_apply_ne_zero
    {n : ℕ} (aLo hi : ℕ)
    (a : HeavyClockTrace n) (ha : ¬a.core.BandLive aLo hi)
    (z : HeavyClockTrace n)
    (haz : heavyClockBandStep n aLo hi a z ≠ 0) :
    ¬z.core.BandLive aLo hi := by
  unfold heavyClockBandStep at haz
  rw [if_neg ha, PMF.pure_apply] at haz
  by_cases hza : z = a
  · rwa [hza]
  · simp [hza] at haz

/-- A live endpoint of an iterate can only come from a live starting state. -/
theorem heavyClockBand_iter_start_live_of_final
    {n T : ℕ} (aLo hi : ℕ)
    (q z : HeavyClockTrace n)
    (hz : iter (heavyClockBandStep n aLo hi) T q z ≠ 0)
    (hzlive : z.core.BandLive aLo hi) :
    q.core.BandLive aLo hi := by
  by_contra hqlive
  have hznot :=
    iter_support_closed
      (heavyClockBandStep n aLo hi)
      (fun a : HeavyClockTrace n => ¬a.core.BandLive aLo hi)
      (fun a ha z haz =>
        heavyClockBandStep_not_live_of_apply_ne_zero
          aLo hi a ha z haz)
      T q z hqlive hz
  exact hznot hzlive

/-- At a positive-mass live time-`T` endpoint, all `T` raw interactions were
live and hence the two occupation counters sum to their initial sum plus `T`. -/
theorem heavyClockBand_iter_tick_sum_of_final_live
    {n : ℕ} (hn : 3 ≤ n) (aLo hi : ℕ) :
    ∀ T (q z : HeavyClockTrace n),
      iter (heavyClockBandStep n aLo hi) T q z ≠ 0 →
      z.core.BandLive aLo hi →
      z.normalTicks + z.blankTicks =
        q.normalTicks + q.blankTicks + T := by
  intro T
  induction T with
  | zero =>
      intro q z hz hzlive
      simp only [iter, PMF.pure_apply] at hz
      by_cases hzq : z = q
      · subst z
        simp
      · simp [hzq] at hz
  | succ T ih =>
      intro q z hz hzlive
      rw [iter_succ, PMF.bind_apply] at hz
      have hex :
          ∃ a, heavyClockBandStep n aLo hi q a *
              iter (heavyClockBandStep n aLo hi) T a z ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        rw [ENNReal.tsum_eq_zero]
        exact h
      obtain ⟨a, ha⟩ := hex
      have hqa : heavyClockBandStep n aLo hi q a ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have haz :
          iter (heavyClockBandStep n aLo hi) T a z ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have halive : a.core.BandLive aLo hi :=
        heavyClockBand_iter_start_live_of_final
          aLo hi a z haz hzlive
      have hstep :=
        heavyClockBandStep_tick_sum_of_live_target
          hn aLo hi q a halive hqa
      have hrest := ih a z haz hzlive
      omega

example :
    (⟨⟨⟨21, 9, 65⟩, by norm_num [BiCfg.HeavyInv]⟩, 0, 0, 0⟩ :
        HeavyTrace 160).BandLive 85 88 := by
  norm_num [HeavyTrace.BandLive, BiCfg.heavyLevel]

end Tri

#print axioms Tri.heavyClockBandStep_map_core
#print axioms Tri.PairComp.nextHeavyClockTrace_tick_sum
#print axioms Tri.PairComp.nextHeavyClockTrace_normalFuel_le
#print axioms Tri.heavyClockBand_iter_fuelClockInv
#print axioms Tri.heavyClockBand_iter_tick_sum_of_final_live

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockMass
import Tri.DoubleBTrace

/-!
# Occupation trace for the two-branch Double-B clock

Every live raw interaction is classified from its pre-state.  A normal tick has
`n ≤ 16y`; every other live tick is counted in the complementary branch.  The
small-gap arithmetic theorem later proves that each complementary tick is
blank-heavy.
-/

namespace Tri

/-- The counted Double-B trace augmented by occupation and masked-fuel
counters. -/
structure DoubleClockTrace (n : ℕ) where
  core : DoubleTrace n
  normalTicks : ℕ
  blankTicks : ℕ
  normalFuel : ℕ

/-- The strict interior of a doubled-level band. -/
def DoubleTrace.BandLive {n : ℕ} (aLo hi : ℕ) (q : DoubleTrace n) : Prop :=
  aLo + 1 ≤ q.cfg.1.doubleLevel ∧ q.cfg.1.doubleLevel + 1 ≤ hi

/-- The free-`Y` branch of the occupation split. -/
def DoubleTrace.NormalTick {n : ℕ} (q : DoubleTrace n) : Prop :=
  n ≤ 16 * q.cfg.1.y

instance {n : ℕ} (aLo hi : ℕ) (q : DoubleTrace n) :
    Decidable (q.BandLive aLo hi) := by
  unfold DoubleTrace.BandLive
  infer_instance

instance {n : ℕ} (q : DoubleTrace n) :
    Decidable q.NormalTick := by
  unfold DoubleTrace.NormalTick
  infer_instance

/-- Advance the core and occupation counters on a supported pair label.  A
zero-weight label leaves the whole trace fixed.  The branch classification is
made from the pre-state. -/
noncomputable def PairComp.nextDoubleClockTrace {n : ℕ}
    (q : DoubleClockTrace n) (k : PairComp) : DoubleClockTrace n :=
  if _hk : PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0 then
    q
  else
    { core := PairComp.nextDoubleTrace q.core k
      normalTicks :=
        q.normalTicks + if q.core.NormalTick then 1 else 0
      blankTicks :=
        q.blankTicks + if q.core.NormalTick then 0 else 1
      normalFuel :=
        q.normalFuel + if q.core.NormalTick then k.fuelInc else 0 }

/-- One raw Double-B interaction while the core is inside the band, frozen
outside. -/
noncomputable def doubleClockBandStep
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ)
    (q : DoubleClockTrace n) : PMF (DoubleClockTrace n) :=
  if q.core.BandLive aLo hi then
    (dbPairPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b
      (by have := q.core.cfg.2; simp only [BiCfg.DoubleInv] at this; omega)).map
        (PairComp.nextDoubleClockTrace q)
  else
    PMF.pure q

/-- Forgetting the occupation counters recovers the corresponding stopped core
step. -/
theorem doubleClockBandStep_map_core
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ) (q : DoubleClockTrace n) :
    (doubleClockBandStep n hn aLo hi q).map DoubleClockTrace.core =
      if q.core.BandLive aLo hi then
        doubleTraceStep n hn q.core
      else
        PMF.pure q.core := by
  unfold doubleClockBandStep
  split_ifs with hlive
  · unfold doubleTraceStep
    rw [PMF.map_comp]
    congr 1
    funext k
    unfold Function.comp PairComp.nextDoubleClockTrace
    by_cases hk :
        PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [dif_pos hk, PairComp.nextDoubleTrace, dif_pos hk]
    · rw [dif_neg hk]
  · exact PMF.pure_map DoubleClockTrace.core q

/-- Exactly one of the two occupation counters advances on each live tick. -/
theorem PairComp.nextDoubleClockTrace_tick_sum {n : ℕ}
    (q : DoubleClockTrace n) (k : PairComp)
    (hk : PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k ≠ 0) :
    (PairComp.nextDoubleClockTrace q k).normalTicks +
        (PairComp.nextDoubleClockTrace q k).blankTicks =
      q.normalTicks + q.blankTicks + 1 := by
  unfold PairComp.nextDoubleClockTrace
  rw [dif_neg hk]
  by_cases hnormal : q.core.NormalTick <;> simp [hnormal] <;> omega

/-- The masked fuel counter never exceeds the core fuel counter if this was
true before the step. -/
theorem PairComp.nextDoubleClockTrace_normalFuel_le {n : ℕ}
    (q : DoubleClockTrace n) (k : PairComp)
    (hq : q.normalFuel ≤ q.core.fuel)
    (hk : PairComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k ≠ 0) :
    (PairComp.nextDoubleClockTrace q k).normalFuel ≤
      (PairComp.nextDoubleClockTrace q k).core.fuel := by
  unfold PairComp.nextDoubleClockTrace
  rw [dif_neg hk]
  rw [PairComp.nextDoubleTrace, dif_neg hk]
  cases k <;>
    simp only [PairComp.fuelInc] <;>
    split_ifs <;> omega

/-- The core fuel ledger together with the fact that masked normal fuel is a
subcounter of total fuel. -/
def DoubleClockTrace.FuelClockInv {n : ℕ}
    (y₀ : ℕ) (q : DoubleClockTrace n) : Prop :=
  q.core.FuelInv y₀ ∧ q.normalFuel ≤ q.core.fuel

/-- A supported stopped-clock step preserves the joint fuel-clock invariant. -/
theorem doubleClockBandStep_fuelClockInv_of_apply_ne_zero
    {n y₀ : ℕ} (hn : 2 ≤ n) (aLo hi : ℕ)
    (a : DoubleClockTrace n) (ha : a.FuelClockInv y₀)
    (z : DoubleClockTrace n)
    (haz : doubleClockBandStep n hn aLo hi a z ≠ 0) :
    z.FuelClockInv y₀ := by
  unfold doubleClockBandStep at haz
  split_ifs at haz with hlive
  · rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
    push_neg at haz
    obtain ⟨k, hk⟩ := haz
    split_ifs at hk with hzk
    · have hwk :
          PairComp.weight a.core.cfg.1.x a.core.cfg.1.y a.core.cfg.1.b k ≠ 0 :=
        fun hw => hk (dbPairPMF_zero_of_weight_zero hw)
      rw [hzk]
      constructor
      · unfold PairComp.nextDoubleClockTrace
        rw [dif_neg hwk]
        exact PairComp.nextDoubleTrace_fuelInv a.core k ha.1 hwk
      · exact PairComp.nextDoubleClockTrace_normalFuel_le a k ha.2 hwk
    · exact absurd rfl hk
  · simp only [PMF.pure_apply] at haz
    by_cases hza : z = a
    · rwa [hza]
    · simp [hza] at haz

/-- The joint fuel-clock invariant holds throughout every finite stopped
occupation trace. -/
theorem doubleClockBand_iter_fuelClockInv
    {n y₀ T : ℕ} (hn : 2 ≤ n) (aLo hi : ℕ)
    (q z : DoubleClockTrace n) (hq : q.FuelClockInv y₀)
    (hz : iter (doubleClockBandStep n hn aLo hi) T q z ≠ 0) :
    z.FuelClockInv y₀ :=
  iter_support_closed
    (doubleClockBandStep n hn aLo hi) (DoubleClockTrace.FuelClockInv y₀)
    (fun a ha z haz =>
      doubleClockBandStep_fuelClockInv_of_apply_ne_zero hn aLo hi a ha z haz)
    T q z hq hz

/-- A supported step ending in the live band started live and advanced exactly
one of the two occupation counters. -/
theorem doubleClockBandStep_tick_sum_of_live_target
    {n : ℕ} (hn : 2 ≤ n) (aLo hi : ℕ)
    (a z : DoubleClockTrace n)
    (hzlive : z.core.BandLive aLo hi)
    (haz : doubleClockBandStep n hn aLo hi a z ≠ 0) :
    a.core.BandLive aLo hi ∧
      z.normalTicks + z.blankTicks =
        a.normalTicks + a.blankTicks + 1 := by
  have halive : a.core.BandLive aLo hi := by
    by_contra halive
    unfold doubleClockBandStep at haz
    rw [if_neg halive, PMF.pure_apply] at haz
    by_cases hza : z = a
    · rw [hza] at hzlive
      exact halive hzlive
    · simp [hza] at haz
  refine ⟨halive, ?_⟩
  unfold doubleClockBandStep at haz
  rw [if_pos halive, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
  push Not at haz
  obtain ⟨k, hk⟩ := haz
  split_ifs at hk with hzk
  · have hwk :
        PairComp.weight a.core.cfg.1.x a.core.cfg.1.y a.core.cfg.1.b k ≠ 0 :=
      fun hw => hk (dbPairPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact PairComp.nextDoubleClockTrace_tick_sum a k hwk
  · exact absurd rfl hk

/-- Once the stopped occupation chain is outside the band, every supported
next state is outside as well. -/
theorem doubleClockBandStep_not_live_of_apply_ne_zero
    {n : ℕ} (hn : 2 ≤ n) (aLo hi : ℕ)
    (a : DoubleClockTrace n) (ha : ¬a.core.BandLive aLo hi)
    (z : DoubleClockTrace n)
    (haz : doubleClockBandStep n hn aLo hi a z ≠ 0) :
    ¬z.core.BandLive aLo hi := by
  unfold doubleClockBandStep at haz
  rw [if_neg ha, PMF.pure_apply] at haz
  by_cases hza : z = a
  · rwa [hza]
  · simp [hza] at haz

/-- A live endpoint of an iterate can only come from a live starting state. -/
theorem doubleClockBand_iter_start_live_of_final
    {n T : ℕ} (hn : 2 ≤ n) (aLo hi : ℕ)
    (q z : DoubleClockTrace n)
    (hz : iter (doubleClockBandStep n hn aLo hi) T q z ≠ 0)
    (hzlive : z.core.BandLive aLo hi) :
    q.core.BandLive aLo hi := by
  by_contra hqlive
  have hznot :=
    iter_support_closed
      (doubleClockBandStep n hn aLo hi)
      (fun a : DoubleClockTrace n => ¬a.core.BandLive aLo hi)
      (fun a ha z haz =>
        doubleClockBandStep_not_live_of_apply_ne_zero
          hn aLo hi a ha z haz)
      T q z hqlive hz
  exact hznot hzlive

/-- At a positive-mass live time-`T` endpoint, all `T` raw interactions were
live and hence the two occupation counters sum to their initial sum plus `T`. -/
theorem doubleClockBand_iter_tick_sum_of_final_live
    {n : ℕ} (hn : 2 ≤ n) (aLo hi : ℕ) :
    ∀ T (q z : DoubleClockTrace n),
      iter (doubleClockBandStep n hn aLo hi) T q z ≠ 0 →
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
          ∃ a, doubleClockBandStep n hn aLo hi q a *
              iter (doubleClockBandStep n hn aLo hi) T a z ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        rw [ENNReal.tsum_eq_zero]
        exact h
      obtain ⟨a, ha⟩ := hex
      have hqa : doubleClockBandStep n hn aLo hi q a ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have haz :
          iter (doubleClockBandStep n hn aLo hi) T a z ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have halive : a.core.BandLive aLo hi :=
        doubleClockBand_iter_start_live_of_final
          hn aLo hi a z haz hzlive
      have hstep :=
        doubleClockBandStep_tick_sum_of_live_target
          hn aLo hi q a halive hqa
      have hrest := ih a z haz hzlive
      omega

end Tri

#print axioms Tri.doubleClockBandStep_map_core
#print axioms Tri.PairComp.nextDoubleClockTrace_tick_sum
#print axioms Tri.PairComp.nextDoubleClockTrace_normalFuel_le
#print axioms Tri.doubleClockBand_iter_fuelClockInv
#print axioms Tri.doubleClockBand_iter_tick_sum_of_final_live

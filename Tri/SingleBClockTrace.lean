/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBBandKernel

/-!
# Occupation trace for the two-branch Single-B clock

This is the Single-B analogue of `HeavyBClockTrace`.  The core is the oriented
`SingleLedger` and the stopped kernel freezes on the repaired four-way band
boundary `SingleBandFrozen`.  The normal tick mask is the free-`Y` condition
`n ≤ 16y`; the masked normal-fuel labels are the two fair creations and the
`Y`-resolution (`xyToX`, `xyToY`, `yb`), matching Double-B's `xy`/`yb` after
splitting the creation pair.

The fuel-to-resolution conversion uses the AGGREGATE oriented blank ledger
`CX+CY+b₀ = b+RX+RY` (no orientation bookkeeping in the clock): the masked
fuel counter is dominated by `CX+CY+RY`, which the ledger caps by
`n + 2·(RX+RY) − b₀`.
-/

namespace Tri

open scoped ENNReal

/-- The counted Single-B ledger augmented by occupation and masked-fuel
counters. -/
structure SingleClockTrace (n : ℕ) where
  core : SingleLedger n
  normalTicks : ℕ
  blankTicks : ℕ
  normalFuel : ℕ

/-- The free-`Y` branch of the occupation split. -/
def SingleLedger.NormalTick {n : ℕ} (q : SingleLedger n) : Prop :=
  n ≤ 16 * q.cfg.1.y

instance SingleLedger.instDecidableNormalTick
    {n : ℕ} (q : SingleLedger n) : Decidable q.NormalTick := by
  unfold SingleLedger.NormalTick
  infer_instance

namespace SingleComp

/-- The normal-branch masked fuel labels: the two fair creations and the
`Y`-resolution. -/
def singleNormalFuelInc : SingleComp → ℕ
  | .xyToX | .xyToY | .yb => 1
  | _ => 0

/-- Advance the Single-B core and occupation counters on a supported event
label.  A zero-weight label leaves the whole trace fixed.  The branch
classification is made from the pre-state. -/
noncomputable def nextSingleClockTrace {n : ℕ}
    (q : SingleClockTrace n) (k : SingleComp) : SingleClockTrace n :=
  if _hk : SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k
      = 0 then
    q
  else
    { core := SingleComp.nextSingleLedger q.core k
      normalTicks :=
        q.normalTicks + if q.core.NormalTick then 1 else 0
      blankTicks :=
        q.blankTicks + if q.core.NormalTick then 0 else 1
      normalFuel :=
        q.normalFuel + if q.core.NormalTick then k.singleNormalFuelInc else 0 }

end SingleComp

/-- One raw Single-B interaction while the core band is live, frozen on the
repaired stopped boundary. -/
noncomputable def singleClockBandStep
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (q : SingleClockTrace n) : PMF (SingleClockTrace n) :=
  if SingleBandFrozen n aLoΛ hiΛ D H q.core then
    PMF.pure q
  else
    (singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b (by
      have h := q.core.cfg.2
      simp only [BiCfg.DoubleInv] at h
      omega)).map (SingleComp.nextSingleClockTrace q)

/-- Forgetting the occupation counters recovers the repaired stopped Single-B
band kernel. -/
theorem singleClockBandStep_map_core
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ) (q : SingleClockTrace n) :
    (singleClockBandStep n hn aLoΛ hiΛ D H q).map SingleClockTrace.core =
      singleBandStop n hn aLoΛ hiΛ D H q.core := by
  unfold singleClockBandStep singleBandStop freeze
  by_cases hB : SingleBandFrozen n aLoΛ hiΛ D H q.core
  · rw [if_pos hB, if_pos hB]
    exact PMF.pure_map SingleClockTrace.core q
  · rw [if_neg hB, if_neg hB]
    unfold singleLedgerStep
    rw [PMF.map_comp]
    apply PMF.map_change_on_zero_mass
    intro k hkdiff
    unfold Function.comp at hkdiff
    by_cases hk :
        SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · unfold SingleComp.nextSingleClockTrace SingleComp.nextSingleLedger
        at hkdiff
      rw [dif_pos hk, dif_pos hk] at hkdiff
      exact absurd rfl hkdiff
    · unfold SingleComp.nextSingleClockTrace at hkdiff
      rw [dif_neg hk] at hkdiff
      exact absurd rfl hkdiff

/-- Exactly one of the two occupation counters advances on each supported raw
interaction. -/
theorem SingleComp.nextSingleClockTrace_tick_sum {n : ℕ}
    (q : SingleClockTrace n) (k : SingleComp)
    (hk : SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k
      ≠ 0) :
    (SingleComp.nextSingleClockTrace q k).normalTicks +
        (SingleComp.nextSingleClockTrace q k).blankTicks =
      q.normalTicks + q.blankTicks + 1 := by
  unfold SingleComp.nextSingleClockTrace
  rw [dif_neg hk]
  by_cases hnormal : q.core.NormalTick <;> simp [hnormal] <;> omega

/-- The masked normal-fuel counter stays dominated by the oriented total
`CX+CY+RY` across every supported event. -/
theorem SingleComp.nextSingleClockTrace_normalFuel_le {n : ℕ}
    (q : SingleClockTrace n) (k : SingleComp)
    (hq : q.normalFuel ≤ q.core.cx + q.core.cy + q.core.ry)
    (hk : SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k
      ≠ 0) :
    (SingleComp.nextSingleClockTrace q k).normalFuel ≤
      (SingleComp.nextSingleClockTrace q k).core.cx +
        (SingleComp.nextSingleClockTrace q k).core.cy +
        (SingleComp.nextSingleClockTrace q k).core.ry := by
  unfold SingleComp.nextSingleClockTrace
  rw [dif_neg hk]
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hk]
  cases k <;>
    simp only [SingleComp.singleNormalFuelInc, SingleComp.cxInc,
      SingleComp.cyInc, SingleComp.ryInc] <;>
    split_ifs <;> omega

/-- The `CX` counter is monotone across one guarded clock event. -/
theorem SingleComp.nextSingleClockTrace_cx_mono {n : ℕ}
    (q : SingleClockTrace n) (k : SingleComp) :
    q.core.cx ≤ (SingleComp.nextSingleClockTrace q k).core.cx := by
  unfold SingleComp.nextSingleClockTrace
  by_cases hk :
      SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
  · rw [dif_pos hk]
  · rw [dif_neg hk]
    change q.core.cx ≤ (SingleComp.nextSingleLedger q.core k).cx
    unfold SingleComp.nextSingleLedger
    rw [dif_neg hk]
    simp

/-- The Single-B fuel-clock invariant: the aggregate oriented blank ledger,
the corrected-`Y` identity, and the fact that masked normal fuel is a
subcounter of `CX+CY+RY`. -/
def SingleClockTrace.FuelClockInv {n : ℕ}
    (b₀ y₀ : ℕ) (q : SingleClockTrace n) : Prop :=
  q.core.BlankLedger b₀ ∧ q.core.CorrectedY y₀ ∧
    q.normalFuel ≤ q.core.cx + q.core.cy + q.core.ry

/-- A supported stopped-clock step preserves the joint fuel-clock invariant. -/
theorem singleClockBandStep_fuelClockInv_of_apply_ne_zero
    {n b₀ y₀ : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (a : SingleClockTrace n) (ha : a.FuelClockInv b₀ y₀)
    (z : SingleClockTrace n)
    (haz : singleClockBandStep n hn aLoΛ hiΛ D H a z ≠ 0) :
    z.FuelClockInv b₀ y₀ := by
  unfold singleClockBandStep at haz
  split_ifs at haz with hB
  · simp only [PMF.pure_apply] at haz
    by_cases hza : z = a
    · rwa [hza]
    · simp [hza] at haz
  · rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
    push Not at haz
    obtain ⟨k, hk⟩ := haz
    split_ifs at hk with hzk
    · have hwk :
          SingleComp.weight a.core.cfg.1.x a.core.cfg.1.y a.core.cfg.1.b k
            ≠ 0 :=
        fun hw => hk (singleCompPMF_zero_of_weight_zero hw)
      rw [hzk]
      refine ⟨?_, ?_, ?_⟩
      · unfold SingleComp.nextSingleClockTrace
        rw [dif_neg hwk]
        exact SingleComp.nextSingleLedger_blankLedger a.core k ha.1 hwk
      · unfold SingleComp.nextSingleClockTrace
        rw [dif_neg hwk]
        exact SingleComp.nextSingleLedger_correctedY a.core k ha.2.1 hwk
      · exact SingleComp.nextSingleClockTrace_normalFuel_le a k ha.2.2 hwk
    · exact absurd rfl hk

/-- The joint fuel-clock invariant holds throughout every finite stopped
occupation trace. -/
theorem singleClockBand_iter_fuelClockInv
    {n b₀ y₀ T : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (q z : SingleClockTrace n) (hq : q.FuelClockInv b₀ y₀)
    (hz : iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q z ≠ 0) :
    z.FuelClockInv b₀ y₀ :=
  iter_support_closed
    (singleClockBandStep n hn aLoΛ hiΛ D H)
    (SingleClockTrace.FuelClockInv b₀ y₀)
    (fun a ha z haz =>
      singleClockBandStep_fuelClockInv_of_apply_ne_zero hn aLoΛ hiΛ D H
        a ha z haz)
    T q z hq hz

/-- The `CX` counter is monotone on the support of one stopped-clock step. -/
theorem singleClockBandStep_cx_mono_of_apply_ne_zero
    {n : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (a z : SingleClockTrace n)
    (haz : singleClockBandStep n hn aLoΛ hiΛ D H a z ≠ 0) :
    a.core.cx ≤ z.core.cx := by
  unfold singleClockBandStep at haz
  split_ifs at haz with hB
  · simp only [PMF.pure_apply] at haz
    by_cases hza : z = a
    · rw [hza]
    · simp [hza] at haz
  · rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
    push Not at haz
    obtain ⟨k, hk⟩ := haz
    split_ifs at hk with hzk
    · rw [hzk]
      exact SingleComp.nextSingleClockTrace_cx_mono a k
    · exact absurd rfl hk

/-- A supported step ending in a live state started live and advanced exactly
one of the two occupation counters. -/
theorem singleClockBandStep_tick_sum_of_live_target
    {n : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (a z : SingleClockTrace n)
    (hzlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H z.core)
    (haz : singleClockBandStep n hn aLoΛ hiΛ D H a z ≠ 0) :
    ¬ SingleBandFrozen n aLoΛ hiΛ D H a.core ∧
      z.normalTicks + z.blankTicks =
        a.normalTicks + a.blankTicks + 1 := by
  have halive : ¬ SingleBandFrozen n aLoΛ hiΛ D H a.core := by
    by_contra halive
    unfold singleClockBandStep at haz
    rw [if_pos halive, PMF.pure_apply] at haz
    by_cases hza : z = a
    · rw [hza] at hzlive
      exact hzlive halive
    · simp [hza] at haz
  refine ⟨halive, ?_⟩
  unfold singleClockBandStep at haz
  rw [if_neg halive, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at haz
  push Not at haz
  obtain ⟨k, hk⟩ := haz
  split_ifs at hk with hzk
  · have hwk :
        SingleComp.weight a.core.cfg.1.x a.core.cfg.1.y a.core.cfg.1.b k
          ≠ 0 :=
      fun hw => hk (singleCompPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact SingleComp.nextSingleClockTrace_tick_sum a k hwk
  · exact absurd rfl hk

/-- Once the stopped occupation chain is frozen, every supported next state is
frozen as well. -/
theorem singleClockBandStep_frozen_of_apply_ne_zero
    {n : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (a : SingleClockTrace n)
    (ha : SingleBandFrozen n aLoΛ hiΛ D H a.core)
    (z : SingleClockTrace n)
    (haz : singleClockBandStep n hn aLoΛ hiΛ D H a z ≠ 0) :
    SingleBandFrozen n aLoΛ hiΛ D H z.core := by
  unfold singleClockBandStep at haz
  rw [if_pos ha, PMF.pure_apply] at haz
  by_cases hza : z = a
  · rwa [hza]
  · simp [hza] at haz

/-- A live endpoint of an iterate can only come from a live starting state. -/
theorem singleClockBand_iter_start_live_of_final
    {n T : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (q z : SingleClockTrace n)
    (hz : iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q z ≠ 0)
    (hzlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H z.core) :
    ¬ SingleBandFrozen n aLoΛ hiΛ D H q.core := by
  by_contra hqlive
  have hznot :=
    iter_support_closed
      (singleClockBandStep n hn aLoΛ hiΛ D H)
      (fun a : SingleClockTrace n => SingleBandFrozen n aLoΛ hiΛ D H a.core)
      (fun a ha z haz =>
        singleClockBandStep_frozen_of_apply_ne_zero hn aLoΛ hiΛ D H
          a ha z haz)
      T q z hqlive hz
  exact hzlive hznot

/-- At a positive-mass live time-`T` endpoint, all `T` raw interactions were
live and hence the two occupation counters sum to their initial sum plus
`T`. -/
theorem singleClockBand_iter_tick_sum_of_final_live
    {n : ℕ} (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ) :
    ∀ T (q z : SingleClockTrace n),
      iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q z ≠ 0 →
      ¬ SingleBandFrozen n aLoΛ hiΛ D H z.core →
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
          ∃ a, singleClockBandStep n hn aLoΛ hiΛ D H q a *
              iter (singleClockBandStep n hn aLoΛ hiΛ D H) T a z ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        rw [ENNReal.tsum_eq_zero]
        exact h
      obtain ⟨a, ha⟩ := hex
      have hqa : singleClockBandStep n hn aLoΛ hiΛ D H q a ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have haz :
          iter (singleClockBandStep n hn aLoΛ hiΛ D H) T a z ≠ 0 := by
        intro h
        apply ha
        simp [h]
      have halive : ¬ SingleBandFrozen n aLoΛ hiΛ D H a.core :=
        singleClockBand_iter_start_live_of_final hn aLoΛ hiΛ D H
          a z haz hzlive
      have hstep :=
        singleClockBandStep_tick_sum_of_live_target hn aLoΛ hiΛ D H
          q a halive hqa
      have hrest := ih a z haz hzlive
      omega

section Inhabitation

example :
    let q : SingleClockTrace 4 :=
      { core := ⟨⟨⟨2, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩
        normalTicks := 0
        blankTicks := 0
        normalFuel := 0 }
    q.FuelClockInv 1 1 := by
  intro q
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [q, SingleLedger.BlankLedger, SingleLedger.CorrectedY]

example :
    ¬ (⟨⟨⟨3, 0, 1⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
        SingleLedger 4).NormalTick := by
  norm_num [SingleLedger.NormalTick]

example :
    (⟨⟨⟨1, 2, 1⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
        SingleLedger 4).NormalTick := by
  norm_num [SingleLedger.NormalTick]

end Inhabitation

end Tri

#print axioms Tri.singleClockBandStep_map_core
#print axioms Tri.SingleComp.nextSingleClockTrace_tick_sum
#print axioms Tri.SingleComp.nextSingleClockTrace_normalFuel_le
#print axioms Tri.singleClockBandStep_fuelClockInv_of_apply_ne_zero
#print axioms Tri.singleClockBand_iter_fuelClockInv
#print axioms Tri.singleClockBandStep_cx_mono_of_apply_ne_zero
#print axioms Tri.singleClockBand_iter_tick_sum_of_final_live

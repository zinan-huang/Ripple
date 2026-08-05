/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBMass
import Tri.DoubleBTrace

/-!
# Counted Single-B trace and exact blank ledger

Each fair `X+Y` creation event increases both the productive counter and the
blank count.  Each `X+B` or `Y+B` resolution event increases both the
productive and resolution counters and removes one blank.  Consequently every
supported path satisfies the exact identity

`productive + initialBlank = currentBlank + 2 * resolve`.
-/

namespace Tri

open scoped ENNReal

/-- Single-B state augmented with productive and resolution counters. -/
structure SingleTrace (n : ℕ) where
  cfg : SingleState n
  productive : ℕ
  resolve : ℕ

/-- Productive events are the two fair creations and the two resolutions. -/
def SingleComp.productiveInc : SingleComp → ℕ
  | .xyToX | .xyToY | .xb | .yb => 1
  | _ => 0

/-- Resolution events consume one blank. -/
def SingleComp.resolveInc : SingleComp → ℕ
  | .xb | .yb => 1
  | _ => 0

/-- Guarded counted update; zero-weight labels leave the trace fixed. -/
noncomputable def SingleComp.nextSingleTrace
    {n : ℕ} (q : SingleTrace n) (k : SingleComp) : SingleTrace n :=
  if hk :
      SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0 then
    q
  else
    { cfg :=
        ⟨SingleComp.next q.cfg.1 k,
          SingleComp.next_doubleInv n q.cfg.1 k q.cfg.2 hk⟩
      productive := q.productive + k.productiveInc
      resolve := q.resolve + k.resolveInc }

/-- One counted Single-B interaction. -/
noncomputable def singleTraceStep
    (n : ℕ) (hn : 2 ≤ n) (q : SingleTrace n) : PMF (SingleTrace n) :=
  (singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega)).map (SingleComp.nextSingleTrace q)

/-- Forgetting the counters recovers the invariant Single-B state step. -/
theorem singleTraceStep_map_cfg
    (n : ℕ) (hn : 2 ≤ n) (q : SingleTrace n) :
    (singleTraceStep n hn q).map SingleTrace.cfg =
      singleStateStep n hn q.cfg := by
  unfold singleTraceStep singleStateStep
  rw [PMF.map_comp]
  apply PMF.map_change_on_zero_mass
  intro k hkdiff
  unfold Function.comp SingleComp.nextSingleTrace
    SingleComp.nextSingleState at hkdiff
  split_ifs at hkdiff with hk
  · exact singleCompPMF_zero_of_weight_zero hk
  · exact absurd rfl hkdiff

/-- Exact pathwise balance between blank creation and resolution. -/
def SingleTrace.BlankLedger
    {n : ℕ} (initialBlank : ℕ) (q : SingleTrace n) : Prop :=
  q.productive + initialBlank = q.cfg.1.b + 2 * q.resolve

/-- The exact blank ledger holds at the initial counted state. -/
theorem SingleTrace.initial_blankLedger
    {n : ℕ} (s : SingleState n) :
    SingleTrace.BlankLedger s.1.b ⟨s, 0, 0⟩ := by
  simp [SingleTrace.BlankLedger]

/-- Every positive-weight event preserves the exact blank ledger. -/
theorem SingleComp.nextSingleTrace_blankLedger
    {n initialBlank : ℕ} (q : SingleTrace n) (k : SingleComp)
    (hq : q.BlankLedger initialBlank)
    (hk : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (SingleComp.nextSingleTrace q k).BlankLedger initialBlank := by
  rcases q with ⟨⟨⟨x, y, b⟩, hinv⟩, productive, resolve⟩
  simp only [SingleTrace.BlankLedger] at hq
  simp only [SingleComp.nextSingleTrace]
  rw [dif_neg hk]
  simp only [SingleTrace.BlankLedger]
  cases k <;>
    simp only [SingleComp.productiveInc, SingleComp.resolveInc,
      SingleComp.next, SingleComp.weight] at hk ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hk; omega)

/-- One counted step preserves the blank ledger on its support. -/
theorem singleTraceStep_blankLedger_of_apply_ne_zero
    {n initialBlank : ℕ} (hn : 2 ≤ n) (q : SingleTrace n)
    (hq : q.BlankLedger initialBlank) (z : SingleTrace n)
    (hqz : singleTraceStep n hn q z ≠ 0) :
    z.BlankLedger initialBlank := by
  unfold singleTraceStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · have hw :
        SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0 :=
      fun hw => hk (singleCompPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact SingleComp.nextSingleTrace_blankLedger q k hq hw
  · exact absurd rfl hk

/-- The exact blank ledger holds along every finite counted trajectory. -/
theorem singleTrace_iter_blankLedger
    {n initialBlank T : ℕ} (hn : 2 ≤ n) (q z : SingleTrace n)
    (hq : q.BlankLedger initialBlank)
    (hz : iter (singleTraceStep n hn) T q z ≠ 0) :
    z.BlankLedger initialBlank :=
  iter_support_closed
    (singleTraceStep n hn) (SingleTrace.BlankLedger initialBlank)
    (fun a ha z haz =>
      singleTraceStep_blankLedger_of_apply_ne_zero hn a ha z haz)
    T q z hq hz

/-- Enough productive events force a corresponding number of resolutions. -/
theorem single_resolve_of_productive
    {n initialBlank M : ℕ} (q : SingleTrace n)
    (hq : q.BlankLedger initialBlank)
    (hprod : n + 2 * M ≤ q.productive + initialBlank) :
    M ≤ q.resolve := by
  have hb : q.cfg.1.b ≤ n := by
    have hinv := q.cfg.2
    simp only [BiCfg.DoubleInv] at hinv
    omega
  unfold SingleTrace.BlankLedger at hq
  omega

end Tri

#print axioms Tri.singleTraceStep_map_cfg
#print axioms Tri.SingleComp.nextSingleTrace_blankLedger
#print axioms Tri.singleTrace_iter_blankLedger
#print axioms Tri.single_resolve_of_productive

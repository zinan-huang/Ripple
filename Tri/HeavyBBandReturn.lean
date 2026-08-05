/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBFeller
import Tri.HeavyBTrace
import Tri.BandRung

/-!
# Returning from an upper Heavy-B band boundary

The band estimates in `HeavyBBand.lean` bound backslide and deadline masses
on the Heavy-B TRACE frozen at band boundaries. To get a `Reaches` on
`heavyStateStep n`, we need to account for returns from the upper boundary.

This file supplies the return comparison, mirroring `DoubleBBandReturn.lean`
but on `HeavyState n` with `heavyLevel` (range [0,n], population constraint
`aLo + bHi + 2 = n`).
-/

namespace Tri

open scoped ENNReal

/-- Starting at least `k` levels above `returnLo`, the Heavy-B state chain
ever returns to `returnLo` or below with probability at most `(bHi/returnLo)^k`. -/
theorem heavyState_upper_return
    {n : ℕ} (returnLo bHi k : ℕ) (hn : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (s : HeavyState n)
    (hs : returnLo + k ≤ BiCfg.heavyLevel s.1) :
    ⨆ T : ℕ, hitProb
        (fun z : HeavyState n => BiCfg.heavyLevel z.1 ≤ returnLo)
        (heavyStateStep n) T s
      ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  obtain ⟨d, hd⟩ : ∃ d, BiCfg.heavyLevel s.1 = returnLo + d :=
    ⟨BiCfg.heavyLevel s.1 - returnLo, by omega⟩
  have hkd : k ≤ d := by omega
  have hne : (returnLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have htop : (returnLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top returnLo
  have hbase : (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞) ≤ 1 := by
    calc (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)
        ≤ (returnLo : ℝ≥0∞) / (returnLo : ℝ≥0∞) :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
      _ = 1 := ENNReal.div_self hne htop
  calc (⨆ T : ℕ, hitProb
        (fun z : HeavyState n => BiCfg.heavyLevel z.1 ≤ returnLo)
        (heavyStateStep n) T s)
      ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ d :=
        heavyB_ruin returnLo bHi d hn hpop hreturnLo hbHi hmaj s hd
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
        pow_le_pow_right_of_le_one' hbase hkd

/-- If failure of `A` implies level at most `returnLo`, then terminal failure
from a state `k` levels above `returnLo` is bounded by the Feller return. -/
theorem heavyState_upper_target_failure
    {n : ℕ} (returnLo bHi k T : ℕ) (hn : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (s : HeavyState n)
    (hs : returnLo + k ≤ BiCfg.heavyLevel s.1)
    (A : HeavyState n → Prop) [DecidablePred A]
    (hfailure : ∀ z, ¬ A z → BiCfg.heavyLevel z.1 ≤ returnLo) :
    (∑' z, if A z then 0 else iter (heavyStateStep n) T s z)
      ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  calc
    (∑' z, if A z then 0 else iter (heavyStateStep n) T s z) ≤
        ∑' z, if returnLo < BiCfg.heavyLevel z.1 then 0
          else iter (heavyStateStep n) T s z := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : A z
      · simp [hz]
      · have hzLo := hfailure z hz
        simp [hz, Nat.not_lt.mpr hzLo]
    _ ≤ ∑' z, if returnLo < BiCfg.heavyLevel z.1 then 0 else
          iter (freeze
            (fun y : HeavyState n => BiCfg.heavyLevel y.1 ≤ returnLo)
            (heavyStateStep n)) T s z :=
      failure_le_failure_freeze
        (B := fun y : HeavyState n => BiCfg.heavyLevel y.1 ≤ returnLo)
        (A := fun y : HeavyState n => returnLo < BiCfg.heavyLevel y.1)
        (by omega) T s
    _ = hitProb
          (fun y : HeavyState n => BiCfg.heavyLevel y.1 ≤ returnLo)
          (heavyStateStep n) T s := by
      unfold hitProb expect ind
      apply tsum_congr
      intro z
      by_cases hz : BiCfg.heavyLevel z.1 ≤ returnLo
      · simp [hz, Nat.not_lt.mpr hz]
      · simp [hz, Nat.lt_of_not_ge hz]
    _ ≤ ⨆ t : ℕ, hitProb
          (fun y : HeavyState n => BiCfg.heavyLevel y.1 ≤ returnLo)
          (heavyStateStep n) t s :=
      le_iSup (fun t : ℕ => hitProb
        (fun y : HeavyState n => BiCfg.heavyLevel y.1 ≤ returnLo)
        (heavyStateStep n) t s) T
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      heavyState_upper_return returnLo bHi k hn hpop
        hreturnLo hbHi hmaj s hs

/-- The Heavy-B state chain stopped outside the open level band. -/
noncomputable def heavyStateBandStop (n aLo hi : ℕ) :
    HeavyState n → PMF (HeavyState n) :=
  freeze (fun s : HeavyState n =>
    BiCfg.heavyLevel s.1 ≤ aLo ∨ hi ≤ BiCfg.heavyLevel s.1) (heavyStateStep n)

/-- Transfer a stopped Heavy-B band estimate back to the original state chain.
An upper-boundary success that later fails `A` is charged to one explicit
Feller return term. -/
theorem heavyState_band_transfer_upper
    {n : ℕ} (aLo hi returnLo bHi k T : ℕ) (hn : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (hgap : returnLo + k ≤ hi)
    (s₀ : HeavyState n)
    (A : HeavyState n → Prop) [DecidablePred A]
    (hlower : ∀ s, A s → aLo < BiCfg.heavyLevel s.1)
    (hfailure : ∀ s, ¬ A s → BiCfg.heavyLevel s.1 ≤ returnLo) :
    (∑' s, if A s then 0 else iter (heavyStateStep n) T s₀ s)
      ≤ (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T s₀ s)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  let B : HeavyState n → Prop := fun s =>
    BiCfg.heavyLevel s.1 ≤ aLo ∨ hi ≤ BiCfg.heavyLevel s.1
  have hcompare :
      (∑' s, if A s then 0 else iter (heavyStateStep n) T s₀ s)
        ≤ (∑' s, if A s then 0 else
            iter (freeze B (heavyStateStep n)) T s₀ s)
          + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
    apply failure_le_failure_freeze_add
    intro s hsB hsA U
    rcases hsB with hsLo | hsHi
    · exact False.elim ((Nat.not_lt_of_ge hsLo) (hlower s hsA))
    · exact heavyState_upper_target_failure returnLo bHi k U hn
        hpop hreturnLo hbHi hmaj s (hgap.trans hsHi) A hfailure
  simpa only [heavyStateBandStop, B] using hcompare

/-! ### Stopped trace band and projection -/

/-- The Heavy-B trace frozen at band boundaries: run the trace while
`aLo < level < hi`, freeze outside. -/
noncomputable def heavyBandStop (n aLo hi : ℕ) :
    HeavyTrace n → PMF (HeavyTrace n) := fun q =>
  if aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
      BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
    heavyTraceStep n q else PMF.pure q

theorem heavyBandStop_eq_freeze {n : ℕ} (aLo hi : ℕ) :
    heavyBandStop n aLo hi
      = freeze (fun q : HeavyTrace n =>
          BiCfg.heavyLevel q.cfg.1 ≤ aLo ∨
            hi ≤ BiCfg.heavyLevel q.cfg.1) (heavyTraceStep n) := by
  funext q
  unfold heavyBandStop freeze
  by_cases h : BiCfg.heavyLevel q.cfg.1 ≤ aLo ∨
      hi ≤ BiCfg.heavyLevel q.cfg.1
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]

/-- Forgetting the counters in one stopped band step gives the stopped
`HeavyState` step. -/
theorem heavyBandStop_map_cfg {n : ℕ} (hn : 3 ≤ n) (aLo hi : ℕ)
    (q : HeavyTrace n) :
    (heavyBandStop n aLo hi q).map HeavyTrace.cfg =
      heavyStateBandStop n aLo hi q.cfg := by
  unfold heavyBandStop heavyStateBandStop freeze
  by_cases hbad :
      BiCfg.heavyLevel q.cfg.1 ≤ aLo ∨ hi ≤ BiCfg.heavyLevel q.cfg.1
  · rw [if_neg (by omega), if_pos hbad]
    exact PMF.pure_map HeavyTrace.cfg q
  · rw [if_pos (by omega), if_neg hbad]
    exact heavyTraceStep_map_cfg hn q

/-- The stopped state-chain iterate is the counter-forgetting pushforward of
the stopped trace iterate. -/
theorem iter_heavyStateBandStop_eq_map {n : ℕ} (hn : 3 ≤ n) (aLo hi : ℕ) :
    ∀ (T : ℕ) (q : HeavyTrace n),
    iter (heavyStateBandStop n aLo hi) T q.cfg =
      (iter (heavyBandStop n aLo hi) T q).map HeavyTrace.cfg := by
  intro T
  induction T with
  | zero => intro q; rw [iter_zero, iter_zero, PMF.pure_map]
  | succ T ih =>
    intro q
    rw [iter_succ, iter_succ, ← heavyBandStop_map_cfg hn aLo hi q,
      PMF.map_bind]
    rw [show (PMF.map HeavyTrace.cfg (heavyBandStop n aLo hi q)).bind
          (iter (heavyStateBandStop n aLo hi) T)
        = (heavyBandStop n aLo hi q).bind
          (fun a => iter (heavyStateBandStop n aLo hi) T (HeavyTrace.cfg a)) by
      simp only [PMF.map, PMF.bind_bind, Function.comp, PMF.pure_bind]]
    congr 1
    funext a
    exact ih a

/-- Failure mass for a configuration predicate is unchanged by forgetting the
counters of the stopped band trace. -/
theorem heavyStateBand_failure_eq_trace {n : ℕ} (hn : 3 ≤ n)
    (aLo hi T : ℕ) (q₀ : HeavyTrace n)
    (A : HeavyState n → Prop) [DecidablePred A] :
    (∑' s, if A s then 0 else
        iter (heavyStateBandStop n aLo hi) T q₀.cfg s) =
      ∑' q, if A q.cfg then 0 else
        iter (heavyBandStop n aLo hi) T q₀ q := by
  rw [iter_heavyStateBandStop_eq_map hn aLo hi T q₀]
  set p := iter (heavyBandStop n aLo hi) T q₀
  let V : HeavyState n → ℝ≥0∞ := fun s => if A s then 0 else 1
  calc
    (∑' s, if A s then 0 else (p.map HeavyTrace.cfg) s) =
        expect (p.map HeavyTrace.cfg) V := by
      unfold expect V
      apply tsum_congr
      intro s
      by_cases hs : A s <;> simp [hs]
    _ = expect p (fun q => V q.cfg) := by rw [expect_map]
    _ = ∑' q, if A q.cfg then 0 else p q := by
      unfold expect V
      apply tsum_congr
      intro q
      by_cases hq : A q.cfg <;> simp [hq]

/-- Trace-form upper transfer: the original chain's failure mass is bounded by
the stopped trace's failure mass plus the Feller return term. -/
theorem heavyBand_transfer_upper {n : ℕ}
    (aLo hi returnLo bHi k T : ℕ) (hn : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (hgap : returnLo + k ≤ hi)
    (q₀ : HeavyTrace n)
    (A : HeavyState n → Prop) [DecidablePred A]
    (hlower : ∀ s, A s → aLo < BiCfg.heavyLevel s.1)
    (hfailure : ∀ s, ¬ A s → BiCfg.heavyLevel s.1 ≤ returnLo) :
    (∑' s, if A s then 0 else
        iter (heavyStateStep n) T q₀.cfg s)
      ≤ (∑' q, if A q.cfg then 0 else
          iter (heavyBandStop n aLo hi) T q₀ q)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  calc
    (∑' s, if A s then 0 else
        iter (heavyStateStep n) T q₀.cfg s)
      ≤ (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      heavyState_band_transfer_upper aLo hi returnLo bHi k T hn
        hpop hreturnLo hbHi hmaj hgap q₀.cfg A hlower hfailure
    _ = (∑' q, if A q.cfg then 0 else
          iter (heavyBandStop n aLo hi) T q₀ q)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
      rw [heavyStateBand_failure_eq_trace hn aLo hi T q₀ A]

end Tri

#print axioms Tri.heavyState_upper_return
#print axioms Tri.heavyState_upper_target_failure
#print axioms Tri.heavyState_band_transfer_upper
#print axioms Tri.heavyBandStop_eq_freeze
#print axioms Tri.heavyBandStop_map_cfg
#print axioms Tri.iter_heavyStateBandStop_eq_map
#print axioms Tri.heavyStateBand_failure_eq_trace
#print axioms Tri.heavyBand_transfer_upper

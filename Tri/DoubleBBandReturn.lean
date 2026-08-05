/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBAssembly
import Tri.BandReturn

/-!
# Returning from an upper Double-B band boundary

The band estimates in `Tri.DoubleBAssembly` use a chain frozen at both level
boundaries.  Freezing at the upper boundary records a hitting event, not an
exact-time statement for the original chain: after first reaching the upper
boundary, the original chain may move down again.

This file supplies the missing return comparison.  It mirrors
`Tri.BandReturn`, using `doubleB_ruin` on the invariant subtype and the
projection from the counted band trace to the stopped `DoubleState` chain.
-/

namespace Tri

open scoped ENNReal

/-- The Double-B state chain stopped outside the open level band. -/
noncomputable def doubleStateBandStop (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ) :
    DoubleState n → PMF (DoubleState n) :=
  freeze (fun s : DoubleState n =>
    s.1.doubleLevel ≤ aLo ∨ hi ≤ s.1.doubleLevel) (doubleStateStep n hn)

/-- Starting at least `k` levels above `returnLo`, the Double-B state chain
ever returns to `returnLo` or below with probability at most the Feller ratio
to the power `k`. -/
theorem doubleState_upper_return
    (n returnLo bHi k : ℕ) (hn : 2 ≤ n)
    (hpop2n : returnLo + bHi + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (s : DoubleState n)
    (hs : returnLo + k ≤ s.1.doubleLevel) :
    ⨆ T : ℕ, hitProb
        (fun z : DoubleState n => z.1.doubleLevel ≤ returnLo)
        (doubleStateStep n hn) T s
      ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  obtain ⟨d, hd⟩ : ∃ d, s.1.doubleLevel = returnLo + d :=
    ⟨s.1.doubleLevel - returnLo, by omega⟩
  have hkd : k ≤ d := by omega
  have hne : (returnLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have htop : (returnLo : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top returnLo
  have hbase : (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞) ≤ 1 := by
    calc
      (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞) ≤
          (returnLo : ℝ≥0∞) / (returnLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
      _ = 1 := ENNReal.div_self hne htop
  calc
    (⨆ T : ℕ, hitProb
        (fun z : DoubleState n => z.1.doubleLevel ≤ returnLo)
        (doubleStateStep n hn) T s)
        ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ d :=
      doubleB_ruin n returnLo bHi d hn hpop2n hreturnLo hbHi hmaj s hd
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      pow_le_pow_right_of_le_one' hbase hkd

/-- If failure of `A` implies level at most `returnLo`, then terminal failure
from a state `k` levels above `returnLo` is covered by the unbounded return
event. -/
theorem doubleState_upper_target_failure
    (n returnLo bHi k T : ℕ) (hn : 2 ≤ n)
    (hpop2n : returnLo + bHi + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (s : DoubleState n)
    (hs : returnLo + k ≤ s.1.doubleLevel)
    (A : DoubleState n → Prop) [DecidablePred A]
    (hfailure : ∀ z, ¬ A z → z.1.doubleLevel ≤ returnLo) :
    (∑' z, if A z then 0 else iter (doubleStateStep n hn) T s z)
      ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  calc
    (∑' z, if A z then 0 else iter (doubleStateStep n hn) T s z) ≤
        ∑' z, if returnLo < z.1.doubleLevel then 0
          else iter (doubleStateStep n hn) T s z := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : A z
      · simp [hz]
      · have hzLo := hfailure z hz
        simp [hz, Nat.not_lt.mpr hzLo]
    _ ≤ ∑' z, if returnLo < z.1.doubleLevel then 0 else
          iter (freeze
            (fun y : DoubleState n => y.1.doubleLevel ≤ returnLo)
            (doubleStateStep n hn)) T s z := by
      exact failure_le_failure_freeze
        (B := fun y : DoubleState n => y.1.doubleLevel ≤ returnLo)
        (A := fun y : DoubleState n => returnLo < y.1.doubleLevel)
        (by omega) T s
    _ = hitProb
          (fun y : DoubleState n => y.1.doubleLevel ≤ returnLo)
          (doubleStateStep n hn) T s := by
      unfold hitProb expect ind
      apply tsum_congr
      intro z
      by_cases hz : z.1.doubleLevel ≤ returnLo
      · simp [hz, Nat.not_lt.mpr hz]
      · simp [hz, Nat.lt_of_not_ge hz]
    _ ≤ ⨆ t : ℕ, hitProb
          (fun y : DoubleState n => y.1.doubleLevel ≤ returnLo)
          (doubleStateStep n hn) t s :=
      le_iSup (fun t : ℕ => hitProb
        (fun y : DoubleState n => y.1.doubleLevel ≤ returnLo)
        (doubleStateStep n hn) t s) T
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      doubleState_upper_return n returnLo bHi k hn hpop2n
        hreturnLo hbHi hmaj s hs

/-- Forgetting the counters in one stopped band step gives the stopped
`DoubleState` step. -/
theorem doubleBandStop_map_cfg
    (n : ℕ) (hn : 2 ≤ n) (aLo hi : ℕ) (q : DoubleTrace n) :
    (doubleBandStop n hn aLo hi q).map DoubleTrace.cfg =
      doubleStateBandStop n hn aLo hi q.cfg := by
  unfold doubleBandStop doubleStateBandStop freeze
  by_cases hbad :
      q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel
  · rw [if_neg (by omega), if_pos hbad]
    exact PMF.pure_map DoubleTrace.cfg q
  · rw [if_pos (by omega), if_neg hbad]
    exact doubleTraceStep_map_cfg n hn q

/-- The stopped state-chain iterate is the counter-forgetting pushforward of
the stopped trace iterate. -/
theorem iter_doubleStateBandStop_eq_map
    (n : ℕ) (hn : 2 ≤ n) (aLo hi T : ℕ) (q : DoubleTrace n) :
    iter (doubleStateBandStop n hn aLo hi) T q.cfg =
      (iter (doubleBandStop n hn aLo hi) T q).map DoubleTrace.cfg :=
  iter_map_equivariant
    (doubleBandStop n hn aLo hi) (doubleStateBandStop n hn aLo hi)
    DoubleTrace.cfg (doubleBandStop_map_cfg n hn aLo hi) T q

/-- Failure mass for a configuration predicate is unchanged by forgetting the
two counters of the stopped band trace. -/
theorem doubleStateBand_failure_eq_trace
    (n : ℕ) (hn : 2 ≤ n) (aLo hi T : ℕ) (q₀ : DoubleTrace n)
    (A : DoubleState n → Prop) [DecidablePred A] :
    (∑' s, if A s then 0 else
        iter (doubleStateBandStop n hn aLo hi) T q₀.cfg s) =
      ∑' q, if A q.cfg then 0 else
        iter (doubleBandStop n hn aLo hi) T q₀ q := by
  rw [iter_doubleStateBandStop_eq_map n hn aLo hi T q₀]
  set p := iter (doubleBandStop n hn aLo hi) T q₀
  let V : DoubleState n → ℝ≥0∞ := fun s => if A s then 0 else 1
  calc
    (∑' s, if A s then 0 else (p.map DoubleTrace.cfg) s) =
        expect (p.map DoubleTrace.cfg) V := by
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

/-- Transfer a stopped Double-B band estimate back to the original state
chain.  An upper-boundary success that later fails `A` is charged to one
explicit Feller return term. -/
theorem doubleState_band_transfer_upper
    (n aLo hi returnLo bHi k T : ℕ) (hn : 2 ≤ n)
    (hpop2n : returnLo + bHi + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (hgap : returnLo + k ≤ hi)
    (s₀ : DoubleState n)
    (A : DoubleState n → Prop) [DecidablePred A]
    (hlower : ∀ s, A s → aLo < s.1.doubleLevel)
    (hfailure : ∀ s, ¬ A s → s.1.doubleLevel ≤ returnLo) :
    (∑' s, if A s then 0 else iter (doubleStateStep n hn) T s₀ s)
      ≤ (∑' s, if A s then 0 else
          iter (doubleStateBandStop n hn aLo hi) T s₀ s)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  let B : DoubleState n → Prop := fun s =>
    s.1.doubleLevel ≤ aLo ∨ hi ≤ s.1.doubleLevel
  have hcompare :
      (∑' s, if A s then 0 else iter (doubleStateStep n hn) T s₀ s)
        ≤ (∑' s, if A s then 0 else
            iter (freeze B (doubleStateStep n hn)) T s₀ s)
          + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
    apply failure_le_failure_freeze_add
    intro s hsB hsA U
    rcases hsB with hsLo | hsHi
    · exact False.elim ((Nat.not_lt_of_ge hsLo) (hlower s hsA))
    · exact doubleState_upper_target_failure n returnLo bHi k U hn
        hpop2n hreturnLo hbHi hmaj s (hgap.trans hsHi) A hfailure
  simpa only [doubleStateBandStop, B] using hcompare

/-- Trace-form upper transfer, ready to consume `band_phase_fail_full`. -/
theorem doubleBand_transfer_upper
    (n aLo hi returnLo bHi k T : ℕ) (hn : 2 ≤ n)
    (hpop2n : returnLo + bHi + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (hgap : returnLo + k ≤ hi)
    (q₀ : DoubleTrace n)
    (A : DoubleState n → Prop) [DecidablePred A]
    (hlower : ∀ s, A s → aLo < s.1.doubleLevel)
    (hfailure : ∀ s, ¬ A s → s.1.doubleLevel ≤ returnLo) :
    (∑' s, if A s then 0 else
        iter (doubleStateStep n hn) T q₀.cfg s)
      ≤ (∑' q, if A q.cfg then 0 else
          iter (doubleBandStop n hn aLo hi) T q₀ q)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  calc
    (∑' s, if A s then 0 else
        iter (doubleStateStep n hn) T q₀.cfg s)
      ≤ (∑' s, if A s then 0 else
          iter (doubleStateBandStop n hn aLo hi) T q₀.cfg s)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      doubleState_band_transfer_upper n aLo hi returnLo bHi k T hn
        hpop2n hreturnLo hbHi hmaj hgap q₀.cfg A hlower hfailure
    _ = (∑' q, if A q.cfg then 0 else
          iter (doubleBandStop n hn aLo hi) T q₀ q)
        + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
      rw [doubleStateBand_failure_eq_trace n hn aLo hi T q₀ A]

/-- A complete stopped-band phase bound transferred to an exact-time
checkpoint of the original `DoubleState` chain.  The stopped upper boundary
`hi` may sit above the public checkpoint `returnLo + 1`; the gap pays the
explicit return term. -/
theorem doubleState_band_phase_fail_full
    (n : ℕ) (hn : 2 ≤ n)
    (aLo bHiR bHiD hi k M T : ℕ)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n) (hmajD : bHiD ≤ aLo)
    (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (wp pp pp' : ℝ≥0∞)
    (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .yb))
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
        else iter (doubleStateStep n hn) T s₀ s)
      ≤ (((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M)
          + (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M))
        + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet := by
  let A : DoubleState n → Prop :=
    fun s => returnLo + 1 ≤ s.1.doubleLevel
  let q₀ : DoubleTrace n := ⟨s₀, 0, 0⟩
  have htransfer :
      (∑' s, if A s then 0 else iter (doubleStateStep n hn) T s₀ s)
        ≤ (∑' q, if A q.cfg then 0 else
            iter (doubleBandStop n hn aLo hi) T q₀ q)
          + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet := by
    exact doubleBand_transfer_upper n aLo hi returnLo bHiRet kRet T hn
      hpopRet hreturnLo hbHiRet hmajRet hreturnGap q₀ A
      (by
        intro s hs
        change returnLo + 1 ≤ s.1.doubleLevel at hs
        omega)
      (by
        intro s hs
        change ¬ returnLo + 1 ≤ s.1.doubleLevel at hs
        omega)
  have hphase :
      (∑' q, if q.cfg.1.doubleLevel + 1 ≤ hi then
          iter (doubleBandStop n hn aLo hi) T q₀ q else 0)
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M)
          + (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M) := by
    simpa only [q₀] using
      (band_phase_fail_full n hn aLo bHiR bHiD hi k M T
        haLohi hpopR haLo hbHiR hmajR heqD hmajD hhi
        w η u hu hrel hwη hw1 hw0 hη1 hηt
        wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't hBprod s₀ hstart)
  have hstopped :
      (∑' q, if A q.cfg then 0 else
          iter (doubleBandStop n hn aLo hi) T q₀ q)
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ s₀.1.doubleLevel / (w ^ (hi - 1) * η ^ M)
          + (pp' + pp * wp) ^ T * 1 / wp ^ (s₀.1.y + 3 * M) := by
    refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) hphase
    by_cases hA : A q.cfg
    · simp [hA]
    · have hqLo : q.cfg.1.doubleLevel ≤ returnLo := by
        change ¬ returnLo + 1 ≤ q.cfg.1.doubleLevel at hA
        omega
      have hqHi : q.cfg.1.doubleLevel + 1 ≤ hi := by omega
      simp [hA, hqHi]
  change (∑' s, if A s then 0 else
      iter (doubleStateStep n hn) T s₀ s) ≤ _
  exact htransfer.trans (add_le_add hstopped le_rfl)

/-- Predicate form of `doubleState_band_phase_fail_full`, suitable for
`Reaches.comp` once a ladder instantiates the arithmetic parameters. -/
theorem doubleState_band_phase_reaches
    (n : ℕ) (hn : 2 ≤ n)
    (aLo bHiR bHiD hi k M T : ℕ)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n) (hmajD : bHiD ≤ aLo)
    (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (wp pp pp' : ℝ≥0∞)
    (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .yb))
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (doubleStateStep n hn) T
      (fun s => s.1.doubleLevel = aLo + k)
      (fun s => returnLo + 1 ≤ s.1.doubleLevel)
      ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M)
          + (pp' + pp * wp) ^ T * 1 /
            wp ^ ((2 * n - (aLo + k)) + 3 * M))
        + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet) := by
  intro s hs
  have hy : s.1.y ≤ 2 * n - (aLo + k) := by
    have hsum := doubleLevel_add_doubleCoLevel s
    have hyle : s.1.y ≤ s.1.doubleCoLevel := by
      simp only [BiCfg.doubleCoLevel]
      omega
    omega
  have hraw := doubleState_band_phase_fail_full n hn
    aLo bHiR bHiD hi k M T haLohi hpopR haLo hbHiR hmajR
    heqD hmajD hhi w η u hu hrel hwη hw1 hw0 hη1 hηt
    wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't hBprod
    returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
    hlowerTarget htargetHi hreturnGap s hs
  have hpow :
      wp ^ ((2 * n - (aLo + k)) + 3 * M) ≤ wp ^ (s.1.y + 3 * M) :=
    pow_le_pow_right_of_le_one' hwp1 (by omega)
  have hprod :
      (pp' + pp * wp) ^ T * 1 / wp ^ (s.1.y + 3 * M)
        ≤ (pp' + pp * wp) ^ T * 1 /
          wp ^ ((2 * n - (aLo + k)) + 3 * M) := by
    exact ENNReal.div_le_div_left hpow _
  rw [hs] at hraw
  exact hraw.trans (add_le_add (add_le_add le_rfl hprod) le_rfl)

/-- Monotone-start form of one phase.  A state may begin above the nominal
level `aLo + k`; all three band terms are then bounded by their values at that
nominal level.  This is the form consumed by a ladder checkpoint
`aLo + k ≤ level`. -/
theorem doubleState_band_phase_reaches_mono
    (n : ℕ) (hn : 2 ≤ n)
    (aLo bHiR bHiD hi k M T : ℕ)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n) (hmajD : bHiD ≤ aLo)
    (hhi : hi ≤ 2 * n)
    (w η u : ℝ≥0∞)
    (hu : u = (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1))
    (hwη : w ≤ η) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (wp pp pp' : ℝ≥0∞)
    (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hppp : pp + pp' = 1)
    (hwpt : wp ≠ ⊤) (hppT : pp ≠ ⊤) (hpp't : pp' ≠ ⊤)
    (hBprod : ∀ q : DoubleTrace n,
      ¬ (q.cfg.1.doubleLevel ≤ aLo ∨ hi ≤ q.cfg.1.doubleLevel) →
      pp ≤ (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
          have := q.cfg.2
          simp only [BiCfg.DoubleInv] at this
          omega) .yb))
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
      ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M)
          + (pp' + pp * wp) ^ T * 1 /
            wp ^ ((2 * n - (aLo + k)) + 3 * M))
        + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet) := by
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
  have hraw := doubleState_band_phase_reaches n hn
    aLo bHiR bHiD hi d M T haLohi hpopR haLo hbHiR hmajR
    heqD hmajD hhi w η u hu hrel hwη hw1 hw0 hη1 hηt
    wp pp pp' hwp1 hwp0 hppp hwpt hppT hpp't hBprod
    returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
    hlowerTarget htargetHi hreturnGap s hd
  have hruin :
      ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ d
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
    pow_le_pow_right_of_le_one' hbaseR hkd
  have hdir :
      w ^ (aLo + d) / (w ^ (hi - 1) * η ^ M)
        ≤ w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M) := by
    exact ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hw1 (by omega)) _
  have hcap : 2 * n - (aLo + d) ≤ 2 * n - (aLo + k) := by omega
  have hpow :
      wp ^ ((2 * n - (aLo + k)) + 3 * M)
        ≤ wp ^ ((2 * n - (aLo + d)) + 3 * M) :=
    pow_le_pow_right_of_le_one' hwp1 (by omega)
  have hprod :
      (pp' + pp * wp) ^ T * 1 /
          wp ^ ((2 * n - (aLo + d)) + 3 * M)
        ≤ (pp' + pp * wp) ^ T * 1 /
          wp ^ ((2 * n - (aLo + k)) + 3 * M) :=
    ENNReal.div_le_div_left hpow _
  exact hraw.trans
    (add_le_add (add_le_add (add_le_add hruin hdir) hprod) le_rfl)

end Tri

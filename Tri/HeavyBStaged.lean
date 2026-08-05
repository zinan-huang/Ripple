/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBProductiveTail
import Tri.HeavyBWindowTail
import Tri.HeavyBRung

/-!
# Heavy-B staged band phase

This file combines the stopped-window direction tail with the raw productive
clock tail.  The only counter bridge is the exact Heavy-B `Y` ledger:
`y + fuel = y0 + 2 * down`.
-/

namespace Tri

open scoped ENNReal

/-- The `Y` ledger is preserved by the stopped Heavy-B band kernel. -/
theorem heavyBandStop_iter_yLedger {n y₀ T aLo hi : ℕ}
    (q z : HeavyTrace n) (hq : q.YLedger y₀)
    (hz : iter (heavyBandStop n aLo hi) T q z ≠ 0) :
    z.YLedger y₀ := by
  refine iter_support_closed (heavyBandStop n aLo hi)
    (HeavyTrace.YLedger y₀) (fun a ha z haz => ?_) T q z hq hz
  unfold heavyBandStop at haz
  split_ifs at haz with hlive
  · exact heavyTraceStep_ledger_of_apply_ne_zero _
      (fun q k hq hk => PairComp.nextHeavyTrace_yLedger q k hq hk)
      a ha z haz
  · rw [PMF.pure_apply] at haz
    by_cases hz2 : z = a
    · rwa [hz2]
    · simp [hz2] at haz

/-- If fewer than `M` resolutions have occurred, the `Y` ledger bounds the
productive counter by `y0 + 3 * M`; the theorem uses an external co-level
witness `cL` so no natural subtraction appears in the statement. -/
theorem heavyTrace_productiveCount_lt_of_resolutions_lt {n y₀ cL M K : ℕ}
    (q : HeavyTrace n) (hy : q.YLedger y₀)
    (hy0le : y₀ ≤ cL) (hK : K = cL + 3 * M)
    (hres : q.up + q.down < M) :
    q.fuel + q.up + q.down < K := by
  simp only [HeavyTrace.YLedger] at hy
  omega

/-- Stopped-band event split: failure to be above `thr` is covered by
backslide, many-resolutions direction failure, or productive-clock starvation.
The clock branch uses the `Y` ledger to convert `up + down < M` into
`fuel + up + down < K`. -/
theorem heavyBand_split
    (n aLo hi thr M K T cL y₀ : ℕ)
    (hthr : thr + 1 = hi) (hK : K = cL + 3 * M)
    (q₀ : HeavyTrace n) (hy₀ : q₀.YLedger y₀) (hy0le : y₀ ≤ cL) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
        iter (heavyBandStop n aLo hi) T q₀ q else 0)
      ≤ (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
            iter (heavyBandStop n aLo hi) T q₀ q else 0))
        + (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ thr ∧ M ≤ q.up + q.down then
            iter (heavyBandStop n aLo hi) T q₀ q else 0))
        + (∑' q, (if (aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
                BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi)
              ∧ q.fuel + q.up + q.down < K then
            iter (heavyBandStop n aLo hi) T q₀ q else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set p := iter (heavyBandStop n aLo hi) T q₀ q with hp
  by_cases hlt : BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi
  · rw [if_pos hlt]
    by_cases hlow : BiCfg.heavyLevel q.cfg.1 ≤ aLo
    · rw [if_pos hlow]
      exact le_trans (self_le_add_right _ _) (self_le_add_right _ _)
    · rw [if_neg hlow]
      by_cases hres : M ≤ q.up + q.down
      · have hlevThr : BiCfg.heavyLevel q.cfg.1 ≤ thr := by omega
        rw [if_pos ⟨hlevThr, hres⟩, zero_add]
        exact self_le_add_right _ _
      · rw [if_neg (by intro h; exact hres h.2)]
        by_cases hp0 : p = 0
        · rw [hp0]
          positivity
        · have hy : q.YLedger y₀ := by
            exact heavyBandStop_iter_yLedger q₀ q hy₀ (by simpa [hp] using hp0)
          have hcount : q.fuel + q.up + q.down < K :=
            heavyTrace_productiveCount_lt_of_resolutions_lt q hy hy0le hK
              (by omega)
          have hlive : aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
              BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi := by
            omega
          rw [if_pos ⟨hlive, hcount⟩, zero_add, zero_add]
  · rw [if_neg hlt]
    positivity

/-- Stopped trace phase failure bound: backslide mass plus direction-deadline
tail plus raw productive-clock starvation. -/
theorem heavyBand_phase_fail
    (n aLo hi thr p q M K T cL y₀ : ℕ) (hn : 3 ≤ n)
    (hthr : thr + 1 = hi) (hK : K = cL + 3 * M)
    (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (pp : ℝ≥0∞) (hpp1 : pp ≤ 1)
    (hfloor : ∀ q : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 →
      BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi →
      pp ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb)
    (q₀ : HeavyTrace n) (hy₀ : q₀.YLedger y₀) (hy0le : y₀ ≤ cL)
    (hc0 : q₀.fuel + q₀.up + q₀.down = 0) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
        iter (heavyBandStop n aLo hi) T q₀ q else 0)
      ≤ (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
            iter (heavyBandStop n aLo hi) T q₀ q else 0))
        + w ^ BiCfg.heavyLevel q₀.cfg.1 / (w ^ thr * η ^ M)
        + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
            ((1 : ℝ≥0∞) / 2) ^ K := by
  have hr0 : q₀.up + q₀.down = 0 := by omega
  refine le_trans (heavyBand_split n aLo hi thr M K T cL y₀
    hthr hK q₀ hy₀ hy0le) ?_
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · exact heavyBandWindowStop_tail_of_guard hn aLo hi p q thr M T hq
      hguard w η u hu hrel hwη hw1 hw0 hη1 hηt q₀ hr0
  · exact heavyBand_productive_tail n aLo hi T K hn pp hpp1 hfloor q₀ hc0

/-- The state band stop is the lower stop followed by an upper freeze. -/
theorem heavyStateBandStop_eq_freeze_upper_lower {n aLo hi : ℕ} :
    heavyStateBandStop n aLo hi =
      freeze (fun s : HeavyState n => hi ≤ BiCfg.heavyLevel s.1)
        (freeze (fun s : HeavyState n => BiCfg.heavyLevel s.1 ≤ aLo)
          (heavyStateStep n)) := by
  funext s
  unfold heavyStateBandStop freeze
  by_cases hU : hi ≤ BiCfg.heavyLevel s.1
  · rw [if_pos (Or.inr hU), if_pos hU]
  · rw [if_neg hU]
    by_cases hL : BiCfg.heavyLevel s.1 ≤ aLo
    · rw [if_pos (Or.inl hL), if_pos hL]
    · rw [if_neg (by omega), if_neg hL]

/-- The lower stopped-band trace mass is bounded by the physical Heavy-B ruin
term from the same starting configuration. -/
theorem heavyBand_ruin_term_le {n : ℕ} (hn : 3 ≤ n)
    (aLo bHi hi k T : ℕ)
    (haLohi : aLo < hi)
    (hpop : aLo + bHi + 2 = n)
    (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo)
    (q₀ : HeavyTrace n)
    (hstart : BiCfg.heavyLevel q₀.cfg.1 = aLo + k) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
        iter (heavyBandStop n aLo hi) T q₀ q else 0)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  classical
  let L : HeavyState n → Prop := fun s => BiCfg.heavyLevel s.1 ≤ aLo
  let A : HeavyState n → Prop := fun s => aLo < BiCfg.heavyLevel s.1
  let U : HeavyState n → Prop := fun s => hi ≤ BiCfg.heavyLevel s.1
  have htrace_state :
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
        =
      (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s) := by
    calc
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
          = ∑' q, if A q.cfg then 0 else
              iter (heavyBandStop n aLo hi) T q₀ q := by
            apply tsum_congr
            intro q
            by_cases hq : A q.cfg
            · simp [A, hq, Nat.not_le.mpr hq]
            · have hle : BiCfg.heavyLevel q.cfg.1 ≤ aLo := by
                dsimp [A] at hq
                omega
              simp [A, hq, hle]
      _ = (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s) := by
            rw [heavyStateBand_failure_eq_trace hn aLo hi T q₀ A]
  have hcompl : ∀ (K : HeavyState n → PMF (HeavyState n)),
      (∑' s, if L s then iter K T q₀.cfg s else 0)
        = 1 - (∑' s, if L s then (0 : ℝ≥0∞) else iter K T q₀.cfg s) := by
    intro K
    have hle1 : (∑' s, if L s then (0 : ℝ≥0∞) else
        iter K T q₀.cfg s) ≤ 1 := by
      calc
        (∑' s, if L s then (0 : ℝ≥0∞) else iter K T q₀.cfg s)
            ≤ ∑' s, iter K T q₀.cfg s :=
              ENNReal.tsum_le_tsum fun s => by split_ifs <;> simp
        _ = 1 := PMF.tsum_coe _
    have hne : (∑' s, if L s then (0 : ℝ≥0∞) else
        iter K T q₀.cfg s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hle1
    have hpt : ∀ s,
        (if L s then iter K T q₀.cfg s else 0)
          + (if L s then (0 : ℝ≥0∞) else iter K T q₀.cfg s)
          = iter K T q₀.cfg s := by
      intro s
      by_cases hs : L s <;> simp [hs]
    have hp : (∑' s, if L s then iter K T q₀.cfg s else 0)
        + (∑' s, if L s then (0 : ℝ≥0∞) else iter K T q₀.cfg s)
        = 1 := by
      rw [← ENNReal.tsum_add, tsum_congr hpt, PMF.tsum_coe]
    rw [← hp, ENNReal.add_sub_cancel_right hne]
  have hnot_le :
      (∑' s, if L s then (0 : ℝ≥0∞) else
          iter (freeze L (heavyStateStep n)) T q₀.cfg s)
        ≤ (∑' s, if L s then (0 : ℝ≥0∞) else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s) := by
    rw [heavyStateBandStop_eq_freeze_upper_lower]
    exact mass_le_freeze (freeze L (heavyStateStep n)) U L
      (fun s hU hL => by dsimp [U, L] at hU hL; omega) T q₀.cfg
  have hstate_lower :
      (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s)
        ≤ hitProb L (heavyStateStep n) T q₀.cfg := by
    calc
      (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s)
          = (∑' s, if L s then
              iter (heavyStateBandStop n aLo hi) T q₀.cfg s else 0) := by
            apply tsum_congr
            intro s
            by_cases hL : L s
            · have hA : ¬ A s := by dsimp [L, A] at hL ⊢; omega
              simp [hL, hA]
            · have hA : A s := by dsimp [L, A] at hL ⊢; omega
              simp [hL, hA]
      _ = 1 - (∑' s, if L s then (0 : ℝ≥0∞) else
            iter (heavyStateBandStop n aLo hi) T q₀.cfg s) := hcompl _
      _ ≤ 1 - (∑' s, if L s then (0 : ℝ≥0∞) else
            iter (freeze L (heavyStateStep n)) T q₀.cfg s) :=
          tsub_le_tsub_left hnot_le 1
      _ = (∑' s, if L s then
            iter (freeze L (heavyStateStep n)) T q₀.cfg s else 0) :=
          (hcompl _).symm
      _ = hitProb L (heavyStateStep n) T q₀.cfg := by
          unfold hitProb expect ind L
          apply tsum_congr
          intro s
          by_cases hs : BiCfg.heavyLevel s.1 ≤ aLo <;> simp [hs]
  calc
    (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
        iter (heavyBandStop n aLo hi) T q₀ q else 0))
        = (∑' s, if A s then 0 else
          iter (heavyStateBandStop n aLo hi) T q₀.cfg s) := htrace_state
    _ ≤ hitProb L (heavyStateStep n) T q₀.cfg := hstate_lower
    _ ≤ ⨆ t : ℕ, hitProb L (heavyStateStep n) t q₀.cfg :=
        le_iSup (fun t : ℕ => hitProb L (heavyStateStep n) t q₀.cfg) T
    _ ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
        simpa [L] using
          heavyB_ruin aLo bHi k hn hpop haLo hbHi hmaj q₀.cfg hstart

/-- Monotone-start physical Heavy-B band phase, with all stopped trace errors
transferred back to the raw state chain and the lower term discharged by ruin. -/
theorem heavyState_band_phase_reaches_mono
    {n : ℕ} (hn : 3 ≤ n)
    (aLo bHiR hi thr k M K T cL : ℕ)
    (haLohi : aLo < hi) (hthr : thr + 1 = hi)
    (hstartCo : aLo + k + cL = n) (hK : K = cL + 3 * M)
    (hpopR : aLo + bHiR + 2 = n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR) (hmajR : bHiR ≤ aLo)
    (p q : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (pp : ℝ≥0∞) (hpp1 : pp ≤ 1)
    (hfloor : ∀ q : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 →
      BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi →
      pp ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb)
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
      ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ (aLo + k) / (w ^ thr * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K)
        + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet) := by
  classical
  intro s hs
  let A : HeavyState n → Prop := fun z =>
    returnLo + 1 ≤ BiCfg.heavyLevel z.1
  let q₀ : HeavyTrace n := ⟨s, 0, 0, 0⟩
  have hy₀ : q₀.YLedger s.1.y := by
    exact HeavyTrace.initial_yLedger s
  have hy0le : s.1.y ≤ cL := by
    have hco := BiCfg.heavyLevel_add_coLevel s.2
    omega
  have hc0 : q₀.fuel + q₀.up + q₀.down = 0 := by
    simp [q₀]
  have htransfer :
      (∑' z, if A z then 0 else iter (heavyStateStep n) T s z)
        ≤ (∑' q, if A q.cfg then 0 else
            iter (heavyBandStop n aLo hi) T q₀ q)
          + ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet := by
    simpa [q₀] using
      heavyBand_transfer_upper aLo hi returnLo bHiRet kRet T hn
        hpopRet hreturnLo hbHiRet hmajRet hreturnGap q₀ A
        (by
          intro z hz
          dsimp [A] at hz
          omega)
        (by
          intro z hz
          dsimp [A] at hz
          omega)
  have hphase0 :
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
        ≤ (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
              iter (heavyBandStop n aLo hi) T q₀ q else 0))
          + w ^ BiCfg.heavyLevel q₀.cfg.1 / (w ^ thr * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K := by
    exact heavyBand_phase_fail n aLo hi thr p q M K T cL s.1.y hn
      hthr hK hq hguard w η u hu hrel hwη hw1 hw0 hη1 hηt
      pp hpp1 hfloor q₀ hy₀ hy0le hc0
  obtain ⟨d, hd⟩ : ∃ d, BiCfg.heavyLevel s.1 = aLo + d :=
    ⟨BiCfg.heavyLevel s.1 - aLo, by omega⟩
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
  have hruinActual :
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ d := by
    exact heavyBand_ruin_term_le hn aLo bHiR hi d T haLohi hpopR
      haLo hbHiR hmajR q₀ (by simpa [q₀] using hd)
  have hruin :
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ aLo then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
    hruinActual.trans (pow_le_pow_right_of_le_one' hbaseR hkd)
  have hdir :
      w ^ BiCfg.heavyLevel q₀.cfg.1 / (w ^ thr * η ^ M)
        ≤ w ^ (aLo + k) / (w ^ thr * η ^ M) := by
    exact ENNReal.div_le_div_right
      (pow_le_pow_right_of_le_one' hw1 (by simpa [q₀] using hs)) _
  have hphase :
      (∑' q, (if BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi then
          iter (heavyBandStop n aLo hi) T q₀ q else 0))
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ (aLo + k) / (w ^ thr * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K :=
    hphase0.trans (add_le_add (add_le_add hruin hdir) le_rfl)
  have hstopped :
      (∑' q, if A q.cfg then 0 else
          iter (heavyBandStop n aLo hi) T q₀ q)
        ≤ ((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k
          + w ^ (aLo + k) / (w ^ thr * η ^ M)
          + ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
              ((1 : ℝ≥0∞) / 2) ^ K := by
    refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) hphase
    by_cases hA : A q.cfg
    · simp [hA]
    · have hqHi : BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi := by
        dsimp [A] at hA
        omega
      simp [hA, hqHi]
  exact htransfer.trans (add_le_add hstopped le_rfl)

end Tri

#print axioms Tri.heavyBandStop_iter_yLedger
#print axioms Tri.heavyTrace_productiveCount_lt_of_resolutions_lt
#print axioms Tri.heavyBand_split
#print axioms Tri.heavyBand_phase_fail
#print axioms Tri.heavyStateBandStop_eq_freeze_upper_lower
#print axioms Tri.heavyBand_ruin_term_le
#print axioms Tri.heavyState_band_phase_reaches_mono

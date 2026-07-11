/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase78SurvivalContracting — the CONTRACTING (`r < 1`) slot-7 / slot-8 ELIMINATOR-drain survivals.

This append-only file edits NO existing file.  It builds the slot-7 (Doty §7 gap-1 eliminator,
`classMassN`) and slot-8 (Doty §8 above-level eliminator, `minorityU`) SURVIVALS by applying the
proven contracting-drain template of `GatedDrainContracting` (slot-5) to the Phase-7 / Phase-8
eliminator potentials.  It is the EXACT mirror of `Phase6SurvivalContracting`, with the
eliminator pieces substituted for the doubling-drain ones.

## The template (REUSED verbatim — `GatedDrainContracting`)
ALL three engines are generic over the kernel / potential / gate:
* `GatedDrift.gated_real_tail_anyr` — the `r`-arbitrary gated tail (NO `hr : 1 ≤ r`); the drain term
  `r^T·Φ T/θ` shrinks iff `r < 1`.
* `expDrainPot_drift_contracting` — the CONTRACTING MGF drift from a per-step DROP floor `ρ` and a
  NEVER-INCREASE property; `contractRate_lt_one` gives `r = contractRate ρ s < 1` for `0 < ρ ≤ 1`,
  `s > 0`.
* `phase{7,8}_survival_contracting` (this file's mirror of `phase6_survival_contracting`) — compose:
  contracting drain + cumulative clock tail + the §6/§7 Post-structure escape; `drain_term_tendsto_zero`
  shows the drain genuinely shrinks.

## The slot-7 / slot-8 substitution
* potential `Φ₇ := classMassN σ` (Phase 7) / `Φ₈ := minorityU σ` (Phase 8).
* gate `G₇ := {c | Inv7Sum n c}` (Phase 7) / `G₈ := {c | Phase8AllMain n c}` (Phase 8) — the
  windowed+structured invariant.  NEVER an `InvClosed` of it.
* per-step DROP floor `ρ := 1 − levelRate E n m = ofReal(E/(n(n−1)))` on the drop event
  `{c' | Φ c' + 1 ≤ Φ c}`, derived from `SlotEngine.slot{7,8}_hdrop_direct` (which bounds the
  `potBelow`-complement mass `≤ levelRate E n m`) via the SAME `potBelow ↔ drop-event` complement
  bridge `Phase6SurvivalContracting.highMass_drop_floor` used for slot 6.
  * `slot7_hdrop_direct` takes the carried §6→§7 Post structure `Phase6To7Structure` (whp; the
    gap-1 eliminator-margin residual — the precise named remainder Doty Lemma 7.4 exports) and the
    margin bound `E7 ≤ 4n/15`; the minority witness half is PROVED inside it.
  * `slot8_hdrop_direct` takes the carried §7→§8 Post structure `Phase7To8Structure` (whp; the
    above-level eliminator-margin residual — Doty Lemma 7.6) and the margin bound `E8 ≤ n/5`.
* NEVER-INCREASE: `Phase7Convergence.potNonincrOn_classMassN` / `Phase8Convergence.potNonincrOn_minorityU`,
  supplying `K c {c' | Φ c < Φ c'} = 0`.
* contracting rate `r := contractRate (1 − levelRate E n m) s = 1 − (1−levelRate)·(1−e^{−s}) < 1`
  whenever the eliminator margin `E > 0` (drop floor positive) and `s > 0`.
* cumulative clock tail `η_clock`: `ClockDepletionCoupling.mgf_depletion_tail_uniform` (phases 7/8
  advance via the SAME depletion counter), carried as a SUM over `range T`, NEVER a one-step `T·η`.
* structural tail `η_struct`: the §6/§7 Post-structure escape, the carried TRUE residual.

## The CONTRACTING `r < 1` (the whole point)
The drain CONTRACTS on the gate: `contractRate (1 − levelRate E n m) s < 1`, verified STRICTLY by
`dropFloor7/8_pos` (giving `0 < 1 − levelRate E n m = ofReal(E/(n(n−1)))` from `E > 0`) fed to
`contractRate_lt_one`.  An `r ≥ 1` "drift" is the vacuous trap; here `r < 1` strictly, so `r^T → 0`
(`drain_term_tendsto_zero`).

## ANTI-TRAP compliance
* NO `InvClosed` / `hClosed` / `levels_PhaseConvergenceW` of any phase window.
* The drain CONTRACTS (`r < 1` STRICTLY, `phase{7,8}_contractRate_lt_one`).
* The clock escape is CUMULATIVE (`∑_{τ<T}`), never a one-step `T·η`.
* Every carried residual is a per-step LOWER bound (drop floor) or an upstream-phase whp Post
  (`Phase6To7Structure` / `Phase7To8Structure`, monotone-structural, NOT a closure of a decreasing
  quantity).  No one-step closure of a decreasing quantity is carried.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedDrainContracting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainEngine

namespace ExactMajority
namespace Phase78SurvivalContracting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 0 — the eliminator DROP floor `ρ = 1 − levelRate E n m = ofReal(E/(n(n−1)))`.

`DrainRates.levelRate E n m = 1 − ofReal(E/(n(n−1)))` (independent of `m`).  The DROP floor consumed
by `expDrainPot_drift_contracting` is its complement `1 − levelRate E n m`; on `n ≥ 2` this equals
`ofReal(E/(n(n−1)))`, positive exactly when the eliminator margin `E > 0`.  This is the NON-VACUITY
linchpin: a zero margin would give `ρ = 0`, hence `r = 1` (vacuous). -/

/-- **The eliminator drop floor `1 − levelRate E n m` equals `ofReal(E/(n(n−1)))`** for `n ≥ 2`.
`levelRate E n m = 1 − ofReal(frac)`, so `1 − levelRate = 1 − (1 − ofReal frac) = ofReal frac`
(via `sub_sub_cancel`, needing `ofReal frac ≤ 1` — which we verify, since `E ≤ n(n−1)` is NOT assumed,
so we instead use that `ofReal frac` may exceed `1`; we present the bound through `min`-free
`sub_sub_cancel` only when `ofReal frac ≤ 1`).  In our use `E` is a small eliminator margin
(`E ≤ 4n/15` or `n/5`), so `frac = E/(n(n−1)) < 1` for `n ≥ 2`; we discharge `ofReal frac ≤ 1`. -/
theorem dropFloorE_eq_ofReal {E n m : ℕ} (hn : 2 ≤ n)
    (hElt : (E : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    1 - DrainRates.levelRate E n m
      = ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  unfold DrainRates.levelRate
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfrac_nonneg : (0 : ℝ) ≤ (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (by positivity) hden.le
  have hfrac_le_one : (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 :=
    (div_le_one hden).mpr hElt
  have hofrac_le_one : ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal hfrac_le_one
  -- goal: `1 − (1 − ofReal frac) = ofReal frac`.
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hofrac_le_one

/-- **The eliminator drop floor `1 − levelRate E n m` is positive** when the eliminator margin
`E > 0` (`hEpos`) and `n ≥ 2` (`hn`).  `1 − levelRate E n m = ofReal(E/(n(n−1)))`, which is `> 0`
exactly when `E > 0`.  This is the NON-VACUITY of the contraction: a zero margin gives `r = 1`. -/
theorem dropFloorE_pos {E n m : ℕ} (hn : 2 ≤ n) (hEpos : 0 < E) :
    0 < 1 - DrainRates.levelRate E n m := by
  -- `1 − levelRate = 1 − (1 − ofReal frac)`; positive iff `levelRate < 1` iff `ofReal frac > 0`.
  unfold DrainRates.levelRate
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfrac_pos : (0 : ℝ) < (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply div_pos _ hden
    have : (1 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hEpos
    linarith
  have hofrac_pos : (0 : ℝ≥0∞) < ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
    ENNReal.ofReal_pos.mpr hfrac_pos
  -- `0 < 1 − (1 − x)` from `1 − x < 1`, i.e. `x > 0` strictly drops `1 − x` below `1`.
  rw [tsub_pos_iff_lt]
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hofrac_pos)

/-- **The eliminator contracting rate is STRICTLY `< 1`.**  `r = contractRate (1 − levelRate E n m) s
< 1` whenever the drop floor is positive (`dropFloorE_pos`, i.e. `E > 0`), `≤ 1` (always,
`tsub_le_self`), and `s > 0`.  The linchpin of non-vacuity: with `r < 1` the drain term `r^T·coef → 0`;
an `r ≥ 1` "drift" would be the vacuous trap. -/
theorem phaseE_contractRate_lt_one {E n m : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hEpos : 0 < E) :
    contractRate (1 - DrainRates.levelRate E n m) s < 1 := by
  apply contractRate_lt_one s hs
  · exact dropFloorE_pos hn hEpos
  · exact tsub_le_self

/-! ## Part 1 (slot 7) — the per-step DROP floor, NEVER-INCREASE, and CONTRACTING drift.

`SlotEngine.slot7_hdrop_direct` bounds the `potBelow (classMassN σ)`-COMPLEMENT mass by
`levelRate E7 n m`; we convert this to the DROP-EVENT floor `1 − levelRate E7 n m ≤ K(drop)` via the
SAME complement bridge as `Phase6SurvivalContracting.highMass_drop_floor`.  The never-increase is
`Phase7Convergence.potNonincrOn_classMassN`. -/

/-- **The slot-7 drop-event floor.**  From `slot7_hdrop_direct` (the `potBelow`-complement ceiling
`≤ levelRate E7 n m`), at an `Inv7Sum` config with `classMassN σ = m`, the one-step kernel mass of the
DROP event `{c' | classMassN σ c' + 1 ≤ classMassN σ b}` is `≥ 1 − levelRate E7 n m`.  The eliminator
margin enters through `hPhase6Post7` (the carried §6→§7 whp Post `Phase6To7Structure`) and the
deterministic bound `hE7 : E7 ≤ 4n/15`. -/
theorem classMassN_drop_floor {n : ℕ} (σ : Sign) (E7 : ℕ) (hn : 2 ≤ n)
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hPhase6Post7 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b)
    {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hInv : Phase7Convergence.Inv7Sum n b)
    (hbm : Phase7Convergence.classMassN σ b = m) :
    1 - DrainRates.levelRate E7 n m
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase7Convergence.classMassN (L := L) (K := K) σ c' + 1
                  ≤ Phase7Convergence.classMassN (L := L) (K := K) σ b} := by
  classical
  set Φ := fun c => Phase7Convergence.classMassN (L := L) (K := K) σ c with hΦ
  have hcompl_le := SlotEngine.slot7_hdrop_direct (L := L) (K := K)
    σ E7 hn hE7 hPhase6Post7 hmpos b hInv hbm
  have hsucc_eq : {c' : Config (AgentState L K) | Φ c' + 1 ≤ Φ b}
      = OneSidedCancel.potBelow Φ m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hΦ, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow Φ m) :=
    OneSidedCancel.potBelow_measurable Φ m
  have hcompl : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m)ᶜ
      = 1 - (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) := by
    have htot : (NonuniformMajority L K).transitionKernel b Set.univ = 1 :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
        |>.measure_univ
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hsucc_eq]
  have hpb_le_one : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq
      ((inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
        |>.measure_univ)
  have hstep : 1 - DrainRates.levelRate E7 n m
      ≤ 1 - (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m)ᶜ := by
    exact tsub_le_tsub_left hcompl_le 1
  rw [hcompl] at hstep
  rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hpb_le_one] at hstep

/-- **`classMassN σ` never increases on `Inv7Sum n`** in the `hnoincr` shape
`K c {c' | classMassN σ c < classMassN σ c'} = 0`.  Directly from `potNonincrOn_classMassN`. -/
theorem classMassN_noincr {n : ℕ} (σ : Sign)
    (b : Config (AgentState L K))
    (hInv : Phase7Convergence.Inv7Sum (L := L) (K := K) n b) :
    (NonuniformMajority L K).transitionKernel b
        {c' | Phase7Convergence.classMassN (L := L) (K := K) σ b
                < Phase7Convergence.classMassN (L := L) (K := K) σ c'} = 0 :=
  Phase7Convergence.potNonincrOn_classMassN (L := L) (K := K) σ n b hInv

/-- **The slot-7 contracting MGF drift** at a level-`m` config `b` on the gate.  The MGF potential
`expDrainPot (classMassN σ) s` contracts by `contractRate (1 − levelRate E7 n m) s` per step. -/
theorem expDrainPot_classMassN_drift {n : ℕ} (σ : Sign) (E7 : ℕ) (hn : 2 ≤ n)
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hPhase6Post7 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b)
    (s : ℝ) (hs : 0 ≤ s) {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hInv : Phase7Convergence.Inv7Sum n b)
    (hbm : Phase7Convergence.classMassN σ b = m) :
    ∫⁻ c', expDrainPot (L := L) (K := K)
        (fun c => Phase7Convergence.classMassN (L := L) (K := K) σ c) s c'
        ∂((NonuniformMajority L K).transitionKernel b)
      ≤ contractRate (1 - DrainRates.levelRate E7 n m) s
          * expDrainPot (L := L) (K := K)
              (fun c => Phase7Convergence.classMassN (L := L) (K := K) σ c) s b := by
  refine expDrainPot_drift_contracting (L := L) (K := K)
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase7Convergence.classMassN (L := L) (K := K) σ c) s hs
    (1 - DrainRates.levelRate E7 n m) b ?_ ?_
  · exact classMassN_drop_floor σ E7 hn hE7 hPhase6Post7 hmpos b hInv hbm
  · exact classMassN_noincr σ b hInv

/-! ## Part 2 (slot 8) — the per-step DROP floor, NEVER-INCREASE, and CONTRACTING drift.

`SlotEngine.slot8_hdrop_direct` bounds the `potBelow (minorityU σ)`-COMPLEMENT mass by
`levelRate E8 n m`; converted to the DROP floor `1 − levelRate E8 n m` by the same bridge.  The
never-increase is `Phase8Convergence.potNonincrOn_minorityU`. -/

/-- **The slot-8 drop-event floor.**  From `slot8_hdrop_direct` (the `potBelow`-complement ceiling
`≤ levelRate E8 n m`), at a `Phase8AllMain` config with `minorityU σ = m`, the one-step kernel mass of
the DROP event `{c' | minorityU σ c' + 1 ≤ minorityU σ b}` is `≥ 1 − levelRate E8 n m`.  The above-level
eliminator margin enters through `hPhase7Post8` (the carried §7→§8 whp Post `Phase7To8Structure`) and
`hE8 : E8 ≤ n/5`. -/
theorem minorityU_drop_floor {n : ℕ} (σ : Sign) (E8 : ℕ) (hn : 2 ≤ n)
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hPhase7Post8 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b)
    {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m) :
    1 - DrainRates.levelRate E8 n m
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase7Convergence.minorityU (L := L) (K := K) σ c' + 1
                  ≤ Phase7Convergence.minorityU (L := L) (K := K) σ b} := by
  classical
  set Φ := fun c => Phase7Convergence.minorityU (L := L) (K := K) σ c with hΦ
  have hcompl_le := SlotEngine.slot8_hdrop_direct (L := L) (K := K)
    σ E8 hn hE8 hPhase7Post8 hmpos b hb8 hbm
  have hsucc_eq : {c' : Config (AgentState L K) | Φ c' + 1 ≤ Φ b}
      = OneSidedCancel.potBelow Φ m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hΦ, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow Φ m) :=
    OneSidedCancel.potBelow_measurable Φ m
  have hcompl : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m)ᶜ
      = 1 - (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) := by
    have htot : (NonuniformMajority L K).transitionKernel b Set.univ = 1 :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
        |>.measure_univ
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hsucc_eq]
  have hpb_le_one : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq
      ((inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
        |>.measure_univ)
  have hstep : 1 - DrainRates.levelRate E8 n m
      ≤ 1 - (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m)ᶜ := by
    exact tsub_le_tsub_left hcompl_le 1
  rw [hcompl] at hstep
  rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hpb_le_one] at hstep

/-- **`minorityU σ` never increases on `Phase8AllMain n`** in the `hnoincr` shape
`K c {c' | minorityU σ c < minorityU σ c'} = 0`.  Directly from `potNonincrOn_minorityU`. -/
theorem minorityU_noincr {n : ℕ} (σ : Sign)
    (b : Config (AgentState L K))
    (hInv : Phase8Convergence.Phase8AllMain (L := L) (K := K) n b) :
    (NonuniformMajority L K).transitionKernel b
        {c' | Phase7Convergence.minorityU (L := L) (K := K) σ b
                < Phase7Convergence.minorityU (L := L) (K := K) σ c'} = 0 :=
  Phase8Convergence.potNonincrOn_minorityU (L := L) (K := K) σ n b hInv

/-- **The slot-8 contracting MGF drift** at a level-`m` config `b` on the gate.  The MGF potential
`expDrainPot (minorityU σ) s` contracts by `contractRate (1 − levelRate E8 n m) s` per step. -/
theorem expDrainPot_minorityU_drift {n : ℕ} (σ : Sign) (E8 : ℕ) (hn : 2 ≤ n)
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hPhase7Post8 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b)
    (s : ℝ) (hs : 0 ≤ s) {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m) :
    ∫⁻ c', expDrainPot (L := L) (K := K)
        (fun c => Phase7Convergence.minorityU (L := L) (K := K) σ c) s c'
        ∂((NonuniformMajority L K).transitionKernel b)
      ≤ contractRate (1 - DrainRates.levelRate E8 n m) s
          * expDrainPot (L := L) (K := K)
              (fun c => Phase7Convergence.minorityU (L := L) (K := K) σ c) s b := by
  refine expDrainPot_drift_contracting (L := L) (K := K)
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase7Convergence.minorityU (L := L) (K := K) σ c) s hs
    (1 - DrainRates.levelRate E8 n m) b ?_ ?_
  · exact minorityU_drop_floor σ E8 hn hE8 hPhase7Post8 hmpos b hb8 hbm
  · exact minorityU_noincr σ b hb8

/-! ## Part 3 — the composed slot-7 / slot-8 SURVIVALS (CONTRACTING `r < 1`).

The EXACT mirror of `Phase6SurvivalContracting.phase6_survival_contracting` (which itself mirrors
`phase5_survival_contracting`).  The two survivals share the same generic body; we state them
separately at the slot-7 / slot-8 gates and potentials, with the §6/§7 Post-structure escape carried
as the abstract structural tail `η_struct`. -/

open GatedDrift

/-- **CONTRACTING slot-7 eliminator-drain survival (`r < 1`).**  Mirrors
`phase6_survival_contracting` with the Phase-7 potential `Φ₇ := classMassN σ` and gate
`G₇ := {c | Inv7Sum n c}`.  The drain engine carries NO `hr : 1 ≤ r`, so `r` is the contracting
`contractRate (1 − levelRate E7 n m) s < 1` (`phaseE_contractRate_lt_one`), making `r^T·Φ₇ c₀/θ`
genuinely shrink.

`Aconf` is the §6→§7 Post-structure escape set (the carried whp residual target — the structural
violation of the carried `Phase6To7Structure`-band, monotone-structural, NOT a closure);
`hcover` says the survival event `{¬ Phase7Done}` is covered by the structural escape `Aconf` plus
the eliminator surplus `{θ ≤ Φ₇}`.  NO `InvClosed` of `Inv7Sum`. -/
theorem phase7_survival_contracting {n : ℕ}
    (Φ₇ : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hdrift : ∀ x ∈ {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c},
      ∫⁻ y, Φ₇ y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ₇ x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (c₀ : Config (AgentState L K))
    (hWin₀ : Phase7Convergence.Inv7Sum (L := L) (K := K) n c₀)
    (εdrain : ℝ≥0)
    (hεdrain : ((T : ℝ≥0∞) * q_leak + r ^ T * Φ₇ c₀ / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (η_clock η_struct : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ η_clock)
    (Phase7Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hStruct : ((NonuniformMajority L K).transitionKernel ^ T) c₀ Aconf ≤ η_struct)
    (hcover : {c : Config (AgentState L K) | ¬ Phase7Done c}
      ⊆ Aconf ∪ {c | θ ≤ Φ₇ c}) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | ¬ Phase7Done c}
      ≤ (εdrain : ℝ≥0∞) + η_clock + η_struct := by
  classical
  have hgated := GatedDrift.gated_real_tail_anyr
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c})
    Φ₇ r hdrift T c₀ θ hθ0 hθtop
  have hesc := GatedDrift.kill_escape_le_prefix_union
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c})
    S q_leak hLeak T c₀ hWin₀
  have hdrain0 :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ₇ c}
        ≤ ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ₇ c₀ / θ :=
    le_trans hgated (add_le_add hesc le_rfl)
  have hdrain : ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ₇ c}
      ≤ (εdrain : ℝ≥0∞) + η_clock := by
    refine le_trans hdrain0 ?_
    calc ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ₇ c₀ / θ
        = ((T : ℝ≥0∞) * q_leak + r ^ T * Φ₇ c₀ / θ)
          + ∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ := by ring
      _ ≤ (εdrain : ℝ≥0∞) + η_clock := add_le_add hεdrain hClock
  set μ := ((NonuniformMajority L K).transitionKernel ^ T) c₀ with hμ
  set Adrain : Set (Config (AgentState L K)) := {c | θ ≤ Φ₇ c} with hAdrain
  calc μ {c | ¬ Phase7Done c}
      ≤ μ (Aconf ∪ Adrain) := measure_mono hcover
    _ ≤ μ Aconf + μ Adrain := measure_union_le _ _
    _ ≤ η_struct + ((εdrain : ℝ≥0∞) + η_clock) := add_le_add hStruct hdrain
    _ = (εdrain : ℝ≥0∞) + η_clock + η_struct := by ring

/-- **CONTRACTING slot-8 eliminator-drain survival (`r < 1`).**  Mirrors
`phase6_survival_contracting` with the Phase-8 potential `Φ₈ := minorityU σ` and gate
`G₈ := {c | Phase8AllMain n c}`.  The drain engine carries NO `hr : 1 ≤ r`, so `r` is the contracting
`contractRate (1 − levelRate E8 n m) s < 1` (`phaseE_contractRate_lt_one`), making `r^T·Φ₈ c₀/θ`
genuinely shrink.

`Aconf` is the §7→§8 Post-structure escape set (the carried whp residual — the structural violation
of `Phase7To8Structure`-band, monotone-structural, NOT a closure).  NO `InvClosed` of
`Phase8AllMain`. -/
theorem phase8_survival_contracting {n : ℕ}
    (Φ₈ : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hdrift : ∀ x ∈ {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c},
      ∫⁻ y, Φ₈ y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ₈ x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (c₀ : Config (AgentState L K))
    (hWin₀ : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c₀)
    (εdrain : ℝ≥0)
    (hεdrain : ((T : ℝ≥0∞) * q_leak + r ^ T * Φ₈ c₀ / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (η_clock η_struct : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ η_clock)
    (Phase8Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hStruct : ((NonuniformMajority L K).transitionKernel ^ T) c₀ Aconf ≤ η_struct)
    (hcover : {c : Config (AgentState L K) | ¬ Phase8Done c}
      ⊆ Aconf ∪ {c | θ ≤ Φ₈ c}) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | ¬ Phase8Done c}
      ≤ (εdrain : ℝ≥0∞) + η_clock + η_struct := by
  classical
  have hgated := GatedDrift.gated_real_tail_anyr
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c})
    Φ₈ r hdrift T c₀ θ hθ0 hθtop
  have hesc := GatedDrift.kill_escape_le_prefix_union
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c})
    S q_leak hLeak T c₀ hWin₀
  have hdrain0 :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ₈ c}
        ≤ ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ₈ c₀ / θ :=
    le_trans hgated (add_le_add hesc le_rfl)
  have hdrain : ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ₈ c}
      ≤ (εdrain : ℝ≥0∞) + η_clock := by
    refine le_trans hdrain0 ?_
    calc ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ₈ c₀ / θ
        = ((T : ℝ≥0∞) * q_leak + r ^ T * Φ₈ c₀ / θ)
          + ∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ := by ring
      _ ≤ (εdrain : ℝ≥0∞) + η_clock := add_le_add hεdrain hClock
  set μ := ((NonuniformMajority L K).transitionKernel ^ T) c₀ with hμ
  set Adrain : Set (Config (AgentState L K)) := {c | θ ≤ Φ₈ c} with hAdrain
  calc μ {c | ¬ Phase8Done c}
      ≤ μ (Aconf ∪ Adrain) := measure_mono hcover
    _ ≤ μ Aconf + μ Adrain := measure_union_le _ _
    _ ≤ η_struct + ((εdrain : ℝ≥0∞) + η_clock) := add_le_add hStruct hdrain
    _ = (εdrain : ℝ≥0∞) + η_clock + η_struct := by ring

/-! ## Part 4 — the drain genuinely SHRINKS (non-vacuity, the whole point).

For both slots the contracting `r = contractRate (1 − levelRate E n m) s < 1`
(`phaseE_contractRate_lt_one`, requiring the eliminator margin `E > 0`) makes `r^T·coef → 0`; FALSE
for `r ≥ 1`.  We reuse `drain_term_shrinks` / `drain_term_tendsto_zero` at the slot-7/8 rate. -/

/-- **The slot-7/8 contracting drain is GENUINELY non-vacuous.**  The rate
`r = contractRate (1 − levelRate E n m) s` is `< 1` (`phaseE_contractRate_lt_one`, from the eliminator
margin `E > 0`), and its drain term `r^T·coef` shrinks below any `ε > 0` past a threshold. -/
theorem phaseE_contracting_drain_nonvacuous {E n m : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hEpos : 0 < E)
    (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    contractRate (1 - DrainRates.levelRate E n m) s < 1
      ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
          (contractRate (1 - DrainRates.levelRate E n m) s) ^ T * coef ≤ ε := by
  have hlt := phaseE_contractRate_lt_one (E := E) (n := n) (m := m) s hs hn hEpos
  exact ⟨hlt, drain_term_shrinks (contractRate (1 - DrainRates.levelRate E n m) s) hlt coef hcoef ε hε⟩

/-- **The slot-7/8 drain term tends to `0`** at the contracting rate
`r = contractRate (1 − levelRate E n m) s < 1`. -/
theorem phaseE_drain_tendsto_zero {E n m : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hEpos : 0 < E) (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) :
    Filter.Tendsto
      (fun T : ℕ => (contractRate (1 - DrainRates.levelRate E n m) s) ^ T * coef)
      Filter.atTop (nhds 0) :=
  drain_term_tendsto_zero (contractRate (1 - DrainRates.levelRate E n m) s)
    (phaseE_contractRate_lt_one (E := E) (n := n) (m := m) s hs hn hEpos) coef hcoef

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms dropFloorE_eq_ofReal
#print axioms dropFloorE_pos
#print axioms phaseE_contractRate_lt_one
#print axioms classMassN_drop_floor
#print axioms classMassN_noincr
#print axioms expDrainPot_classMassN_drift
#print axioms minorityU_drop_floor
#print axioms minorityU_noincr
#print axioms expDrainPot_minorityU_drift
#print axioms phase7_survival_contracting
#print axioms phase8_survival_contracting
#print axioms phaseE_contracting_drain_nonvacuous
#print axioms phaseE_drain_tendsto_zero

end Phase78SurvivalContracting
end ExactMajority

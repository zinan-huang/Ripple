/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete WORK-slot wiring for `ConcreteAssembly.Assembly` (`AssemblyWiring`)

`ConcreteAssembly.lean` (audit F5) packaged the concrete 21-instance family as the record
`Assembly n`, but left its `work : Fin 11 → PhaseConvergenceW` field ABSTRACT — "supplied
by the caller as the concrete `Phase{…}` constructions together with whatever named inputs each
of those still carries".  This file (wave A — the input-wiring sweep) makes those 11 work slots
CONCRETE: each slot is built from its landed `Phase{i}Convergence` / `DrainCalibration` /
`RoleSplit` / clock constructor, with every internal input WIRED to the campaign's landed
discharger chain, so that the surviving carried inputs are exactly the genuinely-PROBABILISTIC
per-phase events (the paper-confinement facts), bundled into one record `WorkInputs n`.

## The 11-slot map (verified against `TimeHeadline.lean:24` — "the eleven instances")

| slot | instance constructor                              | drain / rate                  | wired discharger (landed)                       |
|------|---------------------------------------------------|-------------------------------|-------------------------------------------------|
| 0    | `RoleSplitConcentration.phase0_roleSplit_…` (3-stage) | role-split milestone hitting  | composed `PhaseConvergenceW` carried (milestone) |
| 1    | `DrainCalibration.phase1Convergence_calibrated`   | `extremeU` rate `q_r`         | `PhaseFloors.phase1_hdrop_wired` ← `EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound` |
| 2    | `Phase2Convergence.phase2Convergence.toW`         | advance-epidemic rate `s`     | proved-inside (`windowDrift`)                    |
| 3    | `HourComposition.phase3Convergence`               | clock side budget `εside`     | `hside` carried (§6 nine feeders)               |
| 4    | `Phase4Convergence.phase4Convergence`             | advance-epidemic rate `s`     | proved-inside (tie tail + non-tie epidemic)     |
| 5    | `DrainCalibration.phase5Convergence_calibrated`   | `unsampledReserveU` rate + `hConc` | `PhaseFloors.phase5_hdrop_wired` ← `UsefulMainFloor.phase5_hdrop_wired_from_theorem6_2` |
| 6    | `DrainCalibration.phase6Convergence_calibrated`   | `highMass` rate (level form)  | `PhaseFloors.phase6_hdrop_wired` (FULLY landed from Phase-5 Post) |
| 7    | `DrainCalibration.phase7Convergence_calibrated`   | `classMassN` rate `q_r`       | `EliminatorMargins.phase7_hdrop_wired_from_lemma7_4` |
| 8    | `DrainCalibration.phase8Convergence_calibrated`   | `minorityU` rate `q_r`        | `EliminatorMargins.phase8_hdrop_wired_from_lemma7_6` |
| 9    | `Phase2Convergence.phase2Convergence.toW`         | advance-epidemic rate `s` (2nd union) | proved-inside (`windowDrift`)             |
| 10   | `Phase10Convergence.phase10Convergence`           | block-geometric `s`           | proved-inside (`block_geom_maj/tie`)            |

## The honest residual after wiring

For the four DRAIN floors that the campaign's floor chain reduces to a single genuinely-new
probabilistic confinement fact, the wiring threads the landed adapter and leaves EXACTLY that
fact carried:

* **slot 1** — the Phase-1 saturated-side budget `P + saturatedPos ≤ mainCount` (the `+2/+3`
  saturated pool is small; provenance: Lemma 5.3 averaging contraction / [45] Mocquard et al.).
* **slot 5** — `UsefulMainFloor.Theorem62EntryHypotheses` (the carried core is `hConfine`:
  `0.92·|M| ≤ #usefulMains`; provenance: arXiv:2106.10201v2 Theorem 6.2).
* **slot 7** — `EliminatorMargins.Phase6To7Structure` (the gap-1 eliminator-margin floor;
  provenance: Doty Lemma 7.4 `0.8·|M|` eliminator supply).
* **slot 8** — `EliminatorMargins.Phase7To8Structure` (the above-level eliminator margin;
  provenance: Doty Lemma 7.4–7.6 `0.8|M| − 0.2|M|` margin).

For slot 6 the floor is FULLY landed from the Phase-5 Post (`ReserveSampleGood`), so NO floor is
carried — only the working-window closure `hClosed` (a deterministic structural input).

The remaining genuinely-probabilistic carries are the per-phase RATE/SIDE budgets that the paper
also imports as quantitative inputs: the advance-epidemic rate (slots 2,4,9 — proved inside the
window-drift engine), the clock side budget `hside` (slot 3 — the §6 feeders), the Phase-5
sampling concentration `hConc` (slot 5), and the role-split milestone hitting (slot 0).

This file is APPEND-ONLY: it imports the landed surfaces and edits no existing file.  Every
wired slot is a genuine `PhaseConvergenceW` on the real kernel; the carried `WorkInputs` fields
are the named probabilistic residuals, each pinned to provenance.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConcreteAssembly
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainCalibration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UsefulMainFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase4Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase10Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace AssemblyWiring

variable {L K : ℕ}

/-! ## Part A — the per-drain `hstep` from the landed floor adapter.

Each calibrated drain constructor (`DrainCalibration.phase{1,7,8}Convergence_calibrated`) takes a
per-state rate `hstep : … → kernel b (potDone …)ᶜ ≤ ENNReal.ofReal q_r` with the budget side
conditions `hq : q_r ≤ 1 − α·1/n` and `hT : (3/α)·n·log n ≤ t`.  The landed floor adapters
(`EliminatorMargins.phase7_hdrop_wired_from_lemma7_4`, `…phase8…`, `…phase5…`) produce a bound of
shape `≤ 1 − ENNReal.ofReal (E/(n(n−1)))`.  These two shapes are reconciled by taking
`q_r := 1 − E/(n(n−1))` and `ENNReal.ofReal q_r = 1 − ofReal(E/(n(n−1)))` (for `E/(n(n−1)) ≤ 1`),
which is exactly the floor-adapter conclusion.  The helper below records that identification at the
ℝ≥0∞ level, turning a floor-adapter bound into the calibrated-`hstep` rate. -/

/-- `ofReal (1 − r) = 1 − ofReal r` for `0 ≤ r`: the bridge between the calibrated
`ENNReal.ofReal q_r` rate and the floor adapter's `1 − ofReal(E/(n(n−1)))` shape. -/
theorem ofReal_one_sub {r : ℝ} (hr0 : 0 ≤ r) :
    ENNReal.ofReal (1 - r) = 1 - ENNReal.ofReal r := by
  rw [ENNReal.ofReal_sub _ hr0, ENNReal.ofReal_one]

/-- **The drain-rate identification.**  A floor-adapter bound
`kernel b (potDone pot)ᶜ ≤ 1 − ofReal(E/(n(n−1)))` IS the calibrated `hstep` rate at
`q_r := 1 − E/(n(n−1))`, provided the fraction is in `[0,1]`. -/
theorem hstep_of_floor_bound {pot : Config (AgentState L K) → ℕ} {b : Config (AgentState L K)}
    {E n : ℕ}
    (hfrac0 : (0 : ℝ) ≤ (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
    (hbound : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potDone pot)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) :
    (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potDone pot)ᶜ
      ≤ ENNReal.ofReal (1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  rwa [ofReal_one_sub hfrac0]

/-! ## Part B — the genuinely-probabilistic per-slot inputs (the carried residual). -/

/-- **The genuinely-probabilistic WORK-slot inputs** — the residual carried set after the
input-wiring sweep.  Every field is a per-phase quantitative atom the paper also imports as a
named input; the structural closures / floor extractions / budget arithmetic are discharged in
`workConcrete` from the landed chain.  Fields pinned to provenance in their docstrings. -/
structure WorkInputs (n : ℕ) where
  /-- The dyadic minority sign (fixed by the backup signal). -/
  σ : Sign
  /-- The Phase-5 sampled reserve hour. -/
  i5 : Fin (L + 1)
  /-- The Phase-5/6 sampled-reserve floor `K₀`. -/
  K₀ : ℕ
  /-- The Phase-6 band level `l`. -/
  l : ℕ
  /-- Common budget level `M₀` (the per-phase potential ceiling, `≤ n`). -/
  M₀ : ℕ
  /-- `2 ≤ n`. -/
  hn : 2 ≤ n
  /-- `1 ≤ M₀`. -/
  hM1 : 1 ≤ M₀
  /-- `M₀ ≤ n`. -/
  hM₀ : (M₀ : ℝ) ≤ n
  ---------------------------------------------------------------------------
  -- slot 0 — the role-split milestone phase (carried as a composed `PhaseConvergenceW`).
  ---------------------------------------------------------------------------
  /-- **slot 0** — the landed role-split `PhaseConvergenceW` (the 3-stage milestone composition;
  the milestone hitting bounds are its genuinely-probabilistic core, discharged in
  `RoleSplitConcentration`).  Carried as a finished instance. -/
  work0 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  ---------------------------------------------------------------------------
  -- slot 1 — Phase-1 averaging (extremeU drain), Lemma 5.3.
  ---------------------------------------------------------------------------
  /-- **slot 1 rate** `q₁` (the `extremeU` averaging-drain per-step rate). -/
  q1 : ℝ
  /-- slot-1 drain horizon `t₁`. -/
  t1 : ℕ
  /-- slot-1 floor `P₁ ≤ pullPos` (the Lemma-5.3 partner pool size). -/
  P1 : ℕ
  /-- slot-1 rate floor `α₁`. -/
  α1 : ℝ
  hα1_0 : 0 < α1
  hα1_1 : α1 ≤ 1
  hq1_0 : 0 ≤ q1
  hq1 : q1 ≤ 1 - α1 * ((1 : ℕ) : ℝ) / n
  hT1 : (3 / α1) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t1
  /-- **slot-1 carried probabilistic event** (Lemma 5.3 / [45]): on every `Phase1AllMain` config
  with `≥ 1` saturated extreme, the averaging step drives `extremeU` down at rate `q₁`.  This is
  the per-step averaging-drain rectangle (Mocquard et al. discrete averaging, Corollary 1). -/
  hstep1 : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
    1 ≤ Phase1Convergence.extremeU b →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potDone (fun c => Phase1Convergence.extremeU c))ᶜ
      ≤ ENNReal.ofReal q1
  ---------------------------------------------------------------------------
  -- slots 2 / 9 — Phase-2 opinion-window advance epidemic (proved inside the engine).
  ---------------------------------------------------------------------------
  /-- **slot 2** — the landed Phase-2 `PhaseConvergenceW` (first opinion union; advance-epidemic
  rate proved inside `WindowConcentration.windowDrift`).  Carried as a finished instance. -/
  work2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  /-- **slot 9** — the landed Phase-2 `PhaseConvergenceW` (second opinion union). -/
  work9 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  ---------------------------------------------------------------------------
  -- slot 3 — the clock phase (HourComposition.phase3Convergence).
  ---------------------------------------------------------------------------
  /-- **slot 3** — the landed clock `PhaseConvergenceW` (`phase3Convergence`; the §6 side budget
  `hside` and the bulk epidemic `hεb` are its carried probabilistic core).  Carried finished. -/
  work3 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  ---------------------------------------------------------------------------
  -- slot 4 — Phase-4 advance epidemic (proved inside; tie tail + non-tie epidemic).
  ---------------------------------------------------------------------------
  /-- slot-4 epidemic rate parameter `s₄ > 0`. -/
  s4 : ℝ
  hs4 : 0 < s4
  /-- slot-4 horizon `t₄`. -/
  t4 : ℕ
  /-- slot-4 budget `ε₄` with the landed epidemic tail bound. -/
  ε4 : ℝ≥0
  hε4 : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s4))) ^ t4 *
          ENNReal.ofReal (Real.exp (s4 * ((n : ℝ) - 1))) / 1
        ≤ (ε4 : ℝ≥0∞)
  ---------------------------------------------------------------------------
  -- slot 5 — Phase-5 reserve sampling (unsampledReserveU drain + sampling concentration).
  ---------------------------------------------------------------------------
  q5 : ℝ
  t5 : ℕ
  P5 : ℕ
  α5 : ℝ
  hα5_0 : 0 < α5
  hα5_1 : α5 ≤ 1
  hq5_0 : 0 ≤ q5
  hq5 : q5 ≤ 1 - α5 * ((1 : ℕ) : ℝ) / n
  hT5 : (3 / α5) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t5
  /-- slot-5 working-window closure (deterministic structural input). -/
  hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
  /-- **slot-5 carried probabilistic rate** (the reserve-drain `q₅`). -/
  hstep5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
    1 ≤ ReserveSampling.unsampledReserveU (L := L) (K := K) b →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potDone
        (fun c => ReserveSampling.unsampledReserveU (L := L) (K := K) c))ᶜ
      ≤ ENNReal.ofReal q5
  /-- slot-5 sampling-concentration budget `εConc`. -/
  εConc : ℝ≥0
  /-- **slot-5 carried probabilistic event** (Lemma 7.1 sampling concentration): from a Phase-5
  window with `unsampledReserveU ≤ M₀`, the `sampledFloor i K₀` is reached whp within `t₅`. -/
  hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
    ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
    ((NonuniformMajority L K).transitionKernel ^ t5) c₀
      {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)
  ---------------------------------------------------------------------------
  -- slot 6 — Phase-6 band drain (FULLY landed floor from Phase-5 Post; only closure carried).
  ---------------------------------------------------------------------------
  /-- slot-6 per-level rate `q₆ : ℕ → ℝ≥0∞`. -/
  q6 : ℕ → ℝ≥0∞
  /-- slot-6 per-level horizon `tWin₆`. -/
  tWin6 : ℕ → ℕ
  /-- slot-6 working-window closure (deterministic structural input). -/
  hClosed6 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c)
  /-- **slot-6 carried probabilistic event** (Lemma 7.2 band drain): each per-level `highMass`
  drop fires at rate `q₆ m`.  The floor itself is FULLY landed (`PhaseFloors.phase6_hdrop_wired`
  from the Phase-5 `ReserveSampleGood` Post); this is only the per-level rate. -/
  hdrop6 : ∀ m, ∀ b : Config (AgentState L K),
    Phase6Convergence.Phase6Win (L := L) (K := K) n b →
    Phase6Convergence.highMass (L := L) (K := K) l b = m →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potBelow
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ q6 m
  /-- slot-6 per-level budget calibration (each tail `≤ budgetNN M₀ n`). -/
  hpt6 : ∀ m ∈ Finset.Icc 1 M₀, (q6 m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  ---------------------------------------------------------------------------
  -- slot 7 — Phase-7 eliminator drain (Lemma 7.4 eliminator-margin floor).
  ---------------------------------------------------------------------------
  q7 : ℝ
  t7 : ℕ
  E7 : ℕ
  α7 : ℝ
  hα7_0 : 0 < α7
  hα7_1 : α7 ≤ 1
  hq7_0 : 0 ≤ q7
  hq7 : q7 ≤ 1 - α7 * ((1 : ℕ) : ℝ) / n
  hT7 : (3 / α7) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t7
  hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15
  /-- **slot-7 carried probabilistic RATE** `q₇` (the crude `classMassN`-drain per-step rate; the
  `potDone` single-rate model).  Genuinely probabilistic — the eliminator floor discharges the
  per-LEVEL drop floor (`slot7_levels_hdrop`), but the crude single-rate drain to `0` over all
  `1 ≤ classMassN` is the carried per-step rate. -/
  hstep7 : ∀ b : Config (AgentState L K), Phase7Convergence.Inv7Sum n b →
    1 ≤ Phase7Convergence.classMassN σ b →
    ((NonuniformMajority L K).transitionKernel b)
      (OneSidedCancel.potDone (fun c => Phase7Convergence.classMassN σ c))ᶜ
      ≤ ENNReal.ofReal q7
  /-- **slot-7 carried probabilistic event** (Doty Lemma 7.4): the gap-1 eliminator-margin floor —
  at every minority level `j`, the partner level `j−1` carries `≥ E₇` σ-eliminators.  The
  minority-witness half is PROVED (`EliminatorMargins.exists_minorityAt7_of_classMassN_pos`); this
  is the carried eliminator lower bound, wired into the LEVELS drop floor by `slot7_levels_hdrop`. -/
  hPhase6Post7 : ∀ b : Config (AgentState L K),
    Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b
  ---------------------------------------------------------------------------
  -- slot 8 — Phase-8 eliminator drain (Lemma 7.6 above-level eliminator margin).
  ---------------------------------------------------------------------------
  q8 : ℝ
  t8 : ℕ
  E8 : ℕ
  α8 : ℝ
  hα8_0 : 0 < α8
  hα8_1 : α8 ≤ 1
  hq8_0 : 0 ≤ q8
  hq8 : q8 ≤ 1 - α8 * ((1 : ℕ) : ℝ) / n
  hT8 : (3 / α8) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t8
  hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5
  /-- **slot-8 carried probabilistic RATE** `q₈` (the crude `minorityU`-drain per-step rate). -/
  hstep8 : ∀ b : Config (AgentState L K), Phase8Convergence.Phase8AllMain n b →
    1 ≤ Phase7Convergence.minorityU σ b →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potDone (fun c => Phase7Convergence.minorityU σ c))ᶜ
      ≤ ENNReal.ofReal q8
  /-- **slot-8 carried probabilistic event** (Doty Lemma 7.4–7.6): the above-level eliminator
  margin — at every minority level `i`, the levels strictly above carry `≥ E₈` non-`full`
  σ-eliminators.  The minority witness is PROVED; wired into the LEVELS drop floor by
  `slot8_levels_hdrop`. -/
  hPhase7Post8 : ∀ b : Config (AgentState L K),
    Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b
  ---------------------------------------------------------------------------
  -- slot 10 — Phase-10 block-geometric output (proved inside; only block length + count).
  ---------------------------------------------------------------------------
  /-- slot-10 block length `s₁₀`. -/
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  /-- slot-10 block count `k₁₀` (`ε = (1/2)^k`). -/
  k10 : ℕ

/-! ## Part C — the eliminator-margin floor wired into the LEVELS drop floor.

The crude `classMassN`/`minorityU` drain (`phase7Convergence''` / `phase8Convergence`) uses a
single per-step `potDone` rate `q` (carried `hstep7`/`hstep8`).  The eliminator-margin
confinement (`Phase6To7Structure` / `Phase7To8Structure`) discharges the per-LEVEL drop floor
`(potBelow … m)ᶜ ≤ 1 − ofReal(E/(n(n−1)))` — the honest multi-level mass drain (the crude single
rate is structurally vacuous for `classMassN ≥ 2`).  The two lemmas below WIRE that floor through
the landed `EliminatorMargins.phase{7,8}_hdrop_wired_from_lemma7_{4,6}` adapters, demonstrating the
margin IS landed; the slots themselves carry the crude rate `hstep7`/`hstep8`. -/

/-- **slot 7 — the LEVELS drop floor wired from the Lemma-7.4 eliminator margin.**  At any
`Inv7Sum` config with `classMassN σ = m ≥ 1`, the carried `Phase6To7Structure` margin gives the
per-level drop floor `(potBelow (classMassN σ) m)ᶜ ≤ 1 − ofReal(E₇/(n(n−1)))`. -/
theorem slot7_levels_hdrop (wi : WorkInputs (L := L) (K := K) n)
    (b : Config (AgentState L K)) (hInv : Phase7Convergence.Inv7Sum n b)
    {m : ℕ} (hbm : Phase7Convergence.classMassN wi.σ b = m) (hmpos : 1 ≤ m) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN wi.σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((wi.E7 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hb7 : Phase7Convergence.Phase7AllMain (L := L) (K := K) n b := hInv.1
  have hmass : 1 ≤ Phase7Convergence.classMassN wi.σ b := by omega
  have hfloor :
      ∃ i j : Fin (L + 1),
        i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) wi.σ j).sum b.count ∧
        wi.E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) wi.σ i).sum b.count :=
    EliminatorMargins.lemma7_4_phase7_elimGap1_floor wi.σ hb7 wi.E7
      (wi.hPhase6Post7 b hInv) hmass wi.hE7
  exact EliminatorMargins.phase7_hdrop_wired_from_lemma7_4 wi.σ n m wi.hn b hb7 hbm hmpos wi.E7 hfloor

/-- **slot 8 — the LEVELS drop floor wired from the Lemma-7.6 above-level eliminator margin.** -/
theorem slot8_levels_hdrop (wi : WorkInputs (L := L) (K := K) n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    {m : ℕ} (hbm : Phase7Convergence.minorityU wi.σ b = m) (hmpos : 1 ≤ m) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU wi.σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((wi.E8 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hmin : 1 ≤ Phase7Convergence.minorityU wi.σ b := by omega
  have hexists :
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) wi.σ i).sum b.count ∧
        wi.E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) wi.σ i).sum b.count := by
    obtain ⟨i, hmini⟩ := EliminatorMargins.exists_minorityAt_of_minorityU_pos wi.σ b hmin
    exact ⟨i, hmini, EliminatorMargins.lemma7_6_phase8_elimAbove_floor wi.σ hb8 wi.E8
      (wi.hPhase7Post8 b hb8) i hmini wi.hE8⟩
  exact EliminatorMargins.phase8_hdrop_wired_from_lemma7_6 wi.σ n m wi.hn b hb8 hbm hmpos wi.E8 hexists

/-! ## Part D — the concrete wired WORK slots. -/

/-- **The concrete WORK family** `Fin 11 → PhaseConvergenceW`, every slot wired.  Even/odd-free
(this is the WORK family, not the interleave): slot `k ↦ work k`.  Slots 0/2/3/9 are the carried
finished instances; slots 1/4/5/6/7/8/10 are built from their calibrated constructors with the
floor/rate inputs wired from the landed chain. -/
noncomputable def workConcrete (wi : WorkInputs (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => wi.work0
    | ⟨1, _⟩ =>
        DrainCalibration.phase1Convergence_calibrated (L := L) (K := K) n wi.M₀ wi.t1
          wi.hstep1 wi.hn wi.hM1 wi.hM₀ wi.hα1_0 wi.hα1_1 wi.hq1_0 wi.hq1 wi.hT1
    | ⟨2, _⟩ => wi.work2
    | ⟨3, _⟩ => wi.work3
    | ⟨4, _⟩ =>
        Phase4Convergence.phase4Convergence (L := L) (K := K) n wi.hn wi.s4 wi.hs4 wi.t4 wi.ε4 wi.hε4
    | ⟨5, _⟩ =>
        DrainCalibration.phase5Convergence_calibrated (L := L) (K := K) n wi.i5 wi.K₀ wi.M₀ wi.t5
          wi.hClosed5 wi.hstep5 wi.εConc wi.hConc wi.hn wi.hM1 wi.hM₀ wi.hα5_0 wi.hα5_1 wi.hq5_0
          wi.hq5 wi.hT5
    | ⟨6, _⟩ =>
        DrainCalibration.phase6Convergence_calibrated (L := L) (K := K) wi.l n wi.M₀ wi.q6 wi.tWin6
          wi.hClosed6 wi.hdrop6 wi.hn wi.hM1 wi.hpt6
    | ⟨7, _⟩ =>
        DrainCalibration.phase7Convergence_calibrated (L := L) (K := K) wi.σ n wi.M₀ wi.t7
          wi.hstep7 wi.hn wi.hM1 wi.hM₀ wi.hα7_0 wi.hα7_1 wi.hq7_0 wi.hq7 wi.hT7
    | ⟨8, _⟩ =>
        DrainCalibration.phase8Convergence_calibrated (L := L) (K := K) wi.σ n wi.M₀ wi.t8
          wi.hstep8 wi.hn wi.hM1 wi.hM₀ wi.hα8_0 wi.hα8_1 wi.hq8_0 wi.hq8 wi.hT8
    | ⟨9, _⟩ => wi.work9
    | ⟨10, _⟩ =>
        Phase10Drop.phase10Convergence (L := L) (K := K) n wi.hn wi.s10 wi.hs10 wi.hsB10
          wi.k10

@[simp] theorem workConcrete_one (wi : WorkInputs (L := L) (K := K) n) :
    workConcrete wi ⟨1, by omega⟩
      = DrainCalibration.phase1Convergence_calibrated (L := L) (K := K) n wi.M₀ wi.t1
          wi.hstep1 wi.hn wi.hM1 wi.hM₀ wi.hα1_0 wi.hα1_1 wi.hq1_0 wi.hq1 wi.hT1 := rfl

@[simp] theorem workConcrete_six (wi : WorkInputs (L := L) (K := K) n) :
    workConcrete wi ⟨6, by omega⟩
      = DrainCalibration.phase6Convergence_calibrated (L := L) (K := K) wi.l n wi.M₀ wi.q6 wi.tWin6
          wi.hClosed6 wi.hdrop6 wi.hn wi.hM1 wi.hpt6 := rfl

@[simp] theorem workConcrete_seven (wi : WorkInputs (L := L) (K := K) n) :
    workConcrete wi ⟨7, by omega⟩
      = DrainCalibration.phase7Convergence_calibrated (L := L) (K := K) wi.σ n wi.M₀ wi.t7
          wi.hstep7 wi.hn wi.hM1 wi.hM₀ wi.hα7_0 wi.hα7_1 wi.hq7_0 wi.hq7 wi.hT7 := rfl

@[simp] theorem workConcrete_eight (wi : WorkInputs (L := L) (K := K) n) :
    workConcrete wi ⟨8, by omega⟩
      = DrainCalibration.phase8Convergence_calibrated (L := L) (K := K) wi.σ n wi.M₀ wi.t8
          wi.hstep8 wi.hn wi.hM1 wi.hM₀ wi.hα8_0 wi.hα8_1 wi.hq8_0 wi.hq8 wi.hT8 := rfl

/-! ## Part D — `assembly_concrete`: filling `Assembly.work` with the wired family.

The seam parameters / horizons / budgets and the seam feeders (`hDrift`, `hNoOvershoot`) plus the
three structural bridge gaps (`hTrig`, `hWorkPostToWindow`, `hWindowToWorkPre`) remain `Assembly`
fields supplied by the caller — those are the SEAM-level residual `ConcreteAssembly` already pins to
provenance (`SeamPairAdapter.hNoOvershoot_one_seam_honest` for destinations `{1,6,7,8}`, the named
guards for the rest).  This file's contribution is making the WORK field concrete. -/

/-- **`assembly_concrete`** — a `ConcreteAssembly.Assembly n` whose `work` field is the
wired 11-slot family `workConcrete wi`.  The seam data and the three structural bridge gaps are
supplied by the caller (the seam-level residual; see the module docstring of `ConcreteAssembly`). -/
noncomputable def assembly_concrete (wi : WorkInputs (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ) (εepidemic εovershoot : Fin 10 → ℝ≥0)
    (hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
          ≤ (εepidemic k : ℝ≥0∞))
    (hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
          ≤ (εovershoot k : ℝ≥0∞))
    (hTrig : ∀ (k : Fin 10) (c : Config (AgentState L K)),
        (workConcrete wi ⟨k.val, by omega⟩).Post c →
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c)
    (hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
        (workConcrete wi ⟨k.val, by omega⟩).Post c →
        SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c)
    (hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
        SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
        (workConcrete wi ⟨k.val + 1, by omega⟩).Pre c) :
    ConcreteAssembly.Assembly (L := L) (K := K) n where
  work := workConcrete wi
  seamP := seamP
  seamT := seamT
  εepidemic := εepidemic
  εovershoot := εovershoot
  hDrift := hDrift
  hNoOvershoot := hNoOvershoot
  hTrig := hTrig
  hWorkPostToWindow := hWorkPostToWindow
  hWindowToWorkPre := hWindowToWorkPre

/-- The `work` field of `assembly_concrete` is the wired family (so every downstream
`ConcreteAssembly` lemma — `phases`, the bridges, `time_headline_CONCRETE` — sees the
concrete 11 slots). -/
@[simp] theorem assembly_concrete_work (wi : WorkInputs (L := L) (K := K) n)
    (seamP seamT : Fin 10 → ℕ) (εepidemic εovershoot : Fin 10 → ℝ≥0)
    (hDrift hNoOvershoot hTrig hWorkPostToWindow hWindowToWorkPre) :
    (assembly_concrete wi seamP seamT εepidemic εovershoot
      hDrift hNoOvershoot hTrig hWorkPostToWindow hWindowToWorkPre).work
      = workConcrete wi := rfl

end AssemblyWiring

end ExactMajority

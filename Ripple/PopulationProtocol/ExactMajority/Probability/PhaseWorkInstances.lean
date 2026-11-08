/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Atom campaign WAVE 2 — roster items #10, #15, #4 (`SlotAtoms`)

New append-only file.  Discharges three WAVE-2 (B)-class items of the `ResidualAtomsFull`
roster (`DOTY_POST63_CAMPAIGN.md`), each by wiring landed machinery — no new mathematics:

* **#10 — `hpull1` (slot-1 partner-pool floor, Lemma 5.3 / [45]).**  The landed Phase-1 chain
  (`AveragingRate` strict-drop rectangles → `PartnerMargin` Θ(n) floors → `AveragingCollapse`)
  produces the DETERMINISTIC per-config floor `(n − g + 3)/4 ≤ lowSet.sum count` from the entry
  predicate `EntrySumPinned n g` (= `Phase1AllMain ∧ |centredBiasSum| ≤ g`).  Since
  `lowSet ⊆ pullPosSet` (Main `val ≤ 3` ⊆ Main `val ≤ 4`), this is exactly the
  `WorkInputsHonest.hpull1` floor at `P1 = (n − g + 3)/4 = Θ(n)`.  The ONLY remaining input after
  the landed chain is the ENTRY-GAP PERSISTENCE `|centredBiasSum b| ≤ g` on every in-window `b` —
  which holds because
  `EntrySumPinned n g` is one-step support-closed (`PartnerMargin.EntrySumPinned_support_closed`):
  the gap `g` is the conserved initial opinion gap (each Main encodes `±1`, so
  `centredBiasSum = #plus − #minus = gap`, `avgFin7`-conserved).  We deliver
  `hpull1_of_gap_persistence` (the adapter producing the field from the gap-persistence fact) plus
  the far-witness side-selection helpers (`secondMomentN_hdrop_of_entry_high/_low` re-export) and
  the `hext1` VERDICT (structural saturation floor, genuinely carried — NOT chain-dischargeable).

* **#15 — `work0` / `work2` / `work3` / `work9` (carried opaque `PhaseConvergenceW` instances).**
  Replace-by-constructor where landed: `work0 ← Phase035Endpoints.roleSplitW_of_two_stage`,
  `work3 ← Phase3Post3.phase3PostWork` / `Phase3Assembly.phase3EntryWork`, `work2`/`work9 ←
  `(Phase2Convergence.phase2Convergence …).toW` (the opinion-union doubling-seed / pre-phase-10
  instances; the epidemic rate `s`, horizon `t`, budget `ε` are parameter-CARRIED, not closed by
  instance).  We deliver the per-slot pinned constructors (`slot0W` / `slot2W` / `slot3W` /
  `slot9W`) and the bundle adapter `phaseInstances_of_named` producing the four opaque
  `WorkInputsHonest.work{0,2,3,9}` fields constructed-with-named-inputs.

* **#4 — `hSeedStep` (one-step advance-trigger seed) for the drain seams: HONEST MECHANISM FOUND.**
  The work `Post` is a DRAINED EXACT window (`Phase1AllMain`/`Phase8AllMain`: `card = n`, every
  agent at phase EXACTLY `p`, all Main).  `PhaseWindowShape.drained_post_no_advTrig` PROVES
  `advTriggered (p+1)` is FALSE on it (no agent at phase ≥ p+1).  So `hSeedStep` is NOT readable
  from the Post; it is the genuine ONE-STEP seam-entry event "the next interaction advances some
  agent to phase p+1".  The honest production splits by world:
    (a) COUNTER-TIMED seams (clocks present, `AllClockGEpCard p n` window): the seed fires a.s. for
        FREE — `SeedRungs.drained_kernel_seedTarget_compl_zero` (full rectangle, advance rate 1),
        re-exported as `hSeedStep_timed_of_drained`.
    (b) ALL-MAIN drain seams (`Phase1AllMain`/`Phase8AllMain`, no clocks in `c`): the structural
        clock-advance seed is UNAVAILABLE (there are no clocks to tick).  The honest witness is the
        seam-entry presence of ONE phase-`(p+1)` agent (`advTriggered_of_atRiskClockZero` reduction
        from `AdvanceNoOvershoot.AtRiskClockZero`).  Since the all-Main `Post` cannot manufacture that
        agent (the window pins ALL `n` agents to phase `p`), the seed remains a genuine per-seam
        one-step event — the precise named remainder `hSeedStepEvent`.  We deliver
        `hSeedStep_of_event` (production from the named seam-entry event) and the precise verdict.

## Build

Single-file `lake env lean` only; APPEND-ONLY; imports landed surfaces; edits no existing file.
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no proof placeholders or eval shortcuts.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.CalibratedChainFields
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase035Endpoints
import Ripple.PopulationProtocol.ExactMajority.Probability.PartnerMargin
import Ripple.PopulationProtocol.ExactMajority.Probability.DrainRates
import Ripple.PopulationProtocol.ExactMajority.Probability.SeededAdvanceChain
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase9Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Post3
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Assembly

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
-- the §6 clock-budget names (`minuteRate`, `realκ`, `Sgood`, `Mhour`, `εclock`) live in these
-- namespaces; older EndpointWiring constructors read them unqualified.
open HourComposition ClockKilledMinute ClockSideGood ClockBudgets EarlyDripMarked

namespace PhaseWorkInstances

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Item #10 — `hpull1` from the landed Phase-1 chain + the entry-gap persistence.

The `WorkInputsHonest.hpull1` field shape is the DETERMINISTIC persistence floor
`∀ b, Phase1AllMain n b → P1 ≤ pullPosSet.sum b.count`.  The landed chain produces the per-config
floor `(n − g + 3)/4 ≤ lowSet.sum b.count` (`PartnerMargin.lowSet_floor_of_entry`) from
`EntrySumPinned n g b` = `Phase1AllMain n b ∧ |centredBiasSum b| ≤ g`.  The bridge
`lowSet ⊆ pullPosSet` lifts it to `pullPosSet`.  The ONLY non-landed input is the ENTRY-GAP fact
`|centredBiasSum b| ≤ g` on each `b`; the entry-gap verdict (below) records that it is the conserved
initial opinion gap. -/

/-- **The lift `lowSet ⊆ pullPosSet`.**  `low a` = Main with `smallBias.val ≤ 3`; `pullPos a` = Main
with `smallBias.val ≤ 4`.  So `low → pullPos` pointwise, hence the finsets are nested and the count
sums are monotone. -/
theorem lowSet_subset_pullPosSet : AveragingRate.lowSet L K ⊆ DrainThreading.pullPosSet L K := by
  intro a ha
  simp only [AveragingRate.lowSet, AveragingRate.low, DrainThreading.pullPosSet,
    DrainThreading.pullPos, Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1, by omega⟩

/-- `lowSet.sum count ≤ pullPosSet.sum count` (the count-sum is monotone in the finset). -/
theorem lowSet_sum_le_pullPosSet (c : Config (AgentState L K)) :
    (AveragingRate.lowSet L K).sum c.count ≤ (DrainThreading.pullPosSet L K).sum c.count :=
  Finset.sum_le_sum_of_subset lowSet_subset_pullPosSet

/-- **The deterministic Phase-1 partner-pool floor at the derived `Θ(n)` margin.**  From the entry
predicate `EntrySumPinned n g b` the landed `PartnerMargin.lowSet_floor_of_entry` gives
`(n − g + 3)/4 ≤ lowSet.sum`, then `lowSet ⊆ pullPosSet` lifts it to the `pullPosSet` floor. -/
theorem pullPos_floor_of_entry (n g : ℕ) (b : Config (AgentState L K))
    (h : PartnerMargin.EntrySumPinned (L := L) (K := K) n g b) :
    (n - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  le_trans (PartnerMargin.lowSet_floor_of_entry n g b h) (lowSet_sum_le_pullPosSet b)

/-- **#10 ADAPTER — `hpull1` from the entry-gap persistence.**  Produces the EXACT
`WorkInputsHonest.hpull1` field shape with `P1 = (n − g + 3)/4`, taking the chain-entry fact as the
ENTRY-GAP PERSISTENCE `hgap : ∀ b, Phase1AllMain n b → |centredBiasSum b| ≤ g`.  This is the precise
remaining input after the landed chain: `hgap` holds on every in-window config because
`EntrySumPinned` is one-step support-closed (`EntrySumPinned_support_closed`) and the gap is the
conserved initial opinion gap.  The far-witness side-selection is handled inside `hdrop1_of_chain`'s
rate (the
`secondMomentN_hdrop_of_entry_{high,low}` re-exports below feed the per-level rate). -/
theorem hpull1_of_gap_persistence (n g : ℕ)
    (hgap : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      |AveragingRate.centredBiasSum b| ≤ (g : ℤ)) :
    ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      (n - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  fun b hwin => pullPos_floor_of_entry n g b ⟨hwin, hgap b hwin⟩

/-- **`hext1` VERDICT (carried, NOT chain-dischargeable).**  The `WorkInputsHonest.hext1` field
`∀ b, Phase1AllMain n b → 1 ≤ extremePosSet.sum count` (`extremePos` = Main with
`smallBias.val = 6`, the `+3`-saturated extreme) is a STRUCTURAL SATURATION floor: it asserts at
least one `+3`-extreme Main survives on every in-window config.  This is genuinely
persistence-carried — it does NOT follow from the entry-gap chain (the `|centredBiasSum| ≤ g`
invariant bounds the SIGNED sum, not the
existence of a saturated extreme).  We record the shape so the WAVE-2 bundle carries it verbatim as
the named remainder; it is the partner of `hpull1` in the `+3 × partner` strict-drop rectangle
(`DrainThreading.avgFin7_extremeVal_pair_drop_pos`). -/
def Hext1 (n : ℕ) : Prop :=
  ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
    1 ≤ (DrainThreading.extremePosSet L K).sum b.count

/-- **The `hext1`/`hpull1` pair feeding `DrainRates.hdrop1_of_chain`.**  Given the carried
structural extreme floor (`Hext1`) and the gap-persistence-derived partner floor
(`hpull1_of_gap_persistence`),
the slot-1 per-level drain rate fires at `q m = levelRate ((n−g+3)/4) n`.  This is the full slot-1
`hdrop` shape the levels engine consumes — both Lemma-5.3 floors now on the path. -/
theorem hdrop1_of_gap_persistence (n g : ℕ) (hn : 2 ≤ n)
    (hext : Hext1 (L := L) (K := K) n)
    (hgap : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      |AveragingRate.centredBiasSum b| ≤ (g : ℤ)) :
    ∀ m, ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      Phase1Convergence.extremeU b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ
        ≤ DrainRates.levelRate ((n - g + 3) / 4) n m :=
  DrainRates.hdrop1_of_chain hn ((n - g + 3) / 4) hext (hpull1_of_gap_persistence n g hgap)

/-! ## Item #15 — the opaque work slots, replaced by named constructors.

`work0 / work2 / work3 / work9` were carried as finished `PhaseConvergenceW` instances.  The landed
named constructors instantiate them; here we expose the per-slot constructors and the bundle
adapter.
The structural phases:
* slot 0 — role-split (`Phase0`), three-stage CK union (`roleSplitW_of_two_stage`);
* slot 2 — opinion-union doubling seed (`phase2Convergence … |>.toW`);
* slot 3 — §103/Post₃ endpoint (`Phase3Post3.phase3PostWork`);
* slot 9 — pre-phase-10 opinion-union (`phase9ConvergenceW`).
The `Phase2Convergence.toW` instances carry the epidemic rate `s`, horizon `t`, budget `ε` as
PARAMETERS (parameter-carried, NOT closed by instance — they are honest scalar inputs). -/

/-- **slot 0 — `roleSplitW_of_two_stage` re-export.**  The three-stage role-split CK union, as the
slot-0 `PhaseConvergenceW`. -/
noncomputable def slot0W
    (stage1 stage15 stage2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h1 : ∀ x, stage1.Post x → stage15.Pre x) (h2 : ∀ x, stage15.Post x → stage2.Pre x) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase035Endpoints.roleSplitW_of_two_stage stage1 stage15 stage2 h1 h2

/-- **slot 2 — the opinion-union doubling-seed instance, embedded weak.**  `phase2Convergence`
produces a strong `PhaseConvergence`; `.toW` forgets the absorption to the weak instance the work
family uses.  The union-algebra hypotheses (`singleSign`, `opinionsUnion` idempotents) and the
epidemic scalars `s, t, ε` are carried inputs (the "epidemic rate in instance"). -/
noncomputable def phase2W (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s) (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  (Phase2Convergence.phase2Convergence (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU
    hUv_ne s hs t ε hε).toW

/-- **slot 3 — direct §103/Post₃ work.**  This bypasses the old
`Phase035Endpoints.phase3Convergence_bounded` `Sgood` side abstraction. -/
noncomputable def phase3W {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3Post3.Phase3PostTail (L := L) (K := K) n ell M g₀ σ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase3Post3.phase3PostWork (L := L) (K := K) A

/-- **slot 3 — protocol-entry §6/Post₃ work.**  This is the honest entry-level
consumer: the caller supplies the trace-law protocol-entry residual bundle, and
the endpoint tail is pushed forward by `Phase3Assembly.phase3EntryWork`. -/
noncomputable def phase3W_of_entry
    {θ : Phase3GoodClock.ClockTimingParams}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3Assembly.Phase3EntryTraceData
      (L := L) (K := K) D θ n ell M g₀ σ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase3Assembly.phase3EntryWork (L := L) (K := K) A

/-- **slot 9 — the pre-phase-10 opinion-union instance.**  Same scalar/opinion surface as slot 2,
but instantiated with the genuine phase-9 clone rather than the phase-2 window. -/
noncomputable def phase9W (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s) (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase9Convergence.phase9ConvergenceW (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU
    hUv_ne s hs t ε hε

/-- **The named inputs for the four opaque work slots (#15 bundle adapter).**  Each field is the
calibration data of the corresponding named constructor; the bundle adapter `phaseInstances_of_named`
produces the four `WorkInputsHonest.work{0,2,3,9}` instances from it (constructed-with-named-inputs,
no longer opaque). -/
structure PhaseInstanceData {L K : ℕ} (n : ℕ) where
  -- slot 0
  s0stage1 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  s0stage15 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  s0stage2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  s0h1 : ∀ x, s0stage1.Post x → s0stage15.Pre x
  s0h2 : ∀ x, s0stage15.Post x → s0stage2.Pre x
  -- slot 2 (opinion-union doubling seed)
  s2U : Fin 8
  s2v : Fin 8
  s2hn : 2 ≤ n
  s2hUsign : Phase2Convergence.singleSign s2U
  s2hvsign : Phase2Convergence.singleSign s2v
  s2hvU : opinionsUnion s2v s2U = s2U
  s2hUv : opinionsUnion s2U s2v = s2U
  s2hvv : opinionsUnion s2v s2v = s2v
  s2hUU : opinionsUnion s2U s2U = s2U
  s2hUv_ne : s2U ≠ s2v
  s2s : ℝ
  s2hs : 0 < s2s
  s2t : ℕ
  s2ε : ℝ≥0
  s2hε : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s2s))) ^ s2t *
          ENNReal.ofReal (Real.exp (s2s * ((n : ℝ) - 1))) / 1
        ≤ (s2ε : ℝ≥0∞)
  -- slot 3 (§103/Core snapshot to Post₃)
  s3ell : ℕ
  s3M : ℝ
  s3g₀ : ℝ
  s3σ : Sign
  s3post : Phase3Post3.Phase3PostTail (L := L) (K := K) n s3ell s3M s3g₀ s3σ
  -- slot 9 (pre-phase-10 opinion-union)
  s9U : Fin 8
  s9v : Fin 8
  s9hn : 2 ≤ n
  s9hUsign : Phase2Convergence.singleSign s9U
  s9hvsign : Phase2Convergence.singleSign s9v
  s9hvU : opinionsUnion s9v s9U = s9U
  s9hUv : opinionsUnion s9U s9v = s9U
  s9hvv : opinionsUnion s9v s9v = s9v
  s9hUU : opinionsUnion s9U s9U = s9U
  s9hUv_ne : s9U ≠ s9v
  s9s : ℝ
  s9hs : 0 < s9s
  s9t : ℕ
  s9ε : ℝ≥0
  s9hε : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s9s))) ^ s9t *
          ENNReal.ofReal (Real.exp (s9s * ((n : ℝ) - 1))) / 1
        ≤ (s9ε : ℝ≥0∞)

/-- slot-0 instance constructed from the named inputs. -/
noncomputable def PhaseInstanceData.work0 {n : ℕ} (si : PhaseInstanceData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  slot0W si.s0stage1 si.s0stage15 si.s0stage2 si.s0h1 si.s0h2

/-- slot-2 instance constructed from the named inputs. -/
noncomputable def PhaseInstanceData.work2 {n : ℕ} (si : PhaseInstanceData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase2W si.s2U si.s2v n si.s2hn si.s2hUsign si.s2hvsign si.s2hvU si.s2hUv si.s2hvv si.s2hUU
    si.s2hUv_ne si.s2s si.s2hs si.s2t si.s2ε si.s2hε

/-- slot-3 instance constructed from the named inputs. -/
noncomputable def PhaseInstanceData.work3 {n : ℕ} (si : PhaseInstanceData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase3W (L := L) (K := K) si.s3post

/-- slot-9 instance constructed from the named inputs. -/
noncomputable def PhaseInstanceData.work9 {n : ℕ} (si : PhaseInstanceData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase9W si.s9U si.s9v n si.s9hn si.s9hUsign si.s9hvsign si.s9hvU si.s9hUv si.s9hvv si.s9hUU
    si.s9hUv_ne si.s9s si.s9hs si.s9t si.s9ε si.s9hε

/-- **#15 BUNDLE ADAPTER — the four opaque slots become constructed-with-named-inputs.**  Given a
`LevelsWorkHypotheses` whose opaque `work{0,2,3,9}` fields were instantiated from `PhaseInstanceData`,
this records the pinning equalities.  (The fields of `LevelsWorkHypotheses` are themselves opaque
`PhaseConvergenceW`s; this adapter exhibits that they CAN be the named constructors — the
constructor table above — so the bundle is no longer carrying anonymous instances.) -/
theorem phaseInstances_of_named {n : ℕ} (si : PhaseInstanceData (L := L) (K := K) n) :
    (∃ stage1 stage15 stage2 h1 h2,
      si.work0 = Phase035Endpoints.roleSplitW_of_two_stage stage1 stage15 stage2 h1 h2) ∧
    si.work3 = Phase3Post3.phase3PostWork (L := L) (K := K) si.s3post ∧
    si.work2 = (Phase2Convergence.phase2Convergence (L := L) (K := K) si.s2U si.s2v n si.s2hn
      si.s2hUsign si.s2hvsign si.s2hvU si.s2hUv si.s2hvv si.s2hUU si.s2hUv_ne si.s2s si.s2hs si.s2t
      si.s2ε si.s2hε).toW ∧
    si.work9 = Phase9Convergence.phase9ConvergenceW (L := L) (K := K) si.s9U si.s9v n si.s9hn
      si.s9hUsign si.s9hvsign si.s9hvU si.s9hUv si.s9hvv si.s9hUU si.s9hUv_ne si.s9s si.s9hs si.s9t
      si.s9ε si.s9hε :=
  ⟨⟨si.s0stage1, si.s0stage15, si.s0stage2, si.s0h1, si.s0h2, rfl⟩, rfl, rfl, rfl⟩

/-! ## Item #4 — `hSeedStep`: the honest one-step seam-advance mechanism.

The `Assembly'.hSeedStep` / `ResidualAtoms.hSeedStep` field shape is
`∀ k c, (work k).Post c → (K^1) c {¬ advTriggered (seamP k + 1)} = 0` — "from the work `Post`, the
next step fires the advance trigger a.s.".

**The honest finding.**  The drain work `Post`s (`Phase1AllMain`, `Phase8AllMain`) are DRAINED EXACT
windows: `card = n`, every agent at phase EXACTLY `p`, ALL Main.  On such a window
`advTriggered (p+1)` is FALSE (`PhaseWindowShape.drained_post_no_advTrig`): no agent is at phase
≥ p+1.  So `hSeedStep` is genuinely NOT readable from the `Post` — it is the one-step seam-entry
event "the next interaction advances some agent into phase p+1".

The advance is seeded by phase-`(p+1)` PRESENCE; `AdvanceNoOvershoot.AtRiskClockZero p` (a clock at the
new phase `p+1` with counter `0`) is a sufficient witness (`advTriggered_of_atRiskClockZero`).

**The two honest worlds.**
* (a) COUNTER-TIMED seams — the seam-start configuration is the drained ALL-CLOCK state
  `AllClockGEpCard p n ∧ clockCounterSumAt p = 0 ∧ geCount (p+1) = 0`.  The seed fires for FREE:
  `SeedRungs.drained_kernel_seedTarget_compl_zero` gives the full-rectangle advance (rate 1).
* (b) ALL-MAIN drain seams — the work `Post` is genuinely all-Main
  (`Phase1AllMain`/`Phase8AllMain`), so there are NO clocks in `c` to perform the counter-0
  advance.  The seed is therefore a genuine per-seam ONE-STEP event (a Main agent advances to `p+1`
  on the next interaction), which the
  all-Main `Post` cannot manufacture (it pins all `n` agents to phase `p`).  We carry it as the
  precise named remainder `hSeedStepEvent` and produce `hSeedStep` from it (the trivial wiring). -/

/-- **(a) The counter-timed seed (FREE, `O(1)` deterministic).**  From the drained all-clock
un-seeded seam-start state the one-step seed fires a.s. —
`SeedRungs.drained_kernel_seedTarget_compl_zero` re-stated in the `advTriggered` set via
`advTriggered_iff_seedTarget`.  This is the
`hSeedStep`-shaped value for the counter-timed destinations (`p ∈ {0,1,5,6,7,8}`). -/
theorem hSeedStep_timed_of_drained (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hInv : ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : ConditionalPhaseProgress.clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : AdvanceEpidemics.geCount (L := L) (K := K) (p + 1) c = 0) :
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0 := by
  have hzero := SeedRungs.drained_kernel_seedTarget_compl_zero (L := L) (K := K) p hp n hn c
    hInv hdrain hunseed
  have hset : {c' : Config (AgentState L K) |
        ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (p + 1) c'}
      = (SeedRungs.seedTarget (L := L) (K := K) p)ᶜ := by
    ext c'
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [SeededAdvanceChain.advTriggered_iff_seedTarget p c']
  rw [hset, pow_one]
  exact hzero

/-- **(b) The all-Main drain seed event (the precise named remainder).**  For the all-Main drain
seams the work `Post` cannot supply the seed (no clocks; all `n` agents pinned to phase `p`), so the
honest one-step advance is carried as this named per-seam event: from the work `Post`, the next step
fires the `(p+1)`-trigger a.s.  This is EXACTLY the `hSeedStep` field shape, isolated as the genuine
remainder. -/
def SeedStepEvent (p : ℕ) (workPost : Config (AgentState L K) → Prop) : Prop :=
  ∀ c : Config (AgentState L K), workPost c →
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0

/-- **#4 PRODUCTION — `hSeedStep` from the named seam-entry event.**  The `hSeedStep` field of a
`Assembly'` (per seam `k`, from `(work k).Post`) is produced from the per-seam named event
`hEvent k : SeedStepEvent (seamP k) ((work k).Post)`.  For the all-Main drain seams `hEvent` is the
genuine carried remainder; for the counter-timed seams it is `hSeedStep_timed_of_drained` composed
with the work `Post` ⟹ drained-state read.  This delivers the `Assembly'.hSeedStep` field. -/
theorem hSeedStep_of_event
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hEvent : ∀ k : Fin 10,
      SeedStepEvent (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0 :=
  fun k c hpost => hEvent k c hpost

end PhaseWorkInstances

end Ripple.PopulationProtocol.ExactMajority

-- SUPERSEDED: headline theorem lives in Theorem31.lean.
-- Definitions in this file are still imported by downstream modules.
/-
# FinalAssembly — the WAVE D end-to-end Doty et al. Theorem 3.1 pair + the definitive residual atom list.

This is the *final assembly* of the §6 discharge campaign (`DOTY_POST63_CAMPAIGN.md`).  Every
wave-A/B/C discharger is plugged into the narrowest surface, and the two end-to-end theorems are
produced over a SINGLE inspectable hypothesis bundle `ChainHypotheses` — the definitive statement
of what genuinely remains (the irreducibly-probabilistic paper events).

## What this file delivers

1. `ChainHypotheses n L K C0` — the FINAL ATOM LIST as one Lean structure.  It bundles
   * `wi : CrudeWorkFamily.Hypotheses n` — the 11 WORK-slot probabilistic residual record (each field
     a named per-phase paper event: the Lemma-5.3 averaging rate, the Lemma-7.1 sampling
     concentration, the Lemma-7.2 band rate, the Lemma-7.4/7.6 eliminator margins, …), with the
     structural floors/closures/budget arithmetic already discharged inside `workConcrete`;
   * the 10 EXACT-seam feeders (`hDrift`, `hNoOvershoot`) — wired for destinations `{1,6,7,8}` by
     `SeamPairAdapter`, genuinely carried per-seam guards for `{2,3,4,5,9}`;
   * the two kept structural bridge reads (`hWorkPostToWindow`, `hWindowToWorkPre`) and the NEW
     one-step seed event `hSeedStep` (REPLACING the FALSE `hTrig`, per `SeedTrigWiring`);
   * the assembled-chain budget glue (`Cphase`/`δ`/`T`, the start/end pins, the kernel-power-carried
     `hcompFail`, the per-slot time/budget calibrations).
   Every field is doc-commented with its paper provenance and the landed partial machinery.

2. `whp_bound_of_chainHypotheses` — the conditional whp reduction.
   `SeededAdvanceChain.time_headline`
   (the `hTrig`-free re-cut) instantiated with the assembly built from `ChainHypotheses`:
   conclusion `(K^T) c₀ {¬ stable} ≤ 21/n²` with `T ≤ 21·C0·n·(L+1)`, under `Regime n L K`
   and a `Phase0Initial`-flavoured start.

3. `expected_bound_of_chainHypotheses` — the conditional expectation reduction.
   `ChainEndExpectedTime.expected_time_chain_end`
   fed the SAME wired 21-instance family `phases'` and the on-chain branch classification
   (`BranchAndBudget`'s `ChainEndBranch` builders + on-chain `hBranch`).
   Conclusion `expectedHitting K c₀ (StableDone) ≤ (21·C0 + 4·Cbad)·n·(L+1)`.

## Discipline

Append-only; edits NO existing file.  Single-file `lake env lean` build; `#print axioms` for every
new declaration ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/
`native_decide`.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.SeededAdvanceChain
import Ripple.PopulationProtocol.ExactMajority.Probability.BranchAndBudget
import Ripple.PopulationProtocol.ExactMajority.Probability.PaperRegime

namespace Ripple.PopulationProtocol.ExactMajority
namespace PhaseChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ChainEndAssembly

variable {L K : ℕ}

/-! ## Part 1 — `ChainHypotheses`: THE FINAL ATOM LIST.

A single inspectable bundle holding exactly the surviving named hypotheses of the §6 proof, as Prop
(or instance) fields.  The genuinely-probabilistic paper events live inside `wi` (the `Hypotheses`
record) and the seam feeders; the structural reads (`hWorkPostToWindow`, `hWindowToWorkPre`) and the
narrow one-step seed (`hSeedStep`) are the bridge surface; the budget glue (`Cphase`/`δ`/`hcompFail`/
…) is the assembled-chain calibration.  Nothing is hidden: this structure IS the carried set of the
re-cut headline `SeededAdvanceChain.time_headline`.

`L`/`K` are the ambient protocol parameters (from the section `variable`); `n` is the population
size and `C0` the per-instance time-coefficient ceiling. -/
structure ChainHypotheses (n C0 : ℕ) where
  ----------------------------------------------------------------------------
  -- (A) The 11 WORK-slot probabilistic residual record.
  ----------------------------------------------------------------------------
  /-- **The WORK-slot atoms** (`CrudeWorkFamily.Hypotheses`).  Its named fields are the genuinely
  probabilistic per-phase paper events, each with its landed partial machinery:

  * `work0` — the role-split milestone-hitting composition (Doty et al. role split; `RoleSplitConcentration`
    `phase0_roleSplit_whp_two_stage`).  Carries the irreducible Lemma-5.1 `εfloor` Chernoff content
    INSIDE its `convergence` (`FloorPrefix`; the floor `∑_τ P(assignableCount<a₀)` is NOT assemblable
    from the deterministic count atoms — the concurrent Rule-4 `−2` drains the unassigned-CR pool).
  * `hstep1` (slot 1) — the Lemma-5.3 / [45] (Mocquard et al. discrete averaging Cor. 1) per-step
    averaging-drain rectangle for `extremeU` (`hext`/`hpull` partner-pool floor; deeper route
    `AveragingRate`+`PartnerMargin`).
  * `work2`, `work9` (slots 2, 9) — the Phase-2 opinion-window advance epidemic (`WindowConcentration.
    windowDrift`, rate proved inside the carried instance).
  * `work3` (slot 3) — the §6 clock phase (`HourComposition.phase3Convergence`); carries the
    τ-uniform side budget `hside`, the bulk `hεb`, the hour-entry `hEntry` (εsync reseed), and the
    `ClocksBelowHour` clock-front confinement (`PositionalCluster`) as its probabilistic core.
  * `hε4` (slot 4) — the Phase-4 advance-epidemic tail (`Epidemic`/`EpidemicTime`, proved inside).
  * `hstep5` + `hConc` (slot 5) — the reserve-drain rate `q₅` and the Lemma-7.1 sampled-class
    concentration `εConc` (`SampledClassTail`: the per-step MGF drift is landed; the carried core is
    the rise-probability floor `hrfloor` + the clock-timing escape bound).
  * `hdrop6` (slot 6) — the Lemma-7.2 band per-level rate (floor FULLY landed from the Phase-5 Post).
  * `hstep7` + `hPhase6Post7` (slot 7) — the crude `classMassN` rate + the Lemma-7.4 gap-1
    eliminator margin `Phase6To7Structure` (minority-witness half PROVED; eliminator-count lower
    bound carried, wired to the LEVELS floor by `phase7_levels_hdrop`).
  * `hstep8` + `hPhase7Post8` (slot 8) — the crude `minorityU` rate + the Lemma-7.6 above-level
    eliminator margin `Phase7To8Structure` (likewise; `phase8_levels_hdrop`; honest survival re-cut
    `α₈' = 14/75` per `BranchAndBudget`).
  * `hsB10` (slot 10) — the Phase-10 block-geometric block-length condition (proved inside
    `Phase10Drop`).
  * `hConfine` (slot 5, Theorem 6.2 `arXiv:2106.10201v2`) — the `0.92·|M| ≤ #usefulMains`
    bias-ledger collapse; the `IntegerProfileSquaring`-whp and `Theorem62Paper`'s three whp fields
    feed it.  Carried inside the slot's `convergence`/floor inputs. -/
  wi : CrudeWorkFamily.Hypotheses (L := L) (K := K) n
  ----------------------------------------------------------------------------
  -- (B) The EXACT-seam feeders (Doty et al. seam epidemics, the per-seam advance + no-overshoot guards).
  ----------------------------------------------------------------------------
  /-- Seam source phases `pₖ`. -/
  seamP : Fin 10 → ℕ
  /-- Seam horizons `tₖ`. -/
  seamT : Fin 10 → ℕ
  /-- Seam advance-epidemic budgets `εepidemicₖ`. -/
  εepidemic : Fin 10 → ℝ≥0
  /-- Seam no-overshoot budgets `εovershootₖ`. -/
  εovershoot : Fin 10 → ℝ≥0
  /-- **Per-seam advance-epidemic guard `hDrift`** (the seam opinion/clock epidemic crossing).
  WIRED for destinations `{1,6,7,8}` by `SeamPairAdapter.hNoOvershoot_one_advance`'s advance
  half; a genuinely carried per-seam probabilistic guard for `{2,3,4,5,9}` (Doty et al. seam epidemics). -/
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  /-- **Per-seam no-overshoot guard `εovershoot`** (the seam does not skip past the target phase).
  WIRED for `{1,6,7,8}` (`SeamPairAdapter`); carried per-seam guard for `{2,3,4,5,9}`. -/
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  ----------------------------------------------------------------------------
  -- (C) The bridge surface (structural reads) + the NEW one-step seed (REPLACES the FALSE hTrig).
  ----------------------------------------------------------------------------
  /-- Kept structural read: work `Post` ⟹ seam source window `allPhaseGe pₖ n`
  (`AssemblyBridges.phase{1,5,6,7,8}_window_to_ge`). -/
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (CrudeWorkFamily.workConcrete wi ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  /-- **The NARROW one-step seed event `hSeedStep`** (REPLACING the FALSE `hTrig`): from the work
  `Post`, the NEXT step fires the advance trigger a.s.  For the counter-timed all-clock seams this is
  `O(1)`-deterministic (`SeedRungs.drained_kernel_seedTarget_compl_zero` via `SeedTrigWiring`'s
  world-bridge `advTriggered_iff_seedTarget`); for the all-main drain seams it is the genuine
  per-seam main-advance seed. -/
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (CrudeWorkFamily.workConcrete wi ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  /-- Kept structural read: seam EXACT output window `allPhaseEq (pₖ+1) n` ⟹ work `(k+1)` `Pre`
  (the three genuine per-phase entry residuals: drain budget `Φ ≤ M₀`, role pins `{1,7,8}`, the
  Phase-10 sign/active pins — all carried per `SeedTrigWiring` Item 2; phase-pin half closed inside
  via `PhaseWindowShape.windowEq_card_phase`). -/
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (CrudeWorkFamily.workConcrete wi ⟨k.val + 1, by omega⟩).Pre c
  ----------------------------------------------------------------------------
  -- (D) The assembled-chain budget glue (the calibration of the 21-instance composition).
  ----------------------------------------------------------------------------
  /-- Per-instance time-scaling coefficients `Cphase i ≤ C0`. -/
  Cphase : Fin 21 → ℕ
  /-- Per-instance `n⁻²` budget split `δ i`. -/
  δ : Fin 21 → ℝ≥0
  /-- The start configuration `c₀`. -/
  c₀ : Config (AgentState L K)
  /-- The reference initial configuration `init` (the majority reference). -/
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)

/-! ## Part 2 — the wired assembly `Assembly'` built from the atoms. -/

/-- **The re-cut assembly built from `ChainHypotheses`.**  The work family is the wired
`CrudeWorkFamily.workConcrete wi` (every WORK slot made concrete); the seam feeders / bridges /
one-step seed are the carried fields.  This is the `hTrig`-free `SeededAdvanceChain.Assembly'`. -/
noncomputable def toAssembly' {n C0 : ℕ} (ra : ChainHypotheses (L := L) (K := K) n C0) :
    SeededAdvanceChain.Assembly' (L := L) (K := K) n where
  work := CrudeWorkFamily.workConcrete ra.wi
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := ra.hWorkPostToWindow
  hSeedStep := ra.hSeedStep
  hWindowToWorkPre := ra.hWindowToWorkPre

@[simp] theorem toAssembly'_work {n C0 : ℕ} (ra : ChainHypotheses (L := L) (K := K) n C0) :
    (toAssembly' ra).work = CrudeWorkFamily.workConcrete ra.wi := rfl

/-- The wired 21-instance family of the final assembly (the SHIFTED-seam interleave). -/
noncomputable def phases' {n C0 : ℕ} (ra : ChainHypotheses (L := L) (K := K) n C0) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeededAdvanceChain.phases' (toAssembly' ra)

/-! ## Part 3 — conditional whp reduction over phase residuals.

The re-cut headline `SeededAdvanceChain.time_headline` instantiated with the assembly
built from `ChainHypotheses`, under the paper regime `Regime n L K`.  The conclusion is the
paper's Theorem 3.1 whp half: failure `≤ 21/n²` within `T ≤ 21·C0·n·(L+1)` interactions
(`= O(n log n)` interactions `= O(log n)` parallel time, since `Regime` pins `L = ⌈log₂ n⌉`). -/
theorem whp_bound_of_chainHypotheses {n L K C0 : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (ra : ChainHypotheses (L := L) (K := K) n C0)
    (T : ℕ) (hT : T = ∑ i, (phases' ra i).t)
    (hcompFail :
      ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
        ≤ (∑ i, ((phases' ra i).ε : ℝ≥0∞)))
    (ht : ∀ i, (phases' ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases' ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (hx₀ : (phases' ra ⟨0, by omega⟩).Pre ra.c₀)
    (h_post : ∀ c, (phases' ra ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) ra.init c) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) := by
  -- The regime-polymorphic headline delivers the first two clauses straight through; the third
  -- clause CONSUMES `hReg` (`Regime` pins `L = ⌈log₂ n⌉`), exhibiting the interaction bound as
  -- the paper's `O(n log n) = O(log n)` parallel-time form.
  obtain ⟨herr, htime⟩ :=
    SeededAdvanceChain.time_headline ra.init ra.c₀ (toAssembly' ra)
      ra.Cphase ra.δ T hT hcompFail ht hε hx₀ h_post ra.hC0 ra.hδ
  refine ⟨herr, htime, ?_⟩
  rwa [← hReg.hLlog]

/-! ## Part 4 — conditional expectation reduction over phase residuals.

`ChainEndExpectedTime.expected_time_chain_end` fed the SAME wired family `phases' ra` and the on-chain
branch classification (`BranchAndBudget`'s `chainBranch_*` builders supply the `ChainEndBranch`
content ON the good trajectory; the off-event mass is charged to the whp bad-event probability in the
split-geometric recovery, NOT to a nonexistent deterministic off-event ladder — the carried
`hBranch` IS that reachable-relative conditioning surface, per `HANDOFF_HLADDER`). -/
theorem expected_bound_of_chainHypotheses {n L K C0 Cbad Brecover : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (ra : ChainHypotheses (L := L) (K := K) n C0)
    (hc₀Reach : ReachableFrom L K ra.init ra.c₀)
    (ht : ∀ i, (phases' ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases' ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (hx₀ : (phases' ra ⟨0, by omega⟩).Pre ra.c₀)
    (h_post : ∀ c, (phases' ra ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) ra.init c)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (hBranch :
      ∀ b, ReachableFrom L K ra.init b → b ∈ (StableDone L K ra.init)ᶜ →
        ChainEndBranch (L := L) (K := K) n ra.init b (Brecover : ℝ≥0∞) (βfinal b))
    (hδ : (∑ i, (ra.δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀
      (StableDone L K ra.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞)
    ∧ expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀
      (StableDone L K ra.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (Nat.clog 2 n + 1) : ℕ) : ℝ≥0∞) := by
  -- The first clause is the reachable-relative capstone straight through; the second CONSUMES `hReg`
  -- (`Regime` pins `L = ⌈log₂ n⌉`), exhibiting the expected hitting time as `O(n log n)`.
  have hcap := ChainEndExpectedTime.expected_time_chain_end (L := L) (K := K) (n := n) (C0 := C0)
    (Cbad := Cbad) (Brecover := Brecover) ra.init ra.c₀ hc₀Reach ra.Cphase ra.δ (phases' ra)
    ht hε (SeededAdvanceChain.phases'_h_chain (toAssembly' ra)) hx₀ h_post ra.hC0
    hDone hDoneAbs hBpos βfinal hBranch hδ hrecmass
  refine ⟨hcap, ?_⟩
  rwa [← hReg.hLlog]

end PhaseChain
end Ripple.PopulationProtocol.ExactMajority

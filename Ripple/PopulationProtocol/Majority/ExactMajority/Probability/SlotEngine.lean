-- SUPERSEDED: headline theorem lives in Theorem31.lean.
-- Definitions in this file are still imported by downstream modules.
/-
# SlotEngine — the F1+F2+F3-corrected end-to-end Doty Theorem 3.1 whp half.

This file is the re-cut of `PhaseChain.lean` answering the final adversarial audit
(`/tmp/codex_final_audit.md`).  It fixes three findings, append-only, editing no existing file.

## F1 (CRITICAL) — `hcompFail` PRODUCED, not carried.

`PhaseChain.theorem_3_1_whp` carried `hcompFail` (the assembled bad-event bound at the sum
horizon) as a FREE binder — tautological, since it is essentially the conclusion.  Here the failure
bound is **produced** from the 21-instance composition itself: `TimeHeadline.time_composition_W2`
applied at the concrete family `phases' ra` delivers `.1` — the failure mass at the LITERAL sum
horizon `∑ i, (phases' ra i).t` — and `hT : T = ∑ …` folds it to the opaque `T` via the safe
rewrite direction (`rw [hT]`, the horizon SUBTERM only; never the divergent re-unification of the
whole kernel-power application against the `Fin 21` sum).  `time_headline_CONCRETE'` itself
ALREADY invokes `time_composition_W2` internally and is landed/axiom-clean, so re-invoking it at
the same concrete family elaborates without divergence (Route a of the documented attack — the
ConcreteAssembly heartbeat wall is on a DIFFERENT unification, not this one).  `hcompFail` is GONE
from `theorem_3_1_whp_v2`.

## F2+F3 — the work family made HONEST (levels engine; the dead per-level inputs put ON the path).

`AssemblyWiring.workConcrete` instantiated slots 1/5/7/8 with the CRUDE single-step `potDone`
rate (`DrainCalibration.phase{1,5,7,8}Convergence_calibrated`), which `DrainRates.lean` itself
documents as "structurally vacuous for `Φ ≥ 2`", coinciding with the honest floor only at level
`m = 1`.  The honest per-level machinery was landed but DEAD on the path:
`DrainRates.hdrop{1,5,7,8}_of_chain` (the levels-engine per-level rates), `AssemblyWiring.slot{7,8}_levels_hdrop`
(consuming the eliminator margins `hPhase6Post7`/`hPhase7Post8`).

`workHonest` builds slots 1/5/7/8 on `OneSidedCancel.levels_PhaseConvergenceW` (the same engine
Phase 6 uses), consuming the per-level rates + the genuine margins + the per-level budget, with the
SAME `Pre`/`Post` as the crude slots (both engines have `Pre = Inv ∧ Φ ≤ M₀`, `Post = Inv ∧ Φ = 0`),
so every downstream bridge / seam connects unchanged.  `WorkInputsHonest` is the re-cut residual
record: the crude `hstep1/5/7/8` are DROPPED, replaced by the genuinely-probabilistic per-level
inputs the honest instances consume (the structural floors `hext`/`hpull`/`hmain5`, the eliminator
margins `hPhase6Post7`/`hPhase7Post8` — wired through `slot{7,8}_levels_hdrop` — the per-level
budgets `hpt{1,5,7,8}`, and the sampling concentration `hConc`).

## Discipline

Append-only; edits NO existing file.  Single-file `lake env lean` build; `#print axioms` for every
new declaration ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/
`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainEngine
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CompositionEngine
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PaperRegime

namespace ExactMajority
namespace SlotEngine

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 3 — `WorkInputsHonest`: the F2/F3 re-cut residual record.

The crude `hstep1/5/7/8` fields of `AssemblyWiring.WorkInputs` are DROPPED.  In their place are the
genuinely-probabilistic per-level inputs the honest instances consume: the structural floors
(`hext1`/`hpull1`/`hmain5`), the eliminator margins (`hPhase6Post7`/`hPhase7Post8`, threaded through
`slot{7,8}_levels_hdrop`), the per-level budgets (`hpt1/5/7/8`), and the sampling concentration
(`hConc`).  The structural slots (0/2/3/4/6/9/10) are carried exactly as in `WorkInputs`. -/
structure WorkInputsHonest (n : ℕ) where
  /-- The dyadic minority sign. -/
  σ : Sign
  /-- The Phase-5 sampled reserve hour. -/
  i5 : Fin (L + 1)
  /-- The Phase-5/6 sampled-reserve floor `K₀`. -/
  K₀ : ℕ
  /-- The Phase-6 band level `l`. -/
  l : ℕ
  /-- The Phase-7 eliminator-margin count `E7` (Lemma 7.4). -/
  E7 : ℕ
  /-- The Phase-8 above-level eliminator-margin count `E8` (Lemma 7.6). -/
  E8 : ℕ
  /-- Common budget level `M₀`. -/
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀
  hM₀ : (M₀ : ℝ) ≤ n
  -- slot 0 / 2 / 3 / 9 — carried finished instances (unchanged from `WorkInputs`).
  work0 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work3 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work9 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- slot 1 — HONEST levels inputs (crude `hstep1` DROPPED).
  /-- slot-1 partner-pool floor `P1 ≤ pullPos`. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  /-- slot-1 structural floor: `≥ 1` saturated extreme on every in-window config (PERSISTENCE-carried). -/
  hext1 : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
    1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  /-- slot-1 partner-pool floor `P1 ≤ pullPos` (Lemma 5.3 / [45]; PERSISTENCE-carried). -/
  hpull1 : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
    P1 ≤ (DrainThreading.pullPosSet L K).sum b.count
  /-- slot-1 per-level geometric-tail budget. -/
  hpt1 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P1 n m) ^ (tWin1 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 4 — Phase-4 epidemic (carried scalar inputs, unchanged).
  s4 : ℝ
  hs4 : 0 < s4
  t4 : ℕ
  ε4 : ℝ≥0
  hε4 : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s4))) ^ t4 *
          ENNReal.ofReal (Real.exp (s4 * ((n : ℝ) - 1))) / 1
        ≤ (ε4 : ℝ≥0∞)
  -- slot 5 — HONEST levels drain + concentration (crude `hstep5` DROPPED).
  /-- slot-5 biased-Main floor `P5 ≤ usefulMains` (Theorem 6.2 biased structure). -/
  P5 : ℕ
  tWin5 : ℕ → ℕ
  hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
  /-- slot-5 biased-Main floor (PERSISTENCE-carried; Theorem 6.2). -/
  hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
    P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count
  /-- slot-5 per-level geometric-tail budget. -/
  hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P5 n m) ^ (tWin5 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  /-- slot-5 sampling-concentration budget `εConc` (Lemma 7.1). -/
  εConc : ℝ≥0
  /-- slot-5 sampling concentration at the LEVELS horizon `∑ tWin5 m` (Lemma 7.1). -/
  hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
    ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
    ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
      {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)
  -- slot 6 — Phase-6 band drain (levels engine; carried as in `WorkInputs`).
  q6 : ℕ → ℝ≥0∞
  tWin6 : ℕ → ℕ
  hClosed6 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c)
  hdrop6 : ∀ m, ∀ b : Config (AgentState L K),
    Phase6Convergence.Phase6Win (L := L) (K := K) n b →
    Phase6Convergence.highMass (L := L) (K := K) l b = m →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potBelow
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ q6 m
  hpt6 : ∀ m ∈ Finset.Icc 1 M₀, (q6 m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 7 — HONEST levels eliminator drain (crude `hstep7` DROPPED; margin ON the path).
  tWin7 : ℕ → ℕ
  /-- slot-7 eliminator-margin (Lemma 7.4 `Phase6To7Structure`); PERSISTENCE-carried, consumed by
  `slot7_levels_hdrop` (minority witness PROVED). -/
  hPhase6Post7 : ∀ b : Config (AgentState L K),
    Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b
  hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15
  hpt7 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E7 n m) ^ (tWin7 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 8 — HONEST levels eliminator drain (crude `hstep8` DROPPED; margin ON the path).
  tWin8 : ℕ → ℕ
  /-- slot-8 above-level eliminator-margin (Lemma 7.6 `Phase7To8Structure`); PERSISTENCE-carried,
  consumed by `slot8_levels_hdrop`. -/
  hPhase7Post8 : ∀ b : Config (AgentState L K),
    Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b
  hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5
  hpt8 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E8 n m) ^ (tWin8 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 10 — Phase-10 block-geometric (carried scalar inputs, unchanged).
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  k10 : ℕ

/-! ## Part 4 — the honest work family `workHonest`. -/

/-- **The honest WORK family** `Fin 11 → PhaseConvergenceW`.  Slots 1/5/7/8 are on the LEVELS engine
(consuming the per-level rates + the eliminator margins + the per-level budgets); slots 0/2/3/4/6/9/10
are exactly as in `workConcrete`.  Pre/Post per slot match the crude family, so all bridges
connect. -/
noncomputable def workHonest {n : ℕ} (wi : WorkInputsHonest (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => wi.work0
    | ⟨1, _⟩ => slot1Honest wi.P1 wi.M₀ wi.hn wi.hM1 wi.hext1 wi.hpull1 wi.tWin1 wi.hpt1
    | ⟨2, _⟩ => wi.work2
    | ⟨3, _⟩ => wi.work3
    | ⟨4, _⟩ =>
        Phase4Convergence.phase4Convergence (L := L) (K := K) n wi.hn wi.s4 wi.hs4 wi.t4 wi.ε4 wi.hε4
    | ⟨5, _⟩ =>
        slot5Honest wi.i5 wi.K₀ wi.M₀ wi.P5 wi.hClosed5 wi.hn wi.hM1 wi.hmain5 wi.tWin5 wi.hpt5
          wi.εConc wi.hConc
    | ⟨6, _⟩ =>
        DrainCalibration.phase6Convergence_calibrated (L := L) (K := K) wi.l n wi.M₀ wi.q6 wi.tWin6
          wi.hClosed6 wi.hdrop6 wi.hn wi.hM1 wi.hpt6
    | ⟨7, _⟩ =>
        slot7Honest wi.σ wi.E7 wi.M₀ wi.hn wi.hM1 wi.hE7 wi.hPhase6Post7 wi.tWin7 wi.hpt7
    | ⟨8, _⟩ =>
        slot8Honest wi.σ wi.E8 wi.M₀ wi.hn wi.hM1 wi.hE8 wi.hPhase7Post8 wi.tWin8 wi.hpt8
    | ⟨9, _⟩ => wi.work9
    | ⟨10, _⟩ =>
        Phase10Drop.phase10Convergence (L := L) (K := K) n wi.hn wi.s10 wi.hs10 wi.hsB10 wi.k10

/-! ## Part 5 — `ResidualAtoms`: the V2 residual bundle (bridges over `workHonest`). -/

/-- **The V2 residual atom list.**  Same surface as `PhaseChain.ResidualAtoms`, but the work
family is the HONEST `workHonest wih` (slots 1/5/7/8 on the levels engine) and the crude
`hstep1/5/7/8` are gone (they live nowhere — `WorkInputsHonest` dropped them).  The seam feeders /
bridges / one-step seed are carried over `workHonest`. -/
structure ResidualAtoms (n C0 : ℕ) where
  /-- The honest WORK-slot residual record (levels engine on 1/5/7/8). -/
  wih : WorkInputsHonest (L := L) (K := K) n
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  εepidemic : Fin 10 → ℝ≥0
  εovershoot : Fin 10 → ℝ≥0
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workHonest wih ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workHonest wih ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (workHonest wih ⟨k.val + 1, by omega⟩).Pre c
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)

/-- The honest assembly built from `ResidualAtoms`. -/
noncomputable def toAssembly' {n C0 : ℕ} (ra : ResidualAtoms (L := L) (K := K) n C0) :
    SeedTrigWiring.Assembly' (L := L) (K := K) n where
  work := workHonest ra.wih
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := ra.hWorkPostToWindow
  hSeedStep := ra.hSeedStep
  hWindowToWorkPre := ra.hWindowToWorkPre

@[simp] theorem toAssembly'_work {n C0 : ℕ} (ra : ResidualAtoms (L := L) (K := K) n C0) :
    (toAssembly' ra).work = workHonest ra.wih := rfl

/-- The wired 21-instance family of the honest assembly. -/
noncomputable def phases' {n C0 : ℕ} (ra : ResidualAtoms (L := L) (K := K) n C0) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeedTrigWiring.phases' (toAssembly' ra)

/-- `phases' ra = phases' (toAssembly' ra)` (recorded by `rfl` BEFORE the irreducibility
attribute, so the `phases'`-stated headline can be fed the `phases'`-stated hypotheses through a
cheap `▸` cast — the cast only rewrites the symbolic family in non-kernel-power subterms). -/
theorem phases'_eq {n C0 : ℕ} (ra : ResidualAtoms (L := L) (K := K) n C0) :
    phases' ra = SeedTrigWiring.phases' (toAssembly' ra) := rfl

/-- The re-cut chain map stated over `phases'` (so it feeds the composition without unfolding
`phases'` — the fold divergence stays blocked).  Recorded before irreducibility. -/
theorem phases'_h_chain {n C0 : ℕ} (ra : ResidualAtoms (L := L) (K := K) n C0) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x, (phases' ra i).Post x → (phases' ra ⟨i.val + 1, hi⟩).Pre x :=
  SeedTrigWiring.phases'_h_chain (toAssembly' ra)

-- Block the kernel-power `whnf` from unfolding the heavy honest-slot definitions during the horizon
-- fold (the documented ConcreteAssembly divergence: reducing `(phases' ra i).t` through the
-- `levels_PhaseConvergenceW` honest slots / the seam instances blows the heartbeat budget).  The work
-- family is consumed POLYMORPHICALLY (through `t`/`ε`/`Pre`/`Post` as a `PhaseConvergenceW`), so the
-- composition and the bridges (which take the work `Post`/`Pre` as carried hypotheses) never need to
-- reduce it.  `phases'_eq` reconnects to `phases'` where the headline needs it.
attribute [irreducible] workHonest


/-! ## Part 6 — `theorem_3_1_whp_v2`: the F1+F2+F3-corrected whp half.

`hcompFail` is PRODUCED (F1) from `time_composition_W2` at the concrete honest family; the work
family is the levels-engine `workHonest` (F2/F3).  The only remaining binders are the regime, the
residual atoms, the budget/time arithmetic, the start pin, and the endpoint bridge. -/

-- `fold_pair_to_T` and `whp_of_asm'` extracted to `CompositionEngine.lean` (re-exported via
-- `import CompositionEngine` above, same `ExactMajority.SlotEngine` namespace).

theorem theorem_3_1_whp_v2 {n L K C0 : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (ra : ResidualAtoms (L := L) (K := K) n C0)
    (T : ℕ) (hT : T = ∑ i, (phases' ra i).t)
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
  -- F1: the failure bound is PRODUCED, not carried.  `whp_of_asm'` does the full production+fold over a
  -- FREE `asm` (so the `.1` extraction / fold are symbolic), concluding at the OPAQUE `T`.  We
  -- INSTANTIATE it at `asm := toAssembly' ra` (the honest assembly): pure substitution of an
  -- already-checked proof; the `(K^T)…` output is consumed with `T` opaque — cheap.  `hcompFail` GONE.
  obtain ⟨herr, htime⟩ :=
    whp_of_asm' (C0 := C0) ra.init ra.c₀ (toAssembly' ra) ra.Cphase ra.δ T hT ht hε hx₀ h_post
      ra.hC0 ra.hδ
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]; exact htime

end SlotEngine
end ExactMajority

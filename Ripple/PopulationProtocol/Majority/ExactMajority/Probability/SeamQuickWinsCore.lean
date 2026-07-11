/-
# SeamQuickWinsCore — Generic wave-1 proofs (chain-independent).

The `AtomsWave1Inputs` record and the four generic proof theorems (`wave1_hDrift`,
`wave1_hWorkPostToWindow`, `wave1_hWindowToWorkPre`, `wave1_hNoOvershoot`) extracted from
SeamQuickWins so they do NOT depend on the chain-heavy `SurvivalInputs` import.  The proofs
work with any `wih : WorkInputsHonest` — they never reference `ResidualAtomsFull` or any chain
type from the start-wiring layer.

The V3-packaging adapter `atomsWave1` remains in `SeamQuickWins.lean` (which imports this file
plus `SurvivalInputs`).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SlotEngine
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Atoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamOvershootBridge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamNoOvershoot
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyBridges

namespace ExactMajority
namespace SeamQuickWins

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## The narrowed wave-1 input record.

Everything `ResidualAtomsFull` needs, with the five wave-1 fields replaced by their landed
producers' calibration inputs.  No new mathematics: each non-trivial field below is exactly the
calibration datum the corresponding landed producer (`seam_drift`, `mk_hWorkPostToWindow`,
`mk_hWindowToWorkPre_pin`, `detSeamOvershootBridge_of_wf` + `seam_noOvershoot_tail`) consumes. -/

/-- **Narrowed wave-1 input record for `ResidualAtomsFull`.**  Carries the still-open residuals
verbatim and the calibration data for the five (A)-class producers. -/
structure AtomsWave1Inputs (n C0 : ℕ) where
  /-- The honest WORK-slot residual record (levels engine on 1/5/7/8). -/
  wih : SlotEngine.WorkInputsHonest (L := L) (K := K) n
  /-- Per-seam phase index `p = seamP k`. -/
  seamP : Fin 10 → ℕ
  /-- Per-seam epidemic horizon `t = seamT k`. -/
  seamT : Fin 10 → ℕ
  /-- Per-seam epidemic-drift budget. -/
  εepidemic : Fin 10 → ℝ≥0
  /-- Per-seam no-overshoot budget. -/
  εovershoot : Fin 10 → ℝ≥0
  hn : 2 ≤ n
  -- #1 hDrift calibration: per-seam epidemic rate + the Phase-4-shape arithmetic tail check.
  /-- Per-seam epidemic rate `s k > 0`. -/
  sDrift : Fin 10 → ℝ
  /-- Positivity of the per-seam epidemic rate. -/
  hsDrift : ∀ k, 0 < sDrift k
  /-- The Phase-4-shape arithmetic tail check feeding `seam_drift` per seam (pure arithmetic on
  `s, t, ε`). -/
  hεDrift : ∀ k : Fin 10,
    ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
          (1 - Real.exp (-(sDrift k)))) ^ (seamT k) *
      ENNReal.ofReal (Real.exp (sDrift k * ((n : ℝ) - 1))) / 1
      ≤ (εepidemic k : ℝ≥0∞)
  -- #2 hWorkPostToWindow calibration: per-slot card/phase window read.
  /-- Per-slot window read: each honest work slot's `Post` pins the card and phase
  (`work.Post ⟹ card = n ∧ all-phase = seamP k`); closed by `phase{1,5,6,7,8}_window_to_ge` for the
  pinned destinations. -/
  hwin : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SlotEngine.workHonest wih ⟨k.val, by omega⟩).Post c →
      c.card = n ∧ ∀ a ∈ c, a.phase.val = seamP k
  -- #3 hWindowToWorkPre per-phase entry residual (the carried half).
  /-- Per-phase entry residual: from the card/phase pin of the seam output, deliver the entering
  work window's full `Pre` (the drain-budget / role / sign entry pins; where wave-B landed it). -/
  hEntryPin : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (c.card = n ∧ ∀ a ∈ c, a.phase.val = seamP k + 1) →
      (SlotEngine.workHonest wih ⟨k.val + 1, by omega⟩).Pre c
  -- #5 hNoOvershoot: (a) DetSeamOvershootBridge inputs + (b) the consumed clock-zero tail.
  /-- The counter-reset destination for each seam (`seamP k + 1 ∈ {1,6,7,8}`), feeding
  `detSeamOvershootBridge_of_wf`. -/
  hReset : ∀ k : Fin 10, SeamNoOvershoot.CounterResetDest (seamP k + 1)
  /-- Seam-region well-formedness invariant (`Wf` on every config), feeding
  `detSeamOvershootBridge_of_wf` (the Analysis-layer reachability invariant). -/
  hWf : ∀ c : Config (AgentState L K), SeamNoOvershoot.Wf (L := L) (K := K) c
  /-- **(5b — consumed input, ANOTHER agent's territory: ClockZeroTail).**
  The within-seam no-overshoot tail, stated from the SEAM `Pre`
  (`allPhaseGe (seamP k) n ∧ advTriggered (seamP k+1)`)
  — i.e. exactly the `ResidualAtoms.hNoOvershoot` field shape — but TAKING the deterministic
  overshoot bridge `DetSeamOvershootBridge (seamP k)` as an explicit argument.  Wave 1 PRODUCES that
  bridge (#5a, `detSeamOvershootBridge_of_wf`); the ClockZeroTail agent owns the clock-zero
  concentration that turns the bridge + the seam `Pre` into this bound.  Consumed verbatim; the
  clock-zero concentration is NOT reproved here. -/
  hOvershootTail : ∀ (k : Fin 10),
      SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (seamP k) →
      ∀ (c : Config (AgentState L K)),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
          ≤ (εovershoot k : ℝ≥0∞)
  -- Carried-verbatim still-open V2 residual: #4 one-step seed.
  /-- **#4 `hSeedStep` (carried).**  One-step a.s. seed from each honest work slot's `Post`. -/
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SlotEngine.workHonest wih ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  -- Carried-verbatim budget / config / regime scalars (the arithmetic boilerplate fields).
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)
  -- V3 start / sign honesty atoms (carried verbatim; #12 start (D), #13 sign (C)).
  /-- **#12 `hStart` (carried, primitive start).**  The `Phase0Initial`-honest start. -/
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
  /-- **#12 `hWork0PreOfStart` wiring datum (slot-0 `Pre` pin).**  The deterministic interface
  `Phase0Initial n c₀ → work0.Pre c₀` for the carried role-split slot-0 instance. -/
  hWork0Pin : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
    (wih.work0).Pre c₀
  /-- **#13 `hPhase10Sign` (carried, Doty §11 sign conservation).** -/
  hPhase10Sign : Atoms.Phase10SignMatch (L := L) (K := K) init

/-! ## The five (A)-class producers. -/

/-- **#1 `hDrift` PRODUCED.**  Per seam `k`, `SeamEpidemics.seam_drift` at `p = seamP k`,
`t = seamT k`, `ε = εepidemic k`, rate `sDrift k`, with the arithmetic tail check `hεDrift k`.
Exactly the `ResidualAtoms.hDrift` field shape. -/
theorem wave1_hDrift {n C0 : ℕ} (w : AtomsWave1Inputs (L := L) (K := K) n C0) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (w.seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (w.seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (w.seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (w.seamP k + 1) n c'}
        ≤ (w.εepidemic k : ℝ≥0∞) :=
  fun k c hPre =>
    SeamEpidemics.seam_drift (w.seamP k) n w.hn (w.sDrift k) (w.hsDrift k) (w.seamT k)
      (w.εepidemic k) (w.hεDrift k) c hPre

/-- **#2 `hWorkPostToWindow` PRODUCED.**  `AssemblyBridges.mk_hWorkPostToWindow` over the 11 honest
work slots with the per-slot window read `w.hwin`. -/
theorem wave1_hWorkPostToWindow {n C0 : ℕ} (w : AtomsWave1Inputs (L := L) (K := K) n C0) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SlotEngine.workHonest w.wih ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (w.seamP k) n c :=
  AssemblyBridges.mk_hWorkPostToWindow (SlotEngine.workHonest w.wih) w.seamP w.hwin

/-- **#3 `hWindowToWorkPre` PRODUCED.**  The card/phase half via
`AssemblyBridges.mk_hWindowToWorkPre_pin`, composed with the carried per-phase entry residual
`w.hEntryPin` to reach the entering work window's full `Pre`. -/
theorem wave1_hWindowToWorkPre {n C0 : ℕ} (w : AtomsWave1Inputs (L := L) (K := K) n C0) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (w.seamP k + 1) n c →
      (SlotEngine.workHonest w.wih ⟨k.val + 1, by omega⟩).Pre c :=
  fun k c heq =>
    w.hEntryPin k c (AssemblyBridges.mk_hWindowToWorkPre_pin w.seamP k c heq)

/-- **#5 `hNoOvershoot` PRODUCED.**  The deterministic half `DetSeamOvershootBridge (seamP k)` is
PRODUCED here (#5a) by `SeamNoOvershoot.detSeamOvershootBridge_of_wf` from `w.hReset k` + `w.hWf`,
and FED into the consumed within-seam clock-zero tail `w.hOvershootTail k` (5b — the ClockZeroTail
agent's territory, which owns the clock-zero concentration turning the bridge + the seam `Pre` into
the per-seam no-overshoot bound).  The result is exactly the `ResidualAtoms.hNoOvershoot`
field shape, stated from the seam `Pre`. -/
theorem wave1_hNoOvershoot {n C0 : ℕ} (w : AtomsWave1Inputs (L := L) (K := K) n C0) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (w.seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (w.seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (w.seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (w.seamP k) c'}
        ≤ (w.εovershoot k : ℝ≥0∞) := by
  intro k c hPre
  -- #5(a): PRODUCE the deterministic overshoot bridge from the seam-region `Wf` invariant.
  have hdet : SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (w.seamP k) :=
    SeamNoOvershoot.detSeamOvershootBridge_of_wf (w.seamP k) (w.hReset k) w.hWf
  -- Feed the produced bridge into the consumed 5b clock-zero tail (ClockZeroTail agent's input),
  -- which delivers the per-seam no-overshoot bound from the seam `Pre`.
  exact w.hOvershootTail k hdet c hPre

end SeamQuickWins
end ExactMajority

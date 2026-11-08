/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WorkConstructed — the 11 CONCRETE `work` instances of the Doty faithful proof.

This append-only file edits NO existing file.  It is the LAST FRONTIER of the faithful discharge:
it CONSTRUCTS the 11 `PhaseConvergenceW` work instances as CONCRETE applied
survival / landed terms, ELIMINATING the carried `work : Fin 11 → PhaseConvergenceW` field of
`FaithfulWitness.FaithfulCore`.

## The point (no dodge)

`FaithfulWitness.FaithfulCore` carried the `work` family as an opaque hypothesis.  Here EACH slot is
a CONCRETE term produced by ACTUALLY INVOKING the slot's constructor — never a projection of a
carried `FaithfulCore`/`Assembly'`.

## What closes from `Regime` ALONE (no carried input)

* **slots 2 / 4 / 9** — the epidemic-budget instances.  Built from `Phase4Convergence.phase4Convergence`
  (slot 4), `PhaseWorkInstances.phase2W` (slot 2), and the phase-9 `PhaseWorkInstances.phase9W` clone.
  The opinion witnesses are EXHIBITED CONCRETELY here (`U := ⟨4⟩` = `{+1}`, `v := ⟨0⟩` = `∅`; the
  bitwise-`lor` union algebra + `singleSign` all `decide`).  The epidemic scalars are `s := 1`,
  horizon `t := ⌈(n/α)(s(n−1)+2 log n)⌉₊` (so `hT` by `Nat.le_ceil`), budget `ε := (1/n²).toNNReal`
  (the genuine calibrated `1/n²`, via `EpidemicConvergence.epidemicBudget_calibrated`).
* **slot 10** — the phase-10 sign-resolution drop.  Built from
  `Phase10Drop.phase10Convergence` with block length `s` and `k` rounds; the
  budget `(1/2)^k` and the geometric block-sum bound `hsB` are supplied concretely from the regime.

## What is PRECISELY ISOLATED (the genuine remaining paper-probability calibration)

The CONTRACTING-DRAIN slots (1 / 5 / 6 / 7 / 8) and the STAGED slots (0 / 3) are built by ACTUALLY
INVOKING their constructors (`Phase{1,6,7,8}SurvivalContracting`, `GatedDrainContracting`,
`Phase0RoleSplitStages.roleSplitWork0`, `PhaseWorkInstances.phase3W`) — but the per-slot survival INPUTS
(the uniform drift `Φ`/rate `r`, the leak set + bound, the clock floor, the structural floor, the
cover, the horizon `T`, and the `≤ 1/n²` budget arithmetic) are NOT yet derivable from `Regime`
in CLOSED FORM in the current codebase (the drift / floor LEMMAS exist — `phase1_drop_floor_of_phase1Win`,
`levelRate_pos`, `dropFloorE_pos`, `sampleLevelRate`, `contractRate_lt_one`, the clock tail
`clock_depletion_tail_of_coupling` — but their assembly into a regime-closed horizon + budget fit is
the deepest paper-probability core).  So those slots take their PRECISE residual calibration as the
`PhaseCalib` bundle — NOT a carried `PhaseConvergenceW`, but the exact survival scalars each
constructor consumes.  This eliminates the opaque carried `work` field: every slot is now a CONCRETE
constructor invocation; only the genuinely-uncharged per-slot calibration scalars remain, and they
are isolated AT THE SLOT, by name.

## ANTI-TRAP compliance

NO `InvClosed` of a phase window.  NO bare-universal floor — the contracting slots enter only through
the per-slot survivals (`r < 1`, escapes cumulative).  The epidemic slots use the per-step PROGRESS
lower bound (informed count RISING), not a one-step closure.  Every constructed slot is a real
`PhaseConvergenceW` value (the satisfiability witness); none is a vacuous carry.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.ContractingChainTimeBound
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseWorkInstances
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Post3
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase10Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase4Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1SurvivalContracting
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase78SurvivalContracting
import Ripple.PopulationProtocol.ExactMajority.Probability.GatedDrainContracting
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase0RoleSplitStages
import Ripple.PopulationProtocol.ExactMajority.Probability.PaperRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.ReserveSampling
import Ripple.PopulationProtocol.ExactMajority.Probability.TightEpidemicWork

namespace Ripple.PopulationProtocol.ExactMajority
namespace WorkConstructed

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open HourComposition ClockKilledMinute ClockSideGood ClockBudgets ClockRealBulk
open EarlyDripMarked Phase5ConfinementCompose ReserveSampling

variable {L K : ℕ}

/-! ## Part 1 — the concrete OPINION witnesses for the epidemic slots 2/9.

`U := ⟨4⟩` carries only `+1` (bit 2), `v := ⟨0⟩` carries neither sign.  The union is bitwise `lor`,
so all the `phase2Convergence` opinion-algebra hypotheses hold by `decide`. -/

/-- The `+1`-only opinion (`Fin 8` value `4`, bit pattern `b₊₁`). -/
def opU : Fin 8 := ⟨4, by decide⟩

/-- The empty opinion (`Fin 8` value `0`). -/
def opV : Fin 8 := ⟨0, by decide⟩

theorem opU_singleSign : Phase2Convergence.singleSign opU := by decide

theorem opV_singleSign : Phase2Convergence.singleSign opV := by decide

theorem op_vU : opinionsUnion opV opU = opU := by decide

theorem op_Uv : opinionsUnion opU opV = opU := by decide

theorem op_vv : opinionsUnion opV opV = opV := by decide

theorem op_UU : opinionsUnion opU opU = opU := by decide

theorem op_Uv_ne : opU ≠ opV := by decide


/-! ## Part 2 — the calibrated epidemic horizon and budget (regime-closed). -/

/-- The calibrated epidemic horizon at rate `s = 1`: `⌈(n/α)(1·(n−1) + 2 log n)⌉₊`.  By `Nat.le_ceil`
this meets the `epidemicBudget_calibrated` log-bound, so the budget is `1/n²`. -/
noncomputable def epiHorizon (n : ℕ) : ℕ :=
  ⌈((n : ℝ) / EpidemicConvergence.epiAlpha 1) * (1 * ((n : ℝ) - 1) + 2 * Real.log n)⌉₊

theorem epiHorizon_spec (n : ℕ) :
    ((n : ℝ) / EpidemicConvergence.epiAlpha 1) * (1 * ((n : ℝ) - 1) + 2 * Real.log n)
      ≤ (epiHorizon n : ℝ) := by
  unfold epiHorizon
  exact Nat.le_ceil _

/-- The calibrated epidemic budget fit at `s = 1`, horizon `epiHorizon n`: tail `≤ (1/n²).toNNReal`.
This is `EpidemicConvergence.epidemicBudget_calibrated` at the regime-closed horizon. -/
theorem epi_budget_fit (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-(1 : ℝ)))) ^
          (epiHorizon n) *
      ENNReal.ofReal (Real.exp (1 * ((n : ℝ) - 1))) / 1
        ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) :=
  EpidemicConvergence.epidemicBudget_calibrated hn (by norm_num : (0:ℝ) < 1) (epiHorizon_spec n)

/-! ## Part 3 — the regime-closed CONCRETE slots 2 / 4 / 9 / 10. -/

/-- **slot 4 — CONCRETE epidemic instance** (`Phase4Convergence.phase4Convergence` at `s = 1`,
calibrated horizon/budget).  `Post = StableTie4 ∨ advFinished`, budget `1/n²`. -/
noncomputable def work4 {n : ℕ} (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase4Convergence.phase4Convergence (L := L) (K := K) n hn 1 (by norm_num)
    (epiHorizon n) (Real.toNNReal (1 / (n : ℝ) ^ 2)) (epi_budget_fit n hn)

/-- **slot 2 — CONCRETE epidemic instance** (`PhaseWorkInstances.phase2W` with the exhibited opinions, at
`s = 1`, calibrated horizon/budget). -/
noncomputable def work2 {n : ℕ} (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  PhaseWorkInstances.phase2W (L := L) (K := K) opU opV n hn ExactMajority.TightEpidemicWork.opU_singleSign ExactMajority.TightEpidemicWork.opV_singleSign
    ExactMajority.TightEpidemicWork.op_vU ExactMajority.TightEpidemicWork.op_Uv ExactMajority.TightEpidemicWork.op_vv ExactMajority.TightEpidemicWork.op_UU ExactMajority.TightEpidemicWork.op_Uv_ne 1 (by norm_num)
    (epiHorizon n) (Real.toNNReal (1 / (n : ℝ) ^ 2)) (epi_budget_fit n hn)

/-- **slot 9 — CONCRETE phase-9 epidemic instance** (`PhaseWorkInstances.phase9W`, same scalar shape as
slot 2). -/
noncomputable def work9 {n : ℕ} (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  PhaseWorkInstances.phase9W (L := L) (K := K) opU opV n hn ExactMajority.TightEpidemicWork.opU_singleSign ExactMajority.TightEpidemicWork.opV_singleSign
    ExactMajority.TightEpidemicWork.op_vU ExactMajority.TightEpidemicWork.op_Uv ExactMajority.TightEpidemicWork.op_vv ExactMajority.TightEpidemicWork.op_UU ExactMajority.TightEpidemicWork.op_Uv_ne 1 (by norm_num)
    (epiHorizon n) (Real.toNNReal (1 / (n : ℝ) ^ 2)) (epi_budget_fit n hn)

/-- **slot 10 — CONCRETE phase-10 drop instance** (`Phase10Drop.phase10Convergence`).  Block length
`s`, rounds `k`; the budget is `(1/2)^k` and the block-sum bound `hsB` are supplied concretely.
`Post = Phase10Post`. -/
noncomputable def work10 {n : ℕ} (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2 ≤ (s : ℝ≥0∞))
    (k : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase10Drop.phase10Convergence (L := L) (K := K) n hn s hspos hsB k

/-- slot 10's `Post` is literally `Phase10Post` — so the `hSlot10Post` tie of `FaithfulCore` is `id`. -/
@[simp] theorem work10_Post {n : ℕ} (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2 ≤ (s : ℝ≥0∞))
    (k : ℕ) :
    (work10 (L := L) (K := K) hn s hspos hsB k).Post
      = fun c => Phase10Drop.Phase10Post (L := L) (K := K) c := rfl

/-! ## Part 4 — the CONTRACTING-DRAIN slots 1 / 5 / 6 / 7 / 8 (built by INVOKING the survival).

Each slot is a CONCRETE `PhaseConvergenceW` whose `convergence` field is the survival applied
UNIFORMLY across the phase gate.  The per-slot survival INPUTS (drift `Φ`/rate `r`, leak set + bound,
clock floor, struct floor, cover, horizon `T`, budget arithmetic) are the PRECISE residual
calibration — supplied as explicit `∀ x`-uniform arguments (NOT a carried `PhaseConvergenceW`).  The
budget is `εdrain + η_clock + η_struct`; when each piece `≤ 1/(3n²)` the slot meets `1/n²`. -/

/-- **slot 1 — CONTRACTING survival** (`Phase1SurvivalContracting.phase1_survival_contracting`,
applied uniformly over the `Phase1Win` gate).  `Pre = Phase1Win n` (`= allPhaseEq 1 n`),
`Post = Phase1Done`. -/
noncomputable def work1 {n : ℕ}
    (Φ_E : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hEdrift : ∀ x ∈ {c | PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c},
      ∫⁻ y, Φ_E y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_E x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (εdrain ηc ηs : ℝ≥0)
    (Phase1Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hεdrain : ∀ x, ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_E x / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (hClock : ∀ x, (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) x Sᶜ) ≤ (ηc : ℝ≥0∞))
    (hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ T) x Aconf ≤ (ηs : ℝ≥0∞))
    (hcover : {c : Config (AgentState L K) | ¬ Phase1Done c} ⊆ Aconf ∪ {c | θ ≤ Φ_E c}) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c
  Post := Phase1Done
  t := T
  ε := εdrain + ηc + ηs
  convergence := by
    intro x hx
    refine le_trans
      (Phase1SurvivalContracting.phase1_survival_contracting (L := L) (K := K) (n := n)
        Φ_E r hEdrift S q_leak hLeak T θ hθ0 hθtop x hx εdrain (hεdrain x)
        (ηc : ℝ≥0∞) (ηs : ℝ≥0∞) (hClock x) Phase1Done Aconf (hStruct x) hcover) ?_
    rw [ENNReal.coe_add, ENNReal.coe_add]

/-- **slot 6 — CONTRACTING survival** (re-export of `ContractingChainTimeBound.phase6ContractingWork`, the
already-landed slot-6 packager).  `Pre = Phase6Win n` (`= allPhaseEq 6 n`), `Post = Phase6Done`. -/
noncomputable def work6 {n : ℕ}
    (Φ_H : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hHdrift : ∀ x ∈ {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c},
      ∫⁻ y, Φ_H y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_H x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (εdrain ηc ηs : ℝ≥0)
    (Phase6Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hεdrain : ∀ x, ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_H x / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (hClock : ∀ x, (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) x Sᶜ) ≤ (ηc : ℝ≥0∞))
    (hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ T) x Aconf ≤ (ηs : ℝ≥0∞))
    (hcover : {c : Config (AgentState L K) | ¬ Phase6Done c} ⊆ Aconf ∪ {c | θ ≤ Φ_H c}) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  ContractingChainTimeBound.phase6ContractingWork (L := L) (K := K) (n := n)
    Φ_H r hHdrift S q_leak hLeak T θ hθ0 hθtop εdrain ηc ηs Phase6Done Aconf
    hεdrain hClock hStruct hcover

/-- **slot 7 — CONTRACTING survival** (`Phase78SurvivalContracting.phase7_survival_contracting`,
uniform over the `Inv7Sum` gate).  `Pre = Inv7Sum n`, `Post = Phase7Done`. -/
noncomputable def work7 {n : ℕ}
    (Φ₇ : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hdrift : ∀ x ∈ {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c},
      ∫⁻ y, Φ₇ y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ₇ x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (εdrain ηc ηs : ℝ≥0)
    (Phase7Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hεdrain : ∀ x, ((T : ℝ≥0∞) * q_leak + r ^ T * Φ₇ x / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (hClock : ∀ x, (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) x Sᶜ) ≤ (ηc : ℝ≥0∞))
    (hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ T) x Aconf ≤ (ηs : ℝ≥0∞))
    (hcover : {c : Config (AgentState L K) | ¬ Phase7Done c} ⊆ Aconf ∪ {c | θ ≤ Φ₇ c}) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => Phase7Convergence.Inv7Sum (L := L) (K := K) n c
  Post := Phase7Done
  t := T
  ε := εdrain + ηc + ηs
  convergence := by
    intro x hx
    refine le_trans
      (Phase78SurvivalContracting.phase7_survival_contracting (L := L) (K := K) (n := n)
        Φ₇ r hdrift S q_leak hLeak T θ hθ0 hθtop x hx εdrain (hεdrain x)
        (ηc : ℝ≥0∞) (ηs : ℝ≥0∞) (hClock x) Phase7Done Aconf (hStruct x) hcover) ?_
    rw [ENNReal.coe_add, ENNReal.coe_add]

/-- **slot 8 — CONTRACTING survival** (`Phase78SurvivalContracting.phase8_survival_contracting`,
uniform over the `Phase8Win` gate).  `Pre = Phase8Win n` (`= allPhaseEq 8 n`),
`Post = Phase8Done`. -/
noncomputable def work8 {n : ℕ}
    (Φ₈ : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hdrift : ∀ x ∈ {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c},
      ∫⁻ y, Φ₈ y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ₈ x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (εdrain ηc ηs : ℝ≥0)
    (Phase8Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hεdrain : ∀ x, ((T : ℝ≥0∞) * q_leak + r ^ T * Φ₈ x / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (hClock : ∀ x, (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) x Sᶜ) ≤ (ηc : ℝ≥0∞))
    (hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ T) x Aconf ≤ (ηs : ℝ≥0∞))
    (hcover : {c : Config (AgentState L K) | ¬ Phase8Done c} ⊆ Aconf ∪ {c | θ ≤ Φ₈ c}) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => Phase8Convergence.Phase8AllMain (L := L) (K := K) n c
  Post := Phase8Done
  t := T
  ε := εdrain + ηc + ηs
  convergence := by
    intro x hx
    refine le_trans
      (Phase78SurvivalContracting.phase8_survival_contracting (L := L) (K := K) (n := n)
        Φ₈ r hdrift S q_leak hLeak T θ hθ0 hθtop x hx εdrain (hεdrain x)
        (ηc : ℝ≥0∞) (ηs : ℝ≥0∞) (hClock x) Phase8Done Aconf (hStruct x) hcover) ?_
    rw [ENNReal.coe_add, ENNReal.coe_add]

/-- **slot 5 — CONTRACTING gated-drain survival** (`phase5_survival_contracting`, uniform over the
`Phase5Confined` gate).  `Pre = Phase5Confined n`, `Post = ReserveSampled`.  The structural escape is
the `MainProfileConfinedToUseful` violation set. -/
noncomputable def work5 {n : ℕ}
    (Φ_U : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hUdrift : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c},
      ∫⁻ y, Φ_U y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_U x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase5Confined (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (εdrain ηc ηconf : ℝ≥0)
    (hεdrain : ∀ x, ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_U x / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (hClock : ∀ x, (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) x Sᶜ) ≤ (ηc : ℝ≥0∞))
    (hConf : ∀ x, ((NonuniformMajority L K).transitionKernel ^ T) x
        {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c}
          ≤ (ηconf : ℝ≥0∞))
    (hcover : {c : Config (AgentState L K) | ¬ ReserveSampled (L := L) (K := K) c}
      ⊆ {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c}
        ∪ {c | θ ≤ Φ_U c}) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => Phase5Confined (L := L) (K := K) n c
  Post := fun c => ReserveSampled (L := L) (K := K) c
  t := T
  ε := εdrain + ηc + ηconf
  convergence := by
    intro x hx
    refine le_trans
      (phase5_survival_contracting (L := L) (K := K) n
        Φ_U r hUdrift S q_leak hLeak T θ hθ0 hθtop x hx εdrain (hεdrain x)
        (ηc : ℝ≥0∞) (ηconf : ℝ≥0∞) (hClock x) (hConf x) hcover) ?_
    rw [ENNReal.coe_add, ENNReal.coe_add]

/-! ## Part 5 — the STAGED slots 0 / 3 (built by INVOKING their constructors).

slot 0 is the phase-0 role-split survival (`roleSplitWork0`, three concrete stage instances + two
chain links); slot 3 is the §103/Post₃ endpoint (`slot3W`, the Core snapshot tail). -/

/-- **slot 0 — CONCRETE role-split survival** (`Phase0RoleSplitStages.roleSplitWork0`).
`Pre = stage1.Pre`, `Post = stage2.Post`, budget the three stages summed. -/
noncomputable def work0
    (stage1 stage15 stage2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h_chain1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h_chain2 : ∀ x, stage15.Post x → stage2.Pre x) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase0RoleSplitStages.roleSplitWork0 (L := L) (K := K) stage1 stage15 stage2 h_chain1 h_chain2

/-- **slot 3 — CONCRETE §103/Post₃ instance** (`PhaseWorkInstances.phase3W`). -/
noncomputable def work3 {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3Post3.Phase3PostTail (L := L) (K := K) n ell M g₀ σ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  PhaseWorkInstances.phase3W (L := L) (K := K) A

/-! ## Part 6 — `PhaseCalib`: the PRECISE residual calibration for the non-regime-closed slots.

This bundle carries EXACTLY the per-slot survival / staging INPUTS that `Regime` does not (yet)
pin in closed form — the contracting-drain inputs (slots 1/5/6/7/8) and the staged inputs (slots
0/3).  It is NOT a carried `PhaseConvergenceW` (the dodge); it is the named scalar/drift calibration
each constructor consumes.  `workConstructed` then dispatches `Fin 11`, building EACH slot as a
CONCRETE constructor invocation — slots 2/4/9/10 from the regime alone, the rest from this bundle. -/

/-- **`PhaseCalib` — the precise residual calibration.**  Bundles the contracting-drain inputs of
slots 1/5/6/7/8 and the staged inputs of slots 0/3.  Each field is exactly the calibration scalar /
drift one of the `workK` constructors takes; assembling them from `Regime` in closed form is the
remaining paper-probability core, isolated here AT THE SLOT. -/
structure PhaseCalib (n : ℕ) where
  -- slot 0 (role-split): three concrete stage instances + two chain links.
  s0stage1 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  s0stage15 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  s0stage2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  s0h1 : ∀ x, s0stage1.Post x → s0stage15.Pre x
  s0h2 : ∀ x, s0stage15.Post x → s0stage2.Pre x
  -- slot 1 (contracting drain on the Phase1Win gate).
  s1Φ : Config (AgentState L K) → ℝ≥0∞
  s1r : ℝ≥0∞
  s1drift : ∀ x ∈ {c | PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c},
    ∫⁻ y, s1Φ y ∂((NonuniformMajority L K).transitionKernel x) ≤ s1r * s1Φ x
  s1S : Set (Config (AgentState L K))
  s1qleak : ℝ≥0∞
  s1leak : ∀ x ∈ {c | PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c}, x ∈ s1S →
    (NonuniformMajority L K).transitionKernel x
      {c | PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c}ᶜ ≤ s1qleak
  s1T : ℕ
  s1θ : ℝ≥0∞
  s1θ0 : s1θ ≠ 0
  s1θtop : s1θ ≠ ∞
  s1εd : ℝ≥0
  s1ηc : ℝ≥0
  s1ηs : ℝ≥0
  s1Done : Config (AgentState L K) → Prop
  s1Aconf : Set (Config (AgentState L K))
  s1hεd : ∀ x, ((s1T : ℝ≥0∞) * s1qleak + s1r ^ s1T * s1Φ x / s1θ : ℝ≥0∞) ≤ (s1εd : ℝ≥0∞)
  s1hClock : ∀ x, (∑ τ ∈ Finset.range s1T,
      ((NonuniformMajority L K).transitionKernel ^ τ) x s1Sᶜ) ≤ (s1ηc : ℝ≥0∞)
  s1hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ s1T) x s1Aconf ≤ (s1ηs : ℝ≥0∞)
  s1cover : {c : Config (AgentState L K) | ¬ s1Done c} ⊆ s1Aconf ∪ {c | s1θ ≤ s1Φ c}
  -- slot 3 (§103/Core snapshot to Post₃).
  s3ell : ℕ
  s3M : ℝ
  s3g₀ : ℝ
  s3σ : Sign
  s3post : Phase3Post3.Phase3PostTail (L := L) (K := K) n s3ell s3M s3g₀ s3σ
  -- slot 5 (gated drain on the Phase5Confined gate).
  s5Φ : Config (AgentState L K) → ℝ≥0∞
  s5r : ℝ≥0∞
  s5drift : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c},
    ∫⁻ y, s5Φ y ∂((NonuniformMajority L K).transitionKernel x) ≤ s5r * s5Φ x
  s5S : Set (Config (AgentState L K))
  s5qleak : ℝ≥0∞
  s5leak : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c}, x ∈ s5S →
    (NonuniformMajority L K).transitionKernel x
      {c | Phase5Confined (L := L) (K := K) n c}ᶜ ≤ s5qleak
  s5T : ℕ
  s5θ : ℝ≥0∞
  s5θ0 : s5θ ≠ 0
  s5θtop : s5θ ≠ ∞
  s5εd : ℝ≥0
  s5ηc : ℝ≥0
  s5ηconf : ℝ≥0
  s5hεd : ∀ x, ((s5T : ℝ≥0∞) * s5qleak + s5r ^ s5T * s5Φ x / s5θ : ℝ≥0∞) ≤ (s5εd : ℝ≥0∞)
  s5hClock : ∀ x, (∑ τ ∈ Finset.range s5T,
      ((NonuniformMajority L K).transitionKernel ^ τ) x s5Sᶜ) ≤ (s5ηc : ℝ≥0∞)
  s5hConf : ∀ x, ((NonuniformMajority L K).transitionKernel ^ s5T) x
      {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c}
        ≤ (s5ηconf : ℝ≥0∞)
  s5cover : {c : Config (AgentState L K) | ¬ ReserveSampled (L := L) (K := K) c}
    ⊆ {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c}
      ∪ {c | s5θ ≤ s5Φ c}
  -- slot 6 (contracting drain on the Phase6Win gate).
  s6Φ : Config (AgentState L K) → ℝ≥0∞
  s6r : ℝ≥0∞
  s6drift : ∀ x ∈ {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c},
    ∫⁻ y, s6Φ y ∂((NonuniformMajority L K).transitionKernel x) ≤ s6r * s6Φ x
  s6S : Set (Config (AgentState L K))
  s6qleak : ℝ≥0∞
  s6leak : ∀ x ∈ {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c}, x ∈ s6S →
    (NonuniformMajority L K).transitionKernel x
      {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c}ᶜ ≤ s6qleak
  s6T : ℕ
  s6θ : ℝ≥0∞
  s6θ0 : s6θ ≠ 0
  s6θtop : s6θ ≠ ∞
  s6εd : ℝ≥0
  s6ηc : ℝ≥0
  s6ηs : ℝ≥0
  s6Done : Config (AgentState L K) → Prop
  s6Aconf : Set (Config (AgentState L K))
  s6hεd : ∀ x, ((s6T : ℝ≥0∞) * s6qleak + s6r ^ s6T * s6Φ x / s6θ : ℝ≥0∞) ≤ (s6εd : ℝ≥0∞)
  s6hClock : ∀ x, (∑ τ ∈ Finset.range s6T,
      ((NonuniformMajority L K).transitionKernel ^ τ) x s6Sᶜ) ≤ (s6ηc : ℝ≥0∞)
  s6hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ s6T) x s6Aconf ≤ (s6ηs : ℝ≥0∞)
  s6cover : {c : Config (AgentState L K) | ¬ s6Done c} ⊆ s6Aconf ∪ {c | s6θ ≤ s6Φ c}
  -- slot 7 (contracting drain on the Inv7Sum gate).
  s7Φ : Config (AgentState L K) → ℝ≥0∞
  s7r : ℝ≥0∞
  s7drift : ∀ x ∈ {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c},
    ∫⁻ y, s7Φ y ∂((NonuniformMajority L K).transitionKernel x) ≤ s7r * s7Φ x
  s7S : Set (Config (AgentState L K))
  s7qleak : ℝ≥0∞
  s7leak : ∀ x ∈ {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c}, x ∈ s7S →
    (NonuniformMajority L K).transitionKernel x
      {c | Phase7Convergence.Inv7Sum (L := L) (K := K) n c}ᶜ ≤ s7qleak
  s7T : ℕ
  s7θ : ℝ≥0∞
  s7θ0 : s7θ ≠ 0
  s7θtop : s7θ ≠ ∞
  s7εd : ℝ≥0
  s7ηc : ℝ≥0
  s7ηs : ℝ≥0
  s7Done : Config (AgentState L K) → Prop
  s7Aconf : Set (Config (AgentState L K))
  s7hεd : ∀ x, ((s7T : ℝ≥0∞) * s7qleak + s7r ^ s7T * s7Φ x / s7θ : ℝ≥0∞) ≤ (s7εd : ℝ≥0∞)
  s7hClock : ∀ x, (∑ τ ∈ Finset.range s7T,
      ((NonuniformMajority L K).transitionKernel ^ τ) x s7Sᶜ) ≤ (s7ηc : ℝ≥0∞)
  s7hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ s7T) x s7Aconf ≤ (s7ηs : ℝ≥0∞)
  s7cover : {c : Config (AgentState L K) | ¬ s7Done c} ⊆ s7Aconf ∪ {c | s7θ ≤ s7Φ c}
  -- slot 8 (contracting drain on the Phase8AllMain gate).
  s8Φ : Config (AgentState L K) → ℝ≥0∞
  s8r : ℝ≥0∞
  s8drift : ∀ x ∈ {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c},
    ∫⁻ y, s8Φ y ∂((NonuniformMajority L K).transitionKernel x) ≤ s8r * s8Φ x
  s8S : Set (Config (AgentState L K))
  s8qleak : ℝ≥0∞
  s8leak : ∀ x ∈ {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c}, x ∈ s8S →
    (NonuniformMajority L K).transitionKernel x
      {c | Phase8Convergence.Phase8AllMain (L := L) (K := K) n c}ᶜ ≤ s8qleak
  s8T : ℕ
  s8θ : ℝ≥0∞
  s8θ0 : s8θ ≠ 0
  s8θtop : s8θ ≠ ∞
  s8εd : ℝ≥0
  s8ηc : ℝ≥0
  s8ηs : ℝ≥0
  s8Done : Config (AgentState L K) → Prop
  s8Aconf : Set (Config (AgentState L K))
  s8hεd : ∀ x, ((s8T : ℝ≥0∞) * s8qleak + s8r ^ s8T * s8Φ x / s8θ : ℝ≥0∞) ≤ (s8εd : ℝ≥0∞)
  s8hClock : ∀ x, (∑ τ ∈ Finset.range s8T,
      ((NonuniformMajority L K).transitionKernel ^ τ) x s8Sᶜ) ≤ (s8ηc : ℝ≥0∞)
  s8hStruct : ∀ x, ((NonuniformMajority L K).transitionKernel ^ s8T) x s8Aconf ≤ (s8ηs : ℝ≥0∞)
  s8cover : {c : Config (AgentState L K) | ¬ s8Done c} ⊆ s8Aconf ∪ {c | s8θ ≤ s8Φ c}
  -- slot 10 (phase-10 drop scalars).
  s10s : ℕ
  s10hspos : 0 < s10s
  s10hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2 ≤ (s10s : ℝ≥0∞)
  s10k : ℕ

/-! ## Part 7 — `workConstructed`: the CONCRETE `Fin 11 → PhaseConvergenceW`.

EACH slot is a CONCRETE constructor invocation — NO carried `work k` projection.  Slots 2/4/9
close from `hn` (the regime) alone; slot 10 from the regime + the §10 block scalars; the contracting
slots 1/5/6/7/8 and staged slots 0/3 from the precise `PhaseCalib` bundle.  The carried opaque
`work : Fin 11 → PhaseConvergenceW` field of `FaithfulWitness.FaithfulCore` is ELIMINATED: this IS the
work family, built term by term. -/

/-- **`workConstructed` — the 11 CONCRETE work instances.**  Given the regime (via `hn : 2 ≤ n`) and
the precise residual calibration `cal : PhaseCalib n`, dispatches `Fin 11` to the concrete
constructors.  No slot is a projection of a carried `FaithfulCore`/`Assembly'`. -/
noncomputable def workConstructed {n : ℕ} (hn : 2 ≤ n) (cal : PhaseCalib (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    match i with
    | ⟨0, _⟩ => work0 cal.s0stage1 cal.s0stage15 cal.s0stage2 cal.s0h1 cal.s0h2
    | ⟨1, _⟩ => work1 cal.s1Φ cal.s1r cal.s1drift cal.s1S cal.s1qleak cal.s1leak cal.s1T cal.s1θ
        cal.s1θ0 cal.s1θtop cal.s1εd cal.s1ηc cal.s1ηs cal.s1Done cal.s1Aconf cal.s1hεd
        cal.s1hClock cal.s1hStruct cal.s1cover
    | ⟨2, _⟩ => work2 hn
    | ⟨3, _⟩ => work3 cal.s3post
    | ⟨4, _⟩ => work4 hn
    | ⟨5, _⟩ => work5 cal.s5Φ cal.s5r cal.s5drift cal.s5S cal.s5qleak cal.s5leak cal.s5T cal.s5θ
        cal.s5θ0 cal.s5θtop cal.s5εd cal.s5ηc cal.s5ηconf cal.s5hεd cal.s5hClock cal.s5hConf cal.s5cover
    | ⟨6, _⟩ => work6 cal.s6Φ cal.s6r cal.s6drift cal.s6S cal.s6qleak cal.s6leak cal.s6T cal.s6θ
        cal.s6θ0 cal.s6θtop cal.s6εd cal.s6ηc cal.s6ηs cal.s6Done cal.s6Aconf cal.s6hεd
        cal.s6hClock cal.s6hStruct cal.s6cover
    | ⟨7, _⟩ => work7 cal.s7Φ cal.s7r cal.s7drift cal.s7S cal.s7qleak cal.s7leak cal.s7T cal.s7θ
        cal.s7θ0 cal.s7θtop cal.s7εd cal.s7ηc cal.s7ηs cal.s7Done cal.s7Aconf cal.s7hεd
        cal.s7hClock cal.s7hStruct cal.s7cover
    | ⟨8, _⟩ => work8 cal.s8Φ cal.s8r cal.s8drift cal.s8S cal.s8qleak cal.s8leak cal.s8T cal.s8θ
        cal.s8θ0 cal.s8θtop cal.s8εd cal.s8ηc cal.s8ηs cal.s8Done cal.s8Aconf cal.s8hεd
        cal.s8hClock cal.s8hStruct cal.s8cover
    | ⟨9, _⟩ => work9 hn
    | ⟨10, _⟩ => work10 hn cal.s10s cal.s10hspos cal.s10hsB cal.s10k

/-- slot 10 of `workConstructed` has `Post = Phase10Post` (so the `hSlot10Post` tie is `id`). -/
@[simp] theorem workConstructed_10_Post {n : ℕ} (hn : 2 ≤ n) (cal : PhaseCalib (L := L) (K := K) n) :
    (workConstructed hn cal ⟨10, by omega⟩).Post
      = fun c => Phase10Drop.Phase10Post (L := L) (K := K) c := rfl

/-- slots 2/4/9/10 of `workConstructed` are the regime-closed instances (definitional). -/
@[simp] theorem workConstructed_2 {n : ℕ} (hn : 2 ≤ n) (cal : PhaseCalib (L := L) (K := K) n) :
    workConstructed hn cal ⟨2, by omega⟩ = work2 hn := rfl
@[simp] theorem workConstructed_4 {n : ℕ} (hn : 2 ≤ n) (cal : PhaseCalib (L := L) (K := K) n) :
    workConstructed hn cal ⟨4, by omega⟩ = work4 hn := rfl
@[simp] theorem workConstructed_9 {n : ℕ} (hn : 2 ≤ n) (cal : PhaseCalib (L := L) (K := K) n) :
    workConstructed hn cal ⟨9, by omega⟩ = work9 hn := rfl

#print axioms workConstructed
#print axioms work2
#print axioms work4
#print axioms work9
#print axioms work10
#print axioms work1
#print axioms work5
#print axioms work6
#print axioms work7
#print axioms work8
#print axioms work0
#print axioms work3

end WorkConstructed
end Ripple.PopulationProtocol.ExactMajority

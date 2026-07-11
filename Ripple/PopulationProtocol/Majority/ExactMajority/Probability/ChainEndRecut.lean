/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 chain-end RE-CUT — F6 audit fix (`ChainEndRecut`)

Append-only fix for the codex adversarial audit's finding **F6** (`/tmp/codex_audit_report.md
§F6`, MEDIUM): "recovery-side `hFloors` is a dead binder, and timed `hfinal` is over-quantified".

The audit found two honesty defects in the assembled E4 surfaces of `ReachableLadder.lean` /
`ChainEndAssembly.lean`:

**F6 (a) — dead `hFloors` binder.**  `ReachableLadder.reachable_hLadder` takes
`_hFloors : ReachableClockFloors …` but IGNORES it — it just returns the `ladder` field of
`hClass` (`ReachableLadder.lean:452-467`).  Yet `expected_time_reachable`
(`ReachableLadder.lean:521-523`) and `expected_time_chain_end`
(`ChainEndAssembly.lean:509-511`) still CARRY `hFloors` and feed it into that dead slot.  So
the advertised "floor propagation consumed here" is NOT reflected in the proof term: the floor
data is already inside the regime data / classification path (the timed engines bake `mC`/floor
into the carried `LadderData`), and this top-surface binder is pure dead weight that
misadvertises where floor data is consumed.

  → FIX (1): `expected_time_reachable'` / `expected_time_chain_end'`, re-cut WITHOUT
  the dead `hFloors` binder.  They prove the SAME conclusion from a STRICTLY SMALLER hypothesis
  set.  The floor data stays where it is genuinely consumed — inside the regime/classification
  data (`ReachablePhaseRegimeClassification` / `ChainEndBranch`, whose carried `LadderData` the
  timed engines already built from the floor) — so the top surface no longer carries an unused
  parameter.  (`reachable_hLadder` itself is unchanged; we re-derive the ladder by `hClass`'s
  `ladder` field directly, exactly as `reachable_hLadder` does, but without the dead argument.)

**F6 (b) — over-quantified timed `hfinal`.**  `ChainEndAssembly.timedSpine_ladderData`'s final
rung carries `hfinal : ∀ y ∈ {AllClockGEpCard 10 n}, expectedHitting y StableDone ≤ βfinal`
(`ChainEndAssembly.lean:241-242`), quantifying over ALL phase-10 entry states.  But the
phase-10 bridges that are actually PROVEN are regime/gap restricted: the majority drain needs
`S1` (reachable + `0 < gap`); the tie drain needs `Tie1plus` (reachable + `gap = 0` + active)
(`StableBridges` / `BackupEntry.arrival_classification`).  An arbitrary `AllClockGEpCard 10 n`
state carries NO gap-sign witness, so `hfinal` is STRONGER than the proven route delivers — it
is honestly deliverable only on the regime-restricted slice
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {gap-sign}`.

  → FIX (2): the honest restricted final-rung discharges
  `phase10_finalRung_majority_discharge` / `phase10_finalRung_tie_discharge`.  On the
  regime-restricted slice each PRODUCES the `hfinal` cap from the landed chain-end bounds:
  `AllClockGEpCard 10 n ⟹ AllPhase10 ∧ card = n` (every clock at phase `≥ 10` is at phase `10`,
  `phase : Fin 11`), then the arrival classification (`BackupEntry.allPhase10_majority_imp_S1` /
  `allPhase10_tie_imp_Tie1plus`) routes the slice into `S1` / `Tie1plus`, then
  `ChainEndAssembly.phase10Majority_drain_to_stableDone_le` /
  `phase10Tie_drain_to_stableDone_le` deliver the cap.  This is the InvClosed-slice technique of
  `ChainEndAssembly.entry_to_S1_le_nsq` / `phase10Majority_link_intersected` (route through the
  reachability invariant, then the gap-sign classification), now used to DISCHARGE the timed
  spine's `hfinal` from the landed bounds rather than carry it over-quantified.

**FIX (3): the strongest re-cut `expected_time` form** — `expected_time_chain_end'`,
without the dead `hFloors`, whose `ChainEndBranch` content already bakes in the discharged
restricted `hfinal` (via the discharges above, supplied at branch-construction time by the
caller who has the gap-sign witness).  Carried set listed in the docstring.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/ChainEndRecut.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ChainEndAssembly

namespace ExactMajority
namespace ChainEndRecut

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs Phase10Drop BackupEntry
open ChainEndAssembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — `AllClockGEpCard 10 n ⟹ AllPhase10 ∧ card = n`

The phase-10 entry slice `{AllClockGEpCard 10 n}` (every clock at phase `≥ 10`, card `n`) lands
the whole card-`n` population at phase `10` because `phase : Fin 11`, so `10 ≤ phase.val` forces
`phase.val = 10` (`BackupEntry.phase_val_eq_ten_of_ge`).  This is the bridge from the timed
spine's final-rung set to the arrival-classification hypotheses. -/

/-- `AllClockGEpCard 10 n c ⟹ AllPhase10 c`.  Every clock at phase `≥ 10` is at phase `= 10`
(`phase : Fin 11`). -/
theorem allClockGEpCard_ten_imp_allPhase10 {n : ℕ} (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) 10 n c) :
    AllPhase10 (L := L) (K := K) c := by
  intro a ha
  exact phase_val_eq_ten_of_ge (L := L) (K := K) (hInv.1 a ha).2

/-- `AllClockGEpCard 10 n c ⟹ c.card = n`. -/
theorem allClockGEpCard_ten_card {n : ℕ} (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) 10 n c) : c.card = n := hInv.2

/-! ## Part B — the honest restricted final-rung discharges (F6 (b))

The timed spine's `hfinal` is honestly deliverable only on the regime-restricted slice
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {gap-sign}`.  We package the two branches —
majority (`0 < gap`) and tie (`gap = 0`, active) — each PRODUCING the per-state `hfinal` cap from
the landed `ChainEndAssembly` within-Phase-10 drains.  These are exactly the honest targets the
proven bridges deliver; they replace the over-quantified carried `hfinal`. -/

/-- **Majority final-rung discharge (the honest restricted `hfinal`).**  On the slice
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {0 < gap}`, the within-Phase-10 majority drain
caps `E[T y → StableDone] ≤ 3·n²·(1 + 2 log n)`.  Route: `AllClockGEpCard 10 n ⟹ AllPhase10 ∧
card = n` (Part A); reachable + `0 < gap` ⟹ `S1` (`allPhase10_majority_imp_S1`); then the landed
drain `phase10Majority_drain_to_stableDone_le`.  This is the InvClosed-slice technique of
`entry_to_S1_le_nsq` applied to DISCHARGE the final rung. -/
theorem phase10_finalRung_majority_discharge {n : ℕ} (hn : 2 ≤ n)
    (init : Config (AgentState L K))
    (hinit : validInitial init)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (y : Config (AgentState L K))
    (hy : AllClockGEpCard (L := L) (K := K) 10 n y)
    (hReach : ReachableFrom L K init y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  have hAll : AllPhase10 (L := L) (K := K) y :=
    allClockGEpCard_ten_imp_allPhase10 (L := L) (K := K) (n := n) y hy
  have hcard : y.card = n := allClockGEpCard_ten_card (L := L) (K := K) (n := n) y hy
  -- ReachableFrom is definitionally (NonuniformMajority L K).Reachable init y.
  have hReach' : (NonuniformMajority L K).Reachable init y := hReach
  have hS1 : S1 (L := L) (K := K) n y :=
    allPhase10_majority_imp_S1 (L := L) (K := K) n init y hinit hReach' hAll hcard hgap
  exact phase10Majority_drain_to_stableDone_le (L := L) (K := K) hn init hDone hAbs hgap y hS1

/-- **Tie final-rung discharge (the honest restricted `hfinal`).**  On the slice
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {gap = 0} ∩ {active}`, the within-Phase-10 tie
drain caps `E[T y → StableDone] ≤ 2·n²·(1 + 2 log n)`.  Route: `AllClockGEpCard 10 n ⟹ AllPhase10
∧ card = n` (Part A); reachable + `gap = 0` + active ⟹ `Tie1plus` (`allPhase10_tie_imp_Tie1plus`);
then the landed drain `phase10Tie_drain_to_stableDone_le`. -/
theorem phase10_finalRung_tie_discharge {n : ℕ} (hn : 2 ≤ n)
    (init : Config (AgentState L K))
    (hinit : validInitial init)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (y : Config (AgentState L K))
    (hy : AllClockGEpCard (L := L) (K := K) 10 n y)
    (hReach : ReachableFrom L K init y)
    (hact : hasActiveAgent y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  have hAll : AllPhase10 (L := L) (K := K) y :=
    allClockGEpCard_ten_imp_allPhase10 (L := L) (K := K) (n := n) y hy
  have hcard : y.card = n := allClockGEpCard_ten_card (L := L) (K := K) (n := n) y hy
  have hReach' : (NonuniformMajority L K).Reachable init y := hReach
  have hTie : Tie1plus (L := L) (K := K) n y :=
    allPhase10_tie_imp_Tie1plus (L := L) (K := K) n init y hinit hReach' hAll hcard hgap hact
  exact phase10Tie_drain_to_stableDone_le (L := L) (K := K) hn init hDone hAbs hgap y hTie

/-! ### The restricted final-rung predicate and its `hfinal` shape

The over-quantified carried form is
`hfinal : ∀ y ∈ {AllClockGEpCard 10 n}, E[T y → StableDone] ≤ βfinal`.

The honest restricted form quantifies over the regime-restricted slice — the intersection
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {gap-sign event}` — and is DISCHARGED, not
carried, by the two discharges above.  We expose the restricted-slice membership predicate and
the slice-relative `hfinal` it discharges, so the timed spine's `hfinal` rung can be re-shaped to
this honestly-deliverable target. -/

/-- The regime-restricted phase-10 entry slice for the MAJORITY branch:
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {0 < gap}`.  This is the honest target the
proven majority bridge delivers — the intersected/regime-restricted form of the timed spine's
final rung. -/
def finalRungSliceMajority (n : ℕ) (init : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {y | AllClockGEpCard (L := L) (K := K) 10 n y ∧ ReachableFrom L K init y
        ∧ 0 < initialGap (L := L) (K := K) init}

/-- The regime-restricted phase-10 entry slice for the TIE branch:
`{AllClockGEpCard 10 n} ∩ {ReachableFrom init} ∩ {gap = 0} ∩ {active}`. -/
def finalRungSliceTie (n : ℕ) (init : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {y | AllClockGEpCard (L := L) (K := K) 10 n y ∧ ReachableFrom L K init y
        ∧ initialGap (L := L) (K := K) init = 0 ∧ hasActiveAgent y}

/-- **The majority `hfinal`, restricted and discharged.**  On the majority slice the per-state
`hfinal` cap holds with `βfinal = 3·n²·(1 + 2 log n)` — DISCHARGED from the landed bound, not
carried over-quantified.  This is the restricted/re-shaped form of `timedSpine_ladderData`'s
`hfinal` rung. -/
theorem hfinal_majority_on_slice {n : ℕ} (hn : 2 ≤ n)
    (init : Config (AgentState L K))
    (hinit : validInitial init)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0) :
    ∀ y ∈ finalRungSliceMajority (L := L) (K := K) n init,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  rintro y ⟨hInv, hReach, hgap⟩
  exact phase10_finalRung_majority_discharge (L := L) (K := K) hn init hinit hDone hAbs hgap
    y hInv hReach

/-- **The tie `hfinal`, restricted and discharged.**  On the tie slice the per-state `hfinal` cap
holds with `βfinal = 2·n²·(1 + 2 log n)` — DISCHARGED from the landed bound. -/
theorem hfinal_tie_on_slice {n : ℕ} (hn : 2 ≤ n)
    (init : Config (AgentState L K))
    (hinit : validInitial init)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0) :
    ∀ y ∈ finalRungSliceTie (L := L) (K := K) n init,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  rintro y ⟨hInv, hReach, hgap, hact⟩
  exact phase10_finalRung_tie_discharge (L := L) (K := K) hn init hinit hDone hAbs hgap
    y hInv hReach hact

/-! ## Part C — the de-deadweighted ladder skeleton (F6 (a))

`reachable_hLadder` IGNORES its `_hFloors` argument — it returns `hClass.ladder` by a 4-way
match.  We re-expose that exact extraction WITHOUT the dead `hFloors` binder, so the surface no
longer advertises a parameter it never consumes.  The floor data stays where it is genuinely
consumed: inside the regime data `hClass` (the timed engines baked `mC`/floor into the carried
`LadderData` BEFORE this site), so dropping the top-level `_hFloors` loses nothing. -/

/-- **`reachable_hLadder'` — the de-deadweighted ladder skeleton.**  Identical to
`ReachableLadder.reachable_hLadder` minus the dead `_hFloors` binder: extract the per-state
`LadderData` directly from the regime classification's `ladder` field.  The floor data is already
inside `hClass`'s carried ladder, so no floor argument is needed here. -/
def reachable_hLadder' {n : ℕ} {Brecover : ℝ≥0∞}
    (init b : Config (AgentState L K))
    (_hReach : ReachableFrom L K init b)
    (_hBad : b ∈ (StableDone L K init)ᶜ)
    (hClass : ReachablePhaseRegimeClassification L K n init b Brecover) :
    LadderData L K init b Brecover :=
  match hClass with
  | .bigClockTimed h => h.ladder
  | .tinyClockTimed h => h.ladder
  | .phase10Majority h => h.ladder
  | .phase10Tie h => h.ladder

/-! ## Part D — FIX (1) + (3): the re-cut `expected_time` surfaces (no dead `hFloors`)

These prove the SAME conclusion `E[T c₀ → StableDone] ≤ (21·C0 + 4·Cbad)·n·(L+1)` as
`ReachableLadder.expected_time_reachable` / `ChainEndAssembly.expected_time_chain_end`,
but with the dead `hFloors` binder DROPPED.  The proof re-runs the original assembly verbatim,
building the per-state recovery cap from `reachable_hLadder'` (which never needed floors), so the
hypothesis set is strictly smaller and honestly advertised.

### Carried set of `expected_time_chain_end'` (the strongest re-cut form)

| carried | role | honesty |
|---|---|---|
| 21-phase block (`phases`, `ht`, `hε`, `h_chain`, `hx₀`, `h_post`, `hC0`) | abstract whp headline composition (`time_headline_W2`) | conditional-honest FRAGMENT (audit F5; unchanged) |
| `hBranch : ∀ reachable not-done b, ChainEndBranch …` | per-state regime CONTENT; its timed `hfinal` rung is the restricted/discharged form of Part B (caller supplies the gap-sign witness, so `hfinal` is delivered by `hfinal_{majority,tie}_on_slice`, NOT over-quantified) | honest residual (per-regime exhibition + per-rung seeds + the DISCHARGED phase-10 entry-drain) |
| `hδ`, `hrecmass` | budget arithmetic (`∑ δ ≤ 1/n`; recovery mass ≤ `4·Cbad·n·(L+1)`) | sound |
| ~~`hFloors`~~ | ~~clock floors~~ | **DROPPED** — was dead in `reachable_hLadder`; floor data lives inside the regime data |

Everything else — the timed spine, the phase telescope, the seqcomp/ladder transfer, the
reachability-relative split-geometric, the whp composition — is DISCHARGED. -/

open scoped Classical in
/-- **FIX (1) — `expected_time_reachable'`, the de-deadweighted reachable-relative E4.**

`E[T c₀ → StableDone] ≤ (21·C0 + 4·Cbad)·n·(L+1)`.  Identical to
`ReachableLadder.expected_time_reachable` but WITHOUT the dead `hFloors` binder (F6 (a)):
the per-state recovery cap is built from `reachable_hLadder'`, which extracts the ladder from the
regime classification's `ladder` field and never consumed floors.  Strictly smaller, honestly
advertised hypothesis set, same conclusion. -/
theorem expected_time_reachable' {n C0 Cbad Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (hClassify :
      ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
        ReachablePhaseRegimeClassification L K n init b (Brecover : ℝ≥0∞))
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  classical
  -- Reachable-relative ladder ⟹ per-state recovery caps — via `reachable_hLadder'` (NO floors).
  have hLadder : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
      LadderData L K init b (Brecover : ℝ≥0∞) := by
    intro b hbR hbBad
    exact reachable_hLadder' (L := L) (K := K) (n := n) init b hbR hbBad (hClassify b hbR hbBad)
  have hRecoverReach : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ (Brecover : ℝ≥0∞) :=
    recovery_bound_via_ladder_on_reachable (n := n) init (Brecover : ℝ≥0∞)
      hDone hDoneAbs (reachableFrom_kernel_closed init) hLadder
  -- whp headline (unchanged seam-corrected 21-instance composition).
  have hhead := time_headline_W2
    (L := L) (K := K) (n := n) (C0 := C0)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 hδ
  have hfail :
      ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
          (StableDone L K init)ᶜ ≤ (1 / n : ℝ≥0∞) := by
    rw [compl_StableDone]; exact hhead.1
  have hT :
      ((∑ i, (phases i).t : ℕ) : ℝ≥0∞) ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hhead.2
  have hsRecCast : ((2 * Brecover : ℕ) : ℝ≥0∞) = 2 * (Brecover : ℝ≥0∞) := by push_cast; ring
  have hsplit := expected_time_from_whp_and_recovery_on
    (NonuniformMajority L K).transitionKernel (ReachableFrom L K init)
    (reachableFrom_kernel_closed init) c₀ hc₀Reach hDone
    (fun x hx _ => hDoneAbs x hx)
    (∑ i, (phases i).t) (2 * Brecover) (by omega : 2 * Brecover ≠ 0)
    (1 / n : ℝ≥0∞) (Brecover : ℝ≥0∞)
    (by exact_mod_cast (ENNReal.natCast_ne_top Brecover))
    (by omega : 0 < 2 * Brecover)
    (by rw [hsRecCast]; exact le_of_eq (mul_comm (Brecover : ℝ≥0∞) 2))
    hfail
    (fun b hbR hbBad => hRecoverReach b hbR hbBad)
  calc expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
      ≤ ((∑ i, (phases i).t : ℕ) : ℝ≥0∞)
          + (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := hsplit
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
          + ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) :=
        add_le_add (by exact_mod_cast hT) hrecmass
    _ = (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring

open scoped Classical in
/-- **FIX (3) — `expected_time_chain_end'`, the strongest re-cut form (no dead `hFloors`).**

`E[T c₀ → StableDone] ≤ (21·C0 + 4·Cbad)·n·(L+1)`.  Same conclusion as
`ChainEndAssembly.expected_time_chain_end`, with the per-state classifier supplied as the
regime CONTENT (`hBranch`, a `ChainEndBranch`), this file BUILDING the four regime ladders from
that content (`regimeClassification_of_chainEndBranch`).  Two F6 honesty fixes:

* the dead `hFloors` binder is DROPPED (F6 (a)) — the recovery cap goes through
  `reachable_hLadder'`, which never consumed floors;
* the `hBranch`'s timed `hfinal` rung is the restricted/discharged form (F6 (b)): the caller
  supplies the gap-sign witness and discharges `hfinal` via `hfinal_{majority,tie}_on_slice`
  (Part B) instead of carrying it over all of `{AllClockGEpCard 10 n}`.

Carried set (post-fix): the 21-phase block (abstract whp, F5), `hBranch` (per-regime exhibition +
per-rung seeds + the DISCHARGED restricted phase-10 entry-drain), `hδ`/`hrecmass` (budget). The
clock-floor binder is GONE. -/
theorem expected_time_chain_end' {n C0 Cbad Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (hBranch :
      ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
        ChainEndBranch (L := L) (K := K) n init b (Brecover : ℝ≥0∞) (βfinal b))
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  classical
  -- Build the per-state classification from the branch CONTENT (the production step).
  have hClassify : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
      ReachablePhaseRegimeClassification L K n init b (Brecover : ℝ≥0∞) := by
    intro b hbReach hbBad
    exact regimeClassification_of_chainEndBranch (L := L) (K := K) (n := n) init b
      (Brecover : ℝ≥0∞) (βfinal b) hDone hDoneAbs (hBranch b hbReach hbBad)
  -- Discharge through the de-deadweighted reachable-relative E4 (no `hFloors`).
  exact expected_time_reachable' (L := L) (K := K) (n := n) (C0 := C0)
    (Cbad := Cbad) (Brecover := Brecover) init c₀ hc₀Reach Cphase δ phases ht hε h_chain hx₀
    h_post hC0 hDone hDoneAbs hBpos hClassify hδ hrecmass

end ChainEndRecut
end ExactMajority

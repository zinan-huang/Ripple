/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase1SurvivalContracting — the CONTRACTING (`r < 1`) slot-1 averaging-drain survival.

This append-only file edits NO existing file.  It builds the slot-1 (Doty §5 / Lemma 5.3
integer-averaging) SURVIVAL by applying the proven contracting-drain template of
`GatedDrainContracting` (slot-5) / `Phase6SurvivalContracting` (slot-6) to the Phase-1
saturated-extreme potential `extremeU` (`Phase1Convergence.extremeU`).  It is the EXACT
mirror of `phase6_survival_contracting`, with the Phase-1 averaging pieces substituted.

## The template (REUSED verbatim — `GatedDrainContracting`)
The generic engines, ALL stated over an abstract kernel / potential / gate, are:
* `GatedDrift.gated_real_tail_anyr` — the `r`-arbitrary gated tail (NO `hr : 1 ≤ r`); the drain
  term `r^T·Φ T/θ` shrinks iff `r < 1`.
* `expDrainPot_drift_contracting` — the CONTRACTING MGF drift
  `∫ exp(s·Φ) dK ≤ contractRate ρ s · exp(s·Φ)` on a gate, from a per-step DROP floor `ρ` and a
  NEVER-INCREASE property; `contractRate_lt_one` gives `r = contractRate ρ s < 1` whenever
  `0 < ρ ≤ 1`, `s > 0`.
* `drain_term_tendsto_zero` / `drain_term_shrinks` — the genuine non-vacuity (`r^T·coef → 0`).

We REUSE these directly.  Slot-1 differs ONLY in the concrete substitution.

## The slot-1 substitution
* potential `Φ := extremeU` (Doty §5 saturated-extreme count, `Phase1Convergence.extremeU`):
  the number of phase-1 Mains pinned at the saturated bias ends `±3` — the extreme bias mass the
  averaging interaction drains inward.  `Φ = 0` is the honest Lemma-5.3-shape post `NoExtreme`.
* gate `G1 := {c | Phase1Honest n c}` — the chain-SATISFIABLE phase-only Phase-1 window
  (`HonestWindows.Phase1Honest`, card `= n` ∧ all phase `= 1`, NO role pin — the satisfiable
  window, NOT the unsatisfiable all-Main one).  The drift's structural needs (the `+3` extreme
  witness `hext` and the partner-pool floor `hpull`, Lemma 5.3) are the EXPLICIT isolated residuals
  of `Phase1Honest → ...` shape, carried as binders — NEVER manufactured, NEVER an `InvClosed` of
  the window.  These are exactly the `hext`/`hpull` binders of `HonestDrainSlots.hdrop1_honest`.
* per-step DROP floor `ρ := ofReal(P/(n(n−1)))` on the drop event
  `{c' | extremeU c' + 1 ≤ extremeU c}`, supplied DIRECTLY (no `potBelow`-complement detour) by
  `HonestDrainSlots.phase1_drop_floor_honest` — the COUNTED `extremePosSet ×ˢ pullPosSet` rectangle
  over `n(n−1)` (NOT an external [45] import; the same `drop_prob_of_rect` pair-counting the landed
  `extremeU`/Phase-8 chain uses).  `P` is the partner pool floor, instantiated below from Lemma 5.3.
* NEVER-INCREASE: `HonestWindows.potNonincrOn_extremeU_honest` (`extremeU` is `PotNonincrOn` on
  `Phase1Honest n`), supplying `K c {c' | extremeU c < extremeU c'} = 0`.  Averaging never CREATES
  a saturated extreme (`avgFin7_extremeVal_pair_le`, exhaustive over 49 pairs).
* contracting rate `r := contractRate (ofReal(P/(n(n−1)))) s < 1` whenever the drop floor is
  positive (`P > 0`, `2 ≤ n`) and `s > 0`.

## The CONTRACTING `r < 1` (the whole point)
The drain CONTRACTS on the gate: `contractRate (ofReal(P/(n(n−1)))) s < 1`.  Verified STRICTLY by
`dropFloor1_pos` (the rectangle drop floor `ofReal(P/(n(n−1)))` is `> 0` exactly when `P > 0` and
`n ≥ 2`) feeding `contractRate_lt_one`.  An `r ≥ 1` "drift" is the vacuous trap; here `r < 1`
strictly, so `r^T → 0` (`drain_term_tendsto_zero`).

## The Phase-1 CLOCK mechanism (INVESTIGATED — the escape is the SIMPLE case)
`Phase1Transition` ends with `(clockCounterStep s1, clockCounterStep t1)`: an internal counter
runs.  BUT `clockCounterStep` preserves an agent's `phase` and `role` (`HonestWindows`
`Transition_role_phase1` / the all-Main `Transition_eq_avg_of_phase1_main`), so within the phase-1
window the PHASE field stays at `1`.  Phase 1 is COUNTER-TIMED: the phase ADVANCE (to phase 2)
fires at the clock timeout, which flips `phase` and so LEAVES `Phase1Honest`.  Therefore:
* the gate `Phase1Honest` does NOT spuriously leak during the drain — `extremeU` does not change
  phase, and an applicable phase-1 pair stays phase-1 (the never-increase / honest closure content);
* the ONLY escape is the clock-timeout WINDOW-LEAVE `{c | ¬ Phase1Honest n c}`, carried as the
  abstract one-step leak `q_leak` and the cumulative prefix sum (the `kill_escape_le_prefix_union`
  engine).  Phase-1 clocks ADVANCE the phase only at timeout, so the escape is the CUMULATIVE
  window-leave (NOT a one-step `T·η`), exactly the slot-6 shape; if the window-leave per-step leak
  is `0` (the gate's honest closure), the escape term collapses, but we keep it ABSTRACT to avoid
  any `InvClosed` claim.

## The Lemma-5.3 partner floor `P1 = (mc − g + 3)/4`
The partner-pool floor `hpull` is supplied by `HonestFloorAtoms.hpull1H_of_honestEntry`:
on a `HonestEntry n g mc` window the partner pool `pullPosSet.sum count ≥ P1 = (mc − g + 3)/4`,
a FIXED population scalar (the algebra is PROVEN, role-free).  `phase1_partner_floor_523` wires it
into the `hpull` binder; the survival is then instantiated at `P = P1`.

## ANTI-TRAP compliance
* NO `InvClosed` / `hClosed` / `levels_PhaseConvergenceW` of any phase window.
* The drain CONTRACTS (`r < 1` STRICTLY, `phase1_contractRate_lt_one`).
* The clock escape is CUMULATIVE (`∑_{τ<T}`), never a one-step `T·η`.
* Every carried residual is a per-step LOWER bound (the rectangle drop floor `P/(n(n−1))`, a
  PROGRESS bound) or a monotone window-leave; no one-step closure of a decreasing quantity.
* The partner floor `P1 = (mc − g + 3)/4` is the PROVEN `HonestFloorAtoms` algebra (refutation:
  it is a population count derived from the honest-entry gap, satisfiable, NOT the goal smuggled).

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedDrainContracting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestDrainSlotsCore
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestFloorAtoms

namespace ExactMajority
namespace Phase1SurvivalContracting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the slot-1 per-step DROP floor `ρ = ofReal(P/(n(n−1)))`.

`HonestDrainSlots.phase1_drop_floor_honest` gives the DROP-EVENT floor DIRECTLY (no `potBelow`-
complement detour): on a `Phase1Honest` config with `≥ 1` saturated-extreme witness (`hext`) and a
partner pool of size `≥ P` (`hpull`), the one-step kernel mass of the drop event
`{c' | extremeU c' + 1 ≤ extremeU c}` is `≥ ofReal(P/(n(n−1)))`.  This is exactly the `hdrop` input
shape `expDrainPot_drift_contracting` consumes (since `transitionKernel c = (stepDistOrSelf c).toMeasure`
definitionally). -/

/-- **The slot-1 drop-event floor** in the `transitionKernel` form.  Restates
`HonestDrainSlots.phase1_drop_floor_honest` against `(NonuniformMajority L K).transitionKernel`
(definitionally equal to `(stepDistOrSelf ·).toMeasure`). -/
theorem extremeU_drop_floor {n : ℕ} (hn : 2 ≤ n) (P : ℕ)
    (b : Config (AgentState L K))
    (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n b)
    (hext : 1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU b} := by
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  rw [hKb]
  exact HonestDrainSlots.phase1_drop_floor_honest n hn b hInv P hext hpull

/-! ## Part 2 — the slot-1 NEVER-INCREASE (from `potNonincrOn_extremeU_honest`). -/

/-- **`extremeU` never increases on `Phase1Honest n`** in the `hnoincr` shape
`K c {c' | extremeU c < extremeU c'} = 0`.  Directly from `potNonincrOn_extremeU_honest`.
Averaging never CREATES a saturated extreme (exhaustive `avgFin7_extremeVal_pair_le`); a non-Main
output is never `extremeSt`; hence `extremeU` cannot rise on any applicable phase-1 pair. -/
theorem extremeU_noincr {n : ℕ}
    (b : Config (AgentState L K))
    (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n b) :
    (NonuniformMajority L K).transitionKernel b
        {c' | Phase1Convergence.extremeU b < Phase1Convergence.extremeU c'} = 0 :=
  HonestWindows.potNonincrOn_extremeU_honest n b hInv

/-! ## Part 3 — the slot-1 CONTRACTING MGF drift on `extremeU`.

Instantiate `expDrainPot_drift_contracting` with `U := extremeU`, drop floor
`ρ := ofReal(P/(n(n−1)))`, and the never-increase from `extremeU_noincr`.  The resulting factor is
`contractRate (ofReal(P/(n(n−1)))) s`, shown `< 1` strictly (Part 4). -/

/-- **The slot-1 contracting MGF drift** at a `Phase1Honest` config `b` on the gate.  The MGF
potential `expDrainPot extremeU s` contracts by `contractRate (ofReal(P/(n(n−1)))) s` per step. -/
theorem expDrainPot_extremeU_drift {n : ℕ} (hn : 2 ≤ n) (P : ℕ)
    (s : ℝ) (hs : 0 ≤ s)
    (b : Config (AgentState L K))
    (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n b)
    (hext : 1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    ∫⁻ c', expDrainPot (L := L) (K := K)
        (fun c => Phase1Convergence.extremeU c) s c'
        ∂((NonuniformMajority L K).transitionKernel b)
      ≤ contractRate (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) s
          * expDrainPot (L := L) (K := K)
              (fun c => Phase1Convergence.extremeU c) s b := by
  refine expDrainPot_drift_contracting (L := L) (K := K)
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase1Convergence.extremeU c) s hs
    (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b ?_ ?_
  · exact extremeU_drop_floor hn P b hInv hext hpull
  · exact extremeU_noincr b hInv

/-! ## Part 4 — the CONTRACTING rate `r < 1` (STRICT; the whole point).

`r = contractRate (ofReal(P/(n(n−1)))) s`.  `contractRate_lt_one` needs `0 < ρ` and `ρ ≤ 1` for
`ρ = ofReal(P/(n(n−1)))`.  We supply `0 < ofReal(P/(n(n−1)))` (the rectangle drop floor is positive,
from `P > 0` and `n ≥ 2`) and `ofReal(P/(n(n−1))) ≤ 1` (a probability, from `P ≤ n(n−1)`).  This is
the STRICT verification the anti-trap demands: an `r ≥ 1` drift is vacuous. -/

/-- **The slot-1 drop floor `ofReal(P/(n(n−1)))` is positive** when `0 < P` (`hPpos`) and `2 ≤ n`
(`hn`).  This is the NON-VACUITY of the contraction: a zero drop floor would give `r = 1` (vacuous).
The floor positivity is exactly the rectangle having a nonempty extreme pool (`P ≥ 1`). -/
theorem dropFloor1_pos {P n : ℕ} (hn : 2 ≤ n) (hPpos : 0 < P) :
    0 < ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  apply ENNReal.ofReal_pos.mpr
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  apply div_pos _ hden
  have : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPpos
  linarith

/-- **The slot-1 drop floor `ofReal(P/(n(n−1)))` is `≤ 1`** when `P ≤ n(n−1)` (`hPle`), i.e. the
partner-pool floor cannot exceed the total interaction count — it is a probability.  (Always true
for a counted rectangle pool; here exposed as the explicit hypothesis the rate ceiling needs.) -/
theorem dropFloor1_le_one {P n : ℕ} (hn : 2 ≤ n) (hPle : (P : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 := by
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
  apply ENNReal.ofReal_le_ofReal
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [div_le_one hden]; exact hPle

/-- **The slot-1 contracting rate is STRICTLY `< 1`.**  `r = contractRate (ofReal(P/(n(n−1)))) s < 1`
whenever the drop floor is positive (`dropFloor1_pos`, i.e. `P > 0`), `≤ 1` (`dropFloor1_le_one`,
i.e. `P ≤ n(n−1)`), and `s > 0`.  This is the linchpin of non-vacuity: with `r < 1` the drain term
`r^T·coef → 0` (`drain_term_tendsto_zero`); an `r ≥ 1` "drift" would be the vacuous trap. -/
theorem phase1_contractRate_lt_one {P n : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hPpos : 0 < P) (hPle : (P : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    contractRate (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) s < 1 := by
  apply contractRate_lt_one s hs
  · exact dropFloor1_pos hn hPpos
  · exact dropFloor1_le_one hn hPle

/-! ## Part 5 — the Lemma-5.3 partner floor `P1 = (mc − g + 3)/4` wired into `hpull`.

`HonestFloorAtoms.hpull1H_of_honestEntry` proves (role-free algebra) that on a `HonestEntry n g mc`
window, `pullPosSet.sum count ≥ (mc − g + 3)/4`.  We restate it as the `hpull` binder over
`Phase1Honest` whenever every honest config is a `HonestEntry` (the honest-entry persistence,
carried).  The floor `P1 = (mc − g + 3)/4` is a FIXED population scalar. -/

/-- **The Lemma-5.3 partner floor wired to `hpull` over `Phase1Honest`.**  Given honest-entry
persistence (every `Phase1Honest n b` is a `HonestEntry n g mc b`), the partner-pool floor
`P1 = (mc − g + 3)/4 ≤ pullPosSet.sum count` holds on every gate config — exactly the `hpull` binder
the drift consumes.  The floor algebra is `HonestFloorAtoms.hpull1H_of_honestEntry` (PROVEN). -/
theorem phase1_partner_floor_523 {n : ℕ} (g mc : ℕ)
    (hentry : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
      HonestFloorAtoms.HonestEntry (L := L) (K := K) n g mc b) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
      (mc - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count := by
  intro b hb
  exact HonestFloorAtoms.pullPos_floor_of_honestEntry n g mc b (hentry b hb)

/-! ## Part 6 — the composed slot-1 SURVIVAL (CONTRACTING `r < 1`, genuinely shrinking).

The EXACT mirror of `phase6_survival_contracting`.  From a Phase-1-honest start `c₀`, the
probability that the slot-1 averaging-drain FAILS to drain the saturated-extreme mass
(`{c | θ ≤ Φ_E c}`, the survival of a saturated-extreme surplus) at horizon `T` is at most
`ε_drain + η_clock + η_struct`:

* `ε_drain` — the CONTRACTING drain `r^T·Φ_E c₀/θ` plus the small window-leave leak `T·q_leak`,
  with `r = contractRate (ofReal(P/(n(n−1)))) s < 1` so it GENUINELY SHRINKS;
* `η_clock` — the CUMULATIVE clock-timeout prefix-failure sum `∑_{τ<T} (K^τ) c₀ Sᶜ`, NEVER `T·η`;
* `η_struct` — the §5 window-leave escape (the isolated TRUE residual).

This reuses `phase6_survival_contracting`'s downstream engines via `gated_real_tail_anyr`; we
re-prove the same composition with gate `{c | Phase1Honest n c}` and structural-escape set `Aconf`
ABSTRACT (the §5 residual).  NO `InvClosed` of `Phase1Honest`. -/

open GatedDrift

/-- **CONTRACTING slot-1 averaging-drain survival (`r < 1`).**  Mirrors
`Phase6SurvivalContracting.phase6_survival_contracting` with the Phase-1 potential
`Φ_E := extremeU` and gate `G1 := {c | Phase1Honest n c}`.  The drain engine carries NO `hr : 1 ≤ r`,
so `r` is the contracting `contractRate (ofReal(P/(n(n−1)))) s < 1` (`phase1_contractRate_lt_one`),
making `r^T·Φ_E c₀/θ` genuinely shrink.

`Aconf` is the §5 window-leave / clock-timeout escape set (abstract); `hcover` says the survival
event `{¬ Phase1Done}` is covered by the structural escape `Aconf` plus the saturated-extreme
surplus `{θ ≤ Φ_E}`.  NO `InvClosed` of `Phase1Honest`. -/
theorem phase1_survival_contracting {n : ℕ}
    (Φ_E : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hEdrift : ∀ x ∈ {c | HonestWindows.Phase1Honest (L := L) (K := K) n c},
      ∫⁻ y, Φ_E y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_E x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | HonestWindows.Phase1Honest (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | HonestWindows.Phase1Honest (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (c₀ : Config (AgentState L K))
    (hWin₀ : HonestWindows.Phase1Honest (L := L) (K := K) n c₀)
    (εdrain : ℝ≥0)
    (hεdrain : ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_E c₀ / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (η_clock η_struct : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ η_clock)
    (Phase1Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hStruct : ((NonuniformMajority L K).transitionKernel ^ T) c₀ Aconf ≤ η_struct)
    (hcover : {c : Config (AgentState L K) | ¬ Phase1Done c}
      ⊆ Aconf ∪ {c | θ ≤ Φ_E c}) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | ¬ Phase1Done c}
      ≤ (εdrain : ℝ≥0∞) + η_clock + η_struct := by
  classical
  -- gated tail (NO hr): real high-Φ tail ≤ cemetery escape + CONTRACTING drain supermartingale.
  have hgated := GatedDrift.gated_real_tail_anyr
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | HonestWindows.Phase1Honest (L := L) (K := K) n c})
    Φ_E r hEdrift T c₀ θ hθ0 hθtop
  -- cemetery escape ≤ small leak + cumulative clock prefix-failures.
  have hesc := GatedDrift.kill_escape_le_prefix_union
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | HonestWindows.Phase1Honest (L := L) (K := K) n c})
    S q_leak hLeak T c₀ hWin₀
  -- compose: real tail ≤ (T·q_leak + ∑_{τ<T} Sᶜ) + r^T·Φ_E c₀/θ.
  have hdrain0 :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ_E c}
        ≤ ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ_E c₀ / θ :=
    le_trans hgated (add_le_add hesc le_rfl)
  have hdrain : ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ_E c}
      ≤ (εdrain : ℝ≥0∞) + η_clock := by
    refine le_trans hdrain0 ?_
    calc ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ_E c₀ / θ
        = ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_E c₀ / θ)
          + ∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ := by ring
      _ ≤ (εdrain : ℝ≥0∞) + η_clock := add_le_add hεdrain hClock
  set μ := ((NonuniformMajority L K).transitionKernel ^ T) c₀ with hμ
  set Adrain : Set (Config (AgentState L K)) := {c | θ ≤ Φ_E c} with hAdrain
  calc μ {c | ¬ Phase1Done c}
      ≤ μ (Aconf ∪ Adrain) := measure_mono hcover
    _ ≤ μ Aconf + μ Adrain := measure_union_le _ _
    _ ≤ η_struct + ((εdrain : ℝ≥0∞) + η_clock) := add_le_add hStruct hdrain
    _ = (εdrain : ℝ≥0∞) + η_clock + η_struct := by ring

/-! ## Part 7 — the drain genuinely SHRINKS (non-vacuity, the whole point).

The contracting `r < 1` makes `r^T·coef → 0`; this is FALSE for `r ≥ 1`.  We reuse
`drain_term_tendsto_zero` / `drain_term_shrinks` at the slot-1 rate, combined with
`phase1_contractRate_lt_one`. -/

/-- **The slot-1 contracting drain is GENUINELY non-vacuous.**  The rate
`r = contractRate (ofReal(P/(n(n−1)))) s` is `< 1` (`phase1_contractRate_lt_one`), and its drain term
`r^T·coef` shrinks below any `ε > 0` past a threshold (`drain_term_shrinks`).  This is exactly what
an `r ≥ 1` "drift" CANNOT supply.  Requires the partner pool floor `P > 0`. -/
theorem phase1_contracting_drain_nonvacuous {P n : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hPpos : 0 < P) (hPle : (P : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1))
    (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    contractRate (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) s < 1
      ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
          (contractRate (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) s) ^ T * coef ≤ ε := by
  have hlt := phase1_contractRate_lt_one s hs hn hPpos hPle
  exact ⟨hlt, drain_term_shrinks _ hlt coef hcoef ε hε⟩

/-- **The slot-1 drain term tends to `0`** (the shrink, restated at the slot-1 rate).  For the
contracting `r = contractRate (ofReal(P/(n(n−1)))) s < 1`, `r^T·coef → 0` as `T → ∞`. -/
theorem phase1_drain_tendsto_zero {P n : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hPpos : 0 < P) (hPle : (P : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1))
    (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) :
    Filter.Tendsto
      (fun T : ℕ => (contractRate (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) s) ^ T * coef)
      Filter.atTop (nhds 0) :=
  drain_term_tendsto_zero _ (phase1_contractRate_lt_one s hs hn hPpos hPle) coef hcoef

/-! ## Part 8 — the END-TO-END contracting slot-1 survival from the structural inputs.

The capstone: feed the COUNTED drop floor (`expDrainPot_extremeU_drift`), the contracting rate
(`phase1_contractRate_lt_one`), and the Lemma-5.3 partner floor into the composition — so the only
inputs are the raw structural residuals (`hext`, `hentry` for the partner floor, the abstract
window-leave / clock escape) and the protocol parameters.  The drift hypothesis of
`phase1_survival_contracting` is DISCHARGED from the per-step floor + never-increase. -/

/-- **End-to-end CONTRACTING slot-1 survival from structural inputs.**  Combines the per-step
averaging drop floor (COUNTED rectangle, via `expDrainPot_extremeU_drift`) at the Lemma-5.3 partner
floor `P1 = (mc − g + 3)/4` with the contracting composition.  The drift binder is no longer free:
it is produced from `hext` (the `+3` extreme witness over the gate) and `hentry` (the honest-entry
persistence supplying the partner floor).  The conclusion BUNDLES the contraction
`r = contractRate (ofReal(P1/(n(n−1)))) s < 1` (so `hP1pos`/`hP1le` are genuinely consumed — the
result is NOT vacuous) with the survival tail bound.

Inputs are exactly: the protocol size `n ≥ 2`; the MGF parameter `s > 0`; the extreme witness
`hext`; the honest-entry persistence `hentry` (Lemma 5.3 floor source); the abstract window-leave
escape `S`/`q_leak`/`hLeak`/`hClock`/`Aconf`/`hStruct`/`hcover`; and the budget bookkeeping.  NO
`InvClosed`. -/
theorem phase1_survival_contracting_e2e {n : ℕ} (g mc : ℕ) (hn : 2 ≤ n)
    (hP1pos : 0 < (mc - g + 3) / 4)
    (hP1le : (((mc - g + 3) / 4 : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1))
    (s : ℝ) (hs : 0 < s)
    (hext : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hentry : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
      HonestFloorAtoms.HonestEntry (L := L) (K := K) n g mc b)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | HonestWindows.Phase1Honest (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | HonestWindows.Phase1Honest (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (c₀ : Config (AgentState L K))
    (hWin₀ : HonestWindows.Phase1Honest (L := L) (K := K) n c₀)
    (εdrain : ℝ≥0)
    (hεdrain : ((T : ℝ≥0∞) * q_leak
        + (contractRate (ENNReal.ofReal (((((mc - g + 3) / 4 : ℕ)) : ℝ)
              / ((n : ℝ) * ((n : ℝ) - 1)))) s) ^ T
            * expDrainPot (L := L) (K := K) (fun c => Phase1Convergence.extremeU c) s c₀ / θ
          : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (η_clock η_struct : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ η_clock)
    (Phase1Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hStruct : ((NonuniformMajority L K).transitionKernel ^ T) c₀ Aconf ≤ η_struct)
    (hcover : {c : Config (AgentState L K) | ¬ Phase1Done c}
      ⊆ Aconf ∪ {c | θ ≤ expDrainPot (L := L) (K := K) (fun c => Phase1Convergence.extremeU c) s c}) :
    contractRate (ENNReal.ofReal (((((mc - g + 3) / 4 : ℕ)) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1)))) s < 1
      ∧ ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | ¬ Phase1Done c}
          ≤ (εdrain : ℝ≥0∞) + η_clock + η_struct := by
  classical
  set P1 : ℕ := (mc - g + 3) / 4 with hP1
  set r : ℝ≥0∞ := contractRate (ENNReal.ofReal ((P1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) s with hr
  -- the CONTRACTING rate is STRICTLY < 1 (consumes hP1pos / hP1le; non-vacuity)
  have hrlt : r < 1 := phase1_contractRate_lt_one s hs hn hP1pos hP1le
  -- the Lemma-5.3 partner floor over the gate
  have hpull := phase1_partner_floor_523 (L := L) (K := K) g mc hentry
  -- DISCHARGE the drift binder from the per-step floor + never-increase
  have hEdrift : ∀ x ∈ {c | HonestWindows.Phase1Honest (L := L) (K := K) n c},
      ∫⁻ y, expDrainPot (L := L) (K := K) (fun c => Phase1Convergence.extremeU c) s y
        ∂((NonuniformMajority L K).transitionKernel x)
        ≤ r * expDrainPot (L := L) (K := K) (fun c => Phase1Convergence.extremeU c) s x := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    exact expDrainPot_extremeU_drift hn P1 s hs.le x hx (hext x hx) (hpull x hx)
  -- compose
  refine ⟨hrlt, ?_⟩
  exact phase1_survival_contracting
    (Φ_E := expDrainPot (L := L) (K := K) (fun c => Phase1Convergence.extremeU c) s)
    (r := r) hEdrift S q_leak hLeak T θ hθ0 hθtop c₀ hWin₀ εdrain hεdrain
    η_clock η_struct hClock Phase1Done Aconf hStruct hcover

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms extremeU_drop_floor
#print axioms extremeU_noincr
#print axioms expDrainPot_extremeU_drift
#print axioms dropFloor1_pos
#print axioms dropFloor1_le_one
#print axioms phase1_contractRate_lt_one
#print axioms phase1_partner_floor_523
#print axioms phase1_survival_contracting
#print axioms phase1_contracting_drain_nonvacuous
#print axioms phase1_drain_tendsto_zero
#print axioms phase1_survival_contracting_e2e

end Phase1SurvivalContracting
end ExactMajority

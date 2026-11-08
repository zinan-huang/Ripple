/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Drain RATES — the per-LEVEL drop-rate binder from the landed structural floors

`CrudeWorkFamily.lean` (wave A) made the 11 `Assembly` WORK slots concrete, but left the
per-phase drain RATES (the `hstep`/`hdrop` residuals in its slot table) as carried `Hypotheses`
fields.  This file (wave B — the per-phase drain RATES) discharges the genuinely-landed shape of
those rates: the **per-LEVEL drop-rate binder** consumed by the levels engine
(`OneSidedCancel.levels_PhaseConvergenceW`),

* `hdrop` :  `∀ m, ∀ b, PhaseInv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m`,

at the calibrated per-level rate `q m := 1 − ENNReal.ofReal (E / (n(n−1)))` (constant in `m`).
This is EXACTLY the conclusion the campaign's landed floor adapters produce
(`PhaseFloors.phase{1,5,6,7,8}_hdrop_wired`, `AssemblyWiring.slot{7,8}_levels_hdrop`): the per-step
mass on "the active level-`m` mass does NOT strictly drop" is at most `1 − ofReal(E/(n(n−1)))`,
the honest multi-level mass drain (the drop RECTANGLE is `(minority/eliminator pool) × (partner
pool)`, mass `≥ E`, normalised by the interaction total `n(n−1)`).

## Why per-LEVEL, not the crude single rate `potDone`

The four calibrated drain instances (slots 1/5/7/8) feed `OneSidedCancel.crude_PhaseConvergenceW`
with the SINGLE-rate `potDone` shape `K b (potDone Φ)ᶜ ≤ ofReal q` — "drop to `0` in one step".
That crude rate is, per the campaign doc, "structurally vacuous for `Φ ≥ 2`" (you cannot drain
mass `≥ 2` to `0` in a single interaction at the rectangle rate); it coincides with the landed
floor ONLY at level `m = 1` (`potDone Φ = potBelow Φ 1`, `Φ < 1 ↔ Φ = 0` — recorded as
`potDone_eq_potBelow_one`).  The HONEST, multi-level drain is the per-LEVEL floor, which is what
the levels engine consumes and what the slot-6 instance already carries (`hdrop6`).  This file
delivers that per-level rate for all five drain slots, wired from the landed structural floors.

## The per-slot drain-rate table (wired vs persistence-carried floor)

| slot | binder `Φ`          | floor adapter                          | floor: WIRED or PERSISTENCE-carried `∀ b` |
|------|---------------------|----------------------------------------|-------------------------------------------|
| 1    | `extremeU`          | `PhaseFloors.phase1_hdrop_of_struct`       | `hext` (+3 witness) + `hpull` (Lemma 5.3) — PERSISTENCE-carried |
| 5    | `unsampledReserveU` | `PhaseFloors.phase5_hdrop_of_struct`       | `hres` WIRED from binder alive (`= unsampledReserves.sum`); `hmain` (Thm 6.2) PERSISTENCE-carried |
| 6    | `highMass l`        | `PhaseFloors.phase6_hdrop_of_phase5Post`       | reserve floor WIRED from Phase-5 `ReserveSampleGood` Post (per config) |
| 7    | `classMassN σ`      | `CrudeWorkFamily.phase7_levels_hdrop`    | `Phase6To7Structure` (Lemma 7.4) PERSISTENCE-carried; minority witness PROVED |
| 8    | `minorityU σ`       | `CrudeWorkFamily.phase8_levels_hdrop`    | `Phase7To8Structure` (Lemma 7.6) PERSISTENCE-carried; minority witness PROVED |

"PERSISTENCE-carried `∀ b`" : the structural floor enters as a hypothesis quantified over EVERY
in-phase window config `b`, not merely the entry config — exactly the form the `Hypotheses` fields
(`hPhase6Post7`, `hPhase7Post8`) and the floor-source theorems carry.  The per-level `hdrop` binder
is itself `∀ m, ∀ b`, so the floor MUST persist through the window; the carried form is already the
persistent one.  For slots 7/8 the minority-WITNESS half is PROVED inside the floor lemmas; only
the eliminator-COUNT lower bound is the carried named remainder.  For slots 5/6 the alive-witness
is WIRED from the binder / the prior-phase Post.

APPEND-ONLY: imports the landed surfaces, edits NO existing file.  No sorry/admit/axiom/
native_decide.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.CrudeWorkFamily

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DrainRates

variable {L K : ℕ}

/-! ## Part A — the level-`1` ⇄ `potDone` bridge (the crude-rate coincidence).

`potDone Φ = {Φ = 0}` and `potBelow Φ 1 = {Φ < 1} = {Φ = 0}`, so the crude single-rate `potDone`
shape and the per-level floor coincide at `m = 1`.  Recorded here so the honest scope of the crude
rate (level `1` only) is explicit. -/

/-- `potDone Φ = potBelow Φ 1`: hitting `0` is exactly being strictly below level `1`. -/
theorem potDone_eq_potBelow_one {α : Type*} (Φ : α → ℕ) :
    OneSidedCancel.potDone Φ = OneSidedCancel.potBelow Φ 1 := by
  ext x
  simp only [OneSidedCancel.potDone, OneSidedCancel.potBelow, Set.mem_setOf_eq]
  omega

/-- **The crude-rate coincidence at level 1.**  A landed level-`1` floor
`K b (potBelow Φ 1)ᶜ ≤ 1 − ENNReal.ofReal r` (`0 ≤ r`) IS the calibrated crude `hstep` rate
`K b (potDone Φ)ᶜ ≤ ENNReal.ofReal (1 − r)`.  (Used only when the active mass is exactly `1`; for
`Φ ≥ 2` the crude rate is vacuous and the per-level rate of Part B is the honest one.) -/
theorem hstep_of_potBelow_one_floor {α : Type*} [MeasurableSpace α]
    {Kr : ProbabilityTheory.Kernel α α} {b : α} {Φ : α → ℕ} {r : ℝ}
    (hr0 : 0 ≤ r)
    (hfloor : Kr b (OneSidedCancel.potBelow Φ 1)ᶜ ≤ 1 - ENNReal.ofReal r) :
    Kr b (OneSidedCancel.potDone Φ)ᶜ ≤ ENNReal.ofReal (1 - r) := by
  rw [potDone_eq_potBelow_one, CrudeWorkFamily.ofReal_one_sub hr0]
  exact hfloor

/-! ## Part B — the per-slot per-LEVEL drain-rate dischargers.

Each `hdrop{N}_of_chain` takes the structural floor facts (the persistence-carried named
remainders) and produces the EXACT per-level `hdrop` binder of the levels engine, at the
calibrated per-level rate `q m := 1 − ENNReal.ofReal (E / (n(n−1)))`. -/

/-- The calibrated per-level drain rate `q m := 1 − ENNReal.ofReal (E/(n(n−1)))` (constant in `m`):
the per-step mass on "the level-`m` active pool does NOT strictly drop". -/
noncomputable def levelRate (E n : ℕ) : ℕ → ℝ≥0∞ :=
  fun _ => 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- **slot 1 — the `extremeU` averaging-drain per-level rate.**  From the +3 extreme witness
(`hext`) and the partner-pool floor (`hpull`, Lemma 5.3 / [45]; both PERSISTENCE-carried over every
in-window config `b`), `ExactMajority.DrainThreading.phase1_hdrop_of_struct` gives the per-level drop floor at
`q m := levelRate P n`. -/
theorem hdrop1_of_chain {n : ℕ} (hn : 2 ≤ n) (P : ℕ)
    (hext : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    ∀ m, ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      Phase1Convergence.extremeU b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ ≤ levelRate P n m := by
  intro m b hInv hbm
  exact ExactMajority.DrainThreading.phase1_hdrop_of_struct n m hn b hInv hbm P (hext b hInv) (hpull b hInv)

/-- **slot 5 — the `unsampledReserveU` reserve-drain per-level rate.**  The alive-witness `hres` is
WIRED from the binder shape itself (`unsampledReserveU = unsampledReserves.sum count`; a positive
level `m ≥ 1` makes the pool nonempty).  The biased-Main floor `hmain` (Theorem 6.2, PERSISTENCE-
carried) supplies the eliminator pool; `ExactMajority.DrainThreading.phase5_hdrop_of_struct` gives the rate at
`q m := levelRate P n`. -/
theorem hdrop5_of_chain {n : ℕ} (hn : 2 ≤ n) (P : ℕ)
    (hmain : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K),
      ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      ReserveSampling.unsampledReserveU (L := L) (K := K) b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (ReserveSampling.unsampledReserveU (L := L) (K := K)) m)ᶜ ≤ levelRate P n m := by
  intro m hm1 b hInv hbm
  -- WIRE the alive-witness `hres` from `Φ b = m ≥ 1`: `unsampledReserveU = unsampledReserves.sum`.
  have heq : ReserveSampling.unsampledReserveU (L := L) (K := K) b
      = (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum b.count := by
    rw [ReserveSampling.unsampledReserveU,
      Phase6Convergence.countP_eq_sum_count6
        (fun a : AgentState L K => ReserveSampling.unsampled a) b]
    rfl
  have hres : 1 ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum b.count := by
    rw [← heq, hbm]; exact hm1
  exact ExactMajority.DrainThreading.phase5_hdrop_of_struct n m hn b hInv hbm P hres (hmain b hInv)

/-- **slot 7 — the `classMassN` eliminator-drain per-level rate.**  From the carried
`Phase6To7Structure` (the gap-1 eliminator-margin floor, PERSISTENCE-carried `∀ b` via
`wi.hPhase6Post7`; minority WITNESS PROVED inside `CrudeWorkFamily.phase7_levels_hdrop`), the
per-level drop floor fires at `q m := levelRate wi.E7 n`. -/
theorem hdrop7_of_chain {n : ℕ} (wi : CrudeWorkFamily.Hypotheses (L := L) (K := K) n) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K), Phase7Convergence.Inv7Sum n b →
      Phase7Convergence.classMassN wi.σ b = m →
      ((NonuniformMajority L K).transitionKernel b)
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN wi.σ) m)ᶜ
        ≤ levelRate wi.E7 n m := by
  intro m hm1 b hInv hbm
  exact CrudeWorkFamily.phase7_levels_hdrop wi b hInv hbm hm1

/-- **slot 8 — the `minorityU` eliminator-drain per-level rate.**  From the carried
`Phase7To8Structure` (the above-level eliminator-margin floor, PERSISTENCE-carried `∀ b` via
`wi.hPhase7Post8`; minority WITNESS PROVED inside `CrudeWorkFamily.phase8_levels_hdrop`), the
per-level drop floor fires at `q m := levelRate wi.E8 n`. -/
theorem hdrop8_of_chain {n : ℕ} (wi : CrudeWorkFamily.Hypotheses (L := L) (K := K) n) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K), Phase8Convergence.Phase8AllMain n b →
      Phase7Convergence.minorityU wi.σ b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU wi.σ) m)ᶜ
        ≤ levelRate wi.E8 n m := by
  intro m hm1 b hb8 hbm
  exact CrudeWorkFamily.phase8_levels_hdrop wi b hb8 hbm hm1

/-- **slot 6 — the `highMass l` band-drain per-level rate (floor FULLY landed).**  At a band level
`l` (with `1 ≤ l ≤ L`), from the Phase-5 `ReserveSampleGood i K₀` Post (the reserve floor `K₀`, taken
DIRECTLY from the prior phase — WIRED, no carried floor) and a band-`l` Main witness (`hmain`),
`PhaseFloors.phase6_hdrop_of_phase5Post` gives the per-level rate at `q m := levelRate K₀ n`.  The reserve
floor is the only structural input and it is supplied by the prior phase's Post. -/
theorem hdrop6_of_chain {n : ℕ} (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (hPost : ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b)
    (hmain : ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count) :
    ∀ m, ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) l b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ
        ≤ levelRate K₀ n m := by
  intro m b hInv hbm
  exact PhaseFloors.phase6_hdrop_of_phase5Post σ l n m hn hl1 hlL b hInv hbm i K₀ hhgt hhne
    (hPost b hInv) (hmain b hInv)

/-! ## Part C — the per-level budget at the calibrated horizon.

Each per-level rate `q m = levelRate E n m = 1 − ofReal(E/(n(n−1)))` is `≤ 1 − ofReal(α·m/n)`-shape
(at `α := E·(n−1)/n`-flavoured drain fraction) — but the campaign already calibrates the budget
abstractly in `q m` (`DrainCalibration.rect_pow_le_budget_enn` / `rect_sum_le_phase_budget`).  The
RATE this file delivers is the input `q m` to that calibration: the per-level `hdrop` with the
landed floor.  We record the trivial fact that `levelRate E n m ≤ 1` (a probability), the bound the
budget calibration uses as its rate ceiling. -/

/-- `levelRate E n m ≤ 1`: the per-level drain rate is a probability (it is `1 − ofReal(_)`). -/
theorem levelRate_le_one (E n m : ℕ) : levelRate E n m ≤ 1 := by
  unfold levelRate
  exact tsub_le_self

/-! ## Part D — the rate-discharged WORK slots (slot 6, the levels instance).

Slot 6 is the one calibrated instance built on the LEVELS engine (`phase6Convergence_calibrated`
takes the per-level `hdrop`).  We instantiate it with the landed per-level rate `hdrop6_of_chain`,
discharging the slot-6 drain rate entirely from the structural inputs (the Phase-5 Post + the
band-`l` Main witness + the working-window closure + the per-level budget).  This is the narrowest
slot-6 build: the rate is no longer a free `Hypotheses` field but the wired `levelRate K₀ n`. -/

/-- **slot 6 — the rate-discharged levels instance.**  `phase6Convergence_calibrated` with the
per-level rate supplied by `hdrop6_of_chain` (floor fully landed from the Phase-5 Post) and the
per-level budget `hpt` at the calibrated rate `levelRate K₀ n`.  The only remaining inputs are the
structural Phase-5 Post / band witness / window closure and the budget — no free drain rate. -/
noncomputable def phase6LevelsWork {n : ℕ} (σ : Sign) (l M₀ : ℕ) (hn : 2 ≤ n)
    (hM1 : 1 ≤ M₀) (hl1 : 1 ≤ l) (hlL : l ≤ L) (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (hClosed6 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c))
    (hPost : ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b)
    (hmain : ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count)
    (tWin6 : ℕ → ℕ)
    (hpt6 : ∀ m ∈ Finset.Icc 1 M₀, (levelRate K₀ n m) ^ (tWin6 m)
      ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  DrainCalibration.phase6Convergence_calibrated (L := L) (K := K) l n M₀
    (levelRate K₀ n) tWin6 hClosed6
    (hdrop6_of_chain σ l hn hl1 hlL i K₀ hhgt hhne hPost hmain) hn hM1 hpt6

end DrainRates

end Ripple.PopulationProtocol.ExactMajority

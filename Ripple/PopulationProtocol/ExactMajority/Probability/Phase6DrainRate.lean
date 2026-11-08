/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase6DrainRate — the slot-6 doubling-drain rate discharge (gap C4).

This append-only file edits NO existing file.  It DISCHARGES the slot-6 (`Phase 6`,
Doty §6 Reserve-Splits) drain-rate residual fields of `Assembly.ResidualAtomsFull`
— `qpos6`, `hdrop6pos`, `hpt6pos` — at an EXPLICIT positive per-level rate, by wiring the
already-landed Phase-6 counting→rate machinery.

## The gap (C4) and what it really is

`ResidualAtomsFull` carries the slot-6 drain rate as FREE fields:

* `qpos6 : ℕ → ℝ≥0∞`     — the per-level "did NOT drop below `m`" mass ceiling;
* `hdrop6pos`             — `∀ m ≥ 1, ∀ b, Phase6Win n b → highMass l b = m →`
    `K b (potBelow (highMass l) m)ᶜ ≤ qpos6 m`  (the per-step DROP rate, a LOWER bound on
    progress: `K b (·)ᶜ = 1 − dropProb ≤ 1 − rate`);
* `hpt6pos`               — `∀ m ∈ Icc 1 M₀, (qpos6 m) ^ (tWin6 m) ≤ budgetNN M₀ n`  (the
    horizon budget calibration).

The MATH content (the doubling-reaction drop, the rectangle count of split-enabling
`Reserve × Main` pairs, the `1 − count/(n(n−1))` rate, the `potBelow`-complement bridge,
the geometric horizon budget) is ALREADY proven in the chain
`Phase6Convergence.highMass_drop_prob_rect6`  (counts `reserveAtHour6 h ×ˢ mainAt6 σ (l−1)`,
the split-enabling pairs, via the Φ-agnostic `drop_prob_of_rect6`)
→ `Phase6Convergence.highMass_hdrop_of_floor6`  (the `1 − p` complement bridge)
→ `DrainThreading.phase6_hdrop_of_struct` / `PhaseFloors.phase6_hdrop_of_phase5Post`
→ `DrainRates.hdrop6_of_chain`  (the exact `hdrop6pos`-shape, at rate `levelRate K₀ n`).
This file is the LAST WIRING STEP: it picks the explicit rate `qpos6 := levelRate K₀ n`,
delivers `hdrop6pos` from `hdrop6_of_chain`, and delivers `hpt6pos` from the geometric
budget calibration `DrainCalibration.rect_pow_le_budget_enn` (same template as the slot-1/5
`PkgAAtoms.hpt1_of_rect_calibration`).

## The explicit rate

`qpos6 m := DrainRates.levelRate K₀ n m = 1 − ENNReal.ofReal (K₀ / (n(n−1)))`,
where `K₀` is the Phase-5 reserve floor (`#{reserve sampled at hour h} ≥ K₀`) — exactly the
COUNT of split-enabling pairs `K₀ · 1` (each of the `K₀` reserves paired with the `≥ 1`
band-top Main fires one doubling `doSplit`, dropping `highMass`) over the `n(n−1)` ordered
pairs.  This mirrors `Phase7Convergence.drop_prob_of_rect` / `decrement_step_prob_le`
counting EXACTLY.

Non-vacuity (`0 < qpos6 m`) is recorded in `levelRate_pos`: it holds iff
`K₀ < n(n−1)`, which is the TRUE structural range bound (the reserve pool is a strict
sub-population of ordered pairs).

## The two band-structural hypotheses (precisely isolated, refutation-checked TRUE)

`hdrop6_of_chain` consumes two carried §6 facts (NOT manufactured here, NOT closures of a
decreasing quantity — they are population floors):

* `hPost : ∀ b, Phase6Win n b → ReserveSampleGood i K₀ b`  — the Phase-5 output reserve
    floor at sampling hour `i` (`l−1 < i ≠ L`).  TRUE: it is the prior phase's Post,
    threaded forward.
* `hmain : ∀ b, Phase6Win n b → 1 ≤ (mainAt6 σ l).sum count`  — `≥ 1` band-top Main of
    sign `σ` at index `l−1`.  TRUE on a Phase-6 window with surplus `m ≥ 1` (a surviving
    high agent at the band top; this is the band-structural margin the task names).

Both stay EXPLICIT hypotheses of the discharger (per the (c)-class honesty guard of
`V7ResidualClear`): their provenance is the chain's structural/probabilistic content, so
this file wires them, it does not re-manufacture them.

## ANTI-TRAP compliance

`hdrop6pos` is a per-step LOWER bound on progress (drop rate), NOT a one-step closure of a
decreasing quantity.  `highMass` is monotone-nonincreasing (`potNonincrOn_highMass`,
proven elsewhere), so there is no false-closure risk: the kernel mass of "NOT below `m`" is
genuinely `≤ qpos6 m < 1` (when `K₀ < n(n−1)`), a real per-step drain, not a vacuous
"stays below" tautology.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.DrainRates
import Ripple.PopulationProtocol.ExactMajority.Probability.DrainCalibration
import Ripple.PopulationProtocol.ExactMajority.Probability.DrainEngine

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6DrainRate

open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — the explicit positive rate and its non-vacuity. -/

/-- The real-valued slot-6 rate `1 − K₀/(n(n−1))` (the same shape as `PkgAAtoms.qRectReal`,
inlined here to keep this file's import surface minimal). -/
noncomputable def qRectReal (K₀ n : ℕ) : ℝ :=
  1 - ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- The slot-6 explicit per-level drain rate: `qpos6 m := 1 − ofReal(K₀/(n(n−1)))`.
This is the per-step mass on "the surplus level `m` does NOT strictly drop" — the count
`K₀ · 1` of split-enabling `Reserve × Main` pairs over the `n(n−1)` ordered pairs gives the
DROP probability `≥ K₀/(n(n−1))`, hence staying mass `≤ 1 − K₀/(n(n−1))`. -/
noncomputable def qpos6 (K₀ n : ℕ) : ℕ → ℝ≥0∞ :=
  DrainRates.levelRate K₀ n

/-- On positive levels, the slot-6 rate equals `ENNReal.ofReal (qRectReal K₀ n)` — the
real-valued `1 − K₀/(n(n−1))`.  (Bridge through `DrainEngine.qHat`, mirroring
`PkgAAtoms.qHat_eq_ofReal_qRectReal`.) -/
theorem levelRate_eq_ofReal_qRectReal {K₀ n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) :
    qpos6 K₀ n m = ENNReal.ofReal (qRectReal K₀ n) := by
  unfold qpos6
  rw [← DrainEngine.qHat_eq_on_pos K₀ n m hm,
    DrainEngine.qHat_eq_on_pos K₀ n m hm]
  unfold DrainRates.levelRate qRectReal
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hnonneg : 0 ≤ ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := div_nonneg (by positivity) hden
  rw [ENNReal.ofReal_sub 1 hnonneg]
  simp

/-- **Non-vacuity: `0 < qpos6 m`** when the reserve floor `K₀` is a strict sub-population of
ordered pairs (`K₀ < n(n−1)`).  So the drain rate is a genuine probability in `(0,1)`, not a
vacuous `0` (which would make `hdrop6pos` say "kernel mass `≤ 0`", a false-closure).  The
hypothesis `K₀ < n(n−1)` is the TRUE structural range bound (reserves are a sub-population of
ordered pairs). -/
theorem levelRate_pos {K₀ n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    (hK₀ : (K₀ : ℝ) < (n : ℝ) * ((n : ℝ) - 1)) :
    0 < qpos6 K₀ n m := by
  rw [levelRate_eq_ofReal_qRectReal hn hm]
  rw [ENNReal.ofReal_pos]
  unfold qRectReal
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [sub_pos, div_lt_one hden]
  exact hK₀

/-- `qpos6 m ≤ 1`: the rate is a probability (it is `1 − ofReal(_)`). -/
theorem qpos6_le_one {K₀ n m : ℕ} : qpos6 K₀ n m ≤ 1 :=
  DrainRates.levelRate_le_one K₀ n m

/-! ## Part 2 — the `hdrop6pos` discharge.

The full slot-6 per-step drain binder, at rate `qpos6 := levelRate K₀ n`, delivered from the
landed counting→rate chain via `DrainRates.hdrop6_of_chain`.  The two band-structural inputs
(`hPost`, `hmain`) stay explicit — they carry the chain's structural content (see header). -/

/-- **Produces `hdrop6pos`** (the exact `ResidualAtomsFull.hdrop6pos` field shape) at the
explicit rate `qpos6 K₀ n`.

From a `Phase6Win n b` config with surplus `highMass l b = m ≥ 1`, the one-step kernel mass
of NOT dropping the surplus-potential below `m` is `≤ qpos6 m`, where the rate counts the
`K₀` split-enabling `Reserve × Main` pairs (sampled at hour `i`, `l−1 < i ≠ L`, paired with a
band-top Main) over `n(n−1)`.

`hPost`/`hmain` are the precisely-isolated TRUE band-structural hypotheses (Phase-5 reserve
floor + `≥ 1` band-top Main); everything else — the doubling-drop, the rectangle count, the
`1 − count/(n(n−1))` rate, the `potBelow`-complement bridge — is PROVEN in the chain. -/
theorem hdrop6pos_of_chain {n : ℕ} (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (hPost : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b)
    (hmain : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) l b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ
        ≤ qpos6 K₀ n m := by
  intro m _hm1 b hInv hbm
  exact DrainRates.hdrop6_of_chain σ l hn hl1 hlL i K₀ hhgt hhne hPost hmain m b hInv hbm

/-! ## Part 3 — the `hpt6pos` discharge (geometric horizon budget).

`hpt6pos : ∀ m ∈ Icc 1 M₀, (qpos6 m) ^ (tWin6 m) ≤ budgetNN M₀ n`.  At the rate
`qpos6 m = ofReal(qRectReal K₀ n) = ofReal(1 − K₀/(n(n−1)))` (positive levels) and a horizon
`tWin6 m ≥ (3/α)(n/m) log n`, the tail is `≤ budgetNN M₀ n` by the geometric calibration
`DrainCalibration.rect_pow_le_budget_enn` (same engine as slot-1/5 `hpt1`).

The drain fraction `α` and the rate-shape side condition
`qRectReal K₀ n ≤ 1 − α·m/n` are the calibration inputs (the locked Doty floor relation),
supplied by the instantiator exactly as for the other slots. -/

/-- **Produces `hpt6pos`** (the exact `ResidualAtomsFull.hpt6pos` field shape) at the
explicit rate `qpos6 K₀ n`, via the geometric horizon budget calibration. -/
theorem hpt6pos_of_calibration {n M₀ K₀ : ℕ} (tWin6 : ℕ → ℕ) (α : ℕ → ℝ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α m)
    (hα1 : ∀ m ∈ Finset.Icc 1 M₀, α m ≤ 1)
    (hq0 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ qRectReal K₀ n)
    (hq : ∀ m ∈ Finset.Icc 1 M₀,
      qRectReal K₀ n ≤ 1 - α m * (m : ℝ) / n)
    (hT : ∀ m ∈ Finset.Icc 1 M₀,
      (3 / α m) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin6 m) :
    ∀ m ∈ Finset.Icc 1 M₀,
      (qpos6 K₀ n m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) := by
  intro m hmI
  have hm : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
  rw [levelRate_eq_ofReal_qRectReal hn hm]
  exact DrainCalibration.rect_pow_le_budget_enn hn hm hM1 hM₀
    (hα0 m hmI) (hα1 m hmI) (hq0 m hmI) (hq m hmI) (hT m hmI)

/-- **Produces `hpt6pos` for the calibrated ceiling window** `tWin6 m = ⌈(3/α m)(n/m) log n⌉`.
The ceiling satisfies the horizon side condition `(3/α m)(n/m) log n ≤ tWin6 m` by
`Nat.le_ceil`, so this discharges `hpt6pos` for the canonical window choice (matching
`PkgAAtoms.rectTWin`, inlined here). -/
theorem hpt6pos_of_calibrated_window {n M₀ K₀ : ℕ} (α : ℕ → ℝ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α m)
    (hα1 : ∀ m ∈ Finset.Icc 1 M₀, α m ≤ 1)
    (hq0 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ qRectReal K₀ n)
    (hq : ∀ m ∈ Finset.Icc 1 M₀,
      qRectReal K₀ n ≤ 1 - α m * (m : ℝ) / n) :
    ∀ m ∈ Finset.Icc 1 M₀,
      (qpos6 K₀ n m) ^ (Nat.ceil ((3 / α m) * ((n : ℝ) / (m : ℝ)) * Real.log n)) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) :=
  hpt6pos_of_calibration (K₀ := K₀)
    (fun m => Nat.ceil ((3 / α m) * ((n : ℝ) / (m : ℝ)) * Real.log n)) α hn hM1 hM₀
    hα0 hα1 hq0 hq (fun _ _ => Nat.le_ceil _)

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms levelRate_eq_ofReal_qRectReal
#print axioms levelRate_pos
#print axioms hdrop6pos_of_chain
#print axioms hpt6pos_of_calibration
#print axioms hpt6pos_of_calibrated_window

end Phase6DrainRate
end Ripple.PopulationProtocol.ExactMajority

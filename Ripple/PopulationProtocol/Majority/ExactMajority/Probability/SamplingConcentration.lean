/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SamplingConcentration — the slot-5 sampling-drain rate discharge (gap C3, Doty Lemma 7.1).

This append-only file edits NO existing file.  It DISCHARGES the per-step **sampling drain
rate** of the Phase-5 `unsampledReserveU` potential — the quantitative engine of Doty Lemma
7.1 ("by the end of Phase 5 every Reserve has sampled, whp `1 − O(1/n²)`") — at an EXPLICIT
positive per-level rate, by wiring the already-landed Phase-5 counting→rate machinery, and
supplies the slot-5 concentration `hConc` field from it.

## The gap (C3) and what it really is

`ReserveSampling.phase5SampledConvergence` (the `OneSidedCancel` all-sampled tail) and the
level-decomposed `OneSidedCancel.levels_PhaseConvergenceW` engine both consume a per-step
DROP bound `hstep` / `hdrop` as a FREE input: from a Phase-5-window config with `m ≥ 1`
unsampled Reserves, one step drops the unsampled count below `m` with probability `≥ rate`.

The MATH content (the first-encounter sampling drop, the rectangle count of sampling-enabling
`unsampled-Reserve × biased-Main` pairs, the `count/(n(n−1))` rate, the `unsampledReserveU`
non-increase, the window closure) is ALREADY proven:
* `Phase5Convergence.unsampledReserveU_drop_prob_rect5` — the drop-probability floor
    `(#unsampledReserves · #usefulMains)/(n(n−1))` (counts the Reserve-first rectangle
    `unsampledReserves ×ˢ usefulMains`, via the Φ-agnostic `drop_prob_of_rect5`);
* `ReserveSampling.potNonincrOn_unsampledReserveU` — `unsampledReserveU` is non-increasing;
* `ReserveSampling.phaseGE5Win_InvClosed` — the (super)window closure.

This file is the LAST WIRING STEP: it picks the explicit rate `1 − m/(n(n−1))`, turns the
proven drop floor into the `(potBelow unsampledReserveU m)ᶜ ≤ rate m` shape consumed by
`levels_PhaseConvergenceW` (mirroring `Phase6Convergence.highMass_hdrop_of_floor6`'s `1 − p`
complement bridge and `Phase6DrainRate.hdrop6pos_of_chain`'s discharge), and re-exports the
slot-5 concentration `hConc` field via the already-assembled
`SampledClassAtoms.hConc_field_of_atoms_and_widthSurvival`.

## The explicit rate

`sampleLevelRate n m := 1 − ENNReal.ofReal (m / (n(n−1)))` — the per-step mass on
"the unsampled level `m` does NOT strictly drop".  The count of sampling-enabling pairs is
`(#unsampledReserves) · (#usefulMains) = m · (≥ 1) ≥ m` (each of the `m` unsampled Reserves
paired with a useful biased Main fires one first-encounter sample, dropping `unsampledReserveU`)
over the `n(n−1)` ordered pairs, giving DROP probability `≥ m/(n(n−1))`, hence staying mass
`≤ 1 − m/(n(n−1))`.  This mirrors `Phase6DrainRate`/`Phase7Convergence.drop_prob_of_rect`
counting EXACTLY, but the count is genuinely LEVEL-DEPENDENT (`m`), giving the paper's
`O(n log n)` coupon-collector horizon (vs the crude uniform `Θ(n²)`).

Non-vacuity (`0 < sampleLevelRate n m`) is recorded in `sampleLevelRate_pos`: it holds iff
`m < n(n−1)`, the TRUE structural range bound (the unsampled-Reserve pool is a strict
sub-population of ordered pairs).

## The biased-Main floor (eliminator pool ≥ 1, Doty Thm 6.2) — the precisely isolated C2 residual

The drop count needs `1 ≤ (usefulMains).sum c.count` (at least one useful biased Main, the
eliminator floor).  This is the C2 dependency: a structural LOWER bound that the Phase-6.2
confinement supplies (`usefulMains = biased Mains at index < L`, of which there are `≥ Θ(|M|)`
by Thm 6.2).  It stays an EXPLICIT structured hypothesis

    `hMainFloor : ∀ b, Phase5AllWin n b → 1 ≤ (usefulMains).sum b.count`

REFUTATION-CHECK: this is NOT a false closure of a decreasing quantity.  It is a population
floor on the ELIMINATOR pool (the biased Mains), entirely separate from the monotone target
pool `unsampledReserveU`.  It is TRUE on a Phase-5 window where any biased Main of index `< L`
survives — the Thm-6.2 structural margin.  We PROVE the counting→rate→complement chain GIVEN
this floor; we do not manufacture the floor.

## ANTI-TRAP compliance

`sampleDrain_hdrop` is a per-step LOWER bound on progress (drop rate), NOT a one-step closure
of a decreasing quantity.  `unsampledReserveU` is monotone-nonincreasing
(`ReserveSampling.potNonincrOn_unsampledReserveU`) and the sampled predicate is monotone
(sampling is one-way: `ReserveSampling.unsampled_{fst,snd}_Phase5Transition` show no step ever
CREATES an unsampled Reserve), so there is no false-closure risk: the kernel mass of "NOT below
`m`" is genuinely `≤ sampleLevelRate n m < 1` (when `m < n(n−1)` and a useful Main exists), a
real per-step drain, not a vacuous "stays below" tautology.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SampledClassAtoms

namespace ExactMajority
namespace SamplingConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ReserveSampling Phase5Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 0 — the `unsampledReserveU`/`unsampledReserves`-sum bridge.

`unsampledReserveU c = Multiset.countP unsampled c` and `unsampledReserves = univ.filter
unsampled`, so the potential equals the rectangle's target-pool sum `(unsampledReserves).sum
c.count`.  (Local copy of the `Phase6Convergence.countP_eq_sum_count6` identity; proved here to
keep the import surface minimal.) -/

/-- `unsampledReserveU c = (unsampledReserves).sum c.count`. -/
theorem unsampledReserveU_eq_sum (c : Config (AgentState L K)) :
    unsampledReserveU (L := L) (K := K) c
      = (unsampledReserves (L := L) (K := K)).sum c.count := by
  classical
  unfold unsampledReserveU unsampledReserves
  have hcard : (Multiset.filter (fun a : AgentState L K => unsampled a) c).card
      = Multiset.countP (fun a : AgentState L K => unsampled a) c :=
    (Multiset.countP_eq_card_filter _ _).symm
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => unsampled a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => unsampled a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-! ## Part 1 — the explicit positive level-dependent rate and its non-vacuity. -/

/-- The slot-5 explicit per-level sampling-drain rate: `sampleLevelRate n m := 1 −
ofReal(m/(n(n−1)))`.  This is the per-step mass on "the unsampled level `m` does NOT strictly
drop"; the count `m · (≥ 1)` of sampling-enabling `unsampled-Reserve × biased-Main` pairs over
the `n(n−1)` ordered pairs gives DROP probability `≥ m/(n(n−1))`, hence staying mass
`≤ 1 − m/(n(n−1))`.  Genuinely LEVEL-DEPENDENT (the `m` factor), unlike the constant slot-6
`DrainRates.levelRate K₀ n`. -/
noncomputable def sampleLevelRate (n : ℕ) (m : ℕ) : ℝ≥0∞ :=
  1 - ENNReal.ofReal ((m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- `sampleLevelRate n m ≤ 1`: the rate is a probability (it is `1 − ofReal(_)`). -/
theorem sampleLevelRate_le_one (n m : ℕ) : sampleLevelRate n m ≤ 1 := by
  unfold sampleLevelRate; exact tsub_le_self

/-- **Non-vacuity: `0 < sampleLevelRate n m`** when the level `m` is a strict sub-population of
ordered pairs (`m < n(n−1)`).  So the drain rate is a genuine probability in `(0,1)`, not a
vacuous `0` (which would make the `hdrop` say "kernel mass `≤ 0`", a false closure).  The
hypothesis `(m : ℝ) < n(n−1)` is the TRUE structural range bound (the unsampled-Reserve count
`m` is a sub-population of ordered pairs). -/
theorem sampleLevelRate_pos {n m : ℕ} (hn : 2 ≤ n)
    (hm : (m : ℝ) < (n : ℝ) * ((n : ℝ) - 1)) :
    0 < sampleLevelRate n m := by
  unfold sampleLevelRate
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfrac_lt : (m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) < 1 := by
    rw [div_lt_one hden]; exact hm
  have hfrac_nonneg : 0 ≤ (m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (by positivity) (le_of_lt hden)
  have hlt1 : ENNReal.ofReal ((m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hfrac_nonneg |>.mpr hfrac_lt
  exact tsub_pos_of_lt hlt1

/-! ## Part 2 — the per-step sampling-drain count → rate, given the eliminator floor. -/

/-- **The per-step DROP-probability floor at the level-dependent rate.**  From a Phase-5 window
with `unsampledReserveU c = m` and the eliminator floor `1 ≤ (usefulMains).sum c.count`, the
one-step probability that `unsampledReserveU` strictly drops below `m` is `≥ m/(n(n−1))`.

PROVEN content used: `unsampledReserveU_drop_prob_rect5` (the rectangle floor at numerator
`(#unsampledReserves)·(#usefulMains)`), `unsampledReserveU_eq_sum` (target-pool sum = `m`), and
the carried eliminator floor `hMainFloor` (the isolated C2 residual). -/
theorem sampleDrain_prob_floor (n : ℕ) (hn : 2 ≤ n) (m : ℕ)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin (L := L) (K := K) n c)
    (hm : unsampledReserveU (L := L) (K := K) c = m)
    (hMainFloor : 1 ≤ (usefulMains (L := L) (K := K)).sum c.count) :
    ENNReal.ofReal ((m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | unsampledReserveU (L := L) (K := K) c' + 1
          ≤ unsampledReserveU (L := L) (K := K) c} := by
  classical
  refine le_trans ?_ (unsampledReserveU_drop_prob_rect5 (L := L) (K := K) n hn c hInv)
  apply ENNReal.ofReal_le_ofReal
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  -- numerator monotonicity: m · 1 ≤ (#unsampledReserves) · (#usefulMains), with #unsampled = m.
  have hsum : (unsampledReserves (L := L) (K := K)).sum c.count = m := by
    rw [← unsampledReserveU_eq_sum]; exact hm
  have hnum : (m : ℝ) ≤
      (((unsampledReserves (L := L) (K := K)).sum c.count *
        (usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) := by
    have : m * 1 ≤ (unsampledReserves (L := L) (K := K)).sum c.count *
        (usefulMains (L := L) (K := K)).sum c.count :=
      Nat.mul_le_mul (le_of_eq hsum.symm) hMainFloor
    calc (m : ℝ) = ((m * 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := by exact_mod_cast this
  gcongr

/-- **The `levels` engine `hdrop` from the drop floor (slot 5).**  Mirror of
`Phase6Convergence.highMass_hdrop_of_floor6` / `Phase6DrainRate.hdrop6pos_of_chain`: the kernel's
failure mass on `(potBelow unsampledReserveU m)ᶜ` is `1 − drop-success ≤ sampleLevelRate n m`.

This is the exact per-level `hdrop` shape `OneSidedCancel.levels_PhaseConvergenceW` consumes,
at the explicit level-dependent rate `sampleLevelRate n m`.  `hMainFloor` is the precisely
isolated TRUE eliminator floor (the Thm-6.2 biased-Main lower bound, the C2 dependency);
everything else — the first-encounter drop, the rectangle count, the `m/(n(n−1))` rate, the
`potBelow`-complement bridge — is PROVEN. -/
theorem sampleDrain_hdrop (n : ℕ) (hn : 2 ≤ n)
    (hMainFloor : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ (usefulMains (L := L) (K := K)).sum b.count) :
    ∀ m, ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      unsampledReserveU (L := L) (K := K) b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => unsampledReserveU (L := L) (K := K) c) m)ᶜ
        ≤ sampleLevelRate n m := by
  classical
  intro m b hInv hbm
  set Φ := fun c => unsampledReserveU (L := L) (K := K) c with hΦ
  have hfloor := sampleDrain_prob_floor (L := L) (K := K) n hn m b hInv hbm (hMainFloor b hInv)
  -- complement bridge: K b (potBelow Φ m)ᶜ = 1 − K b (potBelow Φ m) ≤ 1 − floor.
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) | Φ c' + 1 ≤ Φ b}
      = OneSidedCancel.potBelow Φ m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hΦ, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow Φ m) :=
    OneSidedCancel.potBelow_measurable Φ m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow Φ m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow Φ m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : ENNReal.ofReal ((m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure (OneSidedCancel.potBelow Φ m) := by
    rw [← hsucc_eq]; exact hfloor
  unfold sampleLevelRate
  exact tsub_le_tsub_left hp_le 1

/-! ## Part 3 — the slot-5 sampling `PhaseConvergenceW` at the level-dependent rate.

`OneSidedCancel.levels_PhaseConvergenceW` instantiated with `Inv = Phase5AllWin n`,
`Φ = unsampledReserveU` (drift `potNonincrOn_unsampledReserveU`), window closure `hClosed`,
the level rate `sampleLevelRate n`, the `hdrop` produced above from the eliminator floor, and
the horizon budget `hε`.  `Post = Phase5AllWin n ∧ unsampledReserveU = 0 = ReserveSampled`. -/

/-- **Doty Lemma 7.1 (all Reserves sampled), at the explicit level-dependent rate.**

Hypothesis-free but for: the window closure `hClosed`, the isolated eliminator floor
`hMainFloor` (C2 / Thm 6.2), and the horizon budget `hε`.  The per-step drain rate
`sampleLevelRate n m = 1 − m/(n(n−1))` is PROVEN from the counting rectangle. -/
noncomputable def phase5SamplingConvergence (n : ℕ) (hn : 2 ≤ n)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase5AllWin (L := L) (K := K) n c))
    (hMainFloor : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ (usefulMains (L := L) (K := K)).sum b.count)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (sampleLevelRate n m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase5AllWin (L := L) (K := K) n c)
    hClosed
    (fun c => unsampledReserveU (L := L) (K := K) c)
    (potNonincrOn_unsampledReserveU n)
    (sampleLevelRate n)
    (sampleDrain_hdrop (L := L) (K := K) n hn hMainFloor)
    tWin M₀ ε hε

/-- The `Post` of `phase5SamplingConvergence` is exactly `Phase5AllWin n ∧ ReserveSampled`
(every Reserve has sampled). -/
theorem phase5SamplingConvergence_post (n : ℕ) (hn : 2 ≤ n)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase5AllWin (L := L) (K := K) n c))
    (hMainFloor : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ (usefulMains (L := L) (K := K)).sum b.count)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (sampleLevelRate n m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    (phase5SamplingConvergence n hn hClosed hMainFloor tWin M₀ ε hε).Post =
      fun c => Phase5AllWin (L := L) (K := K) n c ∧ ReserveSampled (L := L) (K := K) c := by
  funext c
  simp only [phase5SamplingConvergence, OneSidedCancel.levels_PhaseConvergenceW, ReserveSampled]

/-! ## Part 4 — the slot-5 `hConc` concentration field (the `Assembly` residual slot 5).

The slot-5 `WindowSurvival` concentration field `hConc` consumed in `Assembly` is the
sampled-class floor tail at the slot-5 horizon, already assembled by
`SampledClassAtoms.hConc_field_of_atoms_and_widthSurvival` from the `e5*` inputs.  We re-export it here
(mirroring `Phase6DrainRate`'s discharge of the slot-6 fields) so the slot-5 concentration
surface lives alongside the sampling-drain rate it is paired with.  The `e5reserveFloor` /
`e5classFloor` carried floors are the SAME population floors (unsampled-Reserve count and biased
biased-Main class count) the drain rate above counts; the rate inside is
`SamplingAtoms.rateFloor e5reserveFloor e5classFloor n = (e5reserveFloor · e5classFloor)/(n(n−1))`,
the static-profile analogue of the per-step `m/(n(n−1))` proved here. -/

/-- **Produces the slot-5 `hConc` field** (the exact `Assembly` slot-5 `WindowSurvival`
concentration field shape) — the sampled-class floor tail at the horizon
`∑ m ∈ Finset.Icc 1 M₀, tWin5 m`.  Direct re-export of the assembled Package-E adapter
`SampledClassAtoms.hConc_field_of_atoms_and_widthSurvival`; the inputs are exactly the slot-5 `e5*`
residual fields (`reserveFloor`/`classFloor` = the same population floors the drain rate counts,
`hbridge` the Phase-5/6 separation, `hwidth` the named width-survival export, `hε` the arithmetic
fit). -/
theorem hConc_field_slot5
    (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (reserveFloor classFloor : ℕ)
    (hbudget : reserveFloor * classFloor ≤ n * (n - 1))
    (hres : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      reserveFloor ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum c.count)
    (hcls : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      classFloor ≤ (Phase5Convergence.classMainStates (L := L) (K := K) σ i).sum c.count)
    (K₀ M₀ : ℕ) (tWin5 : ℕ → ℕ) (εConc : ℝ≥0)
    (hbridge : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      SampledClassTail.sampledClassPot (L := L) (K := K) i s c
          < ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) →
      (NonuniformMajority L K).transitionKernel c
        (SampledClassTail.sampledClassGate (L := L) (K := K) n)ᶜ = 0)
    (β : ℝ≥0∞)
    (hwidth : SampledClassAtoms.phase5WidthSurvivalExport (L := L) (K := K) n s i K₀
      (∑ m ∈ Finset.Icc 1 M₀, tWin5 m) β)
    (hε : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      (ENNReal.ofReal (1 - SamplingAtoms.rateFloor reserveFloor classFloor n * (1 - Real.exp (-s))) ^
            (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)
          * SampledClassTail.sampledClassPot (L := L) (K := K) i s c₀ + 0)
        / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
      + (((∑ m ∈ Finset.Icc 1 M₀, tWin5 m) : ℕ) : ℝ≥0∞) * β ≤ (εConc : ℝ≥0∞)) :
    ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
        {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i K₀ c} ≤
          (εConc : ℝ≥0∞) :=
  SampledClassAtoms.hConc_field_of_atoms_and_widthSurvival (L := L) (K := K) σ i hiL n hn s hs
    reserveFloor classFloor hbudget hres hcls K₀ M₀ tWin5 εConc hbridge β hwidth hε

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms unsampledReserveU_eq_sum
#print axioms sampleLevelRate_le_one
#print axioms sampleLevelRate_pos
#print axioms sampleDrain_prob_floor
#print axioms sampleDrain_hdrop
#print axioms phase5SamplingConvergence
#print axioms phase5SamplingConvergence_post
#print axioms hConc_field_slot5

end SamplingConcentration
end ExactMajority

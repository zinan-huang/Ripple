/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — the honest per-regime final-rung stability bridges (`StableBridges`)

This append-only file discharges the single explicit residual left by
`Probability/RegimeClassification.lean`: the per-regime final-rung *bridge*
`progressSet (potBelow Φ 1) ⟹ StableDone`, supplied there as the hypothesis
`hbridge` of each `ladderData_of_*` builder.  We prove the bridges that are
honestly true, and re-shape the spine where the naive bridge is FALSE.

## What each potential's zero-state actually means

`potBelow Φ 1 = {x | Φ x < 1} = {x | Φ x = 0}` (`Φ : Config → ℕ`).  Surveying the
four regime potentials:

* **Phase-10 majority** — `Φ = wrongACount`.  `wrongACount x = 0` means *every*
  agent outputs `A` (`countP (output ≠ A) = 0`).  Combined with the regime fact
  `AllPhase10 x` (from `S1`) and the init-sign match `0 < initialGap init`, this is
  EXACTLY `phase10MajorityWitness init x` (the `A`-disjunct), hence
  `majorityStableEndpoint init x`, hence `x ∈ StableDone`.  **This is the real
  stability bridge** — proven below (`phase10Majority_drained_mem_stableDone`).

* **Phase-10 B-majority** — the mirrored branch uses `Φ = wrongBCount`.
  `wrongBCount x = 0` means every agent outputs `B`; with `AllPhase10 x` (from `S0`)
  and `initialGap init < 0`, this is the `B`-disjunct of `phase10MajorityWitness`.
  Honest bridge proven below (`phase10BMajority_drained_mem_stableDone`).

* **Phase-10 tie** — `Φ = wrongTCount`.  `wrongTCount x = 0` means every agent
  outputs `T`; with `AllPhase10 x` (from `Tie1plus`) and `initialGap init = 0`, this
  is `phase10MajorityWitness init x` (the `T`-disjunct).  Honest bridge proven below
  (`phase10Tie_drained_mem_stableDone`).

* **Timed regimes** — `Φ = clockCounterSumAt p`.  `clockCounterSumAt p x = 0` means
  the phase-`p` clocks have all hit counter `0` — and that triggers **phase
  ADVANCE**, NOT stability.  So `potBelow (clockCounterSumAt p) 1 ⟹ StableDone` is
  NOT honest: the honest rung target is *next-phase entry*, and the ladder must
  continue `p → p+1 → ⋯ → 10 → stable`.  We document this and provide the re-shaped
  spine target (the next-regime entry set), leaving the deterministic
  drained ⟹ advance transition as the named timed residual (Stage-4).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/StableBridges.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RegimeClassification

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

/-! ## Part 1 — the honest Phase-10 membership bridges (pure protocol facts)

The genuine stability bridge for each Phase-10 regime is a *membership* statement:
a drained Phase-10 state (every agent already outputs the verdict letter) whose
init-gap sign matches the regime is a `majorityStableEndpoint`, hence lies in
`StableDone`.  These are pure protocol facts (no probability), proven by unfolding
the potential's zero-state into `phase10MajorityWitness`. -/

/-- `wrongACount c = 0` unpacks to "every agent of `c` outputs `A`". -/
theorem forall_output_A_of_wrongACount_zero {L K : ℕ}
    {c : Config (AgentState L K)} (h : wrongACount (L := L) (K := K) c = 0) :
    ∀ a ∈ c, a.output = .A := by
  intro a ha
  have hne : ¬ (a.output ≠ .A) :=
    (Multiset.countP_eq_zero.1 (by simpa [wrongACount] using h)) a ha
  exact not_not.1 hne

/-- `wrongBCount c = 0` unpacks to "every agent of `c` outputs `B`". -/
theorem forall_output_B_of_wrongBCount_zero {L K : ℕ}
    {c : Config (AgentState L K)} (h : wrongBCount (L := L) (K := K) c = 0) :
    ∀ a ∈ c, a.output = .B := by
  intro a ha
  have hne : ¬ (a.output ≠ .B) :=
    (Multiset.countP_eq_zero.1 (by simpa [wrongBCount] using h)) a ha
  exact not_not.1 hne

/-- `wrongTCount c = 0` unpacks to "every agent of `c` outputs `T`". -/
theorem forall_output_T_of_wrongTCount_zero {L K : ℕ}
    {c : Config (AgentState L K)} (h : wrongTCount (L := L) (K := K) c = 0) :
    ∀ a ∈ c, a.output = .T := by
  intro a ha
  have hne : ¬ (a.output ≠ .T) :=
    (Multiset.countP_eq_zero.1 (by simpa [wrongTCount] using h)) a ha
  exact not_not.1 hne

open Phase10Drop in
/-- **Phase-10 majority stability bridge (membership form).**

A drained `S1`-state `c` (all phase 10, positive signed sum) with `wrongACount c = 0`
(every agent outputs `A`) whose init gap is positive is a `phase10MajorityWitness`,
hence a `majorityStableEndpoint`, hence lies in `StableDone L K init`.

This is the honest content of the phase-10-majority final-rung bridge: the drained
potential `wrongACount = 0`, together with the regime fact `AllPhase10` (from `S1`)
and the init-sign match, IS exactly stability. -/
theorem phase10Majority_drained_mem_stableDone {L K n : ℕ}
    (init c : Config (AgentState L K))
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (hS1 : S1 (L := L) (K := K) n c)
    (hwrong : wrongACount (L := L) (K := K) c = 0) :
    c ∈ StableDone L K init := by
  -- StableDone = {majorityStableEndpoint init}; pick the phase10MajorityWitness disjunct.
  show majorityStableEndpoint (L := L) (K := K) init c
  refine Or.inr (Or.inr (Or.inr ?_))
  -- phase10MajorityWitness: A-disjunct, since gap > 0.
  refine Or.inl ⟨hgap, ?_⟩
  intro a ha
  exact ⟨hS1.1 a ha, forall_output_A_of_wrongACount_zero (L := L) (K := K) hwrong a ha⟩

open Phase10Drop in
/-- **Phase-10 B-majority stability bridge (membership form).**

A drained `S0`-state `c` (all phase 10, negative signed sum) with `wrongBCount c = 0`
(every agent outputs `B`) whose init gap is negative is a `phase10MajorityWitness`,
hence a `majorityStableEndpoint`, hence lies in `StableDone L K init`. -/
theorem phase10BMajority_drained_mem_stableDone {L K n : ℕ}
    (init c : Config (AgentState L K))
    (hgap : initialGap (L := L) (K := K) init < 0)
    (hS0 : S0 (L := L) (K := K) n c)
    (hwrong : wrongBCount (L := L) (K := K) c = 0) :
    c ∈ StableDone L K init := by
  show majorityStableEndpoint (L := L) (K := K) init c
  refine Or.inr (Or.inr (Or.inr ?_))
  -- phase10MajorityWitness: B-disjunct, since gap < 0.
  refine Or.inr (Or.inl ⟨hgap, ?_⟩)
  intro a ha
  exact ⟨hS0.1 a ha, forall_output_B_of_wrongBCount_zero (L := L) (K := K) hwrong a ha⟩

open Phase10Drop in
/-- **Phase-10 tie stability bridge (membership form).**

A drained `Tie1plus`-state `c` (all phase 10, zero signed sum, active) with
`wrongTCount c = 0` (every agent outputs `T`) whose init gap is zero is a
`phase10MajorityWitness` (the `T`-disjunct), hence lies in `StableDone L K init`. -/
theorem phase10Tie_drained_mem_stableDone {L K n : ℕ}
    (init c : Config (AgentState L K))
    (hgap : initialGap (L := L) (K := K) init = 0)
    (hTie : Tie1plus (L := L) (K := K) n c)
    (hwrong : wrongTCount (L := L) (K := K) c = 0) :
    c ∈ StableDone L K init := by
  show majorityStableEndpoint (L := L) (K := K) init c
  refine Or.inr (Or.inr (Or.inr ?_))
  -- phase10MajorityWitness: T-disjunct, since gap = 0.
  refine Or.inr (Or.inr ⟨hgap, ?_⟩)
  intro a ha
  exact ⟨hTie.1.1 a ha, forall_output_T_of_wrongTCount_zero (L := L) (K := K) hwrong a ha⟩

/-! ## Part 2 — the honest bridge as an `expectedHitting` cap

With `StableDone` measurable & absorbing, a state already in `StableDone` has
`expectedHitting … StableDone = 0` (`RecoveryBridges.expectedHitting_eq_zero_of_mem`),
so the membership bridges of Part 1 give the `expectedHitting … ≤ βbridge` shape the
`ladderData_of_*` builders consume, for ANY `βbridge` — the bridge cost is `0`.

The progress set the E2 engine drives toward is `potBelow Φ 1` with NO carried regime
fact.  An arbitrary `y` with `wrongACount y = 0` but NOT `S1` need not be stable, so
the bridge over the BARE `potBelow` set is unprovable.  We therefore route the bridge
through the regime invariant: the honest final-rung target is the INTERSECTED set
`{S1} ∩ potBelow wrongACount 1`, on which the membership bridge applies pointwise. -/

open Phase10Drop in
/-- **Phase-10 majority bridge (expected-hitting form, regime-restricted).**

On the intersected final-rung set `{x | S1 n x ∧ wrongACount x = 0}` (the honest
target carrying the regime invariant), with `StableDone` measurable & absorbing and
the init-sign match `0 < initialGap init`, the expected hitting time of `StableDone`
is `0`.  This is the discharged `hbridge` for the phase-10-majority spine: every
such `y` is already in `StableDone`, so its hitting cost is `0 ≤ βbridge`. -/
theorem phase10Majority_bridge_expectedHitting {L K n : ℕ}
    (init : Config (AgentState L K)) (βbridge : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (y : Config (AgentState L K))
    (hy : y ∈ {x | S1 (L := L) (K := K) n x} ∩
      potBelow (fun c => wrongACount (L := L) (K := K) c) 1) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ βbridge := by
  -- `y ∈ potBelow wrongACount 1` ⇒ `wrongACount y < 1` ⇒ `wrongACount y = 0`.
  have hwrong : wrongACount (L := L) (K := K) y = 0 := by
    have : wrongACount (L := L) (K := K) y < 1 := hy.2
    omega
  have hmem : y ∈ StableDone L K init :=
    phase10Majority_drained_mem_stableDone (L := L) (K := K) (n := n) init y hgap hy.1 hwrong
  rw [expectedHitting_eq_zero_of_mem (NonuniformMajority L K).transitionKernel
    hDoneMeas hAbs hmem]
  exact zero_le'

open Phase10Drop in
/-- **Phase-10 B-majority bridge (expected-hitting form, regime-restricted).**

On `{x | S0 n x ∧ wrongBCount x = 0}`, with `StableDone` absorbing and the
init-gap match `initialGap init < 0`, the expected hitting time of `StableDone` is `0`. -/
theorem phase10BMajority_bridge_expectedHitting {L K n : ℕ}
    (init : Config (AgentState L K)) (βbridge : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : initialGap (L := L) (K := K) init < 0)
    (y : Config (AgentState L K))
    (hy : y ∈ {x | S0 (L := L) (K := K) n x} ∩
      potBelow (fun c => wrongBCount (L := L) (K := K) c) 1) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ βbridge := by
  have hwrong : wrongBCount (L := L) (K := K) y = 0 := by
    have : wrongBCount (L := L) (K := K) y < 1 := hy.2
    omega
  have hmem : y ∈ StableDone L K init :=
    phase10BMajority_drained_mem_stableDone (L := L) (K := K) (n := n) init y
      hgap hy.1 hwrong
  rw [expectedHitting_eq_zero_of_mem (NonuniformMajority L K).transitionKernel
    hDoneMeas hAbs hmem]
  exact zero_le'

open Phase10Drop in
/-- **Phase-10 tie bridge (expected-hitting form, regime-restricted).**

On `{x | Tie1plus n x ∧ wrongTCount x = 0}`, with `StableDone` absorbing and the
init-gap match `initialGap init = 0`, the expected hitting time of `StableDone` is `0`. -/
theorem phase10Tie_bridge_expectedHitting {L K n : ℕ}
    (init : Config (AgentState L K)) (βbridge : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (y : Config (AgentState L K))
    (hy : y ∈ {x | Tie1plus (L := L) (K := K) n x} ∩
      potBelow (fun c => wrongTCount (L := L) (K := K) c) 1) :
    expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
      ≤ βbridge := by
  have hwrong : wrongTCount (L := L) (K := K) y = 0 := by
    have : wrongTCount (L := L) (K := K) y < 1 := hy.2
    omega
  have hmem : y ∈ StableDone L K init :=
    phase10Tie_drained_mem_stableDone (L := L) (K := K) (n := n) init y hgap hy.1 hwrong
  rw [expectedHitting_eq_zero_of_mem (NonuniformMajority L K).transitionKernel
    hDoneMeas hAbs hmem]
  exact zero_le'

/-! ## Part 3 — the re-shaped Phase-10 ladder spines (bridge discharged)

`RegimeClassification.ladderData_of_phase10Majority` targets the BARE progress set
`potBelow wrongACount 1` and takes the bridge as a hypothesis.  We re-shape: target
the INTERSECTED set `{S1} ∩ potBelow wrongACount 1`, whose first link is the E2 cap
routed through the `S1` invariant, and whose bridge is DISCHARGED by Part 2.

### First link to the intersected target

The E2 cap `phase10_expected_stabilization_O_nsq_log` bounds
`E[T from c → potBelow wrongACount 1]` for `c ∈ S1`.  Since `S1` is `InvClosed`
(`Phase10Drop.invClosed_S1`), the trajectory from an `S1`-start stays in `S1`, so the
first time it hits `potBelow wrongACount 1` it is also in `S1`; hence the hitting time
of the INTERSECTED set `{S1} ∩ potBelow` equals that of `potBelow`.  We obtain the
intersected cap via the `_on` occupation machinery. -/

open Phase10Drop in
open scoped Classical in
/-- **Hitting the `S1`-intersected drain target costs no more than hitting the bare
drain target.**  From an `S1`-start the trajectory stays in `S1` (InvClosed), so the
expected hitting time of `{S1} ∩ {wrongACount = 0}` is bounded by that of the bare
`{wrongACount = 0}`.  Combined with the E2 cap this gives the intersected first link. -/
theorem phase10Majority_link_intersected {L K n : ℕ} (hn : 2 ≤ n)
    (y : Config (AgentState L K)) (hy : S1 (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y
        ({x | S1 (L := L) (K := K) n x} ∩
          potBelow (fun c => wrongACount (L := L) (K := K) c) 1)
      ≤ 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  -- The intersected band-occupation `∑' t, (K^t) y ({S1}∩{wrong=0} ∩ Doneᶜ)` is the
  -- expectedHitting of the intersected target; bound it by the bare E2 cap via the
  -- `_on` occupation bound with `J = S1`, `Mid = univ`, `Done = {S1}∩{wrong=0}`.
  -- Simpler: expectedHitting is monotone in the target only downward; here we use
  -- that the bare-target tail dominates the intersected-target tail pointwise because
  -- (K^t) y stays a.e. on S1, so {wrong=0}ᶜ-tail differs from ({S1}∩{wrong=0})ᶜ-tail
  -- only on ¬S1 mass, which is 0.
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Done : Set (Config (AgentState L K)) :=
    {x | S1 (L := L) (K := K) n x} ∩ potBelow (fun c => wrongACount (L := L) (K := K) c) 1
  set Bare : Set (Config (AgentState L K)) :=
    potBelow (fun c => wrongACount (L := L) (K := K) c) 1
  -- Pointwise on each time-slice, the not-Done mass equals the not-Bare mass (a.e.):
  -- {Done}ᶜ = {¬S1} ∪ {Bare}ᶜ, and the {¬S1} part carries 0 mass under (ker^t) y.
  have hS1closed : ∀ b : Config (AgentState L K),
      S1 (L := L) (K := K) n b →
      ker b {x | ¬ S1 (L := L) (K := K) n x} = 0 := invClosed_S1 n
  have hpowS1 : ∀ t : ℕ, (ker ^ t) y {x | ¬ S1 (L := L) (K := K) n x} = 0 :=
    fun t => pow_compl_inv_eq_zero_eh ker (fun b => S1 (L := L) (K := K) n b) hS1closed y hy t
  -- For each t: (ker^t) y Doneᶜ ≤ (ker^t) y Bareᶜ.
  have hslice : ∀ t : ℕ, (ker ^ t) y (Doneᶜ) ≤ (ker ^ t) y (Bareᶜ) := by
    intro t
    have hsub : (Doneᶜ : Set (Config (AgentState L K)))
        ⊆ Bareᶜ ∪ {x | ¬ S1 (L := L) (K := K) n x} := by
      intro z hz
      by_cases hzS1 : S1 (L := L) (K := K) n z
      · -- z ∉ Done with z ∈ S1 ⇒ z ∉ Bare.
        left
        intro hzBare
        exact hz ⟨hzS1, hzBare⟩
      · right; exact hzS1
    calc (ker ^ t) y (Doneᶜ)
        ≤ (ker ^ t) y (Bareᶜ ∪ {x | ¬ S1 (L := L) (K := K) n x}) := measure_mono hsub
      _ ≤ (ker ^ t) y (Bareᶜ) + (ker ^ t) y {x | ¬ S1 (L := L) (K := K) n x} :=
          measure_union_le _ _
      _ = (ker ^ t) y (Bareᶜ) := by rw [hpowS1 t, add_zero]
  -- Sum over t: expectedHitting to Done ≤ expectedHitting to Bare ≤ E2 cap.
  calc expectedHitting ker y Done
      = ∑' t : ℕ, (ker ^ t) y (Doneᶜ) := expectedHitting_eq_tsum ker y Done
    _ ≤ ∑' t : ℕ, (ker ^ t) y (Bareᶜ) := ENNReal.tsum_le_tsum hslice
    _ = expectedHitting ker y Bare := (expectedHitting_eq_tsum ker y Bare).symm
    _ ≤ 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) :=
        phase10_expected_stabilization_O_nsq_log (L := L) (K := K) n hn y hy

open Phase10Drop in
open scoped Classical in
/-- **Phase-10 tie first link to the intersected drain target** (`Tie1plus` analogue). -/
theorem phase10Tie_link_intersected {L K n : ℕ} (hn : 2 ≤ n)
    (y : Config (AgentState L K)) (hy : Tie1plus (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y
        ({x | Tie1plus (L := L) (K := K) n x} ∩
          potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)
      ≤ 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Done : Set (Config (AgentState L K)) :=
    {x | Tie1plus (L := L) (K := K) n x} ∩ potBelow (fun c => wrongTCount (L := L) (K := K) c) 1
  set Bare : Set (Config (AgentState L K)) :=
    potBelow (fun c => wrongTCount (L := L) (K := K) c) 1
  have hTieClosed : ∀ b : Config (AgentState L K),
      Tie1plus (L := L) (K := K) n b →
      ker b {x | ¬ Tie1plus (L := L) (K := K) n x} = 0 := invClosed_Tie1plus n
  have hpowTie : ∀ t : ℕ, (ker ^ t) y {x | ¬ Tie1plus (L := L) (K := K) n x} = 0 :=
    fun t => pow_compl_inv_eq_zero_eh ker (fun b => Tie1plus (L := L) (K := K) n b)
      hTieClosed y hy t
  have hslice : ∀ t : ℕ, (ker ^ t) y (Doneᶜ) ≤ (ker ^ t) y (Bareᶜ) := by
    intro t
    have hsub : (Doneᶜ : Set (Config (AgentState L K)))
        ⊆ Bareᶜ ∪ {x | ¬ Tie1plus (L := L) (K := K) n x} := by
      intro z hz
      by_cases hzTie : Tie1plus (L := L) (K := K) n z
      · left; intro hzBare; exact hz ⟨hzTie, hzBare⟩
      · right; exact hzTie
    calc (ker ^ t) y (Doneᶜ)
        ≤ (ker ^ t) y (Bareᶜ ∪ {x | ¬ Tie1plus (L := L) (K := K) n x}) := measure_mono hsub
      _ ≤ (ker ^ t) y (Bareᶜ) + (ker ^ t) y {x | ¬ Tie1plus (L := L) (K := K) n x} :=
          measure_union_le _ _
      _ = (ker ^ t) y (Bareᶜ) := by rw [hpowTie t, add_zero]
  calc expectedHitting ker y Done
      = ∑' t : ℕ, (ker ^ t) y (Doneᶜ) := expectedHitting_eq_tsum ker y Done
    _ ≤ ∑' t : ℕ, (ker ^ t) y (Bareᶜ) := ENNReal.tsum_le_tsum hslice
    _ = expectedHitting ker y Bare := (expectedHitting_eq_tsum ker y Bare).symm
    _ ≤ 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) :=
        phase10_expected_stabilization_tie_O_nsq_log (L := L) (K := K) n hn y hy

/-! ### The re-shaped Phase-10 ladder builders (bridge discharged)

We now build the `LadderData` directly via the two-rung spine, with the bridge
DISCHARGED by Part 2 (no `hbridge` hypothesis).  The progress (rung-1) set is the
intersected `{S1} ∩ potBelow` so the bridge applies; the first link is
`phase10Majority_link_intersected`; the second link is `phase10Majority_bridge_expectedHitting`. -/

open Phase10Drop in
open scoped Classical in
/-- **Phase-10 majority ladder spine, bridge DISCHARGED.**  From the regime data
(`S1`-state `b`), `StableDone` measurable & absorbing, the init-sign match
`0 < initialGap init`, and the budget, build the `LadderData` to `StableDone` — the
final-rung bridge is no longer a hypothesis but the theorem
`phase10Majority_bridge_expectedHitting`. -/
noncomputable def ladderData_of_phase10Majority_bridged {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞) (hn : 2 ≤ n)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : 0 < initialGap (L := L) (K := K) init)
    (d : Phase10MajorityData L K n b)
    (hsum : 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
      ≤ Brecover) :
    LadderData L K init b Brecover :=
  ladderData_of_two_rung init b Brecover
    {x | S1 (L := L) (K := K) n x}
    ({x | S1 (L := L) (K := K) n x} ∩ potBelow (fun c => wrongACount (L := L) (K := K) c) 1)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    hDoneMeas
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) 0
    d.hS1
    (fun y hy => phase10Majority_link_intersected (L := L) (K := K) hn y hy)
    (fun y hy => phase10Majority_bridge_expectedHitting (L := L) (K := K) (n := n) init 0
      hDoneMeas hAbs hgap y hy)
    hsum

open Phase10Drop in
open scoped Classical in
/-- **Phase-10 tie ladder spine, bridge DISCHARGED.** -/
noncomputable def ladderData_of_phase10Tie_bridged {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞) (hn : 2 ≤ n)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hgap : initialGap (L := L) (K := K) init = 0)
    (d : Phase10TieData L K n b)
    (hsum : 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + 0
      ≤ Brecover) :
    LadderData L K init b Brecover :=
  ladderData_of_two_rung init b Brecover
    {x | Tie1plus (L := L) (K := K) n x}
    ({x | Tie1plus (L := L) (K := K) n x} ∩
      potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    hDoneMeas
    (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) 0
    d.hTie
    (fun y hy => phase10Tie_link_intersected (L := L) (K := K) hn y hy)
    (fun y hy => phase10Tie_bridge_expectedHitting (L := L) (K := K) (n := n) init 0
      hDoneMeas hAbs hgap y hy)
    hsum

/-! ## Part 4 — the timed regimes: why the naive bridge is FALSE, and the honest target

For a timed regime the potential is `Φ = clockCounterSumAt p`, and
`potBelow Φ 1 = {clockCounterSumAt p = 0}` means the phase-`p` clocks have all hit
counter `0`.  In the faithful protocol this triggers **phase advance** — a phase-`p`
clock at counter `0` moves to phase `p+1` (or to the Phase-10 backup on the seam) —
NOT stabilization.  So the bridge `potBelow (clockCounterSumAt p) 1 ⟹ StableDone` is
NOT true: the drained state is in general NOT a `majorityStableEndpoint` (its agents
are still mid-protocol, at phase `p+1 < 10`).

The honest rung target for a timed regime is therefore **next-phase entry**, and the
ladder must continue through the phase chain `p → p+1 → ⋯ → 10`, then the Phase-10
backup's own stability bridge (Parts 1–3) closes it.  We record this as the timed
regime's re-shaped spine SHAPE: the rung-1 set is the next-phase domain, and the
genuine timed residual is the deterministic `drained ⟹ next-phase-domain` transition
plus the per-step phase-advance caps — NOT a direct `⟹ StableDone` bridge.

`timed_phase_chain_target` names the honest rung-1 target set (the next-phase timed
domain or, at `p = 8`/seam, the Phase-10 backup domain), so the spine builder for the
timed regimes can be re-shaped to an `n`-rung chain through phases via the
`RecoveryBridges` telescope (which supports arbitrary ladders).  The deterministic
advance transitions are the documented Stage-4 timed residual. -/

open ConditionalPhaseProgress in
/-- **Honest next-rung target for a timed regime** (the re-shaped spine target).

The drained timed potential `clockCounterSumAt p = 0` triggers phase ADVANCE, so the
honest rung-1 target is the *next-phase* timed domain
`{AllClockGEpCard (p+1) n}` (clocks now at phase `≥ p+1`), NOT `StableDone`.  This
names that target set; the timed spine re-shapes to the chain
`{AllClockGEpCard p n} → {AllClockGEpCard (p+1) n} → ⋯ → Phase-10 backup → StableDone`,
each clock-phase rung capped by the per-phase advance, and the FINAL Phase-10 rung
closed by Part 3.  The per-step advance transition is the documented timed residual. -/
def timed_phase_chain_target (L K n p : ℕ) : Set (Config (AgentState L K)) :=
  {x | AllClockGEpCard (L := L) (K := K) (p + 1) n x}

/-- **The naive timed bridge is not claimed.**  `timed_phase_chain_target` is the
honest rung-1 target: `clockCounterSumAt p = 0` ⟹ entry to the next-phase domain
(phase advance), continuing the ladder — it does NOT assert `⟹ StableDone`.  The
direct timed bridge `potBelow (clockCounterSumAt p) 1 ⟹ StableDone` is FALSE in the
faithful protocol (drained clocks advance to phase `p+1 < 10`, still mid-protocol),
so we deliberately do not fake-discharge it; the timed spine is re-shaped to the
phase chain above, with the per-step advance as the named Stage-4 residual. -/
theorem timed_chain_target_is_next_phase (L K n p : ℕ) :
    timed_phase_chain_target (L := L) (K := K) n p =
      {x | ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) (p + 1) n x} :=
  rfl

end ExactMajority

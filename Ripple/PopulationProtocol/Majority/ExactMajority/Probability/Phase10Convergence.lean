/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 10 — whp convergence instance (`PhaseConvergenceW`)

This file packages the *high-probability* (whp) convergence of the slow Phase-10
backup as a `PhaseConvergenceW` instance, the parallel item to the EXPECTED-time
results of `Phase10ExpectedTime.lean` (Lemma 7.7).

The route is Markov + block restart, built on the generic invariant-relative Markov
tail just added to `ExpectedHitting.lean`:

* the EXPECTED stabilization headlines give, *uniformly over starts in the absorbing
  class* `S1` / `Tie1plus`, `E[hit Done] ≤ O(n² log n)` interactions
  (`phase10_expected_stabilization_O_nsq_log`, `…_tie_O_nsq_log`);
* `bad_le_half_of_expectedHitting_on` converts this to a per-block half-success bound
  for `s` twice the expectation budget: `(K^s) c Doneᶜ ≤ 1/2` from any `J`-state;
* `bad_block_geometric_on` powers it up: `(K^(k·s)) c Doneᶜ ≤ (1/2)^k` over `k`
  blocks, giving `ε = 2^{-k}`.  Taking `k = Θ(log n)` yields `ε = n^{-2}`.

The Done sets `{wrongACount = 0}` (majority) / `{wrongTCount = 0}` (tie) are absorbing
*relative to* the closed invariant via the deterministic unanimity preservation in
`Analysis/Invariants.lean` (`phase10_unanimous_output_preserved_by_step`), NOT via the
stage `PotNonincrOn` (which only gives `wrongACount` non-increase after both cancel
stages).  Once `wrongACount = 0` and all agents are in Phase 10, everyone outputs `A`,
and that unanimous output is preserved forever.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase10ExpectedTime
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

namespace Phase10Drop

open Protocol

/-! ## Absorption of the Done sets relative to the invariant

`{wrongACount = 0}` together with `S1` (so `AllPhase10`) means every agent is in
Phase 10 and outputs `A`; the deterministic unanimity preservation keeps it that way.
Same for `{wrongTCount = 0}` with `Tie1plus`. -/

/-- `wrongACount c = 0` together with `AllPhase10 c` says every agent is in Phase 10
and outputs `A`. -/
theorem unanimousA_of_wrongACount_zero {c : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hw : wrongACount c = 0) :
    ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .A := by
  intro a ha
  refine ⟨hphase a ha, ?_⟩
  have hne : ¬ a.output ≠ Output.A := (Multiset.countP_eq_zero.1 hw) a ha
  exact not_not.mp hne

/-- `wrongBCount c = 0` together with `AllPhase10 c` says every agent is in Phase 10
and outputs `B`. -/
theorem unanimousB_of_wrongBCount_zero {c : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hw : wrongBCount c = 0) :
    ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .B := by
  intro a ha
  refine ⟨hphase a ha, ?_⟩
  have hne : ¬ a.output ≠ Output.B := (Multiset.countP_eq_zero.1 hw) a ha
  exact not_not.mp hne

/-- `wrongTCount c = 0` together with `AllPhase10 c` says every agent is in Phase 10
and outputs `T`. -/
theorem unanimousT_of_wrongTCount_zero {c : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hw : wrongTCount c = 0) :
    ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .T := by
  intro a ha
  refine ⟨hphase a ha, ?_⟩
  have hne : ¬ a.output ≠ Output.T := (Multiset.countP_eq_zero.1 hw) a ha
  exact not_not.mp hne

/-- A support config of a Phase-10 unanimous-`A` base is again unanimous-`A`, hence
has `wrongACount = 0`. -/
theorem wrongACount_step_zero_of_unanimous
    {c c' : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .A)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    wrongACount c' = 0 := by
  -- Extract either a genuine step (StepRel) or self from the support.
  have hu' : ∀ a ∈ c', a.phase.val = 10 ∧ a.output = .A := by
    unfold Protocol.stepDistOrSelf at h
    split_ifs at h with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at *
      split_ifs at * with h_app
      · exact phase10_unanimous_output_preserved_by_step
          (L := L) (K := K) c _ Output.A hu ⟨r₁, r₂, h_app, rfl⟩
      · exact hu
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at h; rw [h]; exact hu
  rw [wrongACount, Multiset.countP_eq_zero]
  intro a ha
  simp only [ne_eq, not_not]
  exact (hu' a ha).2

/-- Same for unanimous-`B`: `wrongBCount` stays `0`. -/
theorem wrongBCount_step_zero_of_unanimous
    {c c' : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .B)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    wrongBCount c' = 0 := by
  have hu' : ∀ a ∈ c', a.phase.val = 10 ∧ a.output = .B := by
    unfold Protocol.stepDistOrSelf at h
    split_ifs at h with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at *
      split_ifs at * with h_app
      · exact phase10_unanimous_output_preserved_by_step
          (L := L) (K := K) c _ Output.B hu ⟨r₁, r₂, h_app, rfl⟩
      · exact hu
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at h; rw [h]; exact hu
  rw [wrongBCount, Multiset.countP_eq_zero]
  intro a ha
  simp only [ne_eq, not_not]
  exact (hu' a ha).2

/-- Same for unanimous-`T` (tie case): `wrongTCount` stays `0`. -/
theorem wrongTCount_step_zero_of_unanimous
    {c c' : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .T)
    (h : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    wrongTCount c' = 0 := by
  have hu' : ∀ a ∈ c', a.phase.val = 10 ∧ a.output = .T := by
    unfold Protocol.stepDistOrSelf at h
    split_ifs at h with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ h
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at *
      split_ifs at * with h_app
      · exact phase10_unanimous_output_preserved_by_step
          (L := L) (K := K) c _ Output.T hu ⟨r₁, r₂, h_app, rfl⟩
      · exact hu
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at h; rw [h]; exact hu
  rw [wrongTCount, Multiset.countP_eq_zero]
  intro a ha
  simp only [ne_eq, not_not]
  exact (hu' a ha).2

/-- **`S1`-relative absorption of `{wrongACount = 0}`.** From an `S1`-state already at
`wrongACount = 0`, the kernel stays in `{wrongACount = 0}`. -/
theorem done_absorbing_maj (n : ℕ) :
    ∀ x ∈ (potBelow (fun c => wrongACount (L := L) (K := K) c) 1),
      S1 (L := L) (K := K) n x →
        (NonuniformMajority L K).transitionKernel x
          (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ = 0 := by
  intro x hx hS1
  obtain ⟨hphase, _, _⟩ := hS1
  have hw : wrongACount x = 0 := by
    simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hx; exact hx
  have hu := unanimousA_of_wrongACount_zero (L := L) (K := K) hphase hw
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    ((potBelow_measurable (fun c => wrongACount c) 1).compl)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff]
  exact wrongACount_step_zero_of_unanimous (L := L) (K := K) hu hc'

/-- **`S0`-relative absorption of `{wrongBCount = 0}`.** -/
theorem done_absorbing_B (n : ℕ) :
    ∀ x ∈ (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1),
      S0 (L := L) (K := K) n x →
        (NonuniformMajority L K).transitionKernel x
          (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ = 0 := by
  intro x hx hS0
  obtain ⟨hphase, _, _⟩ := hS0
  have hw : wrongBCount x = 0 := by
    simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hx; exact hx
  have hu := unanimousB_of_wrongBCount_zero (L := L) (K := K) hphase hw
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    ((potBelow_measurable (fun c => wrongBCount c) 1).compl)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff]
  exact wrongBCount_step_zero_of_unanimous (L := L) (K := K) hu hc'

/-- **`Tie1plus`-relative absorption of `{wrongTCount = 0}`.** -/
theorem done_absorbing_tie (n : ℕ) :
    ∀ x ∈ (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1),
      Tie1plus (L := L) (K := K) n x →
        (NonuniformMajority L K).transitionKernel x
          (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ = 0 := by
  intro x hx hTie
  obtain ⟨⟨hphase, _, _⟩, _⟩ := hTie
  have hw : wrongTCount x = 0 := by
    simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff] at hx; exact hx
  have hu := unanimousT_of_wrongTCount_zero (L := L) (K := K) hphase hw
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    ((potBelow_measurable (fun c => wrongTCount c) 1).compl)]
  refine Set.disjoint_left.mpr fun c' hc' hbad => hbad ?_
  simp only [potBelow, Set.mem_setOf_eq, Nat.lt_one_iff]
  exact wrongTCount_step_zero_of_unanimous (L := L) (K := K) hu hc'

/-! ## Per-block half-success and the block-geometric tail

The expectation budget `B := 3·n²·(1+2 log n)` (majority) / `2·n²·(1+2 log n)` (tie)
is finite; with a block length `s ≥ 2B`, every `S1`/`Tie1plus` start fails to finish
within `s` steps with probability `≤ 1/2`, and over `k` blocks the failure decays as
`(1/2)^k`. -/

/-- The majority expectation budget `3·n²·(1+2 log n)` is finite. -/
theorem budget_maj_ne_top (n : ℕ) :
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) ≠ ⊤ := by
  apply ENNReal.mul_ne_top (by simp)
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top

/-- The tie expectation budget `2·n²·(1+2 log n)` is finite. -/
theorem budget_tie_ne_top (n : ℕ) :
    (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) ≠ ⊤ := by
  apply ENNReal.mul_ne_top (by simp)
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top

/-- **Per-block half-success (majority).** From any `S1`-state, a block of `s ≥ 2B`
steps reaches `{wrongACount = 0}` with probability `≥ 1/2`. -/
theorem block_half_maj (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞))
    (c : Config (AgentState L K)) (hS1 : S1 (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ s) c
      (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ ≤ 1 / 2 := by
  refine bad_le_half_of_expectedHitting_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n)
    (potBelow_measurable (fun c => wrongACount c) 1)
    (done_absorbing_maj n) c hS1 s hspos
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)))
    (budget_maj_ne_top n) ?_ hsB
  exact phase10_expected_stabilization_O_nsq_log n hn c hS1

/-- **Per-block half-success (B-majority).** From any `S0`-state, a block of
`s ≥ 2B` steps reaches `{wrongBCount = 0}` with probability `≥ 1/2`. -/
theorem block_half_B (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞))
    (c : Config (AgentState L K)) (hS0 : S0 (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ s) c
      (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ ≤ 1 / 2 := by
  refine bad_le_half_of_expectedHitting_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S0 (L := L) (K := K) n c) (invClosed_S0 n)
    (potBelow_measurable (fun c => wrongBCount c) 1)
    (done_absorbing_B n) c hS0 s hspos
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)))
    (budget_maj_ne_top n) ?_ hsB
  exact phase10_expected_stabilization_B_O_nsq_log n hn c hS0

/-- **Per-block half-success (tie).** -/
theorem block_half_tie (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞))
    (c : Config (AgentState L K)) (hTie : Tie1plus (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ s) c
      (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ ≤ 1 / 2 := by
  refine bad_le_half_of_expectedHitting_on
    (NonuniformMajority L K).transitionKernel
    (fun c => Tie1plus (L := L) (K := K) n c) (invClosed_Tie1plus n)
    (potBelow_measurable (fun c => wrongTCount c) 1)
    (done_absorbing_tie n) c hTie s hspos
    (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)))
    (budget_tie_ne_top n) ?_ hsB
  exact phase10_expected_stabilization_tie_O_nsq_log n hn c hTie

/-- **Block-geometric tail (majority).** Over `k` blocks of `s ≥ 2B` steps each, the
failure to reach `{wrongACount = 0}` decays as `(1/2)^k`. -/
theorem block_geom_maj (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞))
    (c : Config (AgentState L K)) (hS1 : S1 (L := L) (K := K) n c) (k : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ (k * s)) c
      (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ ≤ (1 / 2) ^ k := by
  refine bad_block_geometric_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n)
    (potBelow_measurable (fun c => wrongACount c) 1)
    (done_absorbing_maj n) s (1 / 2) ?_ c hS1 k
  -- block bound from every S1 not-done state
  intro b hbS1 _
  exact block_half_maj n hn s hspos hsB b hbS1

/-- **Block-geometric tail (B-majority).** -/
theorem block_geom_B (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞))
    (c : Config (AgentState L K)) (hS0 : S0 (L := L) (K := K) n c) (k : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ (k * s)) c
      (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ ≤ (1 / 2) ^ k := by
  refine bad_block_geometric_on
    (NonuniformMajority L K).transitionKernel
    (fun c => S0 (L := L) (K := K) n c) (invClosed_S0 n)
    (potBelow_measurable (fun c => wrongBCount c) 1)
    (done_absorbing_B n) s (1 / 2) ?_ c hS0 k
  intro b hbS0 _
  exact block_half_B n hn s hspos hsB b hbS0

/-- **Block-geometric tail (tie).** -/
theorem block_geom_tie (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞))
    (c : Config (AgentState L K)) (hTie : Tie1plus (L := L) (K := K) n c) (k : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ (k * s)) c
      (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ ≤ (1 / 2) ^ k := by
  refine bad_block_geometric_on
    (NonuniformMajority L K).transitionKernel
    (fun c => Tie1plus (L := L) (K := K) n c) (invClosed_Tie1plus n)
    (potBelow_measurable (fun c => wrongTCount c) 1)
    (done_absorbing_tie n) s (1 / 2) ?_ c hTie k
  intro b hbTie _
  exact block_half_tie n hn s hspos hsB b hbTie

/-! ## Bridge to the unanimity `Post` and the `PhaseConvergenceW` instance

The whp `Post` is the unanimous-output predicate `∃ o, ∀ a ∈ c, phase = 10 ∧
output = o`.  On the (a.e.) `S1`/`Tie1plus` trajectory `AllPhase10` holds, so the only
way `Post` can fail is `wrongACount > 0` (majority) / `wrongTCount > 0` (tie).  Hence
the not-`Post` mass is bounded by the not-done mass, which the block-geometric tail
controls. -/

/-- The whp `Post`: every agent is in Phase 10 with a single common output. -/
def Phase10Post (c : Config (AgentState L K)) : Prop :=
  ∃ o : Output, ∀ a ∈ c, a.phase.val = 10 ∧ a.output = o

/-- On an `AllPhase10` state, `¬ Phase10Post` forces `wrongACount > 0`: if everyone is
in Phase 10 but not unanimously `A`, some agent's output is `≠ A`. -/
theorem wrongACount_pos_of_not_post {c : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hnp : ¬ Phase10Post (L := L) (K := K) c) :
    0 < wrongACount c := by
  rcases Nat.eq_zero_or_pos (wrongACount c) with hw | hpos
  · exact absurd ⟨Output.A, unanimousA_of_wrongACount_zero (L := L) (K := K) hphase hw⟩ hnp
  · exact hpos

/-- On an `AllPhase10` state, `¬ Phase10Post` forces `wrongBCount > 0`. -/
theorem wrongBCount_pos_of_not_post {c : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hnp : ¬ Phase10Post (L := L) (K := K) c) :
    0 < wrongBCount c := by
  rcases Nat.eq_zero_or_pos (wrongBCount c) with hw | hpos
  · exact absurd ⟨Output.B, unanimousB_of_wrongBCount_zero (L := L) (K := K) hphase hw⟩ hnp
  · exact hpos

/-- On an `AllPhase10` state, `¬ Phase10Post` forces `wrongTCount > 0`. -/
theorem wrongTCount_pos_of_not_post {c : Config (AgentState L K)}
    (hphase : AllPhase10 (L := L) (K := K) c) (hnp : ¬ Phase10Post (L := L) (K := K) c) :
    0 < wrongTCount c := by
  rcases Nat.eq_zero_or_pos (wrongTCount c) with hw | hpos
  · exact absurd ⟨Output.T, unanimousT_of_wrongTCount_zero (L := L) (K := K) hphase hw⟩ hnp
  · exact hpos

/-- **Not-`Post` mass ≤ not-done mass (majority).** From an `S1`-start, the trajectory
is a.e. `AllPhase10`, and there `¬Post ⟹ wrongACount > 0`. -/
theorem notPost_le_notDone_maj (n : ℕ) (t : ℕ)
    (c : Config (AgentState L K)) (hS1 : S1 (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {y | ¬ Phase10Post (L := L) (K := K) y} ≤
      ((NonuniformMajority L K).transitionKernel ^ t) c
        (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ := by
  -- {¬Post} ⊆ {wrongACount > 0} ∪ {¬AllPhase10}; the latter carries 0 mass on S1.
  have hcover : {y | ¬ Phase10Post (L := L) (K := K) y} ⊆
      (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ ∪
        {x | ¬ AllPhase10 (L := L) (K := K) x} := by
    intro y hy
    by_cases hphase : AllPhase10 (L := L) (K := K) y
    · left
      simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, Nat.lt_one_iff]
      exact (wrongACount_pos_of_not_post (L := L) (K := K) hphase hy).ne'
    · right; exact hphase
  have hnull : ((NonuniformMajority L K).transitionKernel ^ t) c
      {x | ¬ AllPhase10 (L := L) (K := K) x} = 0 := by
    have hS1c : S1 (L := L) (K := K) n c := hS1
    -- S1 ⊆ AllPhase10, S1 closed ⇒ ¬AllPhase10 mass ≤ ¬S1 mass = 0.
    refine le_antisymm ?_ zero_le'
    calc ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ AllPhase10 (L := L) (K := K) x}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ S1 (L := L) (K := K) n x} := by
          refine measure_mono ?_
          intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          exact fun hS1x => hx hS1x.1
      _ = 0 := pow_not_inv_eq_zero (NonuniformMajority L K).transitionKernel
          (fun c => S1 (L := L) (K := K) n c) (invClosed_S1 n) c hS1c t
  calc ((NonuniformMajority L K).transitionKernel ^ t) c
        {y | ¬ Phase10Post (L := L) (K := K) y}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          ((potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ ∪
            {x | ¬ AllPhase10 (L := L) (K := K) x}) := measure_mono hcover
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ
        + ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ AllPhase10 (L := L) (K := K) x} := measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c
          (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)ᶜ := by
        rw [hnull, add_zero]

/-- **Not-`Post` mass ≤ not-done mass (B-majority).** -/
theorem notPost_le_notDone_B (n : ℕ) (t : ℕ)
    (c : Config (AgentState L K)) (hS0 : S0 (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {y | ¬ Phase10Post (L := L) (K := K) y} ≤
      ((NonuniformMajority L K).transitionKernel ^ t) c
        (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ := by
  have hcover : {y | ¬ Phase10Post (L := L) (K := K) y} ⊆
      (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ ∪
        {x | ¬ AllPhase10 (L := L) (K := K) x} := by
    intro y hy
    by_cases hphase : AllPhase10 (L := L) (K := K) y
    · left
      simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, Nat.lt_one_iff]
      exact (wrongBCount_pos_of_not_post (L := L) (K := K) hphase hy).ne'
    · right; exact hphase
  have hnull : ((NonuniformMajority L K).transitionKernel ^ t) c
      {x | ¬ AllPhase10 (L := L) (K := K) x} = 0 := by
    have hS0c : S0 (L := L) (K := K) n c := hS0
    refine le_antisymm ?_ zero_le'
    calc ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ AllPhase10 (L := L) (K := K) x}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ S0 (L := L) (K := K) n x} := by
          refine measure_mono ?_
          intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          exact fun hS0x => hx hS0x.1
      _ = 0 := pow_not_inv_eq_zero (NonuniformMajority L K).transitionKernel
          (fun c => S0 (L := L) (K := K) n c) (invClosed_S0 n) c hS0c t
  calc ((NonuniformMajority L K).transitionKernel ^ t) c
        {y | ¬ Phase10Post (L := L) (K := K) y}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          ((potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ ∪
            {x | ¬ AllPhase10 (L := L) (K := K) x}) := measure_mono hcover
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ
        + ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ AllPhase10 (L := L) (K := K) x} := measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c
          (potBelow (fun c => wrongBCount (L := L) (K := K) c) 1)ᶜ := by
        rw [hnull, add_zero]

/-- **Not-`Post` mass ≤ not-done mass (tie).** -/
theorem notPost_le_notDone_tie (n : ℕ) (t : ℕ)
    (c : Config (AgentState L K)) (hTie : Tie1plus (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {y | ¬ Phase10Post (L := L) (K := K) y} ≤
      ((NonuniformMajority L K).transitionKernel ^ t) c
        (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ := by
  have hcover : {y | ¬ Phase10Post (L := L) (K := K) y} ⊆
      (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ ∪
        {x | ¬ AllPhase10 (L := L) (K := K) x} := by
    intro y hy
    by_cases hphase : AllPhase10 (L := L) (K := K) y
    · left
      simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, Nat.lt_one_iff]
      exact (wrongTCount_pos_of_not_post (L := L) (K := K) hphase hy).ne'
    · right; exact hphase
  have hnull : ((NonuniformMajority L K).transitionKernel ^ t) c
      {x | ¬ AllPhase10 (L := L) (K := K) x} = 0 := by
    refine le_antisymm ?_ zero_le'
    calc ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ AllPhase10 (L := L) (K := K) x}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ Tie1plus (L := L) (K := K) n x} := by
          refine measure_mono ?_
          intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          exact fun hTx => hx hTx.1.1
      _ = 0 := pow_not_inv_eq_zero (NonuniformMajority L K).transitionKernel
          (fun c => Tie1plus (L := L) (K := K) n c) (invClosed_Tie1plus n) c hTie t
  calc ((NonuniformMajority L K).transitionKernel ^ t) c
        {y | ¬ Phase10Post (L := L) (K := K) y}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          ((potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ ∪
            {x | ¬ AllPhase10 (L := L) (K := K) x}) := measure_mono hcover
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ
        + ((NonuniformMajority L K).transitionKernel ^ t) c
          {x | ¬ AllPhase10 (L := L) (K := K) x} := measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c
          (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)ᶜ := by
        rw [hnull, add_zero]

/-- Coercion helper: `((1/2 : ℝ≥0)^k : ℝ≥0∞) = (1/2 : ℝ≥0∞)^k`. -/
theorem coe_half_pow (k : ℕ) :
    (((1 / 2 : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) = ((1 / 2 : ℝ≥0∞)) ^ k := by
  rw [ENNReal.coe_pow]
  congr 1
  rw [ENNReal.coe_div (by norm_num)]
  simp

/-! ## The `PhaseConvergenceW` instances

Per-case (`Pre = S1` majority, `Pre = Tie1plus` tie) and combined (`Pre = S1 ∨
Tie1plus`).  `t = k·s`, `ε = (1/2)^k`; the block length `s ≥ 2B` and block count `k`
are parameters, with explicit `s(n)`/`k(n)` corollaries below. -/

/-- **Phase-10 whp convergence (majority case).** From an all-phase-10 majority start
(`S1 n`), after `k` blocks of `s ≥ 2·(3 n²(1+2 log n))` interactions the configuration
is unanimous-output with failure probability `≤ (1/2)^k`. -/
noncomputable def phase10Convergence_maj (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞)) (k : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => S1 (L := L) (K := K) n c
  Post := fun c => Phase10Post (L := L) (K := K) c
  t := k * s
  ε := (1 / 2) ^ k
  convergence := by
    intro c hS1
    refine le_trans (notPost_le_notDone_maj n (k * s) c hS1) ?_
    refine le_trans (block_geom_maj n hn s hspos hsB c hS1 k) ?_
    rw [coe_half_pow k]

/-- **Phase-10 whp convergence (B-majority case).** Mirrored from `S1`, with
`S0 n` and done set `{wrongBCount = 0}`. -/
noncomputable def phase10Convergence_B (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞)) (k : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => S0 (L := L) (K := K) n c
  Post := fun c => Phase10Post (L := L) (K := K) c
  t := k * s
  ε := (1 / 2) ^ k
  convergence := by
    intro c hS0
    refine le_trans (notPost_le_notDone_B n (k * s) c hS0) ?_
    refine le_trans (block_geom_B n hn s hspos hsB c hS0 k) ?_
    rw [coe_half_pow k]

/-- **Phase-10 whp convergence (tie case).** -/
noncomputable def phase10Convergence_tie (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞)) (k : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => Tie1plus (L := L) (K := K) n c
  Post := fun c => Phase10Post (L := L) (K := K) c
  t := k * s
  ε := (1 / 2) ^ k
  convergence := by
    intro c hTie
    refine le_trans (notPost_le_notDone_tie n (k * s) c hTie) ?_
    refine le_trans (block_geom_tie n hn s hspos hsB c hTie k) ?_
    rw [coe_half_pow k]

/-- **Phase-10 whp convergence (combined).** `Pre = Phase10Ready`, i.e.
`S1 ∨ S0 ∨ Tie1plus`.  A single block length
`s ≥ 2·(3 n²(1+2 log n))` works for all cases (the tie budget `2B` is smaller). -/
noncomputable def phase10Convergence (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hspos : 0 < s)
    (hsB : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s : ℝ≥0∞)) (k : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => Phase10Ready (L := L) (K := K) n c
  Post := fun c => Phase10Post (L := L) (K := K) c
  t := k * s
  ε := (1 / 2) ^ k
  convergence := by
    intro c hPre
    have hcoe := coe_half_pow k
    rcases hPre with hS1 | hRest
    · refine le_trans (notPost_le_notDone_maj n (k * s) c hS1) ?_
      refine le_trans (block_geom_maj n hn s hspos hsB c hS1 k) ?_
      rw [hcoe]
    · rcases hRest with hS0 | hTie
      · refine le_trans (notPost_le_notDone_B n (k * s) c hS0) ?_
        refine le_trans (block_geom_B n hn s hspos hsB c hS0 k) ?_
        rw [hcoe]
      · -- tie case: derive the tie budget bound from the (larger) majority budget bound.
        have hsB_tie : (2 * (((n ^ 2 : ℕ) : ℝ≥0∞)
            * ENNReal.ofReal (1 + 2 * Real.log n))) * 2 ≤ (s : ℝ≥0∞) := by
          refine le_trans ?_ hsB
          gcongr
          norm_num
        refine le_trans (notPost_le_notDone_tie n (k * s) c hTie) ?_
        refine le_trans (block_geom_tie n hn s hspos hsB_tie c hTie k) ?_
        rw [hcoe]

/-! ## Stable-`Post` corollary

`Phase10Post` is deterministically absorbing — once reached, the unanimous output is
preserved forever (`phase10_unanimous_output_isStable` in `Analysis/Invariants.lean`).
The consumer therefore gets both the whp arrival (`phase10Convergence`) and the
deterministic stability of the limit. -/

/-- **Stable-`Post` corollary.** Every `Phase10Post` configuration is `IsStable` in the
generic population-protocol sense (the limit output is preserved under all reachable
sequences). -/
theorem phase10Post_isStable (c : Config (AgentState L K))
    (hp : Phase10Post (L := L) (K := K) c) :
    (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  obtain ⟨o, ho⟩ := hp
  exact phase10_unanimous_output_isStable (L := L) (K := K) c o ho

end Phase10Drop

end ExactMajority

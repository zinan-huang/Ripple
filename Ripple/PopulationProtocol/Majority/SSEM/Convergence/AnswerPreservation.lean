/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Answer-Field Preservation through `transitionPEM`

Pair-level invariant: applied to any pair of agent states drawn from a
consensus configuration, `transitionPEM` returns a result whose
`.answer` field equals the input's `.answer` field.

The proof is a careful case analysis over the four phases of
Algorithm 1.  Each phase is collapsed by:

  * `RankDeltaSettledFix` — Phase 1 ranking is identity on Settled.
  * `Settled ≠ Resetting` — Phase 2 lines 3–6, Phase 3 epidemic.
  * `swap_does_not_fire` — Phase 4 swap precondition is false at
    consensus (sorted-rank arithmetic).
  * Decision-match lemmas — Phase 4 decision sets `.answer` to a value
    that already equals `majorityAnswer C`.
  * Equal-answer trigger — Phase 4 propagation reset trigger
    `b₀.answer ≠ b₁.answer` is false because all answers equal
    `majorityAnswer C`; only `timer` mutates.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Silent

namespace SSEM

variable {n : ℕ}

/-! ### A pair invariant lifted from a consensus configuration -/

/-- The pair-level invariant capturing what we know about
`(C u, C v)` when `C` is a consensus configuration of dimension `n`. -/
structure ConsensusPair (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion)
    (a : Answer) (nA : ℕ) : Prop where
  settled₀ : s₀.role = .Settled
  settled₁ : s₁.role = .Settled
  answer₀ : s₀.answer = a
  answer₁ : s₁.answer = a
  inputA_iff₀ : x₀ = Opinion.A ↔ s₀.rank.val < nA
  inputA_iff₁ : x₁ = Opinion.A ↔ s₁.rank.val < nA
  /-- `a` is determined by `nA` and the dimension `n`. -/
  majority_eq : a = (if nA > n - nA then Answer.outA
                     else if nA < n - nA then Answer.outB
                     else Answer.outT)
  nA_le : nA ≤ n

/-- Extract the pair invariant from a `IsConsensusConfig`. -/
theorem consensus_pair_of_config {C : Config (AgentState n) Opinion n}
    (h : IsConsensusConfig C) (u v : Fin n) :
    ConsensusPair (C u).1 (C v).1 (C u).2 (C v).2
      (majorityAnswer C) (nAOf C) where
  settled₀ := h.allSettled u
  settled₁ := h.allSettled v
  answer₀ := h.allAnswerCorrect u
  answer₁ := h.allAnswerCorrect v
  inputA_iff₀ := h.input_rank u
  inputA_iff₁ := h.input_rank v
  majority_eq := by
    have hsum := nAOf_add_nBOf C
    unfold majorityAnswer
    have hnB : nBOf C = n - nAOf C := by omega
    rw [hnB]
  nA_le := by have := nAOf_add_nBOf C; omega

/-! ### Boolean / role simplifications -/

theorem role_settled_ne_resetting : (Role.Settled = Role.Resetting) = False := by
  decide

theorem role_resetting_eq_settled : (Role.Resetting = Role.Settled) = False := by
  decide

/-! ### Decision-match lemmas

The decision branches set `.answer` to a value derived from the inputs at
median rank(s). Under the consensus pair invariant, this value already
equals the global majority answer `a`.
-/

namespace ConsensusPair

variable {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} {a : Answer} {nA : ℕ}

/-- Both inputs at the (lower-median, upper-median) pair: the assigned
opinion's answer-encoding equals `a` when the inputs agree. -/
theorem decision_even_same_lower
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hev : n % 2 = 0)
    (hr₀ : s₀.rank.val + 1 = n / 2)
    (hr₁ : s₁.rank.val + 1 = n / 2 + 1)
    (hxx : x₀ = x₁) :
    opinionToAnswer x₀ = a := by
  cases hx : x₀ with
  | A =>
    have h0 : s₀.rank.val < nA := hpair.inputA_iff₀.mp hx
    have h1A : x₁ = Opinion.A := hxx ▸ hx
    have h1 : s₁.rank.val < nA := hpair.inputA_iff₁.mp h1A
    have hgt : nA > n - nA := by omega
    rw [hpair.majority_eq]; simp [hgt, opinionToAnswer]
  | B =>
    have h0 : ¬ s₀.rank.val < nA := fun h' => by
      have := hpair.inputA_iff₀.mpr h'; rw [this] at hx; cases hx
    have h1B : x₁ = Opinion.B := hxx ▸ hx
    have h1 : ¬ s₁.rank.val < nA := fun h' => by
      have := hpair.inputA_iff₁.mpr h'; rw [this] at h1B; cases h1B
    have hlt : nA < n - nA := by omega
    have hngt : ¬ nA > n - nA := by omega
    rw [hpair.majority_eq]; simp [hlt, hngt, opinionToAnswer]

/-- Symmetric variant for the (upper, lower) pair pattern. -/
theorem decision_even_same_upper
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hev : n % 2 = 0)
    (hr₁ : s₁.rank.val + 1 = n / 2)
    (hr₀ : s₀.rank.val + 1 = n / 2 + 1)
    (hxx : x₁ = x₀) :
    opinionToAnswer x₁ = a := by
  cases hx : x₁ with
  | A =>
    have h0 : s₁.rank.val < nA := hpair.inputA_iff₁.mp hx
    have h1A : x₀ = Opinion.A := hxx ▸ hx
    have h1 : s₀.rank.val < nA := hpair.inputA_iff₀.mp h1A
    have hgt : nA > n - nA := by omega
    rw [hpair.majority_eq]; simp [hgt, opinionToAnswer]
  | B =>
    have h0 : ¬ s₁.rank.val < nA := fun h' => by
      have := hpair.inputA_iff₁.mpr h'; rw [this] at hx; cases hx
    have h1B : x₀ = Opinion.B := hxx ▸ hx
    have h1 : ¬ s₀.rank.val < nA := fun h' => by
      have := hpair.inputA_iff₀.mpr h'; rw [this] at h1B; cases h1B
    have hlt : nA < n - nA := by omega
    have hngt : ¬ nA > n - nA := by omega
    rw [hpair.majority_eq]; simp [hlt, hngt, opinionToAnswer]

/-- Tie case: when the median pair has unequal inputs, `a = .outT`. -/
theorem decision_even_diff_lower
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hev : n % 2 = 0)
    (hr₀ : s₀.rank.val + 1 = n / 2)
    (hr₁ : s₁.rank.val + 1 = n / 2 + 1)
    (hne : ¬ x₀ = x₁) :
    a = Answer.outT := by
  cases hx0 : x₀ with
  | A =>
    cases hx1 : x₁ with
    | A => exact absurd (hx0.trans hx1.symm) hne
    | B =>
      have h0 : s₀.rank.val < nA := hpair.inputA_iff₀.mp hx0
      have h1 : ¬ s₁.rank.val < nA := fun h' => by
        have := hpair.inputA_iff₁.mpr h'; rw [this] at hx1; cases hx1
      have heq : nA = n / 2 := by omega
      have hngt : ¬ nA > n - nA := by omega
      have hnlt : ¬ nA < n - nA := by omega
      rw [hpair.majority_eq]; simp [hngt, hnlt]
  | B =>
    cases hx1 : x₁ with
    | A =>
      have h0 : ¬ s₀.rank.val < nA := fun h' => by
        have := hpair.inputA_iff₀.mpr h'; rw [this] at hx0; cases hx0
      have h1 : s₁.rank.val < nA := hpair.inputA_iff₁.mp hx1
      omega
    | B => exact absurd (hx0.trans hx1.symm) hne

theorem decision_even_diff_upper
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hev : n % 2 = 0)
    (hr₁ : s₁.rank.val + 1 = n / 2)
    (hr₀ : s₀.rank.val + 1 = n / 2 + 1)
    (hne : ¬ x₁ = x₀) :
    a = Answer.outT := by
  cases hx0 : x₀ with
  | A =>
    cases hx1 : x₁ with
    | A => exact absurd (hx1.trans hx0.symm) hne
    | B =>
      have h0 : s₀.rank.val < nA := hpair.inputA_iff₀.mp hx0
      have h1 : ¬ s₁.rank.val < nA := fun h' => by
        have := hpair.inputA_iff₁.mpr h'; rw [this] at hx1; cases hx1
      omega
  | B =>
    cases hx1 : x₁ with
    | A =>
      have h0 : ¬ s₀.rank.val < nA := fun h' => by
        have := hpair.inputA_iff₀.mpr h'; rw [this] at hx0; cases hx0
      have h1 : s₁.rank.val < nA := hpair.inputA_iff₁.mp hx1
      have heq : nA = n / 2 := by omega
      have hngt : ¬ nA > n - nA := by omega
      have hnlt : ¬ nA < n - nA := by omega
      rw [hpair.majority_eq]; simp [hngt, hnlt]
    | B => exact absurd (hx1.trans hx0.symm) hne

/-- Decision match for odd `n`: at the unique median rank, the assigned
opinion-answer equals `a`. -/
theorem decision_odd_match
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hodd : ¬ n % 2 = 0) :
    (s₀.rank.val + 1 = ceilHalf n → opinionToAnswer x₀ = a) ∧
    (s₁.rank.val + 1 = ceilHalf n → opinionToAnswer x₁ = a) := by
  have hodd' : n % 2 = 1 := by omega
  have hceil : ceilHalf n = n / 2 + 1 := by unfold ceilHalf; omega
  refine ⟨fun hrk => ?_, fun hrk => ?_⟩
  · -- s₀ at median.
    cases hx : x₀ with
    | A =>
      have hlt : s₀.rank.val < nA := hpair.inputA_iff₀.mp hx
      have hgt : nA > n - nA := by omega
      rw [hpair.majority_eq]; simp [hgt, opinionToAnswer]
    | B =>
      have hge : ¬ s₀.rank.val < nA := fun h' => by
        have := hpair.inputA_iff₀.mpr h'; rw [this] at hx; cases hx
      have hlt : nA < n - nA := by omega
      have hngt : ¬ nA > n - nA := by omega
      rw [hpair.majority_eq]; simp [hlt, hngt, opinionToAnswer]
  · -- s₁ at median.
    cases hx : x₁ with
    | A =>
      have hlt : s₁.rank.val < nA := hpair.inputA_iff₁.mp hx
      have hgt : nA > n - nA := by omega
      rw [hpair.majority_eq]; simp [hgt, opinionToAnswer]
    | B =>
      have hge : ¬ s₁.rank.val < nA := fun h' => by
        have := hpair.inputA_iff₁.mpr h'; rw [this] at hx; cases hx
      have hlt : nA < n - nA := by omega
      have hngt : ¬ nA > n - nA := by omega
      rw [hpair.majority_eq]; simp [hlt, hngt, opinionToAnswer]

/-- Swap precondition fails at any consensus pair. -/
theorem swap_fails (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA) :
    ¬ (s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A) := by
  rintro ⟨hlt, hxB, hxA⟩
  have h0 : ¬ s₀.rank.val < nA := fun h' => by
    have := hpair.inputA_iff₀.mpr h'; rw [this] at hxB; cases hxB
  have h1 : s₁.rank.val < nA := hpair.inputA_iff₁.mp hxA
  have : s₀.rank.val < s₁.rank.val := hlt
  omega

end ConsensusPair

/-! ### Main pair-level theorem

We prove `(transitionPEM ...).1.answer = a ∧ (...).2.answer = a` directly.
Since `s₀.answer = a` and `s₁.answer = a`, the original "preservation"
form follows.

Strategy: unfold, then for each case explicitly identify the result's
.answer fields. Phases 1–3 collapse to identity at Settled. Phase 4 splits
on parity / median patterns.
-/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 2000 in
theorem transitionPEM_consensus_pair_answer_eq
    {trank Rmax nA : ℕ} {a : Answer}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hne : s₀.rank ≠ s₁.rank) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.answer = a ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.answer = a := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) :=
    hRank s₀ s₁ hpair.settled₀ hpair.settled₁ hne
  have hs0 := hpair.settled₀
  have hs1 := hpair.settled₁
  have ha0 := hpair.answer₀
  have ha1 := hpair.answer₁
  have hswap := hpair.swap_fails
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  -- Collapse Phases 1-3 + Phase-4 entry + swap.
  simp only [hRD, hs0, hs1, hswap, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    true_and, and_self, if_true]
  -- After this, (b₀, b₁) inside Phase 4 starts as (s₀, s₁). The remaining goal
  -- is the decision + propagation applied to (s₀, s₁, x₀, x₁).
  by_cases hpar : n % 2 = 0
  · -- Even n.
    simp only [hpar, if_true]
    by_cases h_lu : s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1
    · obtain ⟨hr0, hr1⟩ := h_lu
      simp only [hr0, hr1, and_self, if_true]
      by_cases hxx : x₀ = x₁
      · have hmatch := hpair.decision_even_same_lower hpar hr0 hr1 hxx
        simp only [hxx, if_true]
        rw [hxx] at hmatch
        -- Now hmatch : opinionToAnswer x₁ = a, matching the post-rewrite goal.
        split_ifs <;>
          refine ⟨?_, ?_⟩ <;>
          (first | exact hmatch | exact ha0 | exact ha1 | rfl)
      · simp only [hxx, if_false]
        have ha_eq : a = Answer.outT :=
          hpair.decision_even_diff_lower hpar hr0 hr1 hxx
        -- After decision, both sides set answer := .outT; goal is `.outT = a`.
        split_ifs <;>
          refine ⟨?_, ?_⟩ <;>
          (first | exact ha_eq.symm | exact ha0 | exact ha1 | rfl)
    · simp only [show ¬ (s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1)
        from h_lu, if_false]
      by_cases h_ul : s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1
      · obtain ⟨hr1, hr0⟩ := h_ul
        simp only [hr1, hr0, and_self, if_true]
        by_cases hxx : x₁ = x₀
        · have hmatch := hpair.decision_even_same_upper hpar hr1 hr0 hxx
          simp only [hxx, if_true]
          rw [hxx] at hmatch
          split_ifs <;>
            refine ⟨?_, ?_⟩ <;>
            (first | exact hmatch | exact ha0 | exact ha1 | rfl)
        · simp only [hxx, if_false]
          have ha_eq : a = Answer.outT :=
            hpair.decision_even_diff_upper hpar hr1 hr0 hxx
          split_ifs <;>
            refine ⟨?_, ?_⟩ <;>
            (first | exact ha_eq.symm | exact ha0 | exact ha1 | rfl)
      · simp only [show ¬ (s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1)
          from h_ul, if_false]
        -- Decision is a no-op; (b₀, b₁) = (s₀, s₁) entering propagation.
        split_ifs <;>
          refine ⟨?_, ?_⟩ <;>
          (first | exact ha0 | exact ha1 | rfl)
  · -- Odd n.
    simp only [hpar, if_false]
    obtain ⟨hm0, hm1⟩ := hpair.decision_odd_match hpar
    by_cases hb0 : s₀.rank.val + 1 = ceilHalf n
    · have hma0 : opinionToAnswer x₀ = a := hm0 hb0
      by_cases hb1 : s₁.rank.val + 1 = ceilHalf n
      · have hma1 : opinionToAnswer x₁ = a := hm1 hb1
        simp only [hb0, hb1, if_true]
        split_ifs <;>
          refine ⟨?_, ?_⟩ <;>
          (first | exact hma0 | exact hma1 | rfl)
      · simp only [hb0, hb1, if_true, if_false]
        split_ifs <;>
          refine ⟨?_, ?_⟩ <;>
          (first | exact hma0 | exact ha1 | rfl)
    · by_cases hb1 : s₁.rank.val + 1 = ceilHalf n
      · have hma1 : opinionToAnswer x₁ = a := hm1 hb1
        simp only [hb0, hb1, if_true, if_false]
        split_ifs <;>
          refine ⟨?_, ?_⟩ <;>
          (first | exact ha0 | exact hma1 | rfl)
      · simp only [hb0, hb1, if_false]
        -- Decision is a no-op; (b₀, b₁) = (s₀, s₁) entering propagation. The
        -- propagation cases here are governed by `hb0 = hb1 = ¬(_ = ceilHalf n)`,
        -- so its outer two if-conditions are also false; goal collapses to ha0,ha1.
        first
          | exact ⟨ha0, ha1⟩
          | (split_ifs <;>
              refine ⟨?_, ?_⟩ <;>
              (first | exact ha0 | exact ha1 | rfl))

/-- Original "preservation" form: `.answer` field unchanged. -/
theorem transitionPEM_consensus_pair_answer
    {trank Rmax nA : ℕ} {a : Answer}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hne : s₀.rank ≠ s₁.rank) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.answer = s₀.answer ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.answer = s₁.answer := by
  obtain ⟨h1, h2⟩ := transitionPEM_consensus_pair_answer_eq
    (trank := trank) (Rmax := Rmax) hRank hpair hne
  exact ⟨h1.trans hpair.answer₀.symm, h2.trans hpair.answer₁.symm⟩

end SSEM

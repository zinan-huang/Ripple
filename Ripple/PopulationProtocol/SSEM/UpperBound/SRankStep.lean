/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# One step of `P_EM` on `S_rank` (P3 Lemmas 1 and 2)

For a configuration `C ∈ S_rank` (all agents Settled, pairwise distinct ranks) and a pair
`u ≠ v`, the ranking rule `rankDeltaOSSR` and Phases 1–3 are the identity, and the step is
Phase 4 (swap, decide, propagate) on the pair (`srank_step_eq`). Consequences:

* the step stays in `S_rank` unless it is a Phase-4 reset, which lands in `PT_L`
  (`srank_step_srank_or_ptl`); no reset happens while the median timer is at least `2`
  (`srank_step_srank_of_medT`);
* the median timer `medT` drops by one exactly at the pairs {median, last}
  (`srank_step_medT`);
* the number `misB` of B-agents below rank `n_A` never increases, and drops at every pair
  (B-agent below `n_A`, A-agent at or above `n_A`) (`srank_step_misB_le`, `srank_step_misB_lt`);
* on `S_sw` no swap happens and ranks are kept (`ssorted_step`); a decision pair decides
  (`ssorted_step_decide`); `D` is kept by non-reset steps (`decided_step`), and a reset from `D`
  lands in `Z` (`decided_step_zTwo`); from `D` with median timer `0`, the median meeting an
  agent with a wrong answer resets (`decided_step_reset`);
* `AnsOK` is kept by non-reset steps (`ansOK_step`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.StagesSRankTools

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators

variable {n : ℕ}

/-! ### The median timer test and the majority answer -/

/-- The majority answer as a function of `n_A` (as in `ConsensusPair.majority_eq`). -/
def majOf (n nA : ℕ) : Answer :=
  if nA > n - nA then .outA else if nA < n - nA then .outB else .outT

theorem nAOf_le (C : Config (AgentState n) Opinion n) : nAOf C ≤ n := by
  have := nAOf_add_nBOf C; omega

theorem majorityAnswer_eq_majOf (C : Config (AgentState n) Opinion n) :
    majorityAnswer C = majOf n (nAOf C) := by
  have hsum := nAOf_add_nBOf C
  unfold majorityAnswer majOf
  have hnB : nBOf C = n - nAOf C := by omega
  rw [hnB]

theorem opinionToAnswer_odd {x : Opinion} {r nA : ℕ} (hodd : n % 2 = 1)
    (hr : r + 1 = ceilHalf n) (hx : x = .A ↔ r < nA) (hnA : nA ≤ n) :
    opinionToAnswer x = majOf n nA := by
  unfold majOf
  unfold ceilHalf at hr
  cases x with
  | A =>
    have h := hx.mp rfl
    have e : nA > n - nA := by omega
    simp [opinionToAnswer, e]
  | B =>
    have h : ¬ r < nA := fun h' => by cases hx.mpr h'
    have e1 : ¬ nA > n - nA := by omega
    have e2 : nA < n - nA := by omega
    simp [opinionToAnswer, e1, e2]

theorem opinionToAnswer_even {x₀ x₁ : Opinion} {r₀ r₁ nA : ℕ} (hev : n % 2 = 0)
    (hr₀ : r₀ + 1 = n / 2) (hr₁ : r₁ + 1 = n / 2 + 1) (hx₀ : x₀ = .A ↔ r₀ < nA)
    (hx₁ : x₁ = .A ↔ r₁ < nA) (hnA : nA ≤ n) :
    (if x₀ = x₁ then opinionToAnswer x₀ else .outT) = majOf n nA := by
  unfold majOf
  cases x₀ <;> cases x₁
  · have h1 := hx₁.mp rfl
    have e : nA > n - nA := by omega
    simp [opinionToAnswer, e]
  · have h0 := hx₀.mp rfl
    have h1 : ¬ r₁ < nA := fun h => by cases hx₁.mpr h
    have e1 : ¬ nA > n - nA := by omega
    have e2 : ¬ nA < n - nA := by omega
    simp [e1, e2]
  · have h0 : ¬ r₀ < nA := fun h => by cases hx₀.mpr h
    have h1 := hx₁.mp rfl
    omega
  · have h0 : ¬ r₀ < nA := fun h => by cases hx₀.mpr h
    have e1 : ¬ nA > n - nA := by omega
    have e2 : nA < n - nA := by omega
    simp [opinionToAnswer, e1, e2]

/-! ### `medianTick` -/

@[simp] theorem medianTick_rank (a b : AgentState n) : (medianTick n a b).rank = a.rank := by
  unfold medianTick; split_ifs <;> rfl

@[simp] theorem medianTick_role (a b : AgentState n) : (medianTick n a b).role = a.role := by
  unfold medianTick; split_ifs <;> rfl

@[simp] theorem medianTick_answer (a b : AgentState n) :
    (medianTick n a b).answer = a.answer := by
  unfold medianTick; split_ifs <;> rfl

theorem medianTick_timer (a b : AgentState n) :
    (medianTick n a b).timer =
      if a.rank.val + 1 = ceilHalf n ∧ b.rank.val + 1 = n then a.timer - 1 else a.timer := by
  unfold medianTick; split_ifs <;> rfl

theorem medianTick_of_not_med (a b : AgentState n) (h : ¬ a.rank.val + 1 = ceilHalf n) :
    medianTick n a b = a := by
  unfold medianTick; rw [if_neg (fun h' => h h'.1)]

/-! ### Phase 4 on a pair -/

section Pair

variable (R : ℕ) (b₀ b₁ : AgentState n)

theorem phase4_propagate_of_med0 (h : b₀.rank.val + 1 = ceilHalf n) :
    phase4_propagate n R b₀ b₁ =
      if (medianTick n b₀ b₁).timer = 0 ∧ (medianTick n b₀ b₁).answer ≠ b₁.answer then
        ({ (medianTick n b₀ b₁) with role := .Resetting, leader := .L, resetcount := R },
         { b₁ with
            answer := (medianTick n b₀ b₁).answer, role := .Resetting, leader := .L,
            resetcount := R })
      else (medianTick n b₀ b₁, b₁) := by
  have e : medianTick n b₀ b₁ =
      if b₁.rank.val + 1 = n then { b₀ with timer := b₀.timer - 1 } else b₀ := by
    unfold medianTick; simp only [h, true_and]
  rw [e]
  unfold phase4_propagate
  rw [if_pos h]

theorem phase4_propagate_of_med1 (h0 : ¬ b₀.rank.val + 1 = ceilHalf n)
    (h : b₁.rank.val + 1 = ceilHalf n) :
    phase4_propagate n R b₀ b₁ =
      if (medianTick n b₁ b₀).timer = 0 ∧ (medianTick n b₁ b₀).answer ≠ b₀.answer then
        ({ b₀ with
            answer := (medianTick n b₁ b₀).answer, role := .Resetting, leader := .L,
            resetcount := R },
         { (medianTick n b₁ b₀) with role := .Resetting, leader := .L, resetcount := R })
      else (b₀, medianTick n b₁ b₀) := by
  have e : medianTick n b₁ b₀ =
      if b₀.rank.val + 1 = n then { b₁ with timer := b₁.timer - 1 } else b₁ := by
    unfold medianTick; simp only [h, true_and]
  rw [e]
  unfold phase4_propagate
  rw [if_neg h0, if_pos h]

theorem phase4_propagate_of_none (h0 : ¬ b₀.rank.val + 1 = ceilHalf n)
    (h1 : ¬ b₁.rank.val + 1 = ceilHalf n) : phase4_propagate n R b₀ b₁ = (b₀, b₁) := by
  unfold phase4_propagate
  rw [if_neg h0, if_neg h1]

theorem phase4_propagate_rank :
    (phase4_propagate n R b₀ b₁).1.rank = b₀.rank ∧
      (phase4_propagate n R b₀ b₁).2.rank = b₁.rank := by
  by_cases m0 : b₀.rank.val + 1 = ceilHalf n
  · rw [phase4_propagate_of_med0 R b₀ b₁ m0]
    split_ifs <;> exact ⟨medianTick_rank _ _, rfl⟩
  · by_cases m1 : b₁.rank.val + 1 = ceilHalf n
    · rw [phase4_propagate_of_med1 R b₀ b₁ m0 m1]
      split_ifs <;> exact ⟨rfl, medianTick_rank _ _⟩
    · rw [phase4_propagate_of_none R b₀ b₁ m0 m1]
      exact ⟨rfl, rfl⟩

theorem phase4_propagate_timer (hne : b₀.rank ≠ b₁.rank) :
    (phase4_propagate n R b₀ b₁).1.timer = (medianTick n b₀ b₁).timer ∧
      (phase4_propagate n R b₀ b₁).2.timer = (medianTick n b₁ b₀).timer := by
  have hv : b₀.rank.val ≠ b₁.rank.val := fun h => hne (Fin.ext h)
  by_cases m0 : b₀.rank.val + 1 = ceilHalf n
  · have m1 : ¬ b₁.rank.val + 1 = ceilHalf n := by omega
    rw [phase4_propagate_of_med0 R b₀ b₁ m0, medianTick_of_not_med b₁ b₀ m1]
    split_ifs <;> exact ⟨rfl, rfl⟩
  · rw [medianTick_of_not_med b₀ b₁ m0]
    by_cases m1 : b₁.rank.val + 1 = ceilHalf n
    · rw [phase4_propagate_of_med1 R b₀ b₁ m0 m1]
      split_ifs <;> exact ⟨rfl, rfl⟩
    · rw [phase4_propagate_of_none R b₀ b₁ m0 m1, medianTick_of_not_med b₁ b₀ m1]
      exact ⟨rfl, rfl⟩

/-- Roles after `phase4_propagate` on a Settled pair: no reset (answers kept), or a Phase-4
reset (both Resetting, `resetcount = R`, leaders `L`), caused by a median state whose ticked
timer is `0` and whose answer differs from the partner's; both get the median's answer. -/
theorem phase4_propagate_role (h0 : b₀.role = .Settled) (h1 : b₁.role = .Settled) :
    ((phase4_propagate n R b₀ b₁).1.role = .Settled ∧
        (phase4_propagate n R b₀ b₁).2.role = .Settled ∧
        (phase4_propagate n R b₀ b₁).1.answer = b₀.answer ∧
        (phase4_propagate n R b₀ b₁).2.answer = b₁.answer) ∨
      ((phase4_propagate n R b₀ b₁).1.role = .Resetting ∧
        (phase4_propagate n R b₀ b₁).2.role = .Resetting ∧
        (phase4_propagate n R b₀ b₁).1.resetcount = R ∧
        (phase4_propagate n R b₀ b₁).2.resetcount = R ∧
        (phase4_propagate n R b₀ b₁).1.leader = .L ∧
        (phase4_propagate n R b₀ b₁).2.leader = .L ∧
        ((b₀.rank.val + 1 = ceilHalf n ∧ (medianTick n b₀ b₁).timer = 0 ∧
            b₀.answer ≠ b₁.answer ∧ (phase4_propagate n R b₀ b₁).1.answer = b₀.answer ∧
            (phase4_propagate n R b₀ b₁).2.answer = b₀.answer) ∨
          (b₁.rank.val + 1 = ceilHalf n ∧ (medianTick n b₁ b₀).timer = 0 ∧
            b₁.answer ≠ b₀.answer ∧ (phase4_propagate n R b₀ b₁).1.answer = b₁.answer ∧
            (phase4_propagate n R b₀ b₁).2.answer = b₁.answer))) := by
  by_cases m0 : b₀.rank.val + 1 = ceilHalf n
  · rw [phase4_propagate_of_med0 R b₀ b₁ m0]
    split_ifs with hr
    · right
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨m0, hr.1, ?_, ?_, ?_⟩⟩
      · simpa using hr.2
      · change (medianTick n b₀ b₁).answer = b₀.answer
        simp
      · change (medianTick n b₀ b₁).answer = b₀.answer
        simp
    · left
      exact ⟨by simp [h0], h1, by simp, rfl⟩
  · by_cases m1 : b₁.rank.val + 1 = ceilHalf n
    · rw [phase4_propagate_of_med1 R b₀ b₁ m0 m1]
      split_ifs with hr
      · right
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨m1, hr.1, ?_, ?_, ?_⟩⟩
        · simpa using hr.2
        · change (medianTick n b₁ b₀).answer = b₁.answer
          simp
        · change (medianTick n b₁ b₀).answer = b₁.answer
          simp
      · left
        exact ⟨h0, by simp [h1], rfl, by simp⟩
    · rw [phase4_propagate_of_none R b₀ b₁ m0 m1]
      left
      exact ⟨h0, h1, rfl, rfl⟩

/-- A median state whose ticked timer is `0` and whose answer differs from the partner's
causes a Phase-4 reset. -/
theorem phase4_propagate_reset_of_med0 (h : b₀.rank.val + 1 = ceilHalf n)
    (ht : (medianTick n b₀ b₁).timer = 0) (ha : b₀.answer ≠ b₁.answer) :
    (phase4_propagate n R b₀ b₁).1.role = .Resetting := by
  rw [phase4_propagate_of_med0 R b₀ b₁ h, if_pos ⟨ht, by simpa using ha⟩]

theorem phase4_propagate_reset_of_med1 (hne : b₀.rank ≠ b₁.rank)
    (h : b₁.rank.val + 1 = ceilHalf n)
    (ht : (medianTick n b₁ b₀).timer = 0) (ha : b₁.answer ≠ b₀.answer) :
    (phase4_propagate n R b₀ b₁).1.role = .Resetting := by
  have h0 : ¬ b₀.rank.val + 1 = ceilHalf n := fun h' => hne (Fin.ext (by omega))
  rw [phase4_propagate_of_med1 R b₀ b₁ h0 h, if_pos ⟨ht, by simpa using ha⟩]

end Pair

section Decide

variable (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion)

theorem phase4_decide_eq :
    (phase4_decide n s₀ s₁ x₀ x₁).1 =
        { s₀ with answer := (phase4_decide n s₀ s₁ x₀ x₁).1.answer } ∧
      (phase4_decide n s₀ s₁ x₀ x₁).2 =
        { s₁ with answer := (phase4_decide n s₀ s₁ x₀ x₁).2.answer } := by
  unfold phase4_decide
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem phase4_decide_rank :
    (phase4_decide n s₀ s₁ x₀ x₁).1.rank = s₀.rank ∧
      (phase4_decide n s₀ s₁ x₀ x₁).2.rank = s₁.rank := by
  have h1 := congrArg AgentState.rank (phase4_decide_eq s₀ s₁ x₀ x₁).1
  have h2 := congrArg AgentState.rank (phase4_decide_eq s₀ s₁ x₀ x₁).2
  exact ⟨h1, h2⟩

theorem phase4_decide_timer :
    (phase4_decide n s₀ s₁ x₀ x₁).1.timer = s₀.timer ∧
      (phase4_decide n s₀ s₁ x₀ x₁).2.timer = s₁.timer := by
  have h1 := congrArg AgentState.timer (phase4_decide_eq s₀ s₁ x₀ x₁).1
  have h2 := congrArg AgentState.timer (phase4_decide_eq s₀ s₁ x₀ x₁).2
  exact ⟨h1, h2⟩

theorem phase4_decide_role_eq :
    (phase4_decide n s₀ s₁ x₀ x₁).1.role = s₀.role ∧
      (phase4_decide n s₀ s₁ x₀ x₁).2.role = s₁.role := by
  have h1 := congrArg AgentState.role (phase4_decide_eq s₀ s₁ x₀ x₁).1
  have h2 := congrArg AgentState.role (phase4_decide_eq s₀ s₁ x₀ x₁).2
  exact ⟨h1, h2⟩

/-- Decide writes only to states of median-type rank. -/
theorem phase4_decide_answer_of_not_medType :
    (¬ IsMedType n s₀.rank.val → (phase4_decide n s₀ s₁ x₀ x₁).1.answer = s₀.answer) ∧
      (¬ IsMedType n s₁.rank.val → (phase4_decide n s₀ s₁ x₀ x₁).2.answer = s₁.answer) := by
  unfold IsMedType ceilHalf
  constructor
  · intro h
    unfold phase4_decide
    dsimp only
    unfold ceilHalf
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro h
    unfold phase4_decide
    dsimp only
    unfold ceilHalf
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **Decide on a sorted pair** (P3 Lemma 2): every answer it writes is the majority answer; for
`n` odd it writes to the median, for `n` even to a pair of the two median-type ranks. -/
theorem phase4_decide_sorted (nA : ℕ) (hnA : nA ≤ n) (hx₀ : x₀ = .A ↔ s₀.rank.val < nA)
    (hx₁ : x₁ = .A ↔ s₁.rank.val < nA) (hne : s₀.rank ≠ s₁.rank) :
    ((phase4_decide n s₀ s₁ x₀ x₁).1.answer = majOf n nA ∨
        (phase4_decide n s₀ s₁ x₀ x₁).1.answer = s₀.answer) ∧
      ((phase4_decide n s₀ s₁ x₀ x₁).2.answer = majOf n nA ∨
        (phase4_decide n s₀ s₁ x₀ x₁).2.answer = s₁.answer) ∧
      (n % 2 = 1 → s₀.rank.val + 1 = ceilHalf n →
        (phase4_decide n s₀ s₁ x₀ x₁).1.answer = majOf n nA) ∧
      (n % 2 = 1 → s₁.rank.val + 1 = ceilHalf n →
        (phase4_decide n s₀ s₁ x₀ x₁).2.answer = majOf n nA) ∧
      (n % 2 = 0 → IsMedType n s₀.rank.val → IsMedType n s₁.rank.val →
        (phase4_decide n s₀ s₁ x₀ x₁).1.answer = majOf n nA ∧
          (phase4_decide n s₀ s₁ x₀ x₁).2.answer = majOf n nA) := by
  have hv : s₀.rank.val ≠ s₁.rank.val := fun h => hne (Fin.ext h)
  unfold phase4_decide
  by_cases hev : n % 2 = 0
  · rw [if_pos hev]
    by_cases h1 : s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1
    · rw [if_pos h1]
      have e := opinionToAnswer_even hev h1.1 h1.2 hx₀ hx₁ hnA
      by_cases hxx : x₀ = x₁
      · rw [if_pos hxx] at e ⊢
        exact ⟨Or.inl e, Or.inl e, fun h => by omega, fun h => by omega, fun _ _ _ => ⟨e, e⟩⟩
      · rw [if_neg hxx] at e ⊢
        exact ⟨Or.inl e, Or.inl e, fun h => by omega, fun h => by omega, fun _ _ _ => ⟨e, e⟩⟩
    · rw [if_neg h1]
      by_cases h2 : s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1
      · rw [if_pos h2]
        have e := opinionToAnswer_even hev h2.1 h2.2 hx₁ hx₀ hnA
        by_cases hxx : x₁ = x₀
        · rw [if_pos hxx] at e ⊢
          exact ⟨Or.inl e, Or.inl e, fun h => by omega, fun h => by omega, fun _ _ _ => ⟨e, e⟩⟩
        · rw [if_neg hxx] at e ⊢
          exact ⟨Or.inl e, Or.inl e, fun h => by omega, fun h => by omega, fun _ _ _ => ⟨e, e⟩⟩
      · rw [if_neg h2]
        refine ⟨Or.inr rfl, Or.inr rfl, fun h => by omega, fun h => by omega, ?_⟩
        intro _ m0 m1
        unfold IsMedType ceilHalf at m0 m1
        exfalso
        omega
  · rw [if_neg hev]
    have hodd : n % 2 = 1 := by omega
    dsimp only
    by_cases m0 : s₀.rank.val + 1 = ceilHalf n
    · have e0 := opinionToAnswer_odd hodd m0 hx₀ hnA
      have m1 : ¬ s₁.rank.val + 1 = ceilHalf n := by omega
      rw [if_pos m0, if_neg m1]
      exact ⟨Or.inl e0, Or.inr rfl, fun _ _ => e0, fun _ h => absurd h m1,
        fun h => absurd h hev⟩
    · by_cases m1 : s₁.rank.val + 1 = ceilHalf n
      · have e1 := opinionToAnswer_odd hodd m1 hx₁ hnA
        rw [if_neg m0, if_pos m1]
        exact ⟨Or.inr rfl, Or.inl e1, fun _ h => absurd h m0, fun _ _ => e1,
          fun h => absurd h hev⟩
      · rw [if_neg m0, if_neg m1]
        exact ⟨Or.inr rfl, Or.inr rfl, fun _ h => absurd h m0, fun _ h => absurd h m1,
          fun h => absurd h hev⟩

end Decide

/-! ### The Phase-4 output of a Settled pair -/

/-- Phase 4 of `P_EM` (swap, decide, propagate) on a pair. -/
noncomputable def pair4 (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) : AgentState n × AgentState n :=
  phase4_propagate n (rmaxPaper n)
    (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1 (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1
    (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1 (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).2

theorem phase4_swap_cases (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    phase4_swap s₀ s₁ x₀ x₁ = (s₀, s₁) ∨ phase4_swap s₀ s₁ x₀ x₁ = (s₁, s₀) := by
  unfold phase4_swap
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem transitionPEM_phase4_settled {R : ℕ} {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs0 : s₀.role = .Settled) (hs1 : s₁.role = .Settled) :
    transitionPEM_phase4 n R (s₀, s₁) x₀ x₁ =
      phase4_propagate n R
        (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1 (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1
        (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1 (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).2 := by
  unfold transitionPEM_phase4
  dsimp only
  rw [if_pos ⟨hs0, hs1⟩]

section Pair4

variable {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}

theorem phase4_swap_spec (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    (phase4_swap s₀ s₁ x₀ x₁ = (s₀, s₁) ∧ ¬ (s₀.rank < s₁.rank ∧ x₀ = .B ∧ x₁ = .A)) ∨
      (phase4_swap s₀ s₁ x₀ x₁ = (s₁, s₀) ∧ (s₀.rank < s₁.rank ∧ x₀ = .B ∧ x₁ = .A)) := by
  unfold phase4_swap
  split_ifs with h
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem pair4_rank :
    (pair4 s₀ s₁ x₀ x₁).1.rank = (phase4_swap s₀ s₁ x₀ x₁).1.rank ∧
      (pair4 s₀ s₁ x₀ x₁).2.rank = (phase4_swap s₀ s₁ x₀ x₁).2.rank := by
  unfold pair4
  rw [(phase4_propagate_rank _ _ _).1, (phase4_propagate_rank _ _ _).2,
    (phase4_decide_rank _ _ _ _).1, (phase4_decide_rank _ _ _ _).2]
  exact ⟨rfl, rfl⟩

theorem pair4_of_noswap (h : phase4_swap s₀ s₁ x₀ x₁ = (s₀, s₁)) :
    pair4 s₀ s₁ x₀ x₁ = phase4_propagate n (rmaxPaper n) (phase4_decide n s₀ s₁ x₀ x₁).1
      (phase4_decide n s₀ s₁ x₀ x₁).2 := by
  unfold pair4
  rw [h]

/-- The median-timer term of a state. -/
def medTermS (n : ℕ) (s : AgentState n) : ℕ :=
  if s.rank.val + 1 = ceilHalf n then s.timer else 0

/-- The tick test: one state has the median rank and the other the last rank. -/
def tickS (n : ℕ) (a b : AgentState n) : Prop :=
  (a.rank.val + 1 = ceilHalf n ∧ b.rank.val + 1 = n) ∨
    (b.rank.val + 1 = ceilHalf n ∧ a.rank.val + 1 = n)

instance (a b : AgentState n) : Decidable (tickS n a b) := by unfold tickS; infer_instance

theorem medTermS_tick (a b : AgentState n) (hne : a.rank ≠ b.rank) :
    medTermS n (medianTick n a b) + medTermS n (medianTick n b a) =
      medTermS n a + medTermS n b - (if tickS n a b then 1 else 0) := by
  have hv : a.rank.val ≠ b.rank.val := fun h => hne (Fin.ext h)
  unfold medTermS tickS
  rw [medianTick_rank, medianTick_rank, medianTick_timer, medianTick_timer]
  split_ifs <;> omega

theorem medTermS_congr {s t : AgentState n} (h1 : s.rank = t.rank) (h2 : s.timer = t.timer) :
    medTermS n s = medTermS n t := by
  unfold medTermS; rw [h1, h2]

/-- Phase 4 changes the median-timer terms of a pair exactly by the tick. -/
theorem pair4_medTerm (hne : s₀.rank ≠ s₁.rank) :
    medTermS n (pair4 s₀ s₁ x₀ x₁).1 + medTermS n (pair4 s₀ s₁ x₀ x₁).2 =
      medTermS n s₀ + medTermS n s₁ - (if tickS n s₀ s₁ then 1 else 0) := by
  have gen : ∀ a b : AgentState n, a.rank ≠ b.rank →
      medTermS n (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).1 +
        medTermS n (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).2 =
      medTermS n a + medTermS n b - (if tickS n a b then 1 else 0) := by
    intro a b hab
    have hdr := phase4_decide_rank a b x₀ x₁
    have hdt := phase4_decide_timer a b x₀ x₁
    have hdne : (phase4_decide n a b x₀ x₁).1.rank ≠ (phase4_decide n a b x₀ x₁).2.rank := by
      rw [hdr.1, hdr.2]; exact hab
    have hp := phase4_propagate_timer (rmaxPaper n) _ _ hdne
    have hr := phase4_propagate_rank (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
      (phase4_decide n a b x₀ x₁).2
    have e1 : medTermS n (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
        (phase4_decide n a b x₀ x₁).2).1 = medTermS n (medianTick n a b) := by
      apply medTermS_congr
      · rw [hr.1, hdr.1, medianTick_rank]
      · rw [hp.1, medianTick_timer, medianTick_timer, hdr.1, hdr.2, hdt.1]
    have e2 : medTermS n (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
        (phase4_decide n a b x₀ x₁).2).2 = medTermS n (medianTick n b a) := by
      apply medTermS_congr
      · rw [hr.2, hdr.2, medianTick_rank]
      · rw [hp.2, medianTick_timer, medianTick_timer, hdr.1, hdr.2, hdt.2]
    rw [e1, e2]
    exact medTermS_tick a b hab
  unfold pair4
  rcases phase4_swap_cases s₀ s₁ x₀ x₁ with h | h <;> rw [h]
  · exact gen s₀ s₁ hne
  · rw [gen s₁ s₀ (Ne.symm hne)]
    have ht : tickS n s₁ s₀ ↔ tickS n s₀ s₁ := Or.comm
    simp only [ht]
    omega

/-- Roles after Phase 4 on a Settled pair: no reset (the answers are those written by decide),
or a Phase-4 reset (both Resetting with `resetcount = Rmax` and leader `L`), which needs the
median state of the pair to have timer at most `1`. -/
theorem pair4_role (hs0 : s₀.role = .Settled) (hs1 : s₁.role = .Settled) :
    ((pair4 s₀ s₁ x₀ x₁).1.role = .Settled ∧ (pair4 s₀ s₁ x₀ x₁).2.role = .Settled ∧
        (pair4 s₀ s₁ x₀ x₁).1.answer =
          (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1 (phase4_swap s₀ s₁ x₀ x₁).2
            x₀ x₁).1.answer ∧
        (pair4 s₀ s₁ x₀ x₁).2.answer =
          (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1 (phase4_swap s₀ s₁ x₀ x₁).2
            x₀ x₁).2.answer) ∨
      ((pair4 s₀ s₁ x₀ x₁).1.role = .Resetting ∧ (pair4 s₀ s₁ x₀ x₁).2.role = .Resetting ∧
        (pair4 s₀ s₁ x₀ x₁).1.resetcount = rmaxPaper n ∧
        (pair4 s₀ s₁ x₀ x₁).2.resetcount = rmaxPaper n ∧
        (pair4 s₀ s₁ x₀ x₁).1.leader = .L ∧ (pair4 s₀ s₁ x₀ x₁).2.leader = .L ∧
        ((s₀.rank.val + 1 = ceilHalf n ∧ s₀.timer ≤ 1) ∨
          (s₁.rank.val + 1 = ceilHalf n ∧ s₁.timer ≤ 1))) := by
  have key : ∀ a b : AgentState n, (medianTick n a b).timer = 0 → a.timer ≤ 1 := by
    intro a b h; rw [medianTick_timer] at h; split_ifs at h <;> omega
  have gen : ∀ a b : AgentState n, a.role = .Settled → b.role = .Settled →
      ((phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).1.role = .Settled ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).2.role = .Settled ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).1.answer = (phase4_decide n a b x₀ x₁).1.answer ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).2.answer = (phase4_decide n a b x₀ x₁).2.answer) ∨
      ((phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).1.role = .Resetting ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).2.role = .Resetting ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).1.resetcount = rmaxPaper n ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).2.resetcount = rmaxPaper n ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).1.leader = .L ∧
        (phase4_propagate n (rmaxPaper n) (phase4_decide n a b x₀ x₁).1
          (phase4_decide n a b x₀ x₁).2).2.leader = .L ∧
        ((a.rank.val + 1 = ceilHalf n ∧ a.timer ≤ 1) ∨
          (b.rank.val + 1 = ceilHalf n ∧ b.timer ≤ 1))) := by
    intro a b ha hb
    have hdr := phase4_decide_rank a b x₀ x₁
    have hdt := phase4_decide_timer a b x₀ x₁
    have hdro := phase4_decide_role_eq a b x₀ x₁
    rcases phase4_propagate_role (rmaxPaper n) _ _ (hdro.1.trans ha) (hdro.2.trans hb) with
      h' | ⟨r1, r2, c1, c2, l1, l2, hm⟩
    · exact Or.inl h'
    · refine Or.inr ⟨r1, r2, c1, c2, l1, l2, ?_⟩
      rcases hm with ⟨m, t, -⟩ | ⟨m, t, -⟩
      · have ht := key _ _ t
        rw [hdt.1] at ht
        rw [hdr.1] at m
        exact Or.inl ⟨m, ht⟩
      · have ht := key _ _ t
        rw [hdt.2] at ht
        rw [hdr.2] at m
        exact Or.inr ⟨m, ht⟩
  unfold pair4
  rcases phase4_swap_cases s₀ s₁ x₀ x₁ with h | h <;> rw [h]
  · exact gen s₀ s₁ hs0 hs1
  · rcases gen s₁ s₀ hs1 hs0 with h' | ⟨r1, r2, c1, c2, l1, l2, hm⟩
    · exact Or.inl h'
    · exact Or.inr ⟨r1, r2, c1, c2, l1, l2, hm.symm⟩

/-- The count term of B-agents below rank `nA`. -/
def misTerm (nA : ℕ) (q : AgentState n × Opinion) : ℕ :=
  if q.2 = .B ∧ q.1.rank.val < nA then 1 else 0

/-- Phase 4 never increases the number of B-agents below rank `nA`, and decreases it when a
B-agent below `nA` initiates with an A-agent at or above `nA` (P3 Lemma 12). -/
theorem pair4_misTerm (nA : ℕ) :
    misTerm nA ((pair4 s₀ s₁ x₀ x₁).1, x₀) + misTerm nA ((pair4 s₀ s₁ x₀ x₁).2, x₁) +
        (if x₀ = .B ∧ s₀.rank.val < nA ∧ x₁ = .A ∧ nA ≤ s₁.rank.val then 1 else 0) ≤
      misTerm nA (s₀, x₀) + misTerm nA (s₁, x₁) := by
  have hr := pair4_rank (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
  unfold misTerm
  dsimp only
  rw [hr.1, hr.2]
  rcases phase4_swap_spec s₀ s₁ x₀ x₁ with ⟨h, hc⟩ | ⟨h, hlt, hb, ha⟩
  · rw [h]
    dsimp only
    have hx : ¬ (x₀ = .B ∧ s₀.rank.val < nA ∧ x₁ = .A ∧ nA ≤ s₁.rank.val) := by
      rintro ⟨a, b, c, d⟩
      exact hc ⟨Fin.lt_def.mpr (by omega), a, c⟩
    rw [if_neg hx]
    simp only [add_zero, le_refl]
  · rw [h]
    dsimp only
    subst hb ha
    have := Fin.lt_def.mp hlt
    simp only [true_and]
    split_ifs <;> simp_all <;> omega

end Pair4

/-! ### One step on `S_rank` -/

section Config

variable {hn : 0 < n} {C : Config (AgentState n) Opinion n} {u v : Fin n}

theorem SRank.ne_rank (hC : SRank C) (huv : u ≠ v) : (C u).1.rank ≠ (C v).1.rank :=
  fun h => huv (hC.2 h)

theorem two_le_of_ne (huv : u ≠ v) : 2 ≤ n := by
  have h1 := u.isLt
  have h2 := v.isLt
  have : u.val ≠ v.val := fun h => huv (Fin.ext h)
  omega

theorem step_other' {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n) (u v w : Fin n)
    (hu : w ≠ u) (hv : w ≠ v) : (C.step P u v) w = C w := by
  unfold Config.step
  split_ifs
  · rfl
  · simp [hu, hv]

/-- **The step on `S_rank`**: Phase 4 on the pair, nothing else (P3 Lemma 2). -/
theorem srank_step_eq (hC : SRank C) (huv : u ≠ v) :
    C.step (PEM40 n hn) u v = fun w =>
      if w = u then ((pair4 (C u).1 (C v).1 (C u).2 (C v).2).1, (C u).2)
      else if w = v then ((pair4 (C u).1 (C v).1 (C u).2 (C v).2).2, (C v).2) else C w := by
  have hs0 := hC.1 u
  have hs1 := hC.1 v
  have hne := hC.ne_rank huv
  have hδ : (PEM40 n hn).δ (C u, C v) = pair4 (C u).1 (C v).1 (C u).2 (C v).2 := by
    refine (transitionPEM_eq_phase4_of_settled_fix (trank := 40) (Rmax := rmaxPaper n)
      (x₀ := (C u).2) (x₁ := (C v).2)
      (rankDeltaOSSR_settled_distinct_ranks (Rmax := rmaxPaper n) (Emax := 208 * n)
        (Dmax := 32 * n) (hn := hn) hs0 hs1 hne) hs0 hs1).trans ?_
    exact transitionPEM_phase4_settled hs0 hs1
  funext w
  simp only [Config.step, if_neg huv, hδ]

theorem srank_step_u (hC : SRank C) (huv : u ≠ v) :
    (C.step (PEM40 n hn) u v) u = ((pair4 (C u).1 (C v).1 (C u).2 (C v).2).1, (C u).2) := by
  rw [srank_step_eq hC huv]
  simp

theorem srank_step_v (hC : SRank C) (huv : u ≠ v) :
    (C.step (PEM40 n hn) u v) v = ((pair4 (C u).1 (C v).1 (C u).2 (C v).2).2, (C v).2) := by
  rw [srank_step_eq hC huv]
  simp [Ne.symm huv]

theorem nAOf_step40 (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    nAOf (C.step (PEM40 n hn) u v) = nAOf C :=
  nAOf_step_eq C u v

theorem majorityAnswer_step40 (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    majorityAnswer (C.step (PEM40 n hn) u v) = majorityAnswer C :=
  majorityAnswer_step_eq C u v

/-- Ranks after a step on `S_rank` are those of `C` permuted (identity or the swap of `u, v`). -/
theorem srank_step_rank_perm (hC : SRank C) (huv : u ≠ v) :
    ∃ τ : Equiv.Perm (Fin n),
      ∀ w, ((C.step (PEM40 n hn) u v) w).1.rank = (C (τ w)).1.rank := by
  have hr := pair4_rank (s₀ := (C u).1) (s₁ := (C v).1) (x₀ := (C u).2) (x₁ := (C v).2)
  rcases phase4_swap_cases (C u).1 (C v).1 (C u).2 (C v).2 with h | h
  · refine ⟨Equiv.refl _, fun w => ?_⟩
    rw [Equiv.refl_apply]
    by_cases h1 : w = u
    · subst h1; rw [srank_step_u hC huv]; dsimp only; rw [hr.1, h]
    · by_cases h2 : w = v
      · subst h2; rw [srank_step_v hC huv]; dsimp only; rw [hr.2, h]
      · rw [step_other' _ C u v w h1 h2]
  · refine ⟨Equiv.swap u v, fun w => ?_⟩
    by_cases h1 : w = u
    · subst h1; rw [srank_step_u hC huv, Equiv.swap_apply_left]; dsimp only; rw [hr.1, h]
    · by_cases h2 : w = v
      · subst h2; rw [srank_step_v hC huv, Equiv.swap_apply_right]; dsimp only; rw [hr.2, h]
      · rw [step_other' _ C u v w h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem srank_step_ranks_inj (hC : SRank C) (huv : u ≠ v) :
    Function.Injective (fun w => ((C.step (PEM40 n hn) u v) w).1.rank) := by
  obtain ⟨τ, hτ⟩ := srank_step_rank_perm (hn := hn) hC huv
  intro a b hab
  have h : (C (τ a)).1.rank = (C (τ b)).1.rank := by
    rw [← hτ a, ← hτ b]; exact hab
  exact τ.injective (hC.2 h)

/-- **Reset or not** (P3 Lemma 2): the step stays in `S_rank`, or both agents are reset to
Resetting with `resetcount = Rmax` and leader `L`, and then the median state of the pair had
timer at most `1`. -/
theorem srank_step_cases (hC : SRank C) (huv : u ≠ v) :
    SRank (C.step (PEM40 n hn) u v) ∨
      (((C.step (PEM40 n hn) u v) u).1.role = .Resetting ∧
        ((C.step (PEM40 n hn) u v) v).1.role = .Resetting ∧
        ((C.step (PEM40 n hn) u v) u).1.resetcount = rmaxPaper n ∧
        ((C.step (PEM40 n hn) u v) v).1.resetcount = rmaxPaper n ∧
        ((C.step (PEM40 n hn) u v) u).1.leader = .L ∧
        ((C.step (PEM40 n hn) u v) v).1.leader = .L ∧
        (((C u).1.rank.val + 1 = ceilHalf n ∧ (C u).1.timer ≤ 1) ∨
          ((C v).1.rank.val + 1 = ceilHalf n ∧ (C v).1.timer ≤ 1))) := by
  rw [srank_step_u hC huv, srank_step_v hC huv]
  rcases pair4_role (x₀ := (C u).2) (x₁ := (C v).2) (hC.1 u) (hC.1 v) with
    ⟨r1, r2, -, -⟩ | h
  · left
    refine ⟨fun w => ?_, srank_step_ranks_inj hC huv⟩
    by_cases h1 : w = u
    · subst h1; rw [srank_step_u hC huv]; exact r1
    · by_cases h2 : w = v
      · subst h2; rw [srank_step_v hC huv]; exact r2
      · rw [step_other' _ C u v w h1 h2]; exact hC.1 w
  · right
    exact h

theorem srank_step_srank_or_ptl (hC : SRank C) (huv : u ≠ v) :
    SRank (C.step (PEM40 n hn) u v) ∨ PTL (C.step (PEM40 n hn) u v) := by
  rcases srank_step_cases (hn := hn) hC huv with h | ⟨r1, -, c1, -, l1, -, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨u, r1, c1⟩, ⟨u, l1⟩⟩

/-! ### The median timer -/

/-- The median timer: the sum of the timers of the agents of median rank (on `S_rank`, the
timer of the unique agent of median rank). -/
def medT (C : Config (AgentState n) Opinion n) : ℕ := ∑ w, medTermS n (C w).1

theorem srank_exists_rank (hC : SRank C) (r : Fin n) : ∃ w, (C w).1.rank = r :=
  (Finite.injective_iff_surjective.mp hC.2) r

theorem srank_exists_median (hC : SRank C) (hn2 : 2 ≤ n) :
    ∃ μ, (C μ).1.rank.val + 1 = ceilHalf n := by
  obtain ⟨μ, hμ⟩ := srank_exists_rank hC ⟨ceilHalf n - 1, by unfold ceilHalf; omega⟩
  refine ⟨μ, ?_⟩
  rw [hμ]
  unfold ceilHalf
  dsimp only
  omega

theorem srank_exists_last (hC : SRank C) (hn2 : 2 ≤ n) :
    ∃ ν, (C ν).1.rank.val + 1 = n := by
  obtain ⟨ν, hν⟩ := srank_exists_rank hC ⟨n - 1, by omega⟩
  refine ⟨ν, ?_⟩
  rw [hν]
  dsimp only
  omega

theorem medT_eq (hC : SRank C) {μ : Fin n} (hμ : (C μ).1.rank.val + 1 = ceilHalf n) :
    medT C = (C μ).1.timer := by
  unfold medT
  rw [Finset.sum_eq_single μ]
  · unfold medTermS; rw [if_pos hμ]
  · intro w _ hw
    unfold medTermS
    rw [if_neg]
    intro h
    exact hw (hC.2 (show (C w).1.rank = (C μ).1.rank from Fin.ext (by omega)))
  · intro h; exact absurd (Finset.mem_univ μ) h

/-- **The tick** (P3 Lemma 1(f), Lemma 2): the median timer drops by one exactly at the pairs
{median, last}. -/
theorem srank_step_medT (hC : SRank C) (huv : u ≠ v) :
    medT (C.step (PEM40 n hn) u v) =
      medT C - (if tickS n (C u).1 (C v).1 then 1 else 0) := by
  have hn2 := two_le_of_ne huv
  have hne := hC.ne_rank huv
  have hsum : medT (C.step (PEM40 n hn) u v) + (medTermS n (C u).1 + medTermS n (C v).1) =
      medT C + (medTermS n (pair4 (C u).1 (C v).1 (C u).2 (C v).2).1 +
        medTermS n (pair4 (C u).1 (C v).1 (C u).2 (C v).2).2) := by
    have h := sum_step_add (PEM40 n hn) C u v huv (fun q => medTermS n q.1)
    rw [srank_step_u hC huv, srank_step_v hC huv] at h
    exact h
  rw [pair4_medTerm hne] at hsum
  by_cases ht : tickS n (C u).1 (C v).1
  · rw [if_pos ht] at hsum ⊢
    have hM : medT C = medTermS n (C u).1 + medTermS n (C v).1 := by
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [medT_eq hC h1]
        unfold medTermS
        rw [if_pos h1, if_neg (by unfold ceilHalf at h1 ⊢; omega)]
        ring
      · rw [medT_eq hC h1]
        unfold medTermS
        rw [if_neg (by unfold ceilHalf at h1 ⊢; omega), if_pos h1]
        ring
    omega
  · rw [if_neg ht] at hsum ⊢
    omega

/-- No reset while the median timer is at least `2`. -/
theorem srank_step_srank_of_medT (hC : SRank C) (huv : u ≠ v) (h2 : 2 ≤ medT C) :
    SRank (C.step (PEM40 n hn) u v) := by
  rcases srank_step_cases (hn := hn) hC huv with h | ⟨-, -, -, -, -, -, hm⟩
  · exact h
  · exfalso
    rcases hm with ⟨m, t⟩ | ⟨m, t⟩
    · rw [medT_eq hC m] at h2; omega
    · rw [medT_eq hC m] at h2; omega

/-! ### Misplaced B-agents -/

/-- The number of B-agents of rank below `n_A`. -/
def misB (C : Config (AgentState n) Opinion n) : ℕ := ∑ w, misTerm (nAOf C) (C w)

/-- `misB` never increases on `S_rank`, and drops at every pair (B-agent of rank below `n_A`,
A-agent of rank at least `n_A`) (P3 Lemma 12). -/
theorem srank_step_misB (hC : SRank C) (huv : u ≠ v) :
    misB (C.step (PEM40 n hn) u v) +
        (if (C u).2 = .B ∧ (C u).1.rank.val < nAOf C ∧ (C v).2 = .A ∧
          nAOf C ≤ (C v).1.rank.val then 1 else 0) ≤ misB C := by
  have hnA : nAOf (C.step (PEM40 n hn) u v) = nAOf C := nAOf_step40 C u v
  have hsum := sum_step_add (PEM40 n hn) C u v huv (misTerm (nAOf C))
  rw [srank_step_u hC huv, srank_step_v hC huv] at hsum
  have hp := pair4_misTerm (s₀ := (C u).1) (s₁ := (C v).1) (x₀ := (C u).2) (x₁ := (C v).2)
    (nAOf C)
  simp only [Prod.mk.eta] at hp
  unfold misB
  rw [hnA]
  omega

/-! ### Sorted configurations -/

theorem ssorted_noswap (hC : SSorted C) (u v : Fin n) :
    phase4_swap (C u).1 (C v).1 (C u).2 (C v).2 = ((C u).1, (C v).1) := by
  unfold phase4_swap
  rw [if_neg]
  rintro ⟨hlt, hb, ha⟩
  have hu : ¬ (C u).1.rank.val < nAOf C := fun h => by
    have := (hC.2 u).mpr h
    rw [hb] at this
    cases this
  have hv : (C v).1.rank.val < nAOf C := (hC.2 v).mp ha
  have := Fin.lt_def.mp hlt
  omega

/-- On `S_sw` the ranks do not move. -/
theorem ssorted_step_rank (hC : SSorted C) (huv : u ≠ v) (w : Fin n) :
    ((C.step (PEM40 n hn) u v) w).1.rank = (C w).1.rank := by
  have hr := pair4_rank (s₀ := (C u).1) (s₁ := (C v).1) (x₀ := (C u).2) (x₁ := (C v).2)
  rw [ssorted_noswap hC u v] at hr
  by_cases h1 : w = u
  · subst h1; rw [srank_step_u hC.1 huv]; exact hr.1
  · by_cases h2 : w = v
    · subst h2; rw [srank_step_v hC.1 huv]; exact hr.2
    · rw [step_other' _ C u v w h1 h2]

theorem ssorted_step (hC : SSorted C) (huv : u ≠ v) (hC' : SRank (C.step (PEM40 n hn) u v)) :
    SSorted (C.step (PEM40 n hn) u v) := by
  refine ⟨hC', fun w => ?_⟩
  rw [step_input_preserved, ssorted_step_rank hC huv, nAOf_step40]
  exact hC.2 w

/-- On a non-reset step from `S_rank`, the answers of the pair are those written by decide. -/
theorem srank_step_answers (hC : SRank C) (huv : u ≠ v)
    (hC' : SRank (C.step (PEM40 n hn) u v)) :
    ((C.step (PEM40 n hn) u v) u).1.answer =
        (phase4_decide n (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).1
          (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).2 (C u).2 (C v).2).1.answer ∧
      ((C.step (PEM40 n hn) u v) v).1.answer =
        (phase4_decide n (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).1
          (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).2 (C u).2 (C v).2).2.answer := by
  have hu := hC'.1 u
  rw [srank_step_u hC huv] at hu
  rw [srank_step_u hC huv, srank_step_v hC huv]
  rcases pair4_role (x₀ := (C u).2) (x₁ := (C v).2) (hC.1 u) (hC.1 v) with
    ⟨-, -, a1, a2⟩ | ⟨r1, -⟩
  · exact ⟨a1, a2⟩
  · exfalso
    have : Role.Settled = Role.Resetting := hu.symm.trans r1
    cases this

/-- **`D` is kept by non-reset steps** (P3 Lemma 2). -/
theorem decided_step (hC : Decided C) (huv : u ≠ v) (hC' : SRank (C.step (PEM40 n hn) u v)) :
    Decided (C.step (PEM40 n hn) u v) := by
  have hS := hC.1
  refine ⟨ssorted_step hS huv hC', fun w hw => ?_⟩
  rw [majorityAnswer_step40]
  rw [ssorted_step_rank hS huv w] at hw
  have ha := srank_step_answers hS.1 huv hC'
  rw [ssorted_noswap hS u v] at ha
  have hd := phase4_decide_sorted (C u).1 (C v).1 (C u).2 (C v).2 (nAOf C) (nAOf_le C)
    (hS.2 u) (hS.2 v) (hS.1.ne_rank huv)
  rw [majorityAnswer_eq_majOf]
  by_cases h1 : w = u
  · subst h1
    rw [ha.1]
    rcases hd.1 with e | e
    · exact e
    · rw [e, ← majorityAnswer_eq_majOf]; exact hC.2 w hw
  · by_cases h2 : w = v
    · subst h2
      rw [ha.2]
      rcases hd.2.1 with e | e
      · exact e
      · rw [e, ← majorityAnswer_eq_majOf]; exact hC.2 w hw
    · rw [step_other' _ C u v w h1 h2, ← majorityAnswer_eq_majOf]
      exact hC.2 w hw

/-- A decision pair: for `n` odd, the pair contains the median; for `n` even, both states have
median-type rank. -/
def DecisionPair (n : ℕ) (a b : AgentState n) : Prop :=
  (n % 2 = 1 ∧ (a.rank.val + 1 = ceilHalf n ∨ b.rank.val + 1 = ceilHalf n)) ∨
    (n % 2 = 0 ∧ IsMedType n a.rank.val ∧ IsMedType n b.rank.val)

/-- **A decision pair decides** (P3 Lemma 13): from `S_sw`, a non-reset step on a decision pair
lands in `D`. -/
theorem ssorted_step_decide (hC : SSorted C) (huv : u ≠ v)
    (hC' : SRank (C.step (PEM40 n hn) u v)) (hdec : DecisionPair n (C u).1 (C v).1) :
    Decided (C.step (PEM40 n hn) u v) := by
  have hne := hC.1.ne_rank huv
  have hv : (C u).1.rank.val ≠ (C v).1.rank.val := fun h => hne (Fin.ext h)
  refine ⟨ssorted_step hC huv hC', fun w hw => ?_⟩
  rw [majorityAnswer_step40]
  rw [ssorted_step_rank hC huv w] at hw
  have ha := srank_step_answers hC.1 huv hC'
  rw [ssorted_noswap hC u v] at ha
  have hd := phase4_decide_sorted (C u).1 (C v).1 (C u).2 (C v).2 (nAOf C) (nAOf_le C)
    (hC.2 u) (hC.2 v) hne
  rw [majorityAnswer_eq_majOf]
  have hrk : ∀ a b : Fin n, (C a).1.rank.val = (C b).1.rank.val → a = b :=
    fun a b h => hC.1.2 (Fin.ext h)
  unfold IsMedType ceilHalf at hw
  rcases hdec with ⟨hodd, hm⟩ | ⟨hev, mu, mv⟩
  · -- n odd: `w` has the median rank
    have hw' : (C w).1.rank.val + 1 = ceilHalf n := by unfold ceilHalf; omega
    rcases hm with hm | hm
    · have : w = u := hrk w u (by omega)
      subst this
      rw [ha.1]; exact hd.2.2.1 hodd hm
    · have : w = v := hrk w v (by omega)
      subst this
      rw [ha.2]; exact hd.2.2.2.1 hodd hm
  · unfold IsMedType ceilHalf at mu mv
    have e := hd.2.2.2.2 hev (by unfold IsMedType ceilHalf; omega)
      (by unfold IsMedType ceilHalf; omega)
    have : w = u ∨ w = v := by
      by_cases h : (C w).1.rank.val = (C u).1.rank.val
      · exact Or.inl (hrk w u h)
      · exact Or.inr (hrk w v (by omega))
    rcases this with h | h
    · subst h; rw [ha.1]; exact e.1
    · subst h; rw [ha.2]; exact e.2

/-- **`AnsOK` is kept by non-reset steps** (P3 Lemma 14): decide writes only to median-type
ranks, and swaps move whole states. -/
theorem ansOK_step (hC : SRank C) (hA : AnsOK C) (huv : u ≠ v)
    (hC' : SRank (C.step (PEM40 n hn) u v)) : AnsOK (C.step (PEM40 n hn) u v) := by
  have ha := srank_step_answers hC huv hC'
  have hr := pair4_rank (s₀ := (C u).1) (s₁ := (C v).1) (x₀ := (C u).2) (x₁ := (C v).2)
  intro w _ hw
  rw [majorityAnswer_step40]
  have hsw : ∀ s, (s = (C u).1 ∨ s = (C v).1) → ¬ IsMedType n s.rank.val →
      s.answer = majorityAnswer C := by
    rintro s (rfl | rfl) h
    · exact hA u (hC.1 u) h
    · exact hA v (hC.1 v) h
  have hmem : (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).1 = (C u).1 ∨
        (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).1 = (C v).1 := by
    rcases phase4_swap_cases (C u).1 (C v).1 (C u).2 (C v).2 with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmem2 : (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).2 = (C u).1 ∨
        (phase4_swap (C u).1 (C v).1 (C u).2 (C v).2).2 = (C v).1 := by
    rcases phase4_swap_cases (C u).1 (C v).1 (C u).2 (C v).2 with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases h1 : w = u
  · subst h1
    have hw' := hw
    rw [srank_step_u hC huv] at hw'
    dsimp only at hw'
    rw [hr.1] at hw'
    rw [ha.1, (phase4_decide_answer_of_not_medType _ _ _ _).1 hw']
    exact hsw _ hmem hw'
  · by_cases h2 : w = v
    · subst h2
      have hw' := hw
      rw [srank_step_v hC huv] at hw'
      dsimp only at hw'
      rw [hr.2] at hw'
      rw [ha.2, (phase4_decide_answer_of_not_medType _ _ _ _).2 hw']
      exact hsw _ hmem2 hw'
    · rw [step_other' _ C u v w h1 h2] at hw ⊢
      exact hA w (hC.1 w) hw

/-! ### Resets from `D` -/

/-- On `D`, after decide the median state of the pair carries the majority answer. -/
theorem decided_decide_median (hC : Decided C) (huv : u ≠ v) :
    ((C u).1.rank.val + 1 = ceilHalf n →
        (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).1.answer = majorityAnswer C) ∧
      ((C v).1.rank.val + 1 = ceilHalf n →
        (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).2.answer = majorityAnswer C) := by
  have hS := hC.1
  have hd := phase4_decide_sorted (C u).1 (C v).1 (C u).2 (C v).2 (nAOf C) (nAOf_le C)
    (hS.2 u) (hS.2 v) (hS.1.ne_rank huv)
  rw [majorityAnswer_eq_majOf]
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rcases hd.1 with e | e
    · exact e
    · rw [e, ← majorityAnswer_eq_majOf]; exact hC.2 u (Or.inl hm)
  · rcases hd.2.1 with e | e
    · exact e
    · rw [e, ← majorityAnswer_eq_majOf]; exact hC.2 v (Or.inl hm)

/-- **A reset from `D` lands in `Z`** (P3 Lemma 2). -/
theorem decided_step_zTwo (hC : Decided C) (huv : u ≠ v)
    (hC' : ¬ SRank (C.step (PEM40 n hn) u v)) : ZTwo (C.step (PEM40 n hn) u v) := by
  have hS := hC.1
  have hne := hS.1.ne_rank huv
  have hv' : (C u).1.rank.val ≠ (C v).1.rank.val := fun h => hne (Fin.ext h)
  have hrk : ∀ a b : Fin n, (C a).1.rank.val = (C b).1.rank.val → a = b :=
    fun a b h => hS.1.2 (Fin.ext h)
  have hdr := phase4_decide_rank (C u).1 (C v).1 (C u).2 (C v).2
  have hdro := phase4_decide_role_eq (C u).1 (C v).1 (C u).2 (C v).2
  have hdm := decided_decide_median hC huv
  have hP := pair4_of_noswap (ssorted_noswap hS u v)
  have hR := phase4_propagate_role (rmaxPaper n) _ _ (hdro.1.trans (hS.1.1 u))
    (hdro.2.trans (hS.1.1 v))
  rw [← hP] at hR
  rcases hR with ⟨r1, r2, -, -⟩ | ⟨r1, r2, c1, c2, l1, l2, hm⟩
  · exfalso
    apply hC'
    rcases srank_step_cases (hn := hn) hS.1 huv with h | ⟨r1', -⟩
    · exact h
    · rw [srank_step_u hS.1 huv] at r1'
      dsimp only at r1'
      rw [r1] at r1'
      cases r1'
  · -- the answers of both are the median's answer after decide, which is `maj`
    have hans : (pair4 (C u).1 (C v).1 (C u).2 (C v).2).1.answer = majorityAnswer C ∧
        (pair4 (C u).1 (C v).1 (C u).2 (C v).2).2.answer = majorityAnswer C ∧
        ((C u).1.rank.val + 1 = ceilHalf n ∨ (C v).1.rank.val + 1 = ceilHalf n) := by
      rcases hm with ⟨m, -, -, a1, a2⟩ | ⟨m, -, -, a1, a2⟩
      · rw [hdr.1] at m
        rw [a1, a2, hdm.1 m]
        exact ⟨rfl, rfl, Or.inl m⟩
      · rw [hdr.2] at m
        rw [a1, a2, hdm.2 m]
        exact ⟨rfl, rfl, Or.inr m⟩
    refine ⟨u, v, huv, ?_, ?_, ?_⟩
    · rintro w (rfl | rfl)
      · rw [srank_step_u hS.1 huv, majorityAnswer_step40]
        exact ⟨r1, c1, l1, hans.1⟩
      · rw [srank_step_v hS.1 huv, majorityAnswer_step40]
        exact ⟨r2, c2, l2, hans.2.1⟩
    · intro w hwu hwv
      rw [step_other' _ C u v w hwu hwv]
      refine ⟨hS.1.1 w, fun h => ?_⟩
      rcases hans.2.2 with m | m
      · exact hwu (hrk w u (by omega))
      · exact hwv (hrk w v (by omega))
    · intro w w' hwu hwv hwu' hwv' h
      rw [step_other' _ C u v w hwu hwv, step_other' _ C u v w' hwu' hwv'] at h
      exact hS.1.2 h

/-- **The median with timer `0` meeting a wrong answer resets** (P3 Lemma 17). -/
theorem decided_step_reset (hC : Decided C) (huv : u ≠ v) (h0 : medT C = 0)
    (hpair : ((C u).1.rank.val + 1 = ceilHalf n ∧ (C v).1.answer ≠ majorityAnswer C) ∨
      ((C v).1.rank.val + 1 = ceilHalf n ∧ (C u).1.answer ≠ majorityAnswer C)) :
    ¬ SRank (C.step (PEM40 n hn) u v) := by
  have hS := hC.1
  have hne := hS.1.ne_rank huv
  have hdr := phase4_decide_rank (C u).1 (C v).1 (C u).2 (C v).2
  have hdt := phase4_decide_timer (C u).1 (C v).1 (C u).2 (C v).2
  have hdm := decided_decide_median hC huv
  have hna := phase4_decide_answer_of_not_medType (C u).1 (C v).1 (C u).2 (C v).2
  have hP := pair4_of_noswap (ssorted_noswap hS u v)
  have hdne : (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).1.rank ≠
      (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).2.rank := by
    rw [hdr.1, hdr.2]; exact hne
  have ht0 : ∀ a b : AgentState n, a.timer = 0 → (medianTick n a b).timer = 0 := by
    intro a b h; rw [medianTick_timer]; split_ifs <;> omega
  intro hC'
  have hu := hC'.1 u
  rw [srank_step_u hS.1 huv, hP] at hu
  dsimp only at hu
  rcases hpair with ⟨m, hw⟩ | ⟨m, hw⟩
  · have hwm : ¬ IsMedType n (C v).1.rank.val := fun h => hw (hC.2 v h)
    have hr := phase4_propagate_reset_of_med0 (rmaxPaper n)
      (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).1
      (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).2 (by rw [hdr.1]; exact m)
      (ht0 _ _ (by rw [hdt.1, ← medT_eq hS.1 m]; exact h0))
      (by rw [hdm.1 m, hna.2 hwm]; exact Ne.symm hw)
    rw [hr] at hu
    cases hu
  · have hwm : ¬ IsMedType n (C u).1.rank.val := fun h => hw (hC.2 u h)
    have hr := phase4_propagate_reset_of_med1 (rmaxPaper n)
      (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).1
      (phase4_decide n (C u).1 (C v).1 (C u).2 (C v).2).2 hdne (by rw [hdr.2]; exact m)
      (ht0 _ _ (by rw [hdt.2, ← medT_eq hS.1 m]; exact h0))
      (by rw [hdm.2 m, hna.1 hwm]; exact Ne.symm hw)
    rw [hr] at hu
    cases hu

end Config

end Ripple.PopulationProtocol.SSEM

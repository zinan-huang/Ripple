/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Swap-Phase Reachability from a Specific Timer Bound

This file proves structural lemmas toward eliminating the universal
`h_inv_swap` hypothesis from the master theorem.

## Key insight

The timer at the median agent only decrements when the median interacts
with the max-rank agent in the propagation phase. After a median-max
swap step:

1. The max-rank position gets input B (from the original median position)
2. A position with input B and max rank is NEVER part of a misordered pair
3. Therefore, max position is never moved by subsequent swaps
4. Therefore, no future median-max interaction occurs
5. Therefore, the timer never decrements again

So the timer budget ≥ 2 allows for exactly ONE median-max interaction,
after which the timer stays ≥ 1 permanently.

## Proved lemmas

* `not_misordered_fst_at_max_rank` — max rank too high for fst of misorder
* `not_misordered_snd_at_max_with_B` — input B excludes snd of misorder
* `no_misorder_at_max_with_B` — no median-max misorder when max has B
* `swap_step_exists_8way_with_max_B` — swap step with timer ≥ 1 when max has B
* `step_at_misorder_preserves_max_B` — max position preserved through swaps

## Remaining for timer elimination

To compose these into `swap_reaches_Sswap_from_timer_bound`, one needs
a `transitionPEM_timer_no_max` lemma proving that when neither
interacting agent has max rank, the median's timer field is unchanged
through all phases of transitionPEM (~150 lines of split_ifs + rfl).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.MedianWitnesses

namespace SSEM

variable {n : ℕ}

/-! ### Max-rank position is never misordered when it has input B -/

/-- An agent at the max rank (rank n-1) is never the first
component of a misordered pair (rank too high). -/
theorem not_misordered_fst_at_max_rank
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hu_max : (C u).1.rank.val + 1 = n) :
    ¬ MisorderedPair C (u, v) := by
  intro ⟨_, _, hlt⟩
  have hv_bound := (C v).1.rank.isLt
  have hu_val : (C u).1.rank.val = n - 1 := by omega
  exact absurd (lt_of_lt_of_le hlt (by omega : (C v).1.rank ≤ (C u).1.rank))
    (lt_irrefl _)

/-- An agent with input B is never the second component of a misordered
pair (needs input A). -/
theorem not_misordered_snd_at_max_with_B
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hv_B : (C v).2 = Opinion.B) :
    ¬ MisorderedPair C (u, v) := by
  intro ⟨_, hA, _⟩
  rw [hv_B] at hA
  exact Opinion.noConfusion hA

/-- If the max-rank agent has input B, no median-max misorder exists. -/
theorem no_misorder_at_max_with_B
    {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : 0 < n)
    (h_max_B : ∃ q : Fin n, (C q).1.rank.val + 1 = n ∧ (C q).2 = Opinion.B) :
    ∀ u v : Fin n, MisorderedPair C (u, v) →
      (C u).1.rank.val + 1 ≠ ceilHalf n ∨ (C v).1.rank.val + 1 ≠ n := by
  intro u v hMis
  obtain ⟨q, hq_max, hq_B⟩ := h_max_B
  by_contra h
  push_neg at h
  obtain ⟨hu_med, hv_max⟩ := h
  exact not_misordered_snd_at_max_with_B
    (show (C v).2 = Opinion.B from by
      have : v = q := by
        have hrank_eq : (C v).1.rank = (C q).1.rank := by
          apply Fin.ext; omega
        exact hC.ranks_inj hrank_eq
      rw [this]; exact hq_B)
    hMis

/-! ### Swap-step existence with timer ≥ 1 when max has input B -/

/-- When the max-rank agent has input B, cases 3 and 8 of the 8-way
swap lemma cannot apply (they need v at max rank with input A). So
timer ≥ 1 suffices (instead of ≥ 2). -/
theorem swap_step_exists_8way_with_max_B
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    (hpos : 0 < misorderedCount C)
    (h_max_B : ∃ q : Fin n, (C q).1.rank.val + 1 = n ∧ (C q).2 = Opinion.B)
    (h_med_timer_ge_1 :
      ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer) :
    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
       (¬ n % 2 = 0 ∧ (C v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (C v).1.timer) ∨
       (n % 2 = 0 ∧ (C v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (C v).1.timer ∧ 4 ≤ n) ∨
       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (C v).1.rank.val + 1 ≠ n ∧
        1 ≤ (C u).1.timer ∧ 4 ≤ n) ∨
       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n)) := by
  obtain ⟨q, hq_max, hq_B⟩ := h_max_B
  obtain ⟨u, v, hMis⟩ := exists_misordered_of_pos_count hpos
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hv_not_max : (C v).1.rank.val + 1 ≠ n := by
    intro hv_max
    have hrank_eq : (C v).1.rank = (C q).1.rank := by
      apply Fin.ext; omega
    have : v = q := hC.ranks_inj hrank_eq
    rw [this] at hvA; rw [hq_B] at hvA; exact Opinion.noConfusion hvA
  refine ⟨u, v, ⟨huB, hvA, hlt⟩, ?_⟩
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_timer : 1 ≤ (C u).1.timer := h_med_timer_ge_1 u hu_med
      have hu_med' : (C u).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hu_med
      by_cases hv_upper : (C v).1.rank.val + 1 = n / 2 + 1
      · right; right; right; left
        exact ⟨hpar, hu_med', hv_upper, hn4⟩
      · right; right; right; right; right; right; left
        exact ⟨hpar, hu_med', hv_upper, hv_not_max, hu_timer, hn4⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_timer : 1 ≤ (C v).1.timer := h_med_timer_ge_1 v hv_med
        have hv_med' : (C v).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hv_med
        right; right; right; right; right; left
        exact ⟨hpar, hv_med', hv_timer, hn4⟩
      · left; exact ⟨hu_med, hv_med⟩
  · by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_timer : 1 ≤ (C u).1.timer := h_med_timer_ge_1 u hu_med
      right; left
      exact ⟨hpar, hu_med, hv_not_max, hu_timer⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_timer : 1 ≤ (C v).1.timer := h_med_timer_ge_1 v hv_med
        right; right; right; right; left
        exact ⟨hpar, hv_med, hv_timer⟩
      · left; exact ⟨hu_med, hv_med⟩

/-! ### Max-rank position is fixed through misordered-pair swaps -/

/-- In InSrank with max having input B, the max position is never part
of any misordered pair. Therefore, Config.step at a misordered pair
does not modify the max position's state. -/
theorem step_at_misorder_preserves_max_B
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    {q : Fin n} (hq_max : (C q).1.rank.val + 1 = n) (hq_B : (C q).2 = Opinion.B) :
    (C.step (protocolPEM n trank Rmax rankDelta) u v q).1.rank.val + 1 = n ∧
    (C.step (protocolPEM n trank Rmax rankDelta) u v q).2 = Opinion.B := by
  have huv : u ≠ v := by
    intro h; rw [h] at hMis; exact absurd hMis.2.2 (lt_irrefl _)
  have hqu : q ≠ u := by
    intro h; subst h; exact absurd hMis (not_misordered_fst_at_max_rank hq_max)
  have hqv : q ≠ v := by
    intro h; subst h; exact absurd hMis (not_misordered_snd_at_max_with_B hq_B)
  unfold Config.step
  simp only [if_neg huv, if_neg hqu, if_neg hqv]
  exact ⟨hq_max, hq_B⟩

/-! ### Config.step projection lemmas -/

theorem Config.step_fst_state {Q X Y : Type*} {n : ℕ}
    (P : Protocol Q X Y) (C : Config Q X n) {u v : Fin n} (huv : u ≠ v) :
    (C.step P u v u).1 = (P.δ (C u, C v)).1 := by
  unfold Config.step; simp [huv]

theorem Config.step_snd_state {Q X Y : Type*} {n : ℕ}
    (P : Protocol Q X Y) (C : Config Q X n) {u v : Fin n} (huv : u ≠ v) (hvu : v ≠ u) :
    (C.step P u v v).1 = (P.δ (C u, C v)).2 := by
  unfold Config.step; simp [huv, hvu]

/-! ### General timer preservation through transitionPEM -/

set_option maxHeartbeats 4000000 in
/-- Timer preservation for NON-MISORDERED Settled pairs without max rank.
When the swap doesn't fire, the timer is preserved unchanged. -/
theorem transitionPEM_timer_of_no_max_no_swap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (h_no_max_0 : s₀.rank.val + 1 ≠ n) (h_no_max_1 : s₁.rank.val + 1 ≠ n)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hne : s₀.rank ≠ s₁.rank) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.timer = s₀.timer ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.timer = s₁.timer := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) := hRank s₀ s₁ hs₀ hs₁ hne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hs₀, hs₁, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, h_no_swap]
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true, h_no_max_0, h_no_max_1]
    split_ifs <;> exact ⟨rfl, rfl⟩
  · simp only [hpar, if_false, h_no_max_0, h_no_max_1]
    split_ifs <;> exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- Rank preservation for non-misordered Settled pairs (swap doesn't fire). -/
theorem transitionPEM_rank_of_no_swap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hne : s₀.rank ≠ s₁.rank) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.rank = s₀.rank ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.rank = s₁.rank := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) := hRank s₀ s₁ hs₀ hs₁ hne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hs₀, hs₁, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, h_no_swap]
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true]
    split_ifs <;> exact ⟨rfl, rfl⟩
  · simp only [hpar, if_false]
    split_ifs <;> exact ⟨rfl, rfl⟩

/-! ### Timer preservation through transitionPEM when no max rank (misordered) -/

set_option maxHeartbeats 4000000 in
/-- When both agents are Settled, rankDelta is identity, and NEITHER
has max rank (rank n-1), the timer fields in the transitionPEM result
are exactly the swapped input timers (no decrement, no reset). -/
theorem transitionPEM_timer_of_no_max_at_misorder
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_no_max_u : (C u).1.rank.val + 1 ≠ n)
    (h_no_max_v : (C v).1.rank.val + 1 ≠ n) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.timer = (C v).1.timer ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.timer = (C u).1.timer := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap]
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true]
    split_ifs <;> (try exact ⟨rfl, rfl⟩) <;> simp_all [h_no_max_u, h_no_max_v]
  · simp only [hpar, if_false]
    split_ifs <;> (try exact ⟨rfl, rfl⟩) <;> simp_all [h_no_max_u, h_no_max_v]

set_option maxHeartbeats 8000000 in
/-- When v HAS max rank: result.2.timer ≥ (C u).1.timer - 1. The
decrement happens iff u has median rank (propagation timer fires). -/
theorem transitionPEM_timer_of_v_max_at_misorder
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_no_max_u : (C u).1.rank.val + 1 ≠ n)
    (h_max_v : (C v).1.rank.val + 1 = n)
    (hn4 : 4 ≤ n) :
    (C u).1.timer - 1 ≤ (transitionPEM n trank Rmax rankDelta (C u, C v)).2.timer := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have h_max_ne_med : ¬((C v).1.rank.val + 1 = ceilHalf n) := by
    intro h; unfold ceilHalf at h; omega
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, h_max_ne_med]
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true]
    split_ifs <;> dsimp only [] <;> omega
  · simp only [hpar, if_false]
    split_ifs <;> dsimp only [] <;> omega

/-! ### Timer ≥ 1 preservation at median through swap step -/

/-- When neither agent has max rank, timer ≥ K at median is preserved
through a swap step at a misordered pair. Works for any K. -/
theorem step_at_misorder_preserves_timer_geK
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_no_max_u : (C u).1.rank.val + 1 ≠ n)
    (h_no_max_v : (C v).1.rank.val + 1 ≠ n)
    {K : ℕ}
    (h_ge : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → K ≤ (C μ).1.timer) :
    ∀ μ : Fin n,
      (C.step (protocolPEM n trank Rmax rankDelta) u v μ).1.rank.val + 1 = ceilHalf n →
      K ≤ (C.step (protocolPEM n trank Rmax rankDelta) u v μ).1.timer := by
  have huv : u ≠ v := by
    intro h; rw [h] at hMis; exact absurd hMis.2.2 (lt_irrefl _)
  have h_timer := transitionPEM_timer_of_no_max_at_misorder
    (trank := trank) (Rmax := Rmax) hRank hC hMis h_no_max_u h_no_max_v
  have h_rank := transitionPEM_rank_swap_at_misorder (trank := trank) (Rmax := Rmax) hRank hC hMis
  set P := protocolPEM n trank Rmax rankDelta
  intro μ hμ_med
  by_cases hμu : μ = u
  · rw [hμu] at hμ_med ⊢
    have := congrArg (·.timer) (Config.step_fst_state P C huv)
    have := congrArg (·.rank) (Config.step_fst_state P C huv)
    simp only [P, protocolPEM] at *
    rw [‹(C.step _ u v u).1.timer = _›, h_timer.1]
    rw [‹(C.step _ u v u).1.rank = _›, h_rank.1] at hμ_med
    exact h_ge v hμ_med
  · by_cases hμv : μ = v
    · rw [hμv] at hμ_med ⊢
      have := congrArg (·.timer) (Config.step_snd_state P C huv huv.symm)
      have := congrArg (·.rank) (Config.step_snd_state P C huv huv.symm)
      simp only [P, protocolPEM] at *
      rw [‹(C.step _ u v v).1.timer = _›, h_timer.2]
      rw [‹(C.step _ u v v).1.rank = _›, h_rank.2] at hμ_med
      exact h_ge u hμ_med
    · unfold Config.step at hμ_med ⊢
      simp only [if_neg huv, if_neg hμu, if_neg hμv] at hμ_med ⊢
      exact h_ge μ hμ_med

/-- When v has max rank and timer ≥ 2 at median, the step at misordered
pair (u,v) produces: timer ≥ 1 at median + max has input B. -/
theorem step_at_v_max_gives_right_disjunct
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hv_max : (C v).1.rank.val + 1 = n) (hn4 : 4 ≤ n)
    (h_ge2 : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer) :
    (∀ μ : Fin n,
      (C.step (protocolPEM n trank Rmax rankDelta) u v μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (C.step (protocolPEM n trank Rmax rankDelta) u v μ).1.timer) ∧
    (∃ q : Fin n,
      (C.step (protocolPEM n trank Rmax rankDelta) u v q).1.rank.val + 1 = n ∧
      (C.step (protocolPEM n trank Rmax rankDelta) u v q).2 = Opinion.B) := by
  have huv : u ≠ v := by
    intro h; rw [h] at hMis; exact absurd hMis.2.2 (lt_irrefl _)
  have h_no_max_u : (C u).1.rank.val + 1 ≠ n :=
    fun h => absurd hMis (not_misordered_fst_at_max_rank h)
  have h_rank := transitionPEM_rank_swap_at_misorder
    (trank := trank) (Rmax := Rmax) hRank hC hMis
  have h_v_max_timer := transitionPEM_timer_of_v_max_at_misorder
    (trank := trank) (Rmax := Rmax) hRank hC hMis h_no_max_u hv_max hn4
  have h_step_u := Config.step_fst_state (protocolPEM n trank Rmax rankDelta) C huv
  have h_step_v := Config.step_snd_state (protocolPEM n trank Rmax rankDelta) C huv huv.symm
  have h_u_rank_eq : (C.step (protocolPEM n trank Rmax rankDelta) u v u).1.rank.val =
      (C v).1.rank.val := by
    have := congrArg (fun s => s.rank) h_step_u
    simp only [protocolPEM, h_rank.1] at this
    exact congrArg Fin.val this
  have h_v_rank_eq : (C.step (protocolPEM n trank Rmax rankDelta) u v v).1.rank.val =
      (C u).1.rank.val := by
    have := congrArg (fun s => s.rank) h_step_v
    simp only [protocolPEM, h_rank.2] at this
    exact congrArg Fin.val this
  constructor
  · intro μ hμ
    by_cases hμu : μ = u
    · exfalso; rw [hμu] at hμ; rw [h_u_rank_eq, hv_max] at hμ
      unfold ceilHalf at hμ; omega
    · by_cases hμv : μ = v
      · rw [hμv] at hμ ⊢; rw [h_v_rank_eq] at hμ
        have := h_ge2 u hμ
        have h_v_timer : (C.step (protocolPEM n trank Rmax rankDelta) u v v).1.timer =
            ((protocolPEM n trank Rmax rankDelta).δ (C u, C v)).2.timer := by
          exact congrArg (fun s => s.timer) h_step_v
        rw [h_v_timer]; exact le_trans (by omega) h_v_max_timer
      · unfold Config.step at hμ ⊢
        simp only [if_neg huv, if_neg hμu, if_neg hμv] at hμ ⊢
        exact le_trans (by omega : 1 ≤ 2) (h_ge2 μ hμ)
  · refine ⟨u, ?_, ?_⟩
    · show (C.step (protocolPEM n trank Rmax rankDelta) u v u).1.rank.val + 1 = n
      rw [h_u_rank_eq]; exact hv_max
    · show (C.step (protocolPEM n trank Rmax rankDelta) u v u).2 = Opinion.B
      unfold Config.step; simp [huv]; exact hMis.1

/-! ### Full swap-phase reachability from specific timer bound -/

/-- Enriched swap invariant. -/
def SwapInv (C : Config (AgentState n) Opinion n) : Prop :=
  InSrank C ∧
    ((∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer) ∨
     ((∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer) ∧
      (∃ q : Fin n, (C q).1.rank.val + 1 = n ∧ (C q).2 = Opinion.B)))

/-- SwapInv step function: preserves SwapInv and decreases misorderedCount. -/
theorem swap_step_preserves_SwapInv
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hInv : SwapInv C) (hpos : 0 < misorderedCount C) :
    ∃ u v : Fin n,
      SwapInv (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
      misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v) < misorderedCount C := by
  obtain ⟨hC, hDisj⟩ := hInv
  cases hDisj with
  | inl h_ge2 =>
    obtain ⟨u, v, hMis, hcase⟩ := swap_step_exists_8way_with_timer hC hn4 hpos h_ge2
    obtain ⟨hSrank', hCount'⟩ := swap_step_decreases_eight_way hRank hC hMis hcase
    refine ⟨u, v, ⟨hSrank', ?_⟩, hCount'⟩
    by_cases hv_max : (C v).1.rank.val + 1 = n
    · exact Or.inr (step_at_v_max_gives_right_disjunct hRank hC hMis hv_max hn4 h_ge2)
    · -- v not at max: neither has max → timer preserved ≥ 2 → left disjunct
      have h_no_max_u : (C u).1.rank.val + 1 ≠ n :=
        fun h => absurd hMis (not_misordered_fst_at_max_rank h)
      exact Or.inl (step_at_misorder_preserves_timer_geK hRank hC hMis h_no_max_u hv_max h_ge2)
  | inr h_right =>
    obtain ⟨h_ge1, h_maxB⟩ := h_right
    obtain ⟨u, v, hMis, hcase⟩ := swap_step_exists_8way_with_max_B hC hn4 hpos h_maxB h_ge1
    obtain ⟨hSrank', hCount'⟩ := swap_step_decreases_eight_way hRank hC hMis hcase
    obtain ⟨q, hq_max, hq_B⟩ := h_maxB
    have h_no_max_u : (C u).1.rank.val + 1 ≠ n := by
      intro h; have := hC.ranks_inj (Fin.ext (by omega : (C u).1.rank.val = (C q).1.rank.val))
      subst this; exact absurd hMis (not_misordered_fst_at_max_rank hq_max)
    have h_no_max_v : (C v).1.rank.val + 1 ≠ n := by
      intro h; have := hC.ranks_inj (Fin.ext (by omega : (C v).1.rank.val = (C q).1.rank.val))
      subst this; exact absurd hMis (not_misordered_snd_at_max_with_B hq_B)
    exact ⟨u, v, ⟨hSrank', Or.inr
      ⟨step_at_misorder_preserves_timer_geK (trank := trank) (Rmax := Rmax)
        hRank hC hMis h_no_max_u h_no_max_v h_ge1,
       ⟨q, step_at_misorder_preserves_max_B hC hMis hq_max hq_B⟩⟩⟩, hCount'⟩

/-- **Swap-phase reachability from a specific timer bound.**

Given `InSrank C₀` with timer ≥ 2 at the median (not universally, just
at this specific config), there exists a schedule reaching `InSswap`.

This eliminates the universal `h_inv_swap` hypothesis from the master
theorem. -/
theorem swap_reaches_Sswap_from_timer_bound
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta) (hn4 : 4 ≤ n)
    {C₀ : Config (AgentState n) Opinion n}
    (hC₀ : InSrank C₀)
    (h_timer : ∀ μ : Fin n, (C₀ μ).1.rank.val + 1 = ceilHalf n →
                2 ≤ (C₀ μ).1.timer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSswap (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) := by
  have h_reach := reach_zero_potential
    (protocolPEM n trank Rmax rankDelta)
    SwapInv
    misorderedCount
    (fun C hInv hpos => swap_step_preserves_SwapInv hRank hn4 C hInv hpos)
    C₀
    ⟨hC₀, Or.inl h_timer⟩
  obtain ⟨γ, t, ⟨hSrank, hTimerDisj⟩, hZero⟩ := h_reach
  exact ⟨γ, t, InSswap_of_InSrank_of_count_zero hSrank hZero⟩

/-- Stronger version: also returns timer ≥ 1 at median in the result. -/
theorem swap_reaches_Sswap_from_timer_bound_with_timer
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta) (hn4 : 4 ≤ n)
    {C₀ : Config (AgentState n) Opinion n}
    (hC₀ : InSrank C₀)
    (h_timer : ∀ μ : Fin n, (C₀ μ).1.rank.val + 1 = ceilHalf n →
                2 ≤ (C₀ μ).1.timer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSswap (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      ∀ μ : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        1 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer := by
  have h_reach := reach_zero_potential
    (protocolPEM n trank Rmax rankDelta)
    SwapInv
    misorderedCount
    (fun C hInv hpos => swap_step_preserves_SwapInv hRank hn4 C hInv hpos)
    C₀
    ⟨hC₀, Or.inl h_timer⟩
  obtain ⟨γ, t, ⟨hSrank, hTimerDisj⟩, hZero⟩ := h_reach
  refine ⟨γ, t, InSswap_of_InSrank_of_count_zero hSrank hZero, ?_⟩
  intro μ hμ
  cases hTimerDisj with
  | inl h_ge2 => exact le_trans (by omega : 1 ≤ 2) (h_ge2 μ hμ)
  | inr h_ge1_maxB => exact h_ge1_maxB.1 μ hμ

#print axioms swap_reaches_Sswap_from_timer_bound_with_timer

end SSEM

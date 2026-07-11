/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Swap-step at v-at-Median Misorder Pairs

Companion to the four `swap_step_decreases_at_misorder_u_*` lemmas in
`RankPreservation.lean`.  Those handle the case where the FIRST agent
of the misorder pair (`u`) is at the median rank.  Here we cover the
mirror case where the SECOND agent (`v`) is at the median rank.

Concretely, for a misorder pair `(u, v)` with `(C u).1.rank.val < (C v).1.rank.val`,
`(C u).2 = .B`, `(C v).2 = .A`:
  - If `v` is at the median rank, then after swap fires the post-swap
    `b₀ = (C v).1` (now positionally first but still at rank median)
    triggers the propagation phase's median branch.

Single-step lemma proved here (odd n, v at median, u not at min, timer ≥ 1):
`swap_step_decreases_at_misorder_v_median_odd`.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.RankPreservation

namespace SSEM

variable {n : ℕ}

set_option maxHeartbeats 8000000 in
/-- Specific case: odd `n`, `v` at median rank, `u` not at min rank
(`(C u).1.rank.val ≠ 0` is automatic from `u.rank < v.rank` only if
`v.rank > 0`; we need a separate condition that the inner timer-dec on
the post-swap b₁ does NOT fire), and `(C v).1.timer ≥ 1`.

After swap: b₀ = (C v).1 at median, b₁ = (C u).1 at u's rank.
Propagation: b₀ at median fires.  Inner timer-dec on b₀ checks
`b₁.rank.val + 1 = n` — would fire if u is at max, impossible here
(u.rank < v.rank ≤ n - 1, so u.rank ≤ n - 2 < n - 1 only if v.rank < n).
We require `(C v).1.rank.val + 1 ≠ n` (v not at max) so that even the
worst-case bound on u.rank is < n - 1.  Actually for v at median and
v.rank < n, we have u.rank < median ≤ n - 1, so u.rank.val + 1 ≤
median ≤ n - 1 < n, so inner timer-dec does NOT fire.

Reset is blocked by timer ≥ 1.

Result: `((C v).1 with answer := opinionToAnswer (C u).2, (C u).1)`. -/
theorem transitionPEM_at_misordered_v_median_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hv_med : (C v).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C v).1.timer) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ({(C v).1 with answer := opinionToAnswer (C u).2}, (C u).1) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  -- Post-swap: (b₀, b₁) = ((C v).1, (C u).1).
  -- b₀.rank.val = (C v).1.rank.val = ceilHalf n - 1, so b₀ at median.
  -- b₁.rank.val = (C u).1.rank.val.
  -- Inner timer-dec checks b₁.rank.val + 1 = n.
  -- u.rank < v.rank = ceilHalf n - 1 ≤ n - 2 (for n ≥ 2).
  -- So u.rank.val ≤ ceilHalf n - 2.  u.rank.val + 1 ≤ ceilHalf n - 1.
  -- For n ≥ 2: ceilHalf n - 1 ≤ n - 1 < n, so u.rank.val + 1 < n.
  have h_u_rank_lt : (C u).1.rank.val < (C v).1.rank.val := hlt
  have h_v_rank_lt_n : (C v).1.rank.val < n := (C v).1.rank.isLt
  have h_no_inner_B : ¬ ((C u).1.rank.val + 1 = n) := by omega
  -- u not at median: u.rank.val + 1 ≤ ceilHalf n - 1 < ceilHalf n.
  have h_u_not_med : ¬ ((C u).1.rank.val + 1 = ceilHalf n) := by omega
  -- b₀ at median = ceilHalf n - 1 (rank.val + 1 = ceilHalf n).
  -- For propagation first branch (b₀ at median), this fires.
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hv_med, h_no_inner_B, h_u_not_med]
  -- Reset is blocked: b₀.timer = (C v).1.timer ≥ 1, so timer ≠ 0.
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-- Role-Settled corollary at the v-at-median misorder pair. -/
theorem transitionPEM_role_settled_at_misorder_v_median_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hv_med : (C v).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C v).1.timer) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_v_median_odd hRank hC hMis hpar hv_med h_timer]
  refine ⟨?_, hC.allSettled u⟩
  exact hC.allSettled v

/-- Full single-step swap-step decrease for the v-at-median odd-n case. -/
theorem swap_step_decreases_at_misorder_v_median_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hv_med : (C v).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C v).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_v_median_odd
      hRank hC hMis hpar hv_med h_timer)

/-! ### Even-n v-at-lower-median misorder pair -/

set_option maxHeartbeats 8000000 in
/-- Even `n ≥ 4`, v at lower median (rank n/2 - 1, rank.val + 1 = n/2),
u below v. Misorder pair `(u, v)` triggers swap; post-swap b₀ = (C v).1
sits at the propagation median.  Decision branches don't fire (because
b₁ is below n/2 - 1, so neither median-pair condition matches).  Reset
blocked by timer ≥ 1.  Result: pure state swap `((C v).1, (C u).1)`. -/
theorem transitionPEM_at_misordered_v_lower_median_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hv_med : (C v).1.rank.val + 1 = n / 2)
    (h_timer : 1 ≤ (C v).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    transitionPEM n trank Rmax rankDelta (C u, C v) = ((C v).1, (C u).1) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have h_u_rank_lt : (C u).1.rank.val < (C v).1.rank.val := hlt
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  -- u.rank.val ≤ v.rank.val - 1 = n/2 - 2.
  -- u.rank.val + 1 ≤ n/2 - 1.
  have hv_med_ceil : (C v).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hv_med
  -- Decision branch 1 fails: need b₀ at n/2 ∧ b₁ at n/2+1; b₀ is at n/2 ✓
  -- but b₁ at u.rank ≤ n/2 - 2, so b₁.rank.val + 1 ≤ n/2 - 1 ≠ n/2 + 1.
  have hd1_fail : ¬ ((C v).1.rank.val + 1 = n / 2 ∧
                     (C u).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨_, h⟩; omega
  -- Decision branch 2 fails: need b₁ at n/2 ∧ b₀ at n/2+1.  b₀ at n/2 ≠ n/2+1.
  have hd2_fail : ¬ ((C u).1.rank.val + 1 = n / 2 ∧
                     (C v).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨_, h⟩; omega
  -- After hv_med rewrites (C v).1.rank.val + 1 → n/2, branches become:
  --   Branch 1: n/2 = n/2 ∧ (C u).1.rank.val + 1 = n/2 + 1 → just need to block second conjunct.
  --   Branch 2: (C u).1.rank.val + 1 = n/2 ∧ n/2 = n/2 + 1 → trivially false (n/2 ≠ n/2+1).
  have h_u_ne_med_plus : ¬ ((C u).1.rank.val + 1 = n / 2 + 1) := by omega
  have h_u_ne_med : ¬ ((C u).1.rank.val + 1 = n / 2) := by omega
  have hN1 : ¬ (n / 2 = n / 2 + 1) := by omega
  -- Inner timer-dec: b₁.rank.val + 1 = n? b₁ at u.rank ≤ n/2 - 2, so + 1 ≤ n/2 - 1 < n.
  have h_no_inner_B : ¬ ((C u).1.rank.val + 1 = n) := by omega
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hd1_fail, hd2_fail, h_no_inner_B,
    hv_med_ceil, hceil, h_u_ne_med_plus, h_u_ne_med, hN1, hv_med]
  -- Reset blocked by timer ≥ 1.
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-- Role-Settled at the even-n v-at-lower-median case. -/
theorem transitionPEM_role_settled_at_misorder_v_lower_median_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hv_med : (C v).1.rank.val + 1 = n / 2)
    (h_timer : 1 ≤ (C v).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_v_lower_median_even
        hRank hC hMis hpar hv_med h_timer hn_ge_4]
  exact ⟨hC.allSettled v, hC.allSettled u⟩

/-- Full single-step decrease for even-n v-at-lower-median. -/
theorem swap_step_decreases_at_misorder_v_lower_median_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hv_med : (C v).1.rank.val + 1 = n / 2)
    (h_timer : 1 ≤ (C v).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_v_lower_median_even
      hRank hC hMis hpar hv_med h_timer hn_ge_4)

/-! ### 6-way unified swap-step decrease (covers both u-at-median and v-at-median cases) -/

/-- Six-way unified single-step decrease.  Covers the four original
disjuncts of `swap_step_decreases_four_way` plus two new ones for
v-at-median:
  (i) non-median misorder
  (ii) odd-n, u at median, v not max, timer ≥ 1
  (iii) odd-n, u at median, v at max, timer ≥ 2
  (iv) even-n, u at lower median, v at upper median, n ≥ 4
  (v) odd-n, v at median, timer ≥ 1
  (vi) even-n, v at lower median, n ≥ 4, timer ≥ 1 -/
theorem swap_step_decreases_six_way
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_case :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧ (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (C v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (C v).1.timer) ∨
      (n % 2 = 0 ∧ (C v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (C v).1.timer ∧ 4 ≤ n)) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  rcases h_case with
    ⟨hu_no_med, hv_no_med⟩
    | ⟨hpar, hu_med, hv_no_max, h_timer⟩
    | ⟨hpar, hu_med, hv_max, h_timer⟩
    | ⟨hpar, hu_lower, hv_upper, hn_ge_4⟩
    | ⟨hpar, hv_med, h_timer⟩
    | ⟨hpar, hv_lower, h_timer, hn_ge_4⟩
  · exact swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med
  · exact swap_step_decreases_at_misorder_u_median_odd_v_not_max
      hRank hC hMis hpar hu_med hv_no_max h_timer
  · exact swap_step_decreases_at_misorder_u_median_odd_v_max
      hRank hC hMis hpar hu_med hv_max h_timer
  · exact swap_step_decreases_at_misorder_u_lower_median_even
      hRank hC hMis hpar hu_lower hv_upper hn_ge_4
  · exact swap_step_decreases_at_misorder_v_median_odd
      hRank hC hMis hpar hv_med h_timer
  · exact swap_step_decreases_at_misorder_v_lower_median_even
      hRank hC hMis hpar hv_lower h_timer hn_ge_4

/-! ### Even-n u-at-lower-median misorder pair (v above upper median, v not max) -/

set_option maxHeartbeats 8000000 in
/-- Even `n ≥ 4`, u at lower median (rank.val + 1 = n/2), v at rank
strictly between upper median and max — i.e., v.rank.val + 1 ∉ {n/2 + 1, n}.
Decision branches don't fire; propagation second branch (b₁ at lower median
post-swap) fires but inner timer-dec doesn't (v not at max); reset blocked
by u.timer ≥ 1.  Result: pure state swap `((C v).1, (C u).1)`. -/
theorem transitionPEM_at_misordered_u_lower_median_even_v_above
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_timer : 1 ≤ (C u).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    transitionPEM n trank Rmax rankDelta (C u, C v) = ((C v).1, (C u).1) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hu_med_ceil : (C u).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hu_med
  -- v.rank.val ≥ n/2 from misorder (v.rank > u.rank = n/2 - 1).  And v ≠ upper, ≠ max.
  have h_v_rank_lt_n : (C v).1.rank.val < n := (C v).1.rank.isLt
  have h_v_rank_gt_u : (C u).1.rank.val < (C v).1.rank.val := hlt
  -- Decision branch 1: needs b₀ (= v) at n/2 ∧ b₁ (= u) at n/2+1.  b₁ at n/2 ≠ n/2+1.
  have hd1_fail : ¬ ((C v).1.rank.val + 1 = n / 2 ∧
                     (C u).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨_, h⟩; omega
  -- Decision branch 2: needs b₁ at n/2 ∧ b₀ at n/2+1.  b₁ at n/2 ✓; b₀ at n/2+1 = upper median, excluded.
  have hd2_fail : ¬ ((C u).1.rank.val + 1 = n / 2 ∧
                     (C v).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨_, h⟩; exact hv_no_upper h
  -- v.rank.val + 1 ≠ ceilHalf n (= n/2): v.rank.val ≥ n/2 from misorder.
  have hv_no_med_ceil : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by
    rw [hceil]; omega
  -- After simp substitutes (C u).1.rank.val + 1 → n / 2 (via hu_med), branches need:
  have hN1 : ¬ (n / 2 = n / 2 + 1) := by omega
  have hv_ne_n_div2 : ¬ ((C v).1.rank.val + 1 = n / 2) := by omega
  -- Inner timer-dec on b₁ in second propagation branch checks b₀.rank.val + 1 = n
  -- (= v at max), excluded by hv_no_max.
  have h_no_inner_B : ¬ ((C v).1.rank.val + 1 = n) := hv_no_max
  -- u.rank ≠ max:
  have h_u_no_max : ¬ ((C u).1.rank.val + 1 = n) := by omega
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hd1_fail, hd2_fail,
    hu_med_ceil, hv_no_med_ceil, h_no_inner_B, h_u_no_max, hceil,
    hu_med, hv_no_upper, hN1, hv_ne_n_div2]
  -- Reset blocked by timer ≥ 1.
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-- Role-Settled corollary. -/
theorem transitionPEM_role_settled_at_misorder_u_lower_median_even_v_above
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_timer : 1 ≤ (C u).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_u_lower_median_even_v_above
        hRank hC hMis hpar hu_med hv_no_upper hv_no_max h_timer hn_ge_4]
  exact ⟨hC.allSettled v, hC.allSettled u⟩

/-- Full single-step decrease. -/
theorem swap_step_decreases_at_misorder_u_lower_median_even_v_above
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_timer : 1 ≤ (C u).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_u_lower_median_even_v_above
      hRank hC hMis hpar hu_med hv_no_upper hv_no_max h_timer hn_ge_4)

/-! ### Even-n u-at-lower-median misorder pair, v at max -/

set_option maxHeartbeats 8000000 in
/-- Even `n ≥ 4`, u at lower median (rank.val + 1 = n/2), v at max
(rank.val + 1 = n), u.timer ≥ 2.  Decision doesn't fire.  Propagation
second branch fires; inner timer-dec triggers (v at max), reducing b₁'s
timer by 1.  Reset blocked because post-dec timer ≥ 1.  Result:
`((C v).1, {(C u).1 with timer := (C u).1.timer - 1})`. -/
theorem transitionPEM_at_misordered_u_lower_median_even_v_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C u).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ((C v).1, {(C u).1 with timer := (C u).1.timer - 1}) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hu_med_ceil : (C u).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hu_med
  -- Decision branches both fail.
  have hd1_fail : ¬ ((C v).1.rank.val + 1 = n / 2 ∧
                     (C u).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨h, _⟩; omega
  have hd2_fail : ¬ ((C u).1.rank.val + 1 = n / 2 ∧
                     (C v).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨_, h⟩; omega
  -- v.rank.val + 1 ≠ ceilHalf n.
  have hv_no_med_ceil : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by
    rw [hceil]; omega
  -- After hu_med substitution.
  have hN1 : ¬ (n / 2 = n / 2 + 1) := by omega
  have hv_ne_n_div2 : ¬ ((C v).1.rank.val + 1 = n / 2) := by omega
  have hv_ne_n_div2_plus : ¬ ((C v).1.rank.val + 1 = n / 2 + 1) := by omega
  -- Post-hv_max substitution: n ≠ n/2 (for n ≥ 4), n ≠ n/2 + 1 (for n ≥ 4).
  have hN_ne_div : ¬ (n = n / 2) := by omega
  have hN_ne_div_plus : ¬ (n = n / 2 + 1) := by omega
  -- u.rank ≠ max.
  have h_u_no_max : ¬ ((C u).1.rank.val + 1 = n) := by omega
  -- Block decision input-equality branch as well.
  have hxBA : ¬ (Opinion.B = Opinion.A) := by intro h; cases h
  have hxAB : ¬ (Opinion.A = Opinion.B) := by intro h; cases h
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hd1_fail, hd2_fail,
    hu_med_ceil, hv_no_med_ceil, h_u_no_max, hceil,
    hu_med, hv_max, hN1, hv_ne_n_div2, hv_ne_n_div2_plus,
    huB, hvA, hxBA, hxAB, hN_ne_div, hN_ne_div_plus]
  -- Reset blocked: post-dec timer = (C u).1.timer - 1 ≥ 1 (h_timer ≥ 2).
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-- Role-Settled corollary. -/
theorem transitionPEM_role_settled_at_misorder_u_lower_median_even_v_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C u).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_u_lower_median_even_v_max
        hRank hC hMis hpar hu_med hv_max h_timer hn_ge_4]
  exact ⟨hC.allSettled v, hC.allSettled u⟩

/-- Full single-step decrease for the 8th sub-case. -/
theorem swap_step_decreases_at_misorder_u_lower_median_even_v_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C u).1.timer)
    (hn_ge_4 : 4 ≤ n) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_u_lower_median_even_v_max
      hRank hC hMis hpar hu_med hv_max h_timer hn_ge_4)

/-- Swap-phase reachability via the six-way unified single-step. -/
theorem swap_reaches_Sswap_via_six_way
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
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
                    1 ≤ (C v).1.timer ∧ 4 ≤ n))) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply swap_reaches_Sswap_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, hMis, hcase⟩ := hExists C hC hpos
  exact ⟨u, v, swap_step_decreases_six_way hRank hC hMis hcase⟩

/-! ### 8-way unified swap-step decrease (parity-combined, full coverage) -/

/-- Eight-way unified single-step decrease.  Adds two more disjuncts on top
of `swap_step_decreases_six_way`:
  (vii) even-n, u at lower median, v above upper (not max), timer ≥ 1
  (viii) even-n, u at lower median, v at max, timer ≥ 2

Together with the previous six, these cover EVERY misorder pair structure
under appropriate timer hypotheses (modulo n = 2 edge case). -/
theorem swap_step_decreases_eight_way
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_case :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧ (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
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
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n)) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  rcases h_case with
    h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact swap_step_decreases_six_way hRank hC hMis (Or.inl h1)
  · exact swap_step_decreases_six_way hRank hC hMis (Or.inr (Or.inl h2))
  · exact swap_step_decreases_six_way hRank hC hMis (Or.inr (Or.inr (Or.inl h3)))
  · exact swap_step_decreases_six_way hRank hC hMis
      (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · exact swap_step_decreases_six_way hRank hC hMis
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · exact swap_step_decreases_six_way hRank hC hMis
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6)))))
  · obtain ⟨hpar, hu_med, hv_no_upper, hv_no_max, h_timer, hn_ge_4⟩ := h7
    exact swap_step_decreases_at_misorder_u_lower_median_even_v_above
      hRank hC hMis hpar hu_med hv_no_upper hv_no_max h_timer hn_ge_4
  · obtain ⟨hpar, hu_med, hv_max, h_timer, hn_ge_4⟩ := h8
    exact swap_step_decreases_at_misorder_u_lower_median_even_v_max
      hRank hC hMis hpar hu_med hv_max h_timer hn_ge_4

/-- Swap-phase reachability via the 8-way unified single-step. -/
theorem swap_reaches_Sswap_via_eight_way
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
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
                    (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n))) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply swap_reaches_Sswap_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, hMis, hcase⟩ := hExists C hC hpos
  exact ⟨u, v, swap_step_decreases_eight_way hRank hC hMis hcase⟩

end SSEM

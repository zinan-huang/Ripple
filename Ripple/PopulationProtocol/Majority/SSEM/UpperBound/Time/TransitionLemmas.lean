import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.Bridge

namespace SSEM

/-- phase4_propagate preserves Settled when answers agree. -/
private lemma phase4_propagate_fst_settled_of_eq_answer'
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (heq : b₀.answer = b₁.answer) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Settled := by
  simp only [phase4_propagate]; split_ifs <;> simp_all


/-! ## transitionPEM role preservation for InSswap (Settled) agents -/

theorem transitionPEM_prePhase4_eq_of_settled_distinct
    {n : ℕ} {trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank) :
    transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁ = (s₀, s₁) := by
  unfold transitionPEM_prePhase4
  rw [hFix s₀ s₁ hs₀ hs₁ hne]
  simp [hs₀, hs₁]

theorem transitionPEM_role_settled_or_resetting_of_InSswap
    {n Rmax : ℕ} {trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank) :
    ((transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Settled ∨
      (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) ∧
    ((transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Settled ∨
      (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting) := by
  simp only [transitionPEM]
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne]
  exact transitionPEM_phase4_role_settled_or_resetting hs₀ hs₁

/-! ## No mixed outcome: both Settled or both Resetting after phase4 -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000000 in
private theorem phase4_propagate_fst_resetting_of_settled
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (hs₁ : b₁.role = .Settled)
    (h : (phase4_propagate n Rmax b₀ b₁).1.role = .Resetting) :
    (phase4_propagate n Rmax b₀ b₁).2.role = .Resetting := by
  simp only [phase4_propagate] at h ⊢
  by_cases h1 : b₀.rank.val + 1 = ceilHalf n
  · simp only [h1, ite_true] at h ⊢
    by_cases h2 : b₁.rank.val + 1 = n
    · simp only [h2, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h2, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
  · simp only [h1, ite_false] at h ⊢
    by_cases h4 : b₁.rank.val + 1 = ceilHalf n
    · simp only [h4, ite_true] at h ⊢
      by_cases h5 : b₀.rank.val + 1 = n
      · simp only [h5, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
      · simp only [h5, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h4, ite_false] at h ⊢; rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 200000000 in
private theorem phase4_propagate_snd_resetting_of_settled
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (hs₁ : b₁.role = .Settled)
    (h : (phase4_propagate n Rmax b₀ b₁).2.role = .Resetting) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Resetting := by
  simp only [phase4_propagate] at h ⊢
  by_cases h1 : b₀.rank.val + 1 = ceilHalf n
  · simp only [h1, ite_true] at h ⊢
    by_cases h2 : b₁.rank.val + 1 = n
    · simp only [h2, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h2, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
  · simp only [h1, ite_false] at h ⊢
    by_cases h4 : b₁.rank.val + 1 = ceilHalf n
    · simp only [h4, ite_true] at h ⊢
      by_cases h5 : b₀.rank.val + 1 = n
      · simp only [h5, ite_true] at h ⊢; split_ifs at h ⊢ <;> simp_all
      · simp only [h5, ite_false] at h ⊢; split_ifs at h ⊢ <;> simp_all
    · simp only [h4, ite_false] at h ⊢; rw [hs₁] at h; exact absurd h (by decide)

/-! ## Full transitionPEM no-mixed-outcome for InSswap

After prePhase4 identity + transitionPEM_phase4 unfold, the goal is about
  phase4_propagate n Rmax c₀ c₁
where c₀, c₁ are the outputs of phase4_decide ∘ phase4_swap.
We show c₀, c₁ have Settled roles (swap/decide only change answer, not role),
then apply phase4_propagate_fst/snd_resetting_of_settled.  -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
theorem transitionPEM_fst_resetting_implies_snd_of_InSswap
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting := by
  simp only [transitionPEM] at h ⊢
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h ⊢
  -- Now goal: (transitionPEM_phase4 n Rmax (s₀, s₁) x₀ x₁).2.role = .Resetting
  -- Unfold transitionPEM_phase4 + resolve the "both Settled" guard
  unfold transitionPEM_phase4 at h ⊢
  simp only [hs₀, hs₁, and_self, ite_true] at h ⊢
  -- Now the goal involves let-bound phase4_swap → phase4_decide → phase4_propagate.
  -- Use dsimp to inline the lets, then apply the propagate lemma.

  -- The input to phase4_propagate has Settled roles because
  -- phase4_swap preserves .role (just swaps or identity) and
  -- phase4_decide preserves .role (only changes .answer).
  -- Verify via unfold + split_ifs on swap and decide.
  have hsw₀ : (phase4_swap s₀ s₁ x₀ x₁).1.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsw₁ : (phase4_swap s₀ s₁ x₀ x₁).2.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsd₀ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  have hsd₁ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).2.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  exact phase4_propagate_fst_resetting_of_settled hsd₀ hsd₁ h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
theorem transitionPEM_snd_resetting_implies_fst_of_InSswap
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = .Resetting) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting := by
  simp only [transitionPEM] at h ⊢
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h ⊢
  unfold transitionPEM_phase4 at h ⊢
  simp only [hs₀, hs₁, and_self, ite_true] at h ⊢

  have hsw₀ : (phase4_swap s₀ s₁ x₀ x₁).1.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsw₁ : (phase4_swap s₀ s₁ x₀ x₁).2.role = .Settled := by
    unfold phase4_swap; split_ifs <;> assumption
  have hsd₀ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).1.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  have hsd₁ : (phase4_decide n (phase4_swap s₀ s₁ x₀ x₁).1
      (phase4_swap s₀ s₁ x₀ x₁).2 x₀ x₁).2.role = .Settled := by
    simp only [phase4_decide]; split_ifs <;> simp_all
  exact phase4_propagate_snd_resetting_of_settled hsd₀ hsd₁ h


/-! ## Conditions necessary for Resetting output (odd parity) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- Neither median → propagate identity → not Resetting. -/
theorem transitionPEM_fst_resetting_implies_some_median_odd
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.rank.val + 1 = ceilHalf n ∨ s₁.rank.val + 1 = ceilHalf n := by
  by_contra h_neither
  push_neg at h_neither
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  -- Swap doesn't fire
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  -- Odd decide: neither is median, so both branches are identity
  unfold phase4_decide at h; simp only [hpar, ite_false, h_neither.1, h_neither.2] at h
  -- Propagate: neither ceilHalf → identity
  unfold phase4_propagate at h; simp only [h_neither.1, h_neither.2, ite_false] at h
  rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median + s₁ NOT max + odd, Resetting → s₀.timer = 0. -/
theorem transitionPEM_fst_resetting_s0_med_no_max_odd_timer_zero
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_no_max : s₁.rank.val + 1 ≠ n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.timer = 0 := by
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h; simp only [hpar, ite_false, h_s0_med, ite_true, h_s1_no_med] at h
  unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_no_max, ite_false] at h
  -- Guard: timer = 0 ∧ answer ≠ answer. If timer ≠ 0, guard fails → Settled.
  split_ifs at h with hguard
  · exact hguard.1
  · rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median + s₁ max + odd, Resetting → s₀.timer ≤ 1. -/
theorem transitionPEM_fst_resetting_s0_med_max_odd_timer_le_one
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_max : s₁.rank.val + 1 = n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.timer ≤ 1 := by
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h; simp only [hpar, ite_false, h_s0_med, ite_true, h_s1_no_med] at h
  unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_max, ite_true] at h
  -- Timer decremented: check (timer - 1 = 0 ∧ answer ≠ answer)
  split_ifs at h with hguard
  · omega
  · rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median + odd + Resetting → opinionToAnswer x₀ ≠ s₁.answer. -/
theorem transitionPEM_fst_resetting_s0_med_odd_answer_diff
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    opinionToAnswer x₀ ≠ s₁.answer := by
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h; simp only [hpar, ite_false, h_s0_med, ite_true, h_s1_no_med] at h
  -- Now h is about phase4_propagate with known median.
  -- The propagate guard includes answer ≠ answer.
  -- Case split on whether s₁ is max rank (affects timer decrement but not answer check).
  unfold phase4_propagate at h
  simp only [h_s0_med, ite_true] at h
  by_cases h_s1_max : s₁.rank.val + 1 = n
  · simp only [h_s1_max, ite_true] at h
    split_ifs at h with hguard
    · exact hguard.2
    · rw [hs₀] at h; exact absurd h (by decide)
  · simp only [h_s1_max, ite_false] at h
    split_ifs at h with hguard
    · exact hguard.2
    · rw [hs₀] at h; exact absurd h (by decide)

/-! ## Conditions necessary for Resetting output (even parity) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- Neither median → propagate identity → not Resetting (even case). -/
theorem transitionPEM_fst_resetting_implies_some_median_even
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.rank.val + 1 = ceilHalf n ∨ s₁.rank.val + 1 = ceilHalf n := by
  by_contra h_neither
  push_neg at h_neither
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h
  simp only [hpar, ite_true] at h
  have h_s0_no_lower : s₀.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_neither.1
  have h_s1_no_lower : s₁.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_neither.2
  have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) := by
    exact fun ⟨h1, _⟩ => h_s0_no_lower h1
  have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) := by
    exact fun ⟨h1, _⟩ => h_s1_no_lower h1
  simp only [h_not_dec1, ite_false, h_not_dec2] at h
  unfold phase4_propagate at h; simp only [h_neither.1, h_neither.2, ite_false] at h
  rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median (even) + s₁ max + n ≥ 4, Resetting → s₀.timer ≤ 1.
    For n ≥ 4 even, max rank n ≠ n/2+1, so phase4_decide is identity
    for the (median, max) pair. -/
theorem transitionPEM_fst_resetting_s0_med_max_even_timer_le_one
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (hn4 : 4 ≤ n)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_max : s₁.rank.val + 1 = n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.timer ≤ 1 := by
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have h_s1_not_upper : s₁.rank.val + 1 ≠ n / 2 + 1 := by omega
  have h_s1_no_lower : s₁.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_s1_no_med
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h
  simp only [hpar, ite_true] at h
  have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) := by
    exact fun ⟨_, h2⟩ => h_s1_not_upper h2
  have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) := by
    exact fun ⟨h1, _⟩ => h_s1_no_lower h1
  simp only [h_not_dec1, ite_false, h_not_dec2] at h
  unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_max, ite_true] at h
  split_ifs at h with hguard
  · omega
  · rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₀ median (even) + s₁ max + n ≥ 4 + Resetting → s₀.answer ≠ s₁.answer. -/
theorem transitionPEM_fst_resetting_s0_med_max_even_answer_diff
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (hn4 : 4 ≤ n)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_max : s₁.rank.val + 1 = n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.answer ≠ s₁.answer := by
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have h_s1_not_upper : s₁.rank.val + 1 ≠ n / 2 + 1 := by omega
  have h_s1_no_lower : s₁.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_s1_no_med
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h
  simp only [hpar, ite_true] at h
  have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) := by
    exact fun ⟨_, h2⟩ => h_s1_not_upper h2
  have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) := by
    exact fun ⟨h1, _⟩ => h_s1_no_lower h1
  simp only [h_not_dec1, ite_false, h_not_dec2] at h
  unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_max, ite_true] at h
  split_ifs at h with hguard
  · exact hguard.2
  · rw [hs₀] at h; exact absurd h (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000000 in
/-- s₀ median (even) + s₁ NOT max + Resetting → s₀.timer = 0. -/
theorem transitionPEM_fst_resetting_s0_med_no_max_even_timer_zero
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (h_s0_med : s₀.rank.val + 1 = ceilHalf n)
    (h_s1_no_med : s₁.rank.val + 1 ≠ ceilHalf n)
    (h_s1_no_max : s₁.rank.val + 1 ≠ n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₀.timer = 0 := by
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have h_s0_lower : s₀.rank.val + 1 = n / 2 := by rw [← hceil]; exact h_s0_med
  have h_s1_no_lower : s₁.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_s1_no_med
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  unfold phase4_decide at h
  simp only [hpar, ite_true] at h
  by_cases h_s1_upper : s₁.rank.val + 1 = n / 2 + 1
  · -- Decide fires, contradiction: both answers become equal, propagation can't fire
    exfalso
    have h_dec1 : s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1 := ⟨h_s0_lower, h_s1_upper⟩
    simp only [h_dec1, ite_true] at h
    -- After decide: if x₀ = x₁, both get opinionToAnswer x₀; else both get .outT
    -- In either case, both answers are equal, so propagation guard fails.
    -- Unfold propagate and show role stays Settled.
    by_cases hxx : x₀ = x₁
    · simp only [hxx, ite_true] at h
      -- h is about phase4_propagate of records with same answer (opinionToAnswer x₁)
      -- The propagate guard checks answer ≠ answer, which is False since both are opinionToAnswer x₁
      -- So if-else takes else branch, role stays Settled
      -- Use the fact that phase4_propagate preserves Settled when answers equal
      unfold phase4_propagate at h
      -- After simp, the if-condition involving ceilHalf and rank should resolve
      -- and the answer comparison should be decidably equal
      simp only [h_s0_med, ite_true, h_s1_no_max, ite_false, h_s1_no_med, ne_eq,
        and_self, not_true, and_false, ite_false, hs₀] at h
      exact Role.noConfusion h
    · simp only [hxx, ite_false] at h
      -- Both get .outT, same argument
      unfold phase4_propagate at h
      simp only [h_s0_med, ite_true, h_s1_no_max, ite_false, h_s1_no_med, ne_eq,
        and_self, not_true, and_false, ite_false, hs₀] at h
      exact Role.noConfusion h
  · -- Decide doesn't fire: identity
    have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) :=
      fun ⟨_, h2⟩ => h_s1_upper h2
    have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) :=
      fun ⟨h1, _⟩ => h_s1_no_lower h1
    simp only [h_not_dec1, ite_false, h_not_dec2] at h
    unfold phase4_propagate at h; simp only [h_s0_med, ite_true, h_s1_no_max, ite_false] at h
    split_ifs at h with hguard
    · exact hguard.1
    · rw [hs₀] at h; exact Role.noConfusion h

/-! ## Responder-median necessary conditions (odd parity, s₁ at median) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₁ median + s₀ NOT max + odd, Resetting → s₁.timer = 0. -/
theorem transitionPEM_fst_resetting_s1_med_no_max_odd_timer_zero
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_no_med : s₀.rank.val + 1 ≠ ceilHalf n)
    (h_s1_med : s₁.rank.val + 1 = ceilHalf n)
    (h_s0_no_max : s₀.rank.val + 1 ≠ n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₁.timer = 0 := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) := hFix s₀ s₁ hs₀ hs₁ hne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate at h
  -- Resolve the first propagate if (s₀ not median) before simp can mix hypotheses
  simp only [hRD, hs₀, hs₁, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    h_s0_no_med, h_s1_med, h_s0_no_max] at h
  split_ifs at h with hguard
  · exact hguard.1
  · exact absurd h (by simp [hs₀])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₁ median + s₀ max + odd, Resetting → s₁.timer ≤ 1. -/
theorem transitionPEM_fst_resetting_s1_med_max_odd_timer_le_one
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_no_med : s₀.rank.val + 1 ≠ ceilHalf n)
    (h_s1_med : s₁.rank.val + 1 = ceilHalf n)
    (h_s0_max : s₀.rank.val + 1 = n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₁.timer ≤ 1 := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) := hFix s₀ s₁ hs₀ hs₁ hne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate at h
  -- Two-step simp: first resolve the propagate first-branch with h_s0_no_med
  simp only [hRD, hs₀, hs₁, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    h_s0_no_med, h_s1_med] at h
  -- Now resolve the inner if (s₀ at max rank → timer decrement)
  simp only [h_s0_max, ite_true] at h
  split_ifs at h with hguard
  · omega
  · exact absurd h (by simp [hs₀])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- s₁ median + odd + Resetting → opinionToAnswer x₁ ≠ s₀.answer. -/
theorem transitionPEM_fst_resetting_s1_med_odd_answer_diff
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_s0_no_med : s₀.rank.val + 1 ≠ ceilHalf n)
    (h_s1_med : s₁.rank.val + 1 = ceilHalf n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    opinionToAnswer x₁ ≠ s₀.answer := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) := hFix s₀ s₁ hs₀ hs₁ hne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate at h
  simp only [hRD, hs₀, hs₁, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    h_s0_no_med, h_s1_med] at h
  by_cases h_s0_max : s₀.rank.val + 1 = n
  · simp only [h_s0_max, ite_true] at h
    split_ifs at h with hguard
    · exact hguard.2
    · exact absurd h (by simp [hs₀])
  · simp only [h_s0_max, ite_false] at h
    split_ifs at h with hguard
    · exact hguard.2
    · exact absurd h (by simp [hs₀])

/-! ## Responder-median trace lemmas (odd parity) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- Trace lemma: responder j at median, timer=0, initiator i NOT at median,
    no swap, odd parity. Second branch of phase4_propagate. -/
theorem propagation_reset_fires_no_swap_responder_median_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {i j : Fin n} (hij : i ≠ j)
    (hj_med : (C j).1.rank.val + 1 = ceilHalf n)
    (hi_no_med : (C i).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C j).1.timer = 0)
    (h_no_swap : ¬((C i).1.rank < (C j).1.rank ∧ (C i).2 = Opinion.B ∧ (C j).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C j).2 ≠ (C i).1.answer) :
    transitionPEM n trank Rmax rankDelta (C i, C j) =
      ({ (C i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := opinionToAnswer ((C j).2) },
       { (C j).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := opinionToAnswer ((C j).2) }) := by
  have hi_settled : (C i).1.role = .Settled := hC.allSettled i
  have hj_settled : (C j).1.role = .Settled := hC.allSettled j
  have h_rank_ne : (C i).1.rank ≠ (C j).1.rank := by
    intro hEq
    exact hij (hC.ranks_inj hEq)
  have hRD : rankDelta ((C i).1, (C j).1) = ((C i).1, (C j).1) :=
    hRank (C i).1 (C j).1 hi_settled hj_settled h_rank_ne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hi_settled, hj_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    hi_no_med, hj_med, h_timer]
  split_ifs <;> simp_all

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
/-- Trace lemma: responder j at median, timer=1, initiator i at max rank,
    no swap, odd parity. Timer gets decremented to 0. -/
theorem propagation_reset_fires_no_swap_responder_median_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {i j : Fin n} (hij : i ≠ j)
    (hj_med : (C j).1.rank.val + 1 = ceilHalf n)
    (hi_max : (C i).1.rank.val + 1 = n)
    (h_timer : (C j).1.timer = 1)
    (h_no_swap : ¬((C i).1.rank < (C j).1.rank ∧ (C i).2 = Opinion.B ∧ (C j).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C j).2 ≠ (C i).1.answer) :
    transitionPEM n trank Rmax rankDelta (C i, C j) =
      ({ (C i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := opinionToAnswer ((C j).2) },
       { (C j).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := opinionToAnswer ((C j).2), timer := 0 }) := by
  have hi_settled : (C i).1.role = .Settled := hC.allSettled i
  have hj_settled : (C j).1.role = .Settled := hC.allSettled j
  have h_rank_ne : (C i).1.rank ≠ (C j).1.rank := by
    intro hEq
    exact hij (hC.ranks_inj hEq)
  have hRD : rankDelta ((C i).1, (C j).1) = ((C i).1, (C j).1) :=
    hRank (C i).1 (C j).1 hi_settled hj_settled h_rank_ne
  have hi_no_med : (C i).1.rank.val + 1 ≠ ceilHalf n := by
    unfold ceilHalf at hj_med ⊢
    omega
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have h_reset_cond :
      ((C j).1.timer - 1 = 0 ∧ ¬ (opinionToAnswer (C j).2 = (C i).1.answer)) := by
    refine ⟨by rw [h_timer], ?_⟩
    intro h_eq
    exact h_post_diff h_eq
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  -- First resolve propagate first-branch (i not median) before hi_max can interfere
  simp only [hRD, hi_settled, hj_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    hi_no_med, hj_med]
  simp only [hi_max, hN_ne_ceil, ite_true, ite_false, h_timer]
  simpa [h_timer] using h_reset_cond

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000000 in
theorem propagation_reset_fires_even_no_swap_responder_median_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {i j : Fin n} (hij : i ≠ j)
    (hpar : n % 2 = 0)
    (hj_lower : (C j).1.rank.val + 1 = n / 2)
    (hi_no_lower : (C i).1.rank.val + 1 ≠ n / 2)
    (hi_no_upper : (C i).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C j).1.timer = 0)
    (h_no_swap : ¬((C i).1.rank < (C j).1.rank ∧ (C i).2 = Opinion.B ∧ (C j).2 = Opinion.A))
    (h_post_diff : (C j).1.answer ≠ (C i).1.answer) :
    transitionPEM n trank Rmax rankDelta (C i, C j) =
      ({ (C i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := (C j).1.answer },
       { (C j).1 with role := .Resetting, leader := .L, resetcount := Rmax }) := by
  have hi_settled : (C i).1.role = .Settled := hC.allSettled i
  have hj_settled : (C j).1.role = .Settled := hC.allSettled j
  have h_rank_ne : (C i).1.rank ≠ (C j).1.rank := by
    intro hEq; exact hij (hC.ranks_inj hEq)
  have hRD : rankDelta ((C i).1, (C j).1) = ((C i).1, (C j).1) :=
    hRank (C i).1 (C j).1 hi_settled hj_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hj_ceil : (C j).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hj_lower
  have hi_no_ceil : (C i).1.rank.val + 1 ≠ ceilHalf n := by rw [hceil]; exact hi_no_lower
  have h_dec1 : ¬ ((C i).1.rank.val + 1 = n / 2 ∧ (C j).1.rank.val + 1 = n / 2 + 1) := by
    intro h; exact hi_no_lower h.1
  have h_dec2 : ¬ ((C j).1.rank.val + 1 = n / 2 ∧ (C i).1.rank.val + 1 = n / 2 + 1) := by
    intro h; exact hi_no_upper h.2
  have h_dec1a : ¬ ((C i).1.rank.val + 1 = n / 2 ∧ (C j).1.rank.val = n / 2) := by
    intro h; exact hi_no_lower h.1
  have h_dec2a : ¬ ((C j).1.rank.val + 1 = n / 2 ∧ (C i).1.rank.val = n / 2) := by
    intro h; exact hi_no_upper (by omega)
  have hswap : phase4_swap (C i).1 (C j).1 (C i).2 (C j).2 = ((C i).1, (C j).1) := by
    unfold phase4_swap; simp [h_no_swap]
  have hdec : phase4_decide n (C i).1 (C j).1 (C i).2 (C j).2 = ((C i).1, (C j).1) := by
    unfold phase4_decide; simp [hpar, h_dec1, h_dec2, h_dec1a, h_dec2a]
  have hprop : phase4_propagate n Rmax (C i).1 (C j).1 =
      ({ (C i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := (C j).1.answer },
       { (C j).1 with role := .Resetting, leader := .L, resetcount := Rmax }) := by
    unfold phase4_propagate
    simp only [hi_no_ceil, ite_false, hj_ceil]
    by_cases hi_max : (C i).1.rank.val + 1 = n
    · simp [hi_max, h_timer, h_post_diff]
    · simp [hi_max, h_timer, h_post_diff]
  unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
  simp [hRD, hi_settled, hj_settled, role_settled_ne_resetting, hswap, hdec, hprop]


/-! ## Responder-median necessary conditions (even parity, s₁ at median) -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000000 in
/-- s₁ median (even) + s₀ NOT max + Resetting → s₁.timer = 0. -/
theorem transitionPEM_fst_resetting_s1_med_no_max_even_timer_zero
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (h_s0_no_med : s₀.rank.val + 1 ≠ ceilHalf n)
    (h_s1_med : s₁.rank.val + 1 = ceilHalf n)
    (h_s0_no_max : s₀.rank.val + 1 ≠ n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₁.timer = 0 := by
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have h_s1_lower : s₁.rank.val + 1 = n / 2 := by rw [← hceil]; exact h_s1_med
  have h_s0_no_lower : s₀.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_s0_no_med
  have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) :=
    fun ⟨h1, _⟩ => h_s0_no_lower h1
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  by_cases h_s0_upper : s₀.rank.val + 1 = n / 2 + 1
  · exfalso
    have h_dec2 : s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1 :=
      ⟨h_s1_lower, h_s0_upper⟩
    have hd : phase4_decide n s₀ s₁ x₀ x₁ =
      if x₁ = x₀ then
        ({ s₀ with answer := opinionToAnswer x₁ }, { s₁ with answer := opinionToAnswer x₁ })
      else
        ({ s₀ with answer := .outT }, { s₁ with answer := .outT }) := by
      simp only [phase4_decide, hpar, ite_true]
      have : ¬(↑s₀.rank + 1 = n / 2 ∧ ↑s₁.rank = n / 2) :=
        fun ⟨ha, _⟩ => h_not_dec1 ⟨ha, by omega⟩
      simp [this, h_s1_lower, show ↑s₀.rank = n / 2 from by omega]
    rw [hd] at h; split_ifs at h
    · exact absurd
        (phase4_propagate_fst_settled_of_eq_answer' (n := n) (Rmax := Rmax)
          (b₀ := { s₀ with answer := opinionToAnswer x₁ })
          (b₁ := { s₁ with answer := opinionToAnswer x₁ }) hs₀ rfl)
        (by rw [h]; exact Role.noConfusion)
    · exact absurd
        (phase4_propagate_fst_settled_of_eq_answer' (n := n) (Rmax := Rmax)
          (b₀ := { s₀ with answer := .outT })
          (b₁ := { s₁ with answer := .outT }) hs₀ rfl)
        (by rw [h]; exact Role.noConfusion)
  · have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) :=
      fun ⟨_, h2⟩ => h_s0_upper h2
    have hd : phase4_decide n s₀ s₁ x₀ x₁ = (s₀, s₁) := by
      simp only [phase4_decide, hpar, ite_true]
      have h_nd1 : ¬(↑s₀.rank + 1 = n / 2 ∧ ↑s₁.rank = n / 2) :=
        fun ⟨ha, _⟩ => h_not_dec1 ⟨ha, by omega⟩
      have h_nd2 : ¬(↑s₁.rank + 1 = n / 2 ∧ ↑s₀.rank = n / 2) :=
        fun ⟨ha, hb⟩ => h_not_dec2 ⟨ha, by omega⟩
      simp [h_nd1, h_nd2]
    rw [hd] at h; simp only [Prod.fst, Prod.snd] at h
    unfold phase4_propagate at h
    simp only [h_s0_no_med, ite_false, h_s1_med, ite_true, h_s0_no_max, ite_false] at h
    split_ifs at h with hguard
    · exact hguard.1
    · rw [hs₀] at h; exact Role.noConfusion h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000000 in
/-- s₁ median (even) + s₀ max + n ≥ 4, Resetting → s₁.timer ≤ 1. -/
theorem transitionPEM_fst_resetting_s1_med_max_even_timer_le_one
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (hn4 : 4 ≤ n)
    (h_s0_no_med : s₀.rank.val + 1 ≠ ceilHalf n)
    (h_s1_med : s₁.rank.val + 1 = ceilHalf n)
    (h_s0_max : s₀.rank.val + 1 = n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₁.timer ≤ 1 := by
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have h_s0_no_lower : s₀.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_s0_no_med
  have h_s0_not_upper : s₀.rank.val + 1 ≠ n / 2 + 1 := by omega
  have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) :=
    fun ⟨h1, _⟩ => h_s0_no_lower h1
  have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) :=
    fun ⟨_, h2⟩ => h_s0_not_upper h2
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h; simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  have hd : phase4_decide n s₀ s₁ x₀ x₁ = (s₀, s₁) := by
    simp only [phase4_decide, hpar, ite_true]
    have h_nd1 : ¬(↑s₀.rank + 1 = n / 2 ∧ ↑s₁.rank = n / 2) :=
      fun ⟨ha, _⟩ => h_not_dec1 ⟨ha, by omega⟩
    have h_nd2 : ¬(↑s₁.rank + 1 = n / 2 ∧ ↑s₀.rank = n / 2) :=
      fun ⟨ha, hb⟩ => h_not_dec2 ⟨ha, by omega⟩
    simp [h_nd1, h_nd2]
  rw [hd] at h; simp only [Prod.fst, Prod.snd] at h
  have h_n_ne_ceil : n ≠ ceilHalf n := by omega
  unfold phase4_propagate at h
  simp only [h_s0_no_med, h_n_ne_ceil, ite_false, h_s1_med, ite_true, h_s0_max, ite_true] at h
  split_ifs at h with hguard
  · omega
  · exact absurd h (by simp [hs₀])

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000000 in
/-- s₁ median (even) + Resetting → s₁.answer ≠ s₀.answer. -/
theorem transitionPEM_fst_resetting_s1_med_even_answer_diff
    {n Rmax trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hFix : RankDeltaSettledFix rankDelta)
    (hs₀ : s₀.role = .Settled) (hs₁ : s₁.role = .Settled)
    (hne : s₀.rank ≠ s₁.rank)
    (h_no_swap : ¬(s₀.rank < s₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A))
    (hpar : n % 2 = 0)
    (hn4 : 4 ≤ n)
    (h_s0_no_med : s₀.rank.val + 1 ≠ ceilHalf n)
    (h_s1_med : s₁.rank.val + 1 = ceilHalf n)
    (h : (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = .Resetting) :
    s₁.answer ≠ s₀.answer := by
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have h_s1_lower : s₁.rank.val + 1 = n / 2 := by rw [← hceil]; exact h_s1_med
  have h_s0_no_lower : s₀.rank.val + 1 ≠ n / 2 := by rw [← hceil]; exact h_s0_no_med
  have h_not_dec1 : ¬(s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1) :=
    fun ⟨h1, _⟩ => h_s0_no_lower h1
  simp only [transitionPEM] at h
  rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hs₀ hs₁ hne] at h
  unfold transitionPEM_phase4 at h
  simp only [hs₀, hs₁, and_self, ite_true] at h
  unfold phase4_swap at h; simp only [h_no_swap, ite_false] at h
  by_cases h_s0_upper : s₀.rank.val + 1 = n / 2 + 1
  · exfalso
    have h_dec2 : s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1 :=
      ⟨h_s1_lower, h_s0_upper⟩
    have hd : phase4_decide n s₀ s₁ x₀ x₁ =
      if x₁ = x₀ then
        ({ s₀ with answer := opinionToAnswer x₁ }, { s₁ with answer := opinionToAnswer x₁ })
      else
        ({ s₀ with answer := .outT }, { s₁ with answer := .outT }) := by
      simp only [phase4_decide, hpar, ite_true]
      have : ¬(↑s₀.rank + 1 = n / 2 ∧ ↑s₁.rank = n / 2) :=
        fun ⟨ha, _⟩ => h_not_dec1 ⟨ha, by omega⟩
      simp [this, h_s1_lower, show ↑s₀.rank = n / 2 from by omega]
    rw [hd] at h; split_ifs at h
    · exact absurd
        (phase4_propagate_fst_settled_of_eq_answer' (n := n) (Rmax := Rmax)
          (b₀ := { s₀ with answer := opinionToAnswer x₁ })
          (b₁ := { s₁ with answer := opinionToAnswer x₁ }) hs₀ rfl)
        (by rw [h]; exact Role.noConfusion)
    · exact absurd
        (phase4_propagate_fst_settled_of_eq_answer' (n := n) (Rmax := Rmax)
          (b₀ := { s₀ with answer := .outT })
          (b₁ := { s₁ with answer := .outT }) hs₀ rfl)
        (by rw [h]; exact Role.noConfusion)
  · have h_not_dec2 : ¬(s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1) :=
      fun ⟨_, h2⟩ => h_s0_upper h2
    have hd : phase4_decide n s₀ s₁ x₀ x₁ = (s₀, s₁) := by
      simp only [phase4_decide, hpar, ite_true]
      have h_nd1 : ¬(↑s₀.rank + 1 = n / 2 ∧ ↑s₁.rank = n / 2) :=
        fun ⟨ha, _⟩ => h_not_dec1 ⟨ha, by omega⟩
      have h_nd2 : ¬(↑s₁.rank + 1 = n / 2 ∧ ↑s₀.rank = n / 2) :=
        fun ⟨ha, hb⟩ => h_not_dec2 ⟨ha, by omega⟩
      simp [h_nd1, h_nd2]
    rw [hd] at h; simp only [Prod.fst, Prod.snd] at h
    unfold phase4_propagate at h
    simp only [h_s0_no_med, ite_false, h_s1_med, ite_true] at h
    by_cases h_s0_max : s₀.rank.val + 1 = n
    · simp only [h_s0_max, ite_true] at h
      split_ifs at h with hguard
      · exact hguard.2
      · rw [hs₀] at h; exact Role.noConfusion h
    · simp only [h_s0_max, ite_false] at h
      split_ifs at h with hguard
      · exact hguard.2
      · rw [hs₀] at h; exact Role.noConfusion h

/-! ## Responder-median trace lemma (even parity, timer=1, initiator at max) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000000 in
theorem propagation_reset_fires_even_no_swap_responder_median_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {i j : Fin n} (hij : i ≠ j)
    (hpar : n % 2 = 0)
    (hj_lower : (C j).1.rank.val + 1 = n / 2)
    (hi_max : (C i).1.rank.val + 1 = n)
    (h_timer : (C j).1.timer = 1)
    (h_no_swap : ¬((C i).1.rank < (C j).1.rank ∧ (C i).2 = Opinion.B ∧ (C j).2 = Opinion.A))
    (h_post_diff : (C j).1.answer ≠ (C i).1.answer) :
    transitionPEM n trank Rmax rankDelta (C i, C j) =
      ({ (C i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := (C j).1.answer },
       { (C j).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       timer := 0 }) := by
  have hi_settled : (C i).1.role = .Settled := hC.allSettled i
  have hj_settled : (C j).1.role = .Settled := hC.allSettled j
  have h_rank_ne : (C i).1.rank ≠ (C j).1.rank := by
    intro hEq; exact hij (hC.ranks_inj hEq)
  have hRD : rankDelta ((C i).1, (C j).1) = ((C i).1, (C j).1) :=
    hRank (C i).1 (C j).1 hi_settled hj_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hj_ceil : (C j).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hj_lower
  have hi_no_ceil : (C i).1.rank.val + 1 ≠ ceilHalf n := by rw [hceil]; omega
  have hi_no_lower : (C i).1.rank.val + 1 ≠ n / 2 := by omega
  have hi_not_upper : (C i).1.rank.val + 1 ≠ n / 2 + 1 := by omega
  have h_dec1a : ¬ ((C i).1.rank.val + 1 = n / 2 ∧ (C j).1.rank.val = n / 2) := by
    intro h; exact hi_no_lower h.1
  have h_dec2a : ¬ ((C j).1.rank.val + 1 = n / 2 ∧ (C i).1.rank.val = n / 2) := by
    intro h; exact hi_not_upper (by omega)
  have hswap : phase4_swap (C i).1 (C j).1 (C i).2 (C j).2 = ((C i).1, (C j).1) := by
    unfold phase4_swap; simp [h_no_swap]
  have hdec : phase4_decide n (C i).1 (C j).1 (C i).2 (C j).2 = ((C i).1, (C j).1) := by
    unfold phase4_decide; simp [hpar, h_dec1a, h_dec2a]
  have hprop : phase4_propagate n Rmax (C i).1 (C j).1 =
      ({ (C i).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       answer := (C j).1.answer },
       { (C j).1 with role := .Resetting, leader := .L, resetcount := Rmax,
                       timer := 0 }) := by
    unfold phase4_propagate
    simp only [hi_no_ceil, ite_false, hj_ceil]
    simp [hi_max, h_timer, h_post_diff]
  unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
  simp [hRD, hi_settled, hj_settled, role_settled_ne_resetting, hswap, hdec, hprop]

end SSEM

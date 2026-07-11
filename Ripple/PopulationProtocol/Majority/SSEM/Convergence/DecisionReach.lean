/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Decision-Phase Reachability via Single-Step Reduction

`hDecisionPhase` reduced to a single local hypothesis using the
"wrong answer count" potential — the number of agents whose `.answer`
field disagrees with the global majority.

When the count is zero (all answers correct), an `InSswap`
configuration is precisely an `IsConsensusConfig` (since `Stim = Sswap ∩ Sout`).

The local single-step hypothesis requires showing that from any
`InSswap` configuration with at least one wrong answer there exists an
interaction `(u, v)` that preserves `InSswap` (or, more generally,
returns to it after a finite number of steps via a reset cycle) while
decreasing the wrong-answer count.  The paper's Lemma 11 provides the
probabilistic version of this; the deterministic discharge requires
careful timer/reset management.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.PotentialReach
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapPhase
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.RankPreservation

namespace SSEM

variable {n : ℕ}

/-- Number of agents whose `.answer` disagrees with the global majority. -/
def wrongAnswerCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun v : Fin n => (C v).1.answer ≠ majorityAnswer C)).card

theorem mem_wrongAnswerSet {C : Config (AgentState n) Opinion n} {v : Fin n} :
    v ∈ Finset.univ.filter (fun v : Fin n => (C v).1.answer ≠ majorityAnswer C)
      ↔ (C v).1.answer ≠ majorityAnswer C := by
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Wrong-answer count is zero iff every agent's answer matches the majority. -/
theorem wrongAnswerCount_eq_zero_iff (C : Config (AgentState n) Opinion n) :
    wrongAnswerCount C = 0 ↔ ∀ v, (C v).1.answer = majorityAnswer C := by
  unfold wrongAnswerCount
  rw [Finset.card_eq_zero]
  constructor
  · intro h v
    by_contra hne
    have hmem : v ∈ Finset.univ.filter (fun v => (C v).1.answer ≠ majorityAnswer C) :=
      mem_wrongAnswerSet.mpr hne
    rw [h] at hmem
    exact (Finset.notMem_empty _ hmem).elim
  · intro h
    apply Finset.ext
    intro v
    constructor
    · intro hmem
      exact absurd (h v) (mem_wrongAnswerSet.mp hmem)
    · intro hmem
      exact (Finset.notMem_empty _ hmem).elim

/-- An `InSswap` configuration with all answers correct is a consensus config. -/
theorem isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h0 : wrongAnswerCount C = 0) :
    IsConsensusConfig C where
  allSettled := hC.allSettled
  ranks_inj := hC.ranks_inj
  input_rank := hC.input_rank
  allAnswerCorrect := (wrongAnswerCount_eq_zero_iff C).mp h0

/-- Decision-phase reachability follows from a single-step decreasing-potential
hypothesis.  Used to instantiate `hDecisionPhase` in `Composition.lean`. -/
theorem decision_reaches_consensus_of_singleStep
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hStep : ∀ C : Config (AgentState n) Opinion n,
              InSswap C → 0 < wrongAnswerCount C →
              ∃ u v : Fin n,
                InSswap (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
                wrongAnswerCount
                  (C.step (protocolPEM n trank Rmax rankDelta) u v)
                  < wrongAnswerCount C) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  intro C hC
  obtain ⟨γ, t, hC_t, h0_t⟩ :=
    reach_zero_potential (P := protocolPEM n trank Rmax rankDelta)
      (Pinv := InSswap) (φ := wrongAnswerCount) hStep C hC
  exact ⟨γ, t, isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC_t h0_t⟩

/-- Decision-phase reachability via the **macro-step** variant. -/
theorem decision_reaches_consensus_of_macroStep
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hMacro : ∀ C : Config (AgentState n) Opinion n,
              InSswap C → 0 < wrongAnswerCount C →
              ∃ (γ : DetScheduler n) (k : ℕ),
                InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ k) ∧
                wrongAnswerCount
                  (execution (protocolPEM n trank Rmax rankDelta) C γ k)
                  < wrongAnswerCount C) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  intro C hC
  obtain ⟨γ, t, hC_t, h0_t⟩ :=
    reach_zero_potential_macro (P := protocolPEM n trank Rmax rankDelta)
      (Pinv := InSswap) (φ := wrongAnswerCount) hMacro C hC
  exact ⟨γ, t, isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC_t h0_t⟩

/-- Trivial decision phase reachability when `Sout` already holds: every
`Sswap ∩ Sout = Stim = IsConsensusConfig` configuration is its own
witness with `t = 0`. -/
theorem decision_reaches_consensus_when_Sout
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C : Config (AgentState n) Opinion n} (hC : InSswap C) (hOut : InSout C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  refine ⟨fun _ => default, 0, ?_⟩
  refine { allSettled := hC.allSettled, ranks_inj := hC.ranks_inj,
           input_rank := hC.input_rank, allAnswerCorrect := ?_ }
  exact hOut

/-! ### Median's input matches the majority side (even n with strict majority) -/

/-- For even `n` with strict majority (`nAOf C ≠ nBOf C`), both
medians of an `InSswap` configuration have input matching the majority side. -/
theorem opinionToAnswer_lower_median_eq_majorityAnswer_even
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n} (hμ : (C μ).1.rank.val + 1 = n / 2)
    (hpar : n % 2 = 0) (hne : nAOf C ≠ nBOf C) :
    opinionToAnswer (C μ).2 = majorityAnswer C := by
  have h_total : nAOf C + nBOf C = n := nAOf_add_nBOf C
  -- Lower median rank value: ceilHalf n - 1 = n/2 - 1.
  have hμ_rank : (C μ).1.rank.val = n / 2 - 1 := by omega
  -- Decide median's input via input_rank.
  rcases hxμ : (C μ).2 with _ | _
  · -- (C μ).2 = .A: nAOf C > n/2 - 1, so nAOf C ≥ n/2.  With nA ≠ nB and
    -- nA + nB = n (even): nA > nB ↔ nA > n/2.  We need nA > n/2 here, so
    -- we need nA ≠ n/2 (i.e., nA ≠ nB since both must add to n).
    have h_lt : (C μ).1.rank.val < nAOf C := (hC.input_rank μ).mp hxμ
    have h_ge : nAOf C ≥ n / 2 := by omega
    -- For nA = n/2: nB = n/2 = nA, contradicting hne.  So nA > n/2.
    have h_nA_gt : nAOf C > n / 2 := by
      by_contra h_le
      push_neg at h_le
      have : nAOf C = n / 2 := by omega
      have hnB : nBOf C = n / 2 := by omega
      rw [this, hnB] at hne; exact hne rfl
    have h_AmajB : nAOf C > nBOf C := by omega
    unfold majorityAnswer opinionToAnswer
    simp [h_AmajB]
  · -- (C μ).2 = .B: by inputB ↔ rank ≥ nAOf, n/2 - 1 ≥ nAOf C.
    have h_ge_inputB : ¬ ((C μ).2 = Opinion.A) := by rw [hxμ]; intro h; cases h
    have h_not_lt : ¬ ((C μ).1.rank.val < nAOf C) := by
      intro h_lt
      exact h_ge_inputB ((hC.input_rank μ).mpr h_lt)
    have h_le : nAOf C ≤ n / 2 - 1 := by omega
    -- nB = n - nA ≥ n - (n/2 - 1) = n/2 + 1 > n/2 ≥ nA, so nB > nA.
    have h_BmajA : nBOf C > nAOf C := by
      have h_pos : 0 < n / 2 := by
        -- From hμ : ↑(C μ).1.rank + 1 = n / 2 and 1 ≤ rank+1, so n/2 ≥ 1.
        omega
      omega
    unfold majorityAnswer opinionToAnswer
    simp [show ¬ (nAOf C > nBOf C) from by omega, h_BmajA]

/-- For even `n` with no tie, the **upper** median agent (rank `n/2`) also
has `opinionToAnswer` equal to `majorityAnswer`. Same arithmetic as lower. -/
theorem opinionToAnswer_upper_median_eq_majorityAnswer_even
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n} (hμ : (C μ).1.rank.val + 1 = n / 2 + 1)
    (hpar : n % 2 = 0) (hne : nAOf C ≠ nBOf C) :
    opinionToAnswer (C μ).2 = majorityAnswer C := by
  have h_total : nAOf C + nBOf C = n := nAOf_add_nBOf C
  have hμ_rank : (C μ).1.rank.val = n / 2 := by omega
  rcases hxμ : (C μ).2 with _ | _
  · have h_lt : (C μ).1.rank.val < nAOf C := (hC.input_rank μ).mp hxμ
    have h_gt : nAOf C > n / 2 := by omega
    have h_AmajB : nAOf C > nBOf C := by omega
    unfold majorityAnswer opinionToAnswer
    simp [h_AmajB]
  · have h_ge_inputB : ¬ ((C μ).2 = Opinion.A) := by rw [hxμ]; intro h; cases h
    have h_not_lt : ¬ ((C μ).1.rank.val < nAOf C) := by
      intro h_lt
      exact h_ge_inputB ((hC.input_rank μ).mpr h_lt)
    have h_le : nAOf C ≤ n / 2 := by omega
    have h_BmajA : nBOf C > nAOf C := by
      by_contra h_not_gt
      push_neg at h_not_gt
      have : nAOf C = n / 2 := by omega
      have hnB : nBOf C = n / 2 := by omega
      rw [this, hnB] at hne; exact hne rfl
    unfold majorityAnswer opinionToAnswer
    simp [show ¬ (nAOf C > nBOf C) from by omega, h_BmajA]

/-! ### Median's input matches the majority side (odd n) -/

/-- For odd `n`, an `InSswap` configuration's median agent has input
matching the majority side: `opinionToAnswer (C μ).2 = majorityAnswer C`. -/
theorem opinionToAnswer_median_eq_majorityAnswer_odd
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n} (hμ : (C μ).1.rank.val + 1 = ceilHalf n)
    (hpar : ¬ n % 2 = 0) :
    opinionToAnswer (C μ).2 = majorityAnswer C := by
  have h_total : nAOf C + nBOf C = n := nAOf_add_nBOf C
  have h_ceil : ceilHalf n = (n + 1) / 2 := rfl
  -- Median rank value: (C μ).1.rank.val = ceilHalf n - 1.
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  -- Decide median's input via input_rank.
  rcases hxμ : (C μ).2 with _ | _
  · -- (C μ).2 = .A: by input_rank, ceilHalf n - 1 < nAOf C, so nAOf C ≥ ceilHalf n.
    have h_lt : (C μ).1.rank.val < nAOf C := (hC.input_rank μ).mp hxμ
    have h_ge : nAOf C ≥ ceilHalf n := by omega
    -- For odd n: ceilHalf n > n / 2, so nAOf C > nBOf C.
    have h_AmajB : nAOf C > nBOf C := by
      have : ceilHalf n + ceilHalf n > n := by
        rw [h_ceil]; omega
      omega
    unfold majorityAnswer opinionToAnswer
    simp [h_AmajB]
  · -- (C μ).2 = .B: by inputB ↔ rank ≥ nAOf, ceilHalf n - 1 ≥ nAOf C.
    have h_ge_inputB : ¬ ((C μ).2 = Opinion.A) := by rw [hxμ]; intro h; cases h
    have h_not_lt : ¬ ((C μ).1.rank.val < nAOf C) := by
      intro h_lt
      exact h_ge_inputB ((hC.input_rank μ).mpr h_lt)
    have h_ge : nAOf C ≤ (C μ).1.rank.val := by omega
    -- (C μ).1.rank.val = ceilHalf n - 1.
    have h_le : nAOf C ≤ ceilHalf n - 1 := by omega
    -- For odd n: nAOf C < ceilHalf n, so nBOf C > nAOf C.
    have h_BmajA : nBOf C > nAOf C := by
      have : ceilHalf n + ceilHalf n > n := by
        rw [h_ceil]; omega
      have h_pos : 0 < ceilHalf n := by rw [h_ceil]; omega
      omega
    unfold majorityAnswer opinionToAnswer
    simp [show ¬ (nAOf C > nBOf C) from by omega, h_BmajA]

/-! ### Single-step decision at the median pair (even n ≥ 4, agreed inputs) -/

set_option maxHeartbeats 8000000 in
/-- At a no-swap median-pair `(u, v)` with even `n ≥ 4`, agreed inputs
(both `.A` or both `.B`), and Settled roles, `transitionPEM` returns the
pair with both answers set to `opinionToAnswer (C u).2`. -/
theorem transitionPEM_at_median_pair_even_agreed_inputs
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hn_ge_4 : 4 ≤ n) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ({(C u).1 with answer := opinionToAnswer (C u).2},
         {(C v).1 with answer := opinionToAnswer (C u).2}) := by
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (by intro h; have := congrArg Fin.val h; omega)
  -- Swap precondition: rank_u < rank_v ∧ x_u = .B ∧ x_v = .A.  We have
  -- rank_u < rank_v (from hu_med, hv_upper) but x_u = x_v (h_inputs_agree),
  -- so we can't have x_u = .B AND x_v = .A simultaneously.
  have h_no_swap : ¬ ((C u).1.rank < (C v).1.rank ∧
                      (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    intro ⟨_, hxuB, hxvA⟩
    rw [h_inputs_agree, hxvA] at hxuB; cases hxuB
  -- Post-rewrite version (after h_inputs_agree fires): same fact with
  -- (C u).2 replaced by (C v).2.
  have h_no_swap' : ¬ ((C u).1.rank < (C v).1.rank ∧
                       (C v).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    intro ⟨_, hB, hA⟩; rw [hA] at hB; cases hB
  -- Even more contracted: ¬ ((C v).2 = .B ∧ (C v).2 = .A).
  have h_xv_BA : ¬ ((C v).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    intro ⟨hB, hA⟩; rw [hA] at hB; cases hB
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hu_med_ceil : (C u).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hu_med
  have hv_no_med_ceil : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by rw [hceil, hv_upper]; omega
  have hv_no_max : ¬ ((C v).1.rank.val + 1 = n) := by rw [hv_upper]; omega
  have hN1 : ¬ (n / 2 + 1 = n / 2) := fun h => by omega
  have hN2 : ¬ (n / 2 = n / 2 + 1) := fun h => by omega
  have hN3 : ¬ (n / 2 + 1 = n) := fun h => by omega
  -- Decision branch 1 fires: b₀ at n/2 ∧ b₁ at n/2 + 1.
  have hd1 : (C u).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val + 1 = n / 2 + 1 :=
    ⟨hu_med, hv_upper⟩
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hpar, h_no_swap, h_no_swap', h_xv_BA,
    h_inputs_agree, hd1,
    hu_med, hv_upper, hN1, hN2, hN3, hu_med_ceil,
    hv_no_med_ceil, hv_no_max, hceil]

/-- Lifted to `Config.step`: the step at `(u, v)` modifies both u and v's
.answer to `opinionToAnswer (C u).2`. -/
theorem step_at_median_pair_even_agreed_inputs
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hn_ge_4 : 4 ≤ n) :
    C.step (protocolPEM n trank Rmax rankDelta) u v =
      fun w => if w = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
               else if w = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
               else C w := by
  funext w
  unfold Config.step
  simp only [if_neg huv]
  show (if w = u then
          ((transitionPEM n trank Rmax rankDelta (C u, C v)).1, (C u).2)
        else if w = v then
          ((transitionPEM n trank Rmax rankDelta (C u, C v)).2, (C v).2)
        else C w) = _
  rw [transitionPEM_at_median_pair_even_agreed_inputs
        hRank hsu hsv hpar hu_med hv_upper h_inputs_agree hn_ge_4]

set_option maxHeartbeats 8000000 in
/-- For the even-n median-pair step with strict majority and at least one
of `u, v` currently wrong, `wrongAnswerCount` strictly decreases. -/
theorem wrongAnswerCount_decreases_at_median_pair_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hne : nAOf C ≠ nBOf C)
    (hn_ge_4 : 4 ≤ n)
    (h_at_least_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
                             (C v).1.answer ≠ majorityAnswer C) :
    wrongAnswerCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < wrongAnswerCount C := by
  classical
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hC'_eq := step_at_median_pair_even_agreed_inputs
                   (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
                   hRank huv hsu hsv hpar hu_med hv_upper h_inputs_agree hn_ge_4
  have hMaj : majorityAnswer (C.step (protocolPEM n trank Rmax rankDelta) u v) =
              majorityAnswer C :=
    majorityAnswer_step_eq (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) C u v
  -- opinionToAnswer (C u).2 = majorityAnswer C (lower median + strict majority).
  have h_correct : opinionToAnswer (C u).2 = majorityAnswer C :=
    opinionToAnswer_lower_median_eq_majorityAnswer_even hC hu_med hpar hne
  -- Both u, v become correct after the step.
  have h_u_post : (C.step (protocolPEM n trank Rmax rankDelta) u v u).1.answer =
                   majorityAnswer C := by
    rw [hC'_eq]; simp; exact h_correct
  have h_v_post : (C.step (protocolPEM n trank Rmax rankDelta) u v v).1.answer =
                   majorityAnswer C := by
    rw [hC'_eq]; have hvu : v ≠ u := fun h => huv h.symm
    simp [hvu]; exact h_correct
  -- Other agents unchanged.
  have h_other_post : ∀ w, w ≠ u → w ≠ v →
      (C.step (protocolPEM n trank Rmax rankDelta) u v w).1.answer = (C w).1.answer := by
    intro w hwu hwv; rw [hC'_eq]; simp [hwu, hwv]
  -- wrongAnswerSet shrinks by removing every wrong-from-{u,v}.
  set Sc := Finset.univ.filter (fun w : Fin n => (C w).1.answer ≠ majorityAnswer C)
    with hSc
  set Sc' := Finset.univ.filter
    (fun w : Fin n =>
      (C.step (protocolPEM n trank Rmax rankDelta) u v w).1.answer ≠
      majorityAnswer (C.step (protocolPEM n trank Rmax rankDelta) u v))
    with hSc'
  -- u ∉ Sc', v ∉ Sc' (they became correct).
  -- For every other w, w ∈ Sc' iff w ∈ Sc.
  have hSc'_subset : Sc' ⊆ Sc.erase u := by
    intro w hw_in
    rw [hSc', Finset.mem_filter] at hw_in
    obtain ⟨_, hne'⟩ := hw_in
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hwu_eq
      rw [hwu_eq, h_u_post, hMaj] at hne'
      exact hne' rfl
    · rw [hSc, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases hwu : w = u
      · rw [hwu, h_u_post, hMaj] at hne'; exact (hne' rfl).elim
      · by_cases hwv : w = v
        · rw [hwv, h_v_post, hMaj] at hne'; exact (hne' rfl).elim
        · rw [h_other_post w hwu hwv, hMaj] at hne'; exact hne'
  -- Sc' has at most card(Sc.erase u) ≤ card(Sc) - 1 (when u ∈ Sc) elements.
  -- And we know at least one of u, v is in Sc; so card(Sc) ≥ 1.
  -- Combined: card(Sc') ≤ card(Sc.erase u) and Sc' is missing both u and v
  -- when at least one was wrong.  We use a simpler bound: Sc' ⊆ Sc \ {u, v}
  -- if v ∈ Sc, OR Sc' ⊆ Sc \ {u} otherwise.
  -- Cleanest: Sc' ⊆ Sc.erase u (proved) and v ∉ Sc' (because v became correct).
  have hv_not_in_Sc' : v ∉ Sc' := by
    rw [hSc', Finset.mem_filter]
    intro ⟨_, hne'⟩
    rw [h_v_post, hMaj] at hne'
    exact hne' rfl
  have hu_not_in_Sc' : u ∉ Sc' := by
    rw [hSc', Finset.mem_filter]
    intro ⟨_, hne'⟩
    rw [h_u_post, hMaj] at hne'
    exact hne' rfl
  -- card(Sc') ≤ card(Sc.erase u) ≤ card(Sc) - 1 (when u ∈ Sc).
  -- If u ∈ Sc: card(Sc') ≤ card(Sc) - 1 < card(Sc).
  -- If u ∉ Sc: then v ∈ Sc (by h_at_least_one_wrong).
  --   Sc' ⊆ Sc.erase u = Sc (since u ∉ Sc).  Also v ∉ Sc' but v ∈ Sc, so
  --   Sc' ⊊ Sc.
  rcases h_at_least_one_wrong with h_u_wrong | h_v_wrong
  · -- u ∈ Sc.
    have hu_in_Sc : u ∈ Sc := by
      rw [hSc, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h_u_wrong⟩
    have h_card_le : Sc'.card ≤ (Sc.erase u).card := Finset.card_le_card hSc'_subset
    have h_erase : (Sc.erase u).card = Sc.card - 1 := Finset.card_erase_of_mem hu_in_Sc
    have h_card_pos : 0 < Sc.card := Finset.card_pos.mpr ⟨u, hu_in_Sc⟩
    show Sc'.card < Sc.card
    omega
  · -- v ∈ Sc, possibly u ∉ Sc.
    have hv_in_Sc : v ∈ Sc := by
      rw [hSc, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h_v_wrong⟩
    -- Sc' ⊆ Sc.erase u; need to also show v ∉ Sc' (already proved as hv_not_in_Sc').
    -- So Sc' ⊆ (Sc.erase u).erase v.
    have hSc'_subset_2 : Sc' ⊆ (Sc.erase u).erase v := by
      intro w hw
      rw [Finset.mem_erase]
      refine ⟨?_, hSc'_subset hw⟩
      intro hwv_eq; rw [hwv_eq] at hw; exact hv_not_in_Sc' hw
    by_cases hu_in_Sc : u ∈ Sc
    · have h_card_le : Sc'.card ≤ ((Sc.erase u).erase v).card := Finset.card_le_card hSc'_subset_2
      have h_erase_u : (Sc.erase u).card = Sc.card - 1 := Finset.card_erase_of_mem hu_in_Sc
      have hv_in_erase : v ∈ Sc.erase u := by
        rw [Finset.mem_erase]; exact ⟨fun h => huv h.symm, hv_in_Sc⟩
      have h_erase_v : ((Sc.erase u).erase v).card = (Sc.erase u).card - 1 :=
        Finset.card_erase_of_mem hv_in_erase
      have h_card_pos : 0 < Sc.card := Finset.card_pos.mpr ⟨v, hv_in_Sc⟩
      show Sc'.card < Sc.card
      omega
    · -- u ∉ Sc, so Sc.erase u = Sc.
      have h_erase_u_eq : Sc.erase u = Sc := Finset.erase_eq_of_notMem hu_in_Sc
      have h_card_le : Sc'.card ≤ ((Sc.erase u).erase v).card := Finset.card_le_card hSc'_subset_2
      rw [h_erase_u_eq] at h_card_le
      have h_erase_v : (Sc.erase v).card = Sc.card - 1 := Finset.card_erase_of_mem hv_in_Sc
      have h_card_pos : 0 < Sc.card := Finset.card_pos.mpr ⟨v, hv_in_Sc⟩
      show Sc'.card < Sc.card
      omega

/-! ### InSswap preservation under the even-n median-pair step -/

set_option maxHeartbeats 8000000 in
/-- The even-n median-pair step preserves `InSswap`. -/
theorem step_at_median_pair_even_preserves_InSswap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hn_ge_4 : 4 ≤ n) :
    InSswap (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hC'_eq := step_at_median_pair_even_agreed_inputs
                   (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
                   hRank huv hsu hsv hpar hu_med hv_upper h_inputs_agree hn_ge_4
  have hvu : v ≠ u := fun h => huv h.symm
  have h_role_eq : ∀ w, (C.step (protocolPEM n trank Rmax rankDelta) u v w).1.role =
                        (C w).1.role := by
    intro w; rw [hC'_eq]
    by_cases hwu : w = u
    · simp [hwu]
    · by_cases hwv : w = v
      · subst hwv; simp [hwu, hvu]
      · simp [hwu, hwv]
  have h_rank_eq : ∀ w, (C.step (protocolPEM n trank Rmax rankDelta) u v w).1.rank =
                        (C w).1.rank := by
    intro w; rw [hC'_eq]
    by_cases hwu : w = u
    · subst hwu; simp
    · by_cases hwv : w = v
      · subst hwv; simp [hwu, hvu]
      · simp [hwu, hwv]
  have h_input_eq : ∀ w, (C.step (protocolPEM n trank Rmax rankDelta) u v w).2 =
                         (C w).2 := by
    intro w; rw [hC'_eq]
    by_cases hwu : w = u
    · simp [hwu]
    · by_cases hwv : w = v
      · subst hwv; simp [hwu, hvu]
      · simp [hwu, hwv]
  have h_nA_eq : nAOf (C.step (protocolPEM n trank Rmax rankDelta) u v) = nAOf C :=
    nAOf_step_eq (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) C u v
  refine { allSettled := ?_, ranks_inj := ?_, input_rank := ?_ }
  · intro w; rw [h_role_eq]; exact hC.allSettled w
  · intro w₁ w₂ hw
    have : (C w₁).1.rank = (C w₂).1.rank := by
      rw [← h_rank_eq w₁, ← h_rank_eq w₂]; exact hw
    exact hC.ranks_inj this
  · intro w
    rw [h_input_eq, h_rank_eq, h_nA_eq]
    exact hC.input_rank w

/-- Full single-step decision lemma at the even-n median pair: preserves
InSswap and strictly decreases wrongAnswerCount (under strict majority +
at least one of u, v wrong). -/
theorem decision_step_at_median_pair_even_decreases
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hne : nAOf C ≠ nBOf C)
    (hn_ge_4 : 4 ≤ n)
    (h_at_least_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
                             (C v).1.answer ≠ majorityAnswer C) :
    InSswap (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    wrongAnswerCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < wrongAnswerCount C :=
  ⟨step_at_median_pair_even_preserves_InSswap hRank hC huv hpar hu_med hv_upper
     h_inputs_agree hn_ge_4,
   wrongAnswerCount_decreases_at_median_pair_even hRank hC huv hpar hu_med hv_upper
     h_inputs_agree hne hn_ge_4 h_at_least_one_wrong⟩

/-- Decision-phase reachability via the even-n median-pair single-step. -/
theorem decision_reaches_consensus_via_median_pair_even
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : n % 2 = 0)
    (hne_global : ∀ C : Config (AgentState n) Opinion n,
                   InSswap C → nAOf C ≠ nBOf C)
    (hn_ge_4 : 4 ≤ n)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                0 < wrongAnswerCount C →
                ∃ u v : Fin n, u ≠ v ∧
                  (C u).1.rank.val + 1 = n / 2 ∧
                  (C v).1.rank.val + 1 = n / 2 + 1 ∧
                  (C u).2 = (C v).2 ∧
                  ((C u).1.answer ≠ majorityAnswer C ∨
                   (C v).1.answer ≠ majorityAnswer C)) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply decision_reaches_consensus_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, huv, hu_med, hv_upper, h_inputs_agree, h_one_wrong⟩ := hExists C hC hpos
  exact ⟨u, v, decision_step_at_median_pair_even_decreases
    hRank hC huv hpar hu_med hv_upper h_inputs_agree (hne_global C hC) hn_ge_4 h_one_wrong⟩

/-! ### Single-step decision at the median (odd n, no swap fires) -/

set_option maxHeartbeats 8000000 in
/-- At a pair `(u, v)` where:
  * both `u, v` are Settled,
  * `u` is at the median rank (`rank.val + 1 = ceilHalf n`),
  * `v` is not at the median rank,
  * `v` is not at the maximum rank,
  * `(C u).1.rank > (C v).1.rank` (so the swap precondition's rank check fails),
  * `n` is odd,
  * `(C u).1.timer ≥ 1` (so reset is blocked even if answers differ),
  * `rankDelta` is identity at Settled pairs,

`transitionPEM` returns `({(C u).1 with answer := opinionToAnswer (C u).2}, (C v).1)`. -/
theorem transitionPEM_at_median_no_swap_odd_v_not_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C u).1.rank)
    (h_timer : 1 ≤ (C u).1.timer) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ({(C u).1 with answer := opinionToAnswer (C u).2}, (C v).1) := by
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (fun h => absurd h.symm (ne_of_lt h_rank_gt))
  -- Swap precondition fails: rank_u < rank_v is False.
  have h_no_swap_rank : ¬ ((C u).1.rank < (C v).1.rank) := by
    intro h; exact absurd h (lt_asymm h_rank_gt)
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hpar, hu_med, hv_no_med, hv_no_max,
    h_no_swap_rank]
  -- After simp: swap doesn't fire, (b₀, b₁) = ((C u).1, (C v).1).
  -- Decision: b₀ = u at median fires, sets b₀.answer := opinionToAnswer x₀.
  -- b₁ = v not at median, unchanged.
  -- Propagation: b₀ at median, b₁ not at max → no inner timer-dec.
  -- Reset: b₀.timer ≥ 1, blocked.
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-- Lifted to `Config.step`: the step at `(u, v)` modifies `(C u).1.answer`
to `opinionToAnswer (C u).2` and leaves `v` untouched (and all other agents). -/
theorem step_at_median_no_swap_odd_v_not_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C u).1.rank)
    (h_timer : 1 ≤ (C u).1.timer) :
    C.step (protocolPEM n trank Rmax rankDelta) u v =
      fun w => if w = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
               else if w = v then ((C v).1, (C v).2)
               else C w := by
  funext w
  unfold Config.step
  simp only [if_neg huv]
  show (if w = u then
          ((transitionPEM n trank Rmax rankDelta (C u, C v)).1, (C u).2)
        else if w = v then
          ((transitionPEM n trank Rmax rankDelta (C u, C v)).2, (C v).2)
        else C w) = _
  rw [transitionPEM_at_median_no_swap_odd_v_not_max
        hRank hsu hsv hpar hu_med hv_no_med hv_no_max h_rank_gt h_timer]

/-! ### wrongAnswerCount strictly decreases at the median (odd n) -/

set_option maxHeartbeats 8000000 in
/-- Under the step at the median pair `(μ, v)` of the previous lemma, the
median's `.answer` flips from wrong to correct (since
`opinionToAnswer (C μ).2 = majorityAnswer C` for odd n by InSswap input_rank);
all other agents unchanged.  Hence `wrongAnswerCount` strictly decreases. -/
theorem wrongAnswerCount_decreases_at_median_no_swap_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C μ).1.rank)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    wrongAnswerCount (C.step (protocolPEM n trank Rmax rankDelta) μ v)
      < wrongAnswerCount C := by
  classical
  let C' := C.step (protocolPEM n trank Rmax rankDelta) μ v
  -- Use step_at_median to characterize C'.
  have hsμ : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hC'_eq : C.step (protocolPEM n trank Rmax rankDelta) μ v =
      fun w => if w = μ then ({(C μ).1 with answer := opinionToAnswer (C μ).2}, (C μ).2)
               else if w = v then ((C v).1, (C v).2)
               else C w :=
    step_at_median_no_swap_odd_v_not_max
      (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
      hRank hμv hsμ hsv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer
  -- majorityAnswer is preserved.
  have hMaj : majorityAnswer C' = majorityAnswer C :=
    majorityAnswer_step_eq (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) C μ v
  -- (C' μ).1.answer = opinionToAnswer (C μ).2 = majorityAnswer C.
  have hC'μ_answer : (C' μ).1.answer = majorityAnswer C := by
    show (C.step (protocolPEM n trank Rmax rankDelta) μ v μ).1.answer = majorityAnswer C
    rw [hC'_eq]; simp
    exact opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  -- (C' w).1.answer = (C w).1.answer for w ≠ μ.
  have hC'_other : ∀ w, w ≠ μ → (C' w).1.answer = (C w).1.answer := by
    intro w hwμ
    show (C.step (protocolPEM n trank Rmax rankDelta) μ v w).1.answer = (C w).1.answer
    rw [hC'_eq]
    have hvμ : v ≠ μ := fun h => hμv h.symm
    by_cases hwv : w = v
    · subst hwv; simp [hwμ, hvμ]
    · simp [hwμ, hwv]
  -- The wrongAnswerSet of C' = wrongAnswerSet of C minus {μ}.
  set Sc := Finset.univ.filter (fun w : Fin n => (C w).1.answer ≠ majorityAnswer C)
    with hSc
  set Sc' := Finset.univ.filter (fun w : Fin n => (C' w).1.answer ≠ majorityAnswer C')
    with hSc'
  have hμ_in_Sc : μ ∈ Sc := by
    rw [hSc]; rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h_μ_wrong⟩
  have hSc'_eq : Sc' = Sc.erase μ := by
    apply Finset.ext
    intro w
    rw [hSc', Finset.mem_filter, Finset.mem_erase, hSc, Finset.mem_filter]
    constructor
    · intro ⟨_, hne⟩
      refine ⟨?_, Finset.mem_univ _, ?_⟩
      · -- w ≠ μ: if w = μ, (C' μ).1.answer = majorityAnswer = majorityAnswer C', contradicts hne.
        intro hμeq
        rw [hμeq] at hne
        rw [hC'μ_answer, hMaj] at hne
        exact hne rfl
      · intro h_C_w
        rw [hC'_other w (by intro hwμ; rw [hwμ] at hne; rw [hC'μ_answer, hMaj] at hne; exact hne rfl), hMaj] at hne
        exact hne h_C_w
    · intro ⟨hwμ, _, h_C_w⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hC'_other w hwμ, hMaj]
      exact h_C_w
  -- Cardinality:
  have h_card_Sc' : Sc'.card = Sc.card - 1 := by
    rw [hSc'_eq]; exact Finset.card_erase_of_mem hμ_in_Sc
  have h_card_Sc_pos : 0 < Sc.card := Finset.card_pos.mpr ⟨μ, hμ_in_Sc⟩
  show Sc'.card < Sc.card
  omega

/-! ### InSswap preservation under the median no-swap step -/

set_option maxHeartbeats 8000000 in
/-- The step at the median no-swap pair preserves `InSswap`: roles stay
Settled, ranks unchanged (so injective), inputs unchanged (so input_rank
holds for the same nAOf). -/
theorem step_at_median_no_swap_odd_preserves_InSswap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C μ).1.rank)
    (h_timer : 1 ≤ (C μ).1.timer) :
    InSswap (C.step (protocolPEM n trank Rmax rankDelta) μ v) := by
  have hsμ : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hC'_eq : C.step (protocolPEM n trank Rmax rankDelta) μ v =
      fun w => if w = μ then ({(C μ).1 with answer := opinionToAnswer (C μ).2}, (C μ).2)
               else if w = v then ((C v).1, (C v).2)
               else C w :=
    step_at_median_no_swap_odd_v_not_max
      (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
      hRank hμv hsμ hsv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer
  -- Role/rank/input projections
  have h_role_eq : ∀ w, (C.step (protocolPEM n trank Rmax rankDelta) μ v w).1.role =
                        (C w).1.role := by
    intro w
    rw [hC'_eq]
    have hvμ : v ≠ μ := fun h => hμv h.symm
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · subst hwv; simp [hwμ, hvμ]
      · simp [hwμ, hwv]
  have h_rank_eq : ∀ w, (C.step (protocolPEM n trank Rmax rankDelta) μ v w).1.rank =
                        (C w).1.rank := by
    intro w
    rw [hC'_eq]
    have hvμ : v ≠ μ := fun h => hμv h.symm
    by_cases hwμ : w = μ
    · subst hwμ; simp
    · by_cases hwv : w = v
      · subst hwv; simp [hwμ, hvμ]
      · simp [hwμ, hwv]
  have h_input_eq : ∀ w, (C.step (protocolPEM n trank Rmax rankDelta) μ v w).2 =
                         (C w).2 := by
    intro w
    rw [hC'_eq]
    have hvμ : v ≠ μ := fun h => hμv h.symm
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · subst hwv; simp [hwμ, hvμ]
      · simp [hwμ, hwv]
  have h_nA_eq : nAOf (C.step (protocolPEM n trank Rmax rankDelta) μ v) = nAOf C :=
    nAOf_step_eq (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) C μ v
  refine { allSettled := ?_, ranks_inj := ?_, input_rank := ?_ }
  · intro w; rw [h_role_eq]; exact hC.allSettled w
  · intro w₁ w₂ hw
    have : (C w₁).1.rank = (C w₂).1.rank := by
      rw [← h_rank_eq w₁, ← h_rank_eq w₂]; exact hw
    exact hC.ranks_inj this
  · intro w
    rw [h_input_eq, h_rank_eq, h_nA_eq]
    exact hC.input_rank w

/-- Full single-step decision lemma at the median (odd n, no-swap pair):
preserves InSswap and strictly decreases wrongAnswerCount. -/
theorem decision_step_at_median_no_swap_odd_decreases
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C μ).1.rank)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    InSswap (C.step (protocolPEM n trank Rmax rankDelta) μ v) ∧
    wrongAnswerCount (C.step (protocolPEM n trank Rmax rankDelta) μ v)
      < wrongAnswerCount C :=
  ⟨step_at_median_no_swap_odd_preserves_InSswap hRank hC hμv hpar hμ_med
     hv_no_med hv_no_max h_rank_gt h_timer,
   wrongAnswerCount_decreases_at_median_no_swap_odd hRank hC hμv hpar hμ_med
     hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong⟩

/-- Decision-phase reachability via the median-wrong-decision single-step:
from any `InSswap` with positive wrong-count, if we always have a
witnessing `(μ, v)` with the median-wrong-decision structure, we reach a
consensus configuration. -/
theorem decision_reaches_consensus_via_median_wrong_odd
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : ¬ n % 2 = 0)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                0 < wrongAnswerCount C →
                ∃ μ v : Fin n, μ ≠ v ∧
                  (C μ).1.rank.val + 1 = ceilHalf n ∧
                  (C v).1.rank.val + 1 ≠ ceilHalf n ∧
                  (C v).1.rank.val + 1 ≠ n ∧
                  (C v).1.rank < (C μ).1.rank ∧
                  1 ≤ (C μ).1.timer ∧
                  (C μ).1.answer ≠ majorityAnswer C) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply decision_reaches_consensus_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨μ, v, hμv, hμ_med, hv_no_med, hv_no_max, h_rank_gt, h_timer, h_μ_wrong⟩ :=
    hExists C hC hpos
  exact ⟨μ, v, decision_step_at_median_no_swap_odd_decreases
    hRank hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong⟩

/-! ### Composite Theorem 4 corollary: four-way swap + median-wrong-odd decision -/

/-- Theorem 4 corollary combining the four-way unified swap-step and the
median-wrong-decision (odd `n`).  Requires:
  * Burman ranking convergence (external),
  * a witness for the four-way swap existence at every `InSrank` with
    positive misorderedCount,
  * `n` is odd,
  * a witness for the median-wrong-decision existence at every `InSswap`
    with positive `wrongAnswerCount`.

This closes the "median-wrong" half of the decision-phase obligation; the
"median-correct, some-non-median-wrong" case still requires macro-step
machinery (reset cycle) — that's the residual gap. -/
theorem P_EM_solves_SSEM_via_four_way_and_median_wrong_decision
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : ¬ n % 2 = 0)
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hSwapExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    0 < misorderedCount C →
                    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
                       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)))
    (hDecExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                   0 < wrongAnswerCount C →
                   ∃ μ v : Fin n, μ ≠ v ∧
                     (C μ).1.rank.val + 1 = ceilHalf n ∧
                     (C v).1.rank.val + 1 ≠ ceilHalf n ∧
                     (C v).1.rank.val + 1 ≠ n ∧
                     (C v).1.rank < (C μ).1.rank ∧
                     1 ≤ (C μ).1.timer ∧
                     (C μ).1.answer ≠ majorityAnswer C) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_via_phases hRank hRankPhase
    (swap_reaches_Sswap_via_four_way hRank hSwapExists)
    (decision_reaches_consensus_via_median_wrong_odd hRank hpar hDecExists)

end SSEM

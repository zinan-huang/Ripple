/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Decision Step for Even-n Tie Case

When n is even and nA = nB (exact tie), the median pair has different
inputs. The decision step sets both answers to `.outT` = majorityAnswer.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.DecisionReach

namespace SSEM

variable {n : ℕ}

/-! ### majorityAnswer = .outT when tie -/

theorem majorityAnswer_eq_outT_of_tie
    {C : Config (AgentState n) Opinion n}
    (hTie : nAOf C = nBOf C) :
    majorityAnswer C = .outT := by
  unfold majorityAnswer
  simp only [hTie, lt_irrefl, if_false, ite_self]

/-! ### Transition equation for disagreed inputs -/

set_option maxHeartbeats 16000000 in
theorem transitionPEM_at_median_pair_even_disagreed_inputs
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_disagree : (C u).2 ≠ (C v).2)
    (h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hn_ge_4 : 4 ≤ n) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ({(C u).1 with answer := .outT},
         {(C v).1 with answer := .outT}) := by
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (by intro h; have := congrArg Fin.val h; omega)
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hu_med_ceil : (C u).1.rank.val + 1 = ceilHalf n := by rw [hceil]; exact hu_med
  have hv_no_med_ceil : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by rw [hceil, hv_upper]; omega
  have hv_no_max : ¬ ((C v).1.rank.val + 1 = n) := by rw [hv_upper]; omega
  have hN1 : ¬ (n / 2 + 1 = n / 2) := fun h => by omega
  have hN2 : ¬ (n / 2 = n / 2 + 1) := fun h => by omega
  have hN3 : ¬ (n / 2 + 1 = n) := fun h => by omega
  have h_ne_sym : (C v).2 ≠ (C u).2 := Ne.symm h_inputs_disagree
  -- The swap condition requires x₀ = B ∧ x₁ = A, which h_no_swap rules out
  have h_no_swap_full : ¬ ((C u).1.rank < (C v).1.rank ∧
                      (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    intro ⟨_, hB, hA⟩; exact h_no_swap ⟨hB, hA⟩
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hpar, h_no_swap_full,
    hu_med, hv_upper, hN1, hN2, hN3, hu_med_ceil,
    hv_no_med_ceil, hv_no_max, hceil,
    h_inputs_disagree, h_ne_sym]

/-! ### Lifted to Config.step -/

theorem step_at_median_pair_even_disagreed_inputs
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_disagree : (C u).2 ≠ (C v).2)
    (h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hn_ge_4 : 4 ≤ n) :
    let P := protocolPEM n trank Rmax rankDelta
    let C' := C.step P u v
    (C' u).1 = {(C u).1 with answer := .outT} ∧
    (C' v).1 = {(C v).1 with answer := .outT} ∧
    (∀ w, w ≠ u → w ≠ v → C' w = C w) ∧
    (∀ w, (C' w).2 = (C w).2) := by
  have htr := transitionPEM_at_median_pair_even_disagreed_inputs
    (trank := trank) (Rmax := Rmax) hRank hsu hsv hpar hu_med hv_upper h_inputs_disagree
    h_no_swap hn_ge_4
  have hvu : v ≠ u := Ne.symm huv
  set P := protocolPEM n trank Rmax rankDelta
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (C.step P u v u).1 = _
    unfold Config.step; simp only [if_neg huv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C u, C v)).1 = _; rw [htr]
  · show (C.step P u v v).1 = _
    unfold Config.step; simp only [if_neg huv, if_neg hvu, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C u, C v)).2 = _; rw [htr]
  · intro w hw hwv; show C.step P u v w = C w
    unfold Config.step; simp only [if_neg huv, if_neg hw, if_neg hwv]
  · intro w; show (C.step P u v w).2 = (C w).2
    unfold Config.step
    by_cases hw : w = u
    · subst hw; simp [huv]
    · by_cases hwv : w = v
      · subst hwv; simp [huv, hw]
      · simp [huv, hw, hwv]

/-! ### Decision step decreases wrongAnswerCount -/

theorem decision_step_at_median_pair_even_tie_decreases
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_disagree : (C u).2 ≠ (C v).2)
    (hTie : nAOf C = nBOf C)
    (hn_ge_4 : 4 ≤ n)
    (h_at_least_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
                             (C v).1.answer ≠ majorityAnswer C) :
    let P := protocolPEM n trank Rmax rankDelta
    InSswap (C.step P u v) ∧
    wrongAnswerCount (C.step P u v) < wrongAnswerCount C := by
  set P := protocolPEM n trank Rmax rankDelta
  have hsu := hC.allSettled u
  have hsv := hC.allSettled v
  -- Derive no-swap from InSswap: u at rank n/2-1 with nA = n/2, so u has input A
  have h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    intro ⟨hxuB, _⟩
    have hsum := nAOf_add_nBOf C
    have : (C u).2 = Opinion.A :=
      (hC.input_rank u).mpr (by omega)
    rw [this] at hxuB; cases hxuB
  obtain ⟨h_u, h_v, h_others, h_inputs⟩ :=
    step_at_median_pair_even_disagreed_inputs
      hRank huv hsu hsv hpar hu_med hv_upper h_inputs_disagree h_no_swap hn_ge_4
  have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hTie
  have hMaj : majorityAnswer (C.step P u v) = majorityAnswer C :=
    majorityAnswer_step_eq (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta) C u v
  -- Both u, v become correct (.outT = majorityAnswer)
  have h_u_correct : (C.step P u v u).1.answer = majorityAnswer C := by
    rw [h_u]; exact h_outT.symm
  have h_v_correct : (C.step P u v v).1.answer = majorityAnswer C := by
    rw [h_v]; exact h_outT.symm
  constructor
  · -- InSswap preserved
    constructor
    · constructor
      · intro w
        by_cases hw : w = u
        · rw [hw, h_u]; exact hC.allSettled u
        · by_cases hwv : w = v
          · rw [hwv, h_v]; exact hC.allSettled v
          · rw [h_others w hw hwv]; exact hC.allSettled w
      · intro w₁ w₂ heq
        have h_rank_w : ∀ w, (C.step P u v w).1.rank = (C w).1.rank := by
          intro w
          by_cases hw : w = u
          · rw [hw, h_u]
          · by_cases hwv : w = v
            · rw [hwv, h_v]
            · rw [h_others w hw hwv]
        simp only [h_rank_w] at heq; exact hC.ranks_inj heq
    · intro w
      have h_rank_w : (C.step P u v w).1.rank = (C w).1.rank := by
        by_cases hw : w = u
        · rw [hw, h_u]
        · by_cases hwv : w = v
          · rw [hwv, h_v]
          · rw [h_others w hw hwv]
      have h_nA : nAOf (C.step P u v) = nAOf C := by
        unfold nAOf Config.agentsWithInput Config.inputOf
        congr 1; ext w'; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs] at h; exact h⟩,
               fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs]; exact h⟩⟩
      rw [h_inputs w, h_rank_w, h_nA]; exact hC.input_rank w
  · -- wrongAnswerCount decreases
    classical
    set Sc := Finset.univ.filter (fun w : Fin n => (C w).1.answer ≠ majorityAnswer C)
    set Sc' := Finset.univ.filter
      (fun w : Fin n =>
        (C.step P u v w).1.answer ≠ majorityAnswer (C.step P u v))
    suffices h : Sc' ⊂ Sc from Finset.card_lt_card h
    have hSub : Sc' ⊆ Sc := by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rw [hMaj] at hw
      by_cases hwu : w = u
      · exact absurd h_u_correct (by rw [hwu] at hw; exact hw.2)
      · by_cases hwv : w = v
        · exact absurd h_v_correct (by rw [hwv] at hw; exact hw.2)
        · rw [h_others w hwu hwv] at hw; exact hw.2
    rw [Finset.ssubset_iff_of_subset hSub]
    rcases h_at_least_one_wrong with hwu | hwv
    · exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwu⟩,
             Finset.mem_filter.not.mpr (by push_neg; intro; rw [hMaj]; exact h_u_correct)⟩
    · exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv⟩,
             Finset.mem_filter.not.mpr (by push_neg; intro; rw [hMaj]; exact h_v_correct)⟩

end SSEM

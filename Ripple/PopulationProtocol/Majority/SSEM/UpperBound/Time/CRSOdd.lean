import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.Bridge
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.TransitionLemmas

namespace SSEM

open scoped ENNReal

/-! ### Helper: InSswap preserved when both outputs stay Settled -/

private theorem InSswap_preserved_of_output_settled
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (hri : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role = .Settled)
    (hrj : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j j).1.role = .Settled) :
    InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have h_rank_w : ∀ w, (D.step P i j w).1.rank = (D w).1.rank :=
    fun w => step_rank_preserved_of_InSswap hn0 hS w
  have h_input_w : ∀ w, (D.step P i j w).2 = (D w).2 :=
    fun w => step_input_preserved P D i j w
  have h_nA : nAOf (D.step P i j) = nAOf D := by
    simp only [P, PEMProtocolCoupled, PEMProtocol]
    exact nAOf_step_eq (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w
    by_cases hwi : w = i
    · exact hwi ▸ hri
    · by_cases hwj : w = j
      · exact hwj ▸ hrj
      · show (D.step P i j w).1.role = .Settled
        have : D.step P i j w = D w := by unfold Config.step; simp [hij, hwi, hwj]
        rw [this]; exact hS.allSettled w
  · intro w₁ w₂ heq
    have : (D w₁).1.rank = (D w₂).1.rank := by
      rw [← h_rank_w w₁, ← h_rank_w w₂]; exact heq
    exact hS.ranks_inj this
  · intro w
    rw [h_input_w, h_rank_w, h_nA]
    exact hS.input_rank w

/-! ### Helper: apply trace to get CRS when i is median (odd case)

Given a trace equality transitionPEM ... = (out₁, out₂), and knowing
i is median with odd parity, constructs CorrectResetSeed. -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
private theorem CRS_from_odd_trace
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (h_i_med : (D i).1.rank.val + 1 = ceilHalf n)
    (hOdd : n % 2 ≠ 0)
    {out₁ out₂ : AgentState n}
    (htr : transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j) = (out₁, out₂))
    (h_out1_role : out₁.role = .Resetting)
    (h_out1_rc : out₁.resetcount = Rmax)
    (h_out1_leader : out₁.leader = .L)
    (h_out1_ans : out₁.answer = opinionToAnswer (D i).2)
    (h_out2_role : out₂.role = .Resetting)
    (h_out2_rc : out₂.resetcount = Rmax)
    (h_out2_ans : out₂.answer = opinionToAnswer (D i).2) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  -- Link step outputs to trace outputs
  have h_step_i : (D.step P i j i).1 = out₁ := by
    rw [h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 = out₁
    rw [htr]
  have h_step_j : (D.step P i j j).1 = out₂ := by
    rw [h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2 = out₂
    rw [htr]
  have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  have hμ_majority : opinionToAnswer (D i).2 = majorityAnswer D :=
    opinionToAnswer_median_eq_majorityAnswer_odd hS h_i_med hOdd
  have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
    intro w hw hwv; unfold Config.step; simp [hij, hw, hwv]
  have h_nrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
    unfold nonResettingCount
    set S := Finset.univ.filter (fun w : Fin n => (D.step P i j w).1.role ≠ .Resetting)
    have hi_not : i ∉ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [h_step_i]; exact h_out1_role
    have hj_not : j ∉ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [h_step_j]; exact h_out2_role
    have hS_sub : S ⊆ (Finset.univ \ {i, j}) := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi_not (h ▸ hw), fun h => hj_not (h ▸ hw)⟩
    calc S.card ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card :=
          Finset.card_le_card hS_sub
      _ = n - 2 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
            Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
  refine ⟨⟨i, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [h_step_i]; exact h_out1_role
  · rw [h_step_i, h_out1_rc]
    exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
  · rw [h_step_i]; exact h_out1_leader
  · rw [h_step_i, h_out1_ans, hμ_majority, h_maj]
  · intro w hw_res
    by_cases hwi : w = i
    · subst hwi
      exact ⟨by rw [h_step_i, h_out1_rc]; omega, by rw [h_step_i, h_out1_ans, hμ_majority, h_maj]⟩
    · by_cases hwj : w = j
      · subst hwj
        exact ⟨by rw [h_step_j, h_out2_rc]; omega, by rw [h_step_j, h_out2_ans, hμ_majority, h_maj]⟩
      · exfalso
        rw [show (D.step P i j w).1 = (D w).1 from
          congrArg Prod.fst (h_post_others w hwi hwj)] at hw_res
        rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res


/-! ### Helper: apply trace to get CRS when j (responder) is median (odd case)

Same as CRS_from_odd_trace but with j at median rank.
Both output answers equal opinionToAnswer (D j).2 (median's opinion). -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
private theorem CRS_from_odd_trace_responder_median
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (h_j_med : (D j).1.rank.val + 1 = ceilHalf n)
    (hOdd : n % 2 ≠ 0)
    {out₁ out₂ : AgentState n}
    (htr : transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j) = (out₁, out₂))
    (h_out1_role : out₁.role = .Resetting)
    (h_out1_rc : out₁.resetcount = Rmax)
    (h_out1_leader : out₁.leader = .L)
    (h_out1_ans : out₁.answer = opinionToAnswer (D j).2)
    (h_out2_role : out₂.role = .Resetting)
    (h_out2_rc : out₂.resetcount = Rmax)
    (h_out2_ans : out₂.answer = opinionToAnswer (D j).2) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  have h_step_i : (D.step P i j i).1 = out₁ := by
    rw [h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).1 = out₁
    rw [htr]
  have h_step_j : (D.step P i j j).1 = out₂ := by
    rw [h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (D i, D j)).2 = out₂
    rw [htr]
  have h_maj : majorityAnswer (D.step P i j) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  have hμ_majority : opinionToAnswer (D j).2 = majorityAnswer D :=
    opinionToAnswer_median_eq_majorityAnswer_odd hS h_j_med hOdd
  have h_post_others : ∀ w, w ≠ i → w ≠ j → (D.step P i j w) = D w := by
    intro w hw hwv; unfold Config.step; simp [hij, hw, hwv]
  have h_nrc : nonResettingCount (D.step P i j) ≤ n - 2 := by
    unfold nonResettingCount
    set S := Finset.univ.filter (fun w : Fin n => (D.step P i j w).1.role ≠ .Resetting)
    have hi_not : i ∉ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [h_step_i]; exact h_out1_role
    have hj_not : j ∉ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [h_step_j]; exact h_out2_role
    have hS_sub : S ⊆ (Finset.univ \ {i, j}) := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi_not (h ▸ hw), fun h => hj_not (h ▸ hw)⟩
    calc S.card ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card :=
          Finset.card_le_card hS_sub
      _ = n - 2 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
            Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
  refine ⟨⟨i, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [h_step_i]; exact h_out1_role
  · rw [h_step_i, h_out1_rc]
    exact lt_of_le_of_lt h_nrc (lt_of_lt_of_le (by omega) hRmax)
  · rw [h_step_i]; exact h_out1_leader
  · rw [h_step_i, h_out1_ans, hμ_majority, h_maj]
  · intro w hw_res
    by_cases hwi : w = i
    · subst hwi
      exact ⟨by rw [h_step_i, h_out1_rc]; omega, by rw [h_step_i, h_out1_ans, hμ_majority, h_maj]⟩
    · by_cases hwj : w = j
      · subst hwj
        exact ⟨by rw [h_step_j, h_out2_rc]; omega, by rw [h_step_j, h_out2_ans, hμ_majority, h_maj]⟩
      · exfalso
        rw [show (D.step P i j w).1 = (D w).1 from
          congrArg Prod.fst (h_post_others w hwi hwj)] at hw_res
        rw [hS.allSettled w] at hw_res; exact Role.noConfusion hw_res

/-! ### CRS from both-Resetting step outputs (odd case) -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
private theorem CRS_of_both_resetting_odd
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hOdd : n % 2 ≠ 0)
    {i j : Fin n} (hij : i ≠ j)
    (h_i_res : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role = .Resetting)
    (h_j_res : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j j).1.role = .Resetting) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hsi : (D i).1.role = .Settled := hS.toInSrank.allSettled i
  have hsj : (D j).1.role = .Settled := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hFix := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0)
  have h_no_swap := hS.swap_condition_false i j
  -- Resetting at transitionPEM level
  have h_i_res_raw : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D i, D j)).1.role = .Resetting := by
    have h_fst := Config.step_fst_state P D hij
    rw [← show ∀ p, P.δ p = transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) p
      from fun _ => rfl, ← congrArg AgentState.role h_fst]; exact h_i_res
  -- Determine which agent is median
  have h_med := transitionPEM_fst_resetting_implies_some_median_odd
    (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
    hFix hsi hsj hrij h_no_swap hOdd h_i_res_raw
  rcases h_med with h_i_med | h_j_med
  · -- i is the median agent
    have hv_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n :=
      fun h => hrij (Fin.ext (Nat.add_right_cancel (h_i_med.trans h.symm)))
    have h_ans_diff := transitionPEM_fst_resetting_s0_med_odd_answer_diff
      (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
      hFix hsi hsj hrij h_no_swap hOdd h_i_med hv_no_med h_i_res_raw
    by_cases hv_max : (D j).1.rank.val + 1 = n
    · -- j max rank: timer ≤ 1
      have h_tl := transitionPEM_fst_resetting_s0_med_max_odd_timer_le_one
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h_no_swap hOdd h_i_med hv_no_med hv_max h_i_res_raw
      by_cases hTimer0 : (D i).1.timer = 0
      · exact CRS_from_odd_trace hn0 hRmax hS hij h_i_med hOdd
          (propagation_reset_fires_no_swap_trace hFix hS.toInSrank hij h_i_med hv_no_med
            hTimer0 h_no_swap hOdd h_ans_diff)
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      · have hTimer1 : (D i).1.timer = 1 := by omega
        exact CRS_from_odd_trace hn0 hRmax hS hij h_i_med hOdd
          (propagation_reset_fires_no_swap_max_timer_one_trace hFix hS.toInSrank hn4 hij h_i_med
            hv_max hTimer1 h_no_swap hOdd h_ans_diff)
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    · -- j NOT max rank: timer = 0
      have hTimer0 := transitionPEM_fst_resetting_s0_med_no_max_odd_timer_zero
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h_no_swap hOdd h_i_med hv_no_med hv_max h_i_res_raw
      exact CRS_from_odd_trace hn0 hRmax hS hij h_i_med hOdd
        (propagation_reset_fires_no_swap_trace hFix hS.toInSrank hij h_i_med hv_no_med
          hTimer0 h_no_swap hOdd h_ans_diff)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · -- j is the median agent: symmetric trace lemmas (responder at median)
    have hi_no_med : (D i).1.rank.val + 1 ≠ ceilHalf n :=
      fun h => hrij (Fin.ext (Nat.add_right_cancel (h.trans h_j_med.symm)))
    have h_ans_diff := transitionPEM_fst_resetting_s1_med_odd_answer_diff
      (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
      hFix hsi hsj hrij h_no_swap hOdd hi_no_med h_j_med h_i_res_raw
    by_cases hi_max : (D i).1.rank.val + 1 = n
    · -- i max rank: timer ≤ 1
      have h_tl := transitionPEM_fst_resetting_s1_med_max_odd_timer_le_one
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h_no_swap hOdd hi_no_med h_j_med hi_max h_i_res_raw
      by_cases hTimer0 : (D j).1.timer = 0
      · exact CRS_from_odd_trace_responder_median hn0 hRmax hS hij h_j_med hOdd
          (propagation_reset_fires_no_swap_responder_median_trace hFix hS.toInSrank hij h_j_med hi_no_med
            hTimer0 h_no_swap hOdd h_ans_diff)
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      · have hTimer1 : (D j).1.timer = 1 := by omega
        exact CRS_from_odd_trace_responder_median hn0 hRmax hS hij h_j_med hOdd
          (propagation_reset_fires_no_swap_responder_median_max_timer_one_trace hFix hS.toInSrank hn4 hij h_j_med
            hi_max hTimer1 h_no_swap hOdd h_ans_diff)
          (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    · -- i NOT max rank: timer = 0
      have hTimer0 := transitionPEM_fst_resetting_s1_med_no_max_odd_timer_zero
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h_no_swap hOdd hi_no_med h_j_med hi_max h_i_res_raw
      exact CRS_from_odd_trace_responder_median hn0 hRmax hS hij h_j_med hOdd
        (propagation_reset_fires_no_swap_responder_median_trace hFix hS.toInSrank hij h_j_med hi_no_med
          hTimer0 h_no_swap hOdd h_ans_diff)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

/-! ### Main theorem: odd InSswap break → CorrectResetSeed -/

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem step_InSswap_break_creates_CorrectResetSeed_odd
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    (hOdd : n % 2 ≠ 0)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · exfalso; apply hS'; subst hij; simp [Config.step]; exact hS
  have hsi : (D i).1.role = .Settled := hS.toInSrank.allSettled i
  have hsj : (D j).1.role = .Settled := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  have hP_δ : ∀ p, P.δ p = transitionPEM n Rmax Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn0) p := fun _ => rfl
  have h_fst := Config.step_fst_state P D hij
  have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
  have hRoles := transitionPEM_role_settled_or_resetting_of_InSswap
    (trank := Rmax) (Rmax := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
    hFix hsi hsj hrij
  have h_role_i : (D.step P i j i).1.role = .Settled ∨
      (D.step P i j i).1.role = .Resetting := by
    rw [congrArg AgentState.role h_fst, hP_δ]; exact hRoles.1
  have h_role_j : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    rw [congrArg AgentState.role h_snd, hP_δ]; exact hRoles.2
  rcases h_role_i with h_i_set | h_i_res
  · rcases h_role_j with h_j_set | h_j_res
    · exfalso; apply hS'
      exact InSswap_preserved_of_output_settled hn0 hS hij h_i_set h_j_set
    · exfalso
      have h_snd_res : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).2.role = .Resetting := by
        rw [← hP_δ, ← congrArg AgentState.role h_snd]; exact h_j_res
      have h_fst_res := transitionPEM_snd_resetting_implies_fst_of_InSswap
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h_snd_res
      have h_i_set' : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).1.role = .Settled := by
        rw [← hP_δ, ← congrArg AgentState.role h_fst]; exact h_i_set
      rw [h_fst_res] at h_i_set'; exact Role.noConfusion h_i_set'
  · have h_i_res' : (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D i, D j)).1.role = .Resetting := by
      rw [← hP_δ, ← congrArg AgentState.role h_fst]; exact h_i_res
    have h_snd_res := transitionPEM_fst_resetting_implies_snd_of_InSswap
      (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
      hFix hsi hsj hrij h_i_res'
    have h_j_res : (D.step P i j j).1.role = .Resetting := by
      rw [congrArg AgentState.role h_snd, hP_δ]; exact h_snd_res
    exact CRS_of_both_resetting_odd hn4 hn0 hRmax hS hOdd hij h_i_res h_j_res

end SSEM

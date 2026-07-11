import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time

namespace SSEM

private theorem correctResetSeed_step_even_lower_timer_one_max_wrong
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    CorrectResetSeed
      (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hsnap :
      (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
        (C' μ).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
        h_no_swap h_post_diff)
  have htr :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v) =
        ({ (C μ).1 with
            timer := 0, role := .Resetting, leader := .L,
            resetcount := Rmax },
         { (C v).1 with
            role := .Resetting, leader := .L, resetcount := Rmax,
            answer := (C μ).1.answer }) := by
    simpa using
      (propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
        h_no_swap h_post_diff)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hfst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v)).1.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v)).2.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          rw [hsnap.1] at hx_not
          exact hx_not rfl
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      unfold nonResettingCount
      rw [← hS]
      omega
    have hn_pos : 0 < n := by omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
    omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  change CorrectResetSeed C'
  refine ⟨⟨μ, hsnap.1, ?_, hsnap.2.2.1, hμ_ans'⟩, ?_⟩
  · rw [hsnap.2.1]
    exact hN_bound
  · intro w hw
    by_cases hwμ : w = μ
    · subst w
      refine ⟨?_, hμ_ans'⟩
      rw [hsnap.2.1]
      exact hRmax_pos
    · by_cases hwv : w = v
      · subst w
        refine ⟨?_, hv_ans'⟩
        rw [hsnap.2.2.2.2.1]
        exact hRmax_pos
      · have hOldSettled : (C' w).1.role = .Settled := by
          dsimp [C', P]
          simp [Config.step, hμv, hwμ, hwv, hC.allSettled w]
        rw [hOldSettled] at hw
        cases hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 64000000 in
private theorem correctResetSeed_step_even_max_lower_timer_one_wrong
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hpar : n % 2 = 0)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    CorrectResetSeed
      (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) v μ) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let C' : Config (AgentState n) Opinion n := C.step P v μ
  have h_no_swap :
      ¬ ((C v).1.rank < (C μ).1.rank ∧
        (C v).2 = Opinion.B ∧ (C μ).2 = Opinion.A) := by
    intro h
    have hlt : (C v).1.rank.val < (C μ).1.rank.val := h.1
    omega
  have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hv_settled : (C v).1.role = .Settled := hC.toInSrank.allSettled v
  have hμ_settled : (C μ).1.role = .Settled := hC.toInSrank.allSettled μ
  have h_rank_ne : (C v).1.rank ≠ (C μ).1.rank := by
    intro hEq
    exact hvμ (hC.toInSrank.ranks_inj hEq)
  have hRD : rankDeltaOSSR Rmax Emax Dmax hn0 ((C v).1, (C μ).1) =
      ((C v).1, (C μ).1) :=
    rankDeltaOSSR_satisfies_fix
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      (C v).1 (C μ).1 hv_settled hμ_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    exact ceilHalf_eq_half_of_even hpar
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have h_dec1 :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧
          (C μ).1.rank.val + 1 = n / 2 + 1) := by
    intro h
    omega
  have h_dec2 :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧
          (C v).1.rank.val + 1 = n / 2 + 1) := by
    intro h
    exact hv_not_upper h.2
  have htr :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ) =
        ({ (C v).1 with
            answer := (C μ).1.answer, role := .Resetting, leader := .L,
            resetcount := Rmax },
         { (C μ).1 with
            timer := 0, role := .Resetting, leader := .L,
            resetcount := Rmax }) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hv_settled, hμ_settled, ne_eq,
      role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false, and_self, if_true, h_no_swap,
      hpar, h_dec1, h_dec2, hv_not_ceil, hμ_ceil, hv_max, h_timer,
      h_post_diff]
    split_ifs <;> simp_all
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C v μ)
  have hfst := Config.step_fst_state P C hvμ
  have hsnd := Config.step_snd_state P C hvμ hvμ.symm
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.role hfst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).1.role = .Resetting
    rw [htr]
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.role hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.resetcount hfst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).1.resetcount = Rmax
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.resetcount hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).2.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.leader hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).2.leader = .L
    rw [htr]
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).2.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hfst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C v, C μ)).1.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          rw [hμ_role] at hx_not
          exact hx_not rfl
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      unfold nonResettingCount
      rw [← hS]
      omega
    have hn_pos : 0 < n := by omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
    omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  change CorrectResetSeed C'
  refine ⟨⟨μ, hμ_role, ?_, hμ_leader, hμ_ans'⟩, ?_⟩
  · rw [hμ_rc]
    exact hN_bound
  · intro w hw
    by_cases hwμ : w = μ
    · subst w
      refine ⟨?_, hμ_ans'⟩
      rw [hμ_rc]
      exact hRmax_pos
    · by_cases hwv : w = v
      · subst w
        refine ⟨?_, hv_ans'⟩
        rw [hv_rc]
        exact hRmax_pos
      · have hOldSettled : (C' w).1.role = .Settled := by
          dsimp [C', P]
          simp [Config.step, hvμ, hwv, hwμ, hC.allSettled w]
        rw [hOldSettled] at hw
        cases hw

/-- For even n with MedianAnswerCorrect and timer > 0, when InSswap breaks,
CorrectResetSeed holds. Timer was 1, partner at rank-n. Phase4_decide
doesn't fire (pair ≠ (n/2,n/2+1)). Median answer unchanged (correct from
MedC). Propagation fires with correct answer → CRS. -/
set_option maxHeartbeats 64000000 in
theorem step_InSswap_break_even_MedC_timer_pos
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    (hEven : n % 2 = 0)
    {μ' : Fin n} (hTimerPos : (D μ').1.timer ≠ 0)
    (hμ'_med : (D μ').1.rank.val + 1 = ceilHalf n)
    {i j : Fin n}
    (hS' : ¬ InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    CorrectResetSeed (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  have hT : MedianTimerAtLeast 1 D := by
    intro μ'' hμ''_med
    have : μ'' = μ' := hS.toInSrank.ranks_inj (Fin.ext (by omega))
    subst this; omega
  exact step_InSswap_break_creates_CorrectResetSeed_even_timer_pos hn4 hn0 hRmax hS hM hEven hT hS'

end SSEM

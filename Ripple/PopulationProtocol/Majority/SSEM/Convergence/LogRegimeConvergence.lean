import Ripple.PopulationProtocol.Majority.SSEM.Convergence.LogTreeReset

namespace SSEM

variable {τ : ℕ}

set_option maxHeartbeats 4000000 in
theorem transitionPEM_dormant_dt_decrease_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧ (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧ (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0 ∧
    (C' w).1.delaytimer = (C w).1.delaytimer - 1 ∧ (C' w).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_dt_decrease
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_F hℓ_dt hw_dt
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.delaytimer h_fst]
    exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem transitionPEM_dormant_leader_low_dt_wakes_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : (C ℓ).1.delaytimer ≤ 1) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank = ⟨0, hn⟩ ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    ((C' w).1.role = .Unsettled ∨
      ((C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rcases h_rd.2.2.2.2 with hw_unsettled | hw_reset
    · rw [hw_unsettled] at hboth
      exact Role.noConfusion hboth.2
    · rw [hw_reset.1] at hboth
      exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact h_pass.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.children h_fst]
    exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rcases h_rd.2.2.2.2 with hw_unsettled | hw_reset
    · exact Or.inl (by
        rw [congrArg AgentState.role h_snd]
        exact h_pass.2.2.2.2.2.2.1 ▸ hw_unsettled)
    · exact Or.inr ⟨by
        rw [congrArg AgentState.role h_snd]
        exact h_pass.2.2.2.2.2.2.1 ▸ hw_reset.1, by
        rw [congrArg AgentState.resetcount h_snd]
        exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ hw_reset.2⟩

theorem transitionPEM_dormant_leader_low_dt_follower_leader_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : (C ℓ).1.delaytimer ≤ 1) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' w).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_leader_low_dt_follower_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_role := rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rcases h_role.2.2.2.2 with hw_unsettled | hw_reset
    · rw [hw_unsettled] at hboth
      exact Role.noConfusion hboth.2
    · rw [hw_reset.1] at hboth
      exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  change (Config.step P C ℓ w w).1.leader = .F
  rw [congrArg AgentState.leader h_snd]
  exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd

theorem transitionPEM_dormant_follower_low_dt_unsettles_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_dt : (C w).1.delaytimer ≤ 1) (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧
    (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Unsettled ∧
    (C' w).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_follower_low_dt_unsettles
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_dt hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.delaytimer h_fst]
    exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

theorem transitionPEM_dormant_leader_with_unsettled_follower_wakes_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_unsettled : (C w).1.role = .Unsettled) (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank = ⟨0, hn⟩ ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Unsettled ∧
    (C' w).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_leader_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_res hℓ_rc hℓ_L (by rw [hw_unsettled]; decide)
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    have hw_role :
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Unsettled := by
      rw [h_rd.2.2.2.2]
      exact hw_unsettled
    rw [hw_role] at hboth
    exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact h_pass.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.children h_fst]
    exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    change
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ, C w)).1.leader = .L
    rw [h_pass.2.1, h_rd.2.2.2.1]
    exact hℓ_L
  · rw [congrArg AgentState.role h_snd]
    change
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ, C w)).2.role = .Unsettled
    rw [h_pass.2.2.2.2.2.2.1, h_rd.2.2.2.2]
    exact hw_unsettled
  · rw [congrArg AgentState.leader h_snd]
    change
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ, C w)).2.leader = .F
    rw [h_pass.2.2.2.2.2.2.2.1, h_rd.2.2.2.2]
    exact hw_F

theorem transitionPEM_settled_meets_dormant_trace_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (_hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank.val = 0 ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Unsettled ∧
    (C' w).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_settled_meets_dormant
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_settled hw_res hw_rc hw_F
  have h_rd_leader := rankDeltaOSSR_settled_meets_dormant_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_settled hw_res hw_rc hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩
    rw [h_rd.2] at h2
    exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
    rw [h_pass.1, congrArg AgentState.role h_rd.1]
    exact hℓ_settled
  · rw [congrArg AgentState.rank h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
    rw [h_pass.2.2.1, congrArg AgentState.rank h_rd.1]
    exact hℓ_rank0
  · rw [congrArg AgentState.children h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.children = 0
    rw [h_pass.2.2.2.1, congrArg AgentState.children h_rd.1]
    exact hℓ_children
  · rw [congrArg AgentState.leader h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.leader = .L
    rw [h_pass.2.1, congrArg AgentState.leader h_rd.1]
    exact hℓ_L
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd_leader

theorem step_dormant_dt_decrease_preserves_uniform_answer_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (ha_role : (C a).1.role = .Resetting)
    (ha_rc : (C a).1.resetcount = 0)
    (hb_role : (C b).1.role = .Resetting)
    (hb_rc : (C b).1.resetcount = 0)
    (ha_L : (C a).1.leader = .L)
    (hb_F : (C b).1.leader = .F)
    (ha_dt : 1 < (C a).1.delaytimer)
    (hb_dt : 1 < (C b).1.delaytimer) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) a b) w).1.answer = m := by
  exact
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm hab hAllM
      (by rintro ⟨_, ha_not⟩; exact ha_not ha_role)
      (by rintro ⟨_, hb_not⟩; exact hb_not hb_role)
      (rankDeltaOSSR_dormant_dt_decrease_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        ha_role ha_rc hb_role hb_rc ha_L hb_F ha_dt hb_dt)

theorem step_dormant_leader_low_dt_preserves_uniform_answer_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (ha_role : (C a).1.role = .Resetting)
    (ha_rc : (C a).1.resetcount = 0)
    (ha_dt : (C a).1.delaytimer ≤ 1)
    (ha_L : (C a).1.leader = .L)
    (hb_role : (C b).1.role = .Resetting)
    (hb_rc : (C b).1.resetcount = 0)
    (hb_F : (C b).1.leader = .F) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) a b) w).1.answer = m := by
  exact
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm hab hAllM
      (by rintro ⟨_, ha_not⟩; exact ha_not ha_role)
      (by rintro ⟨_, hb_not⟩; exact hb_not hb_role)
      (rankDeltaOSSR_dormant_leader_low_dt_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        ha_role ha_rc ha_dt ha_L hb_role hb_rc hb_F)

theorem step_dormant_follower_low_dt_preserves_uniform_answer_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (ha_role : (C a).1.role = .Resetting)
    (ha_rc : (C a).1.resetcount = 0)
    (ha_dt : 1 < (C a).1.delaytimer)
    (ha_L : (C a).1.leader = .L)
    (hb_role : (C b).1.role = .Resetting)
    (hb_rc : (C b).1.resetcount = 0)
    (hb_dt : (C b).1.delaytimer ≤ 1)
    (hb_F : (C b).1.leader = .F) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) a b) w).1.answer = m := by
  exact
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm hab hAllM
      (by rintro ⟨_, ha_not⟩; exact ha_not ha_role)
      (by rintro ⟨_, hb_not⟩; exact hb_not hb_role)
      (rankDeltaOSSR_dormant_follower_low_dt_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        ha_role ha_rc ha_dt ha_L hb_role hb_rc hb_dt hb_F)

theorem step_settled_meets_dormant_preserves_uniform_answer_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (ha_settled : (C a).1.role = .Settled)
    (hb_role : (C b).1.role = .Resetting)
    (hb_rc : (C b).1.resetcount = 0)
    (hb_F : (C b).1.leader = .F) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) a b) w).1.answer = m := by
  exact
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm hab hAllM
      (by
        rintro ⟨ha_reset, _ha_not⟩
        have h := rankDeltaOSSR_settled_meets_dormant
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          ha_settled hb_role hb_rc hb_F
        rw [h.1] at ha_reset
        rw [ha_settled] at ha_reset
        exact Role.noConfusion ha_reset)
      (by rintro ⟨_, hb_not⟩; exact hb_not hb_role)
      (rankDeltaOSSR_settled_meets_dormant_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        ha_settled hb_role hb_rc hb_F)

theorem step_dormant_leader_unsettled_preserves_uniform_answer_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (ha_role : (C a).1.role = .Resetting)
    (ha_rc : (C a).1.resetcount = 0)
    (ha_L : (C a).1.leader = .L)
    (hb_unsettled : (C b).1.role = .Unsettled) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) a b) w).1.answer = m := by
  have hb_not_res : (C b).1.role ≠ .Resetting := by
    rw [hb_unsettled]
    decide
  have hb_not_settled : (C b).1.role ≠ .Settled := by
    rw [hb_unsettled]
    decide
  exact
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm hab hAllM
      (by rintro ⟨_, ha_not⟩; exact ha_not ha_role)
      (by
        rintro ⟨hb_reset, _hb_not⟩
        have h := rankDeltaOSSR_dormant_leader_wakes
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          ha_role ha_rc ha_L hb_not_res
        rw [h.2.2.2.2] at hb_reset
        exact hb_not_res hb_reset)
      (rankDeltaOSSR_dormant_leader_wakes_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        ha_role ha_rc ha_L hb_not_res hb_not_settled)

/-!
This file records the log-regime rethreading audit facts that can be
discharged from the current public interfaces.

The new logarithmic reset theorem needs an explicit lower bound on the
seed's reset fuel.  The existing epidemic seed package `CorrectResetSeed`
only exposes `nonResettingCount C < resetcount`; its callers know the reset
step wrote `Rmax`, but that fact is erased before re-entry.  Consequently the
capstone log theorem cannot be obtained by a wrapper around the existing
chain without strengthening the seed-or-progress interface.
-/

set_option maxHeartbeats 8000000 in
/-- Explicit log-fueled seed reaches the all-fresh reset state. -/
theorem log_seed_to_all_fresh
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (hRlog : Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hseed :
      ∃ r : Fin n,
        (C r).1.role = .Resetting ∧ Rmax ≤ (C r).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, FreshResettingAt Dmax C' w := by
  exact
    all_fresh_from_log_seed_unconditional
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (R := Rmax)
      (hn := hn) hDmax hn2 hRlog C hseed

set_option maxHeartbeats 12000000 in
/-- Log-fueled answer-faithful reset growth reaches the existing Phase-A
bridge without the old linear `nonResettingCount < resetcount` budget.

This is the usable downstream bridge from the balanced-tree construction:
Phase A produces an all-`Resetting`, positive-resetcount configuration with
uniform majority answer and a surviving leader, then the proven positive
all-resetting bridge performs the standard dormant/ranking normalization. -/
theorem log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) (hDmax : 1 < Dmax) (hDmax_n : n ≤ Dmax)
    (hRmax : 0 < Rmax)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : Nat.clog 2 n + 1 ≤ (C r).1.resetcount)
    (hr_L : (C r).1.leader = .L)
    (hm₀ : m₀ = majorityAnswer C)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      ResAns m₀ C' ∧
      (∀ w : Fin n, (C' w).1.answer ≠ .phi) ∧
      majorityAnswer C' = majorityAnswer C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨Lgrow, hAllFloor, hAnsGrow, hLeaderGrow⟩ :=
    balanced_tree_growth_floor_answer_leader
      (τ := Rmax) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (d := 1) (hn := hn)
      hDmax (by omega : 0 < 1) C r hr_role hr_log hr_L hAllAns
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lgrow
  have hMaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, hP] using
      majorityAnswer_runPairs_eq
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) C Lgrow
  have hm₁ : m₀ = majorityAnswer C₁ := by
    rw [hMaj₁]
    exact hm₀
  have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
    intro w
    simpa [C₁, hP] using (hAllFloor w).1
  have hAllPos₁ : ∀ w : Fin n, 0 < (C₁ w).1.resetcount := by
    intro w
    have hw : 1 ≤ (C₁ w).1.resetcount := by
      simpa [C₁, hP] using (hAllFloor w).2
    omega
  have hUniform₁ : ∀ w : Fin n, (C₁ w).1.answer = m₀ := by
    intro w
    have hw : (C₁ w).1.answer = majorityAnswer C₁ := by
      simpa [C₁, hP] using hAnsGrow w (by
        simpa [C₁, hP] using hAllReset₁ w)
    rw [← hm₁] at hw
    exact hw
  have hHasL₁ : ∃ ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
    ⟨r, by simpa [C₁, hP] using hLeaderGrow⟩
  obtain ⟨Ltail, hFresh, hRes, hNoPhi, hMajTail⟩ :=
    all_resetting_pos_with_leader_uniform_to_FreshRankingStart_resAns_noPhi
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := m₀) hn4 hRmax hDmax_n
      (C := C₁) hAllReset₁ hAllPos₁ hHasL₁ hm₁ hUniform₁
  refine ⟨Lgrow ++ Ltail, ?_, ?_, ?_, ?_⟩
  · rw [runPairs_append]
    exact hFresh
  · rw [runPairs_append]
    exact hRes
  · rw [runPairs_append]
    exact hNoPhi
  · rw [runPairs_append]
    rw [hMajTail]
    exact hMaj₁

/-- The role component exposed by an all-fresh endpoint. -/
theorem all_resetting_of_all_fresh
    {Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w) :
    ∀ w : Fin n, (C w).1.role = .Resetting := by
  intro w
  exact (hFresh w).1

/-- The resetcount-zero component exposed by an all-fresh endpoint. -/
theorem all_resetcount_zero_of_all_fresh
    {Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w) :
    ∀ w : Fin n, (C w).1.resetcount = 0 := by
  intro w
  exact (hFresh w).2.1

/-- The delaytimer component exposed by an all-fresh endpoint. -/
theorem all_delaytimer_eq_of_all_fresh
    {Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w) :
    ∀ w : Fin n, (C w).1.delaytimer = Dmax := by
  intro w
  exact (hFresh w).2.2

set_option maxHeartbeats 12000000 in
theorem phase3bc_from_awakening_uniform_answer_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi) (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      (∀ w : Fin n, (C' w).1.answer = m) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  suffices sweep :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        IsAwakeningConfig C₀ →
        (∀ w : Fin n, (C₀ w).1.answer = m) →
        (awakeningResettingFollowers C₀).card = k →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          FreshRankingStart C' ∧
          (∀ w : Fin n, (C' w).1.answer = m) by
    simpa [hP] using
      sweep (awakeningResettingFollowers C).card C hAwake hAllM rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hAwake₀ hAllM₀ hcard
    rcases hAwake₀ with ⟨hUnique, hLeaderOK, hFollowerOK⟩
    obtain ⟨root, hroot_L, hroot_unique⟩ := hUnique
    by_cases hk0 : k = 0
    · refine ⟨[], ?_, ?_⟩
      · simp only [runPairs_nil]
        have hroot_ok := hLeaderOK root hroot_L
        refine ⟨root, hroot_ok.1, hroot_ok.2.1, hroot_ok.2.2, ?_⟩
        intro w hw_ne_root
        have hw_F : (C₀ w).1.leader = .F := by
          cases hw_leader : (C₀ w).1.leader with
          | L =>
              have hw_eq : w = root := hroot_unique w hw_leader
              exact False.elim (hw_ne_root hw_eq)
          | F => rfl
        rcases hFollowerOK w hw_F with hw_un | hw_res
        · exact hw_un
        · exfalso
          have hw_bad : w ∈ awakeningResettingFollowers C₀ := by
            dsimp [awakeningResettingFollowers]
            simp [hw_F, hw_res.1]
          have hpos : 0 < (awakeningResettingFollowers C₀).card :=
            Finset.card_pos.mpr ⟨w, hw_bad⟩
          omega
      · simpa using hAllM₀
    · have hpos : 0 < (awakeningResettingFollowers C₀).card := by
        rw [hcard]
        omega
      obtain ⟨w, hw_bad⟩ := Finset.card_pos.mp hpos
      have hw_F : (C₀ w).1.leader = .F :=
        (Finset.mem_filter.mp hw_bad).2.1
      have hw_res : (C₀ w).1.role = .Resetting :=
        (Finset.mem_filter.mp hw_bad).2.2
      have hw_rc : (C₀ w).1.resetcount = 0 := by
        rcases hFollowerOK w hw_F with hw_un | hw_reset
        · rw [hw_un] at hw_res
          cases hw_res
        · exact hw_reset.2
      have hroot_ne_w : root ≠ w := by
        intro hrw
        subst w
        rw [hroot_L] at hw_F
        cases hw_F
      let C₁ : Config (AgentState n) Opinion n := C₀.step P root w
      have hroot_ok := hLeaderOK root hroot_L
      have htrace := by
        simpa [P, C₁] using
          (transitionPEM_settled_meets_dormant_trace_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := root) (w := w) hroot_ne_w
            hroot_ok.1 hroot_ok.2.1 hroot_ok.2.2 hroot_L
            hw_res hw_rc hw_F)
      have hOthers : ∀ x : Fin n, x ≠ root → x ≠ w → C₁ x = C₀ x := by
        intro x hxroot hxw
        dsimp [C₁]
        simp [Config.step, hroot_ne_w, hxroot, hxw]
      have hAwake₁ : IsAwakeningConfig C₁ := by
        refine ⟨?_, ?_, ?_⟩
        · refine ⟨root, htrace.2.2.2.1, ?_⟩
          intro y hyL
          by_cases hyroot : y = root
          · exact hyroot
          · by_cases hyw : y = w
            · subst y
              rw [htrace.2.2.2.2.2] at hyL
              cases hyL
            · have hy_old : (C₀ y).1.leader = .L := by
                have hxy := hOthers y hyroot hyw
                rw [hxy] at hyL
                exact hyL
              exact hroot_unique y hy_old
        · intro y hyL
          have hyroot : y = root := by
            by_cases hyroot : y = root
            · exact hyroot
            · by_cases hyw : y = w
              · subst y
                rw [htrace.2.2.2.2.2] at hyL
                cases hyL
              · have hy_old : (C₀ y).1.leader = .L := by
                  have hxy := hOthers y hyroot hyw
                  rw [hxy] at hyL
                  exact hyL
                exact hroot_unique y hy_old
          subst y
          exact ⟨htrace.1, htrace.2.1, htrace.2.2.1⟩
        · intro y hyF
          by_cases hyroot : y = root
          · subst y
            rw [htrace.2.2.2.1] at hyF
            cases hyF
          · by_cases hyw : y = w
            · subst y
              exact Or.inl htrace.2.2.2.2.1
            · have hyF_old : (C₀ y).1.leader = .F := by
                have hxy := hOthers y hyroot hyw
                rw [hxy] at hyF
                exact hyF
              have hy_ok := hFollowerOK y hyF_old
              rw [hOthers y hyroot hyw]
              exact hy_ok
      have hAllM₁ : ∀ x : Fin n, (C₁ x).1.answer = m := by
        simpa [C₁, hP] using
          (step_settled_meets_dormant_preserves_uniform_answer_trank
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (a := root) (b := w)
            hm hroot_ne_w hAllM₀ hroot_ok.1 hw_res hw_rc hw_F)
      have hsubset :
          awakeningResettingFollowers C₁ ⊆
            (awakeningResettingFollowers C₀).erase w := by
        intro x hx
        have hxF : (C₁ x).1.leader = .F := (Finset.mem_filter.mp hx).2.1
        have hxR : (C₁ x).1.role = .Resetting := (Finset.mem_filter.mp hx).2.2
        have hx_ne_w : x ≠ w := by
          intro hxw
          subst x
          rw [htrace.2.2.2.2.1] at hxR
          cases hxR
        have hx_ne_root : x ≠ root := by
          intro hxroot
          subst x
          rw [htrace.1] at hxR
          cases hxR
        have hx_old_state := hOthers x hx_ne_root hx_ne_w
        have hx_old : x ∈ awakeningResettingFollowers C₀ := by
          dsimp [awakeningResettingFollowers]
          rw [hx_old_state] at hxF hxR
          simp [hxF, hxR]
        exact Finset.mem_erase.mpr ⟨hx_ne_w, hx_old⟩
      have hcard_lt : (awakeningResettingFollowers C₁).card < k := by
        have hle := Finset.card_le_card hsubset
        have herase : ((awakeningResettingFollowers C₀).erase w).card =
            (awakeningResettingFollowers C₀).card - 1 :=
          Finset.card_erase_of_mem hw_bad
        rw [herase, hcard] at hle
        omega
      obtain ⟨Ltail, hFreshTail, hAllTail⟩ :=
        IH (awakeningResettingFollowers C₁).card hcard_lt
          C₁ hAwake₁ hAllM₁ rfl
      refine ⟨[(root, w)] ++ Ltail, ?_, ?_⟩
      · rw [runPairs_append]
        change FreshRankingStart (runPairs P C₁ Ltail)
        exact hFreshTail
      · rw [runPairs_append]
        change ∀ x : Fin n, (runPairs P C₁ Ltail x).1.answer = m
        exact hAllTail

set_option maxHeartbeats 16000000 in
theorem phase3a_to_awakening_uniform_answer_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      IsAwakeningConfig C' ∧
      (∀ w : Fin n, (C' w).1.answer = m) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  rcases hDormant with ⟨hAllR₀, hAllRc0₀, hUnique₀, hLeaderCases₀⟩
  obtain ⟨ℓ, hℓ_L₀, hℓ_unique₀⟩ := hUnique₀
  have hne_of_fin (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  obtain ⟨w, hw_ne_ℓ⟩ := hne_of_fin ℓ
  have hℓw : ℓ ≠ w := hw_ne_ℓ.symm
  have hw_F₀ : (C w).1.leader = .F := by
    cases hw_leader : (C w).1.leader with
    | L =>
        have hw_eq : w = ℓ := hℓ_unique₀ w hw_leader
        exact False.elim (hw_ne_ℓ hw_eq)
    | F => rfl
  have hDormant₀ : IsDormantConfig C :=
    ⟨hAllR₀, hAllRc0₀, ⟨ℓ, hℓ_L₀, hℓ_unique₀⟩, hLeaderCases₀⟩
  suffices wake :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        IsDormantConfig C₀ →
        (C₀ ℓ).1.leader = .L →
        (C₀ w).1.leader = .F →
        (∀ x : Fin n, (C₀ x).1.answer = m) →
        (C₀ ℓ).1.delaytimer ≤ k →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          IsAwakeningConfig C' ∧
          (∀ x : Fin n, (C' x).1.answer = m) by
    simpa [hP] using
      wake (C ℓ).1.delaytimer C hDormant₀ hℓ_L₀ hw_F₀ hAllM le_rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hDorm hℓ_L hw_F hAllM₀ hdt_le
    rcases hDorm with ⟨hAllR, hAllRc0, hUnique, hLeaderCases⟩
    have hUnique_saved : ∃! x : Fin n, (C₀ x).1.leader = .L := hUnique
    obtain ⟨oldℓ, _holdℓ_L, hOldUnique⟩ := hUnique
    by_cases hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1
    · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
      have hstep := by
        simpa [P] using
          (transitionPEM_dormant_leader_low_dt_wakes_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAllRc0 ℓ) hℓ_low hℓ_L
            (hAllR w) (hAllRc0 w) hw_F)
      have hw_leader₁ : (C₁ w).1.leader = .F := by
        simpa [C₁, P] using
          (transitionPEM_dormant_leader_low_dt_follower_leader_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAllRc0 ℓ) hℓ_low hℓ_L
            (hAllR w) (hAllRc0 w) hw_F)
      have hOthers₁ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₁ x = C₀ x := by
        intro x hxℓ hxw
        dsimp [C₁]
        simp [Config.step, hℓw, hxℓ, hxw]
      have hAllM₁ : ∀ x : Fin n, (C₁ x).1.answer = m := by
        simpa [C₁, hP] using
          (step_dormant_leader_low_dt_preserves_uniform_answer_trank
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (a := ℓ) (b := w)
            hm hℓw hAllM₀ (hAllR ℓ) (hAllRc0 ℓ) hℓ_low hℓ_L
            (hAllR w) (hAllRc0 w) hw_F)
      refine ⟨[(ℓ, w)], ?_, ?_⟩
      · change IsAwakeningConfig C₁
        exact awakening_of_pair_trace
          (C := C₀) (C' := C₁) (ℓ := ℓ) (w := w)
          ⟨hAllR, hAllRc0, hUnique_saved, hLeaderCases⟩ hℓw hℓ_L
          hstep.2.2.2.1 hstep.1 (congrArg Fin.val hstep.2.1)
          hstep.2.2.1 hw_leader₁ hstep.2.2.2.2 hOthers₁
      · exact hAllM₁
    · have hℓ_high : 1 < (C₀ ℓ).1.delaytimer := by omega
      by_cases hw_low : (C₀ w).1.delaytimer ≤ 1
      · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        let C₂ : Config (AgentState n) Opinion n := C₁.step P ℓ w
        have hstep₁ := by
          simpa [P] using
            (transitionPEM_dormant_follower_low_dt_unsettles_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAllRc0 ℓ) hℓ_high hℓ_L
              (hAllR w) (hAllRc0 w) hw_low hw_F)
        have hAllM₁ : ∀ x : Fin n, (C₁ x).1.answer = m := by
          simpa [C₁, hP] using
            (step_dormant_follower_low_dt_preserves_uniform_answer_trank
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (a := ℓ) (b := w)
              hm hℓw hAllM₀ (hAllR ℓ) (hAllRc0 ℓ) hℓ_high hℓ_L
              (hAllR w) (hAllRc0 w) hw_low hw_F)
        have hstep₂ := by
          simpa [P, C₁] using
            (transitionPEM_dormant_leader_with_unsettled_follower_wakes_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (ℓ := ℓ) (w := w) hℓw
              hstep₁.1 hstep₁.2.1 hstep₁.2.2.2.1
              hstep₁.2.2.2.2.1 hstep₁.2.2.2.2.2)
        have hAllM₂ : ∀ x : Fin n, (C₂ x).1.answer = m := by
          simpa [C₂, hP] using
            (step_dormant_leader_unsettled_preserves_uniform_answer_trank
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (a := ℓ) (b := w)
              hm hℓw hAllM₁ hstep₁.1 hstep₁.2.1
              hstep₁.2.2.2.1 hstep₁.2.2.2.2.1)
        have hOthers₂ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₂ x = C₀ x := by
          intro x hxℓ hxw
          dsimp [C₂, C₁]
          simp [Config.step, hℓw, hxℓ, hxw]
        refine ⟨[(ℓ, w), (ℓ, w)], ?_, ?_⟩
        · change IsAwakeningConfig C₂
          exact awakening_of_pair_trace
            (C := C₀) (C' := C₂) (ℓ := ℓ) (w := w)
            ⟨hAllR, hAllRc0, hUnique_saved, hLeaderCases⟩ hℓw hℓ_L
            hstep₂.2.2.2.1 hstep₂.1 (congrArg Fin.val hstep₂.2.1)
            hstep₂.2.2.1 hstep₂.2.2.2.2.2
            (Or.inl hstep₂.2.2.2.2.1) hOthers₂
        · exact hAllM₂
      · have hw_high : 1 < (C₀ w).1.delaytimer := by omega
        let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        have hstep := by
          simpa [P] using
            (transitionPEM_dormant_dt_decrease_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAllRc0 ℓ) hℓ_L
              (hAllR w) (hAllRc0 w) hw_F hℓ_high hw_high)
        have hAllM₁ : ∀ x : Fin n, (C₁ x).1.answer = m := by
          simpa [C₁, hP] using
            (step_dormant_dt_decrease_preserves_uniform_answer_trank
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (a := ℓ) (b := w)
              hm hℓw hAllM₀ (hAllR ℓ) (hAllRc0 ℓ)
              (hAllR w) (hAllRc0 w) hℓ_L hw_F hℓ_high hw_high)
        have hOthers₁ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₁ x = C₀ x := by
          intro x hxℓ hxw
          dsimp [C₁]
          simp [Config.step, hℓw, hxℓ, hxw]
        have hAllR₁ : ∀ x : Fin n, (C₁ x).1.role = .Resetting := by
          intro x
          by_cases hxℓ : x = ℓ
          · subst x
            exact hstep.1
          · by_cases hxw : x = w
            · subst x
              exact hstep.2.2.2.2.1
            · rw [hOthers₁ x hxℓ hxw]
              exact hAllR x
        have hAllRc0₁ : ∀ x : Fin n, (C₁ x).1.resetcount = 0 := by
          intro x
          by_cases hxℓ : x = ℓ
          · subst x
            exact hstep.2.1
          · by_cases hxw : x = w
            · subst x
              exact hstep.2.2.2.2.2.1
            · rw [hOthers₁ x hxℓ hxw]
              exact hAllRc0 x
        have hUnique₁ : ∃! x : Fin n, (C₁ x).1.leader = .L := by
          refine ⟨ℓ, hstep.2.2.2.1, ?_⟩
          intro x hxL
          by_cases hxℓ : x = ℓ
          · exact hxℓ
          · by_cases hxw : x = w
            · subst x
              rw [hstep.2.2.2.2.2.2.2] at hxL
              cases hxL
            · have hx_old : (C₀ x).1.leader = .L := by
                rw [hOthers₁ x hxℓ hxw] at hxL
                exact hxL
              have hx_old_eq : x = oldℓ := hOldUnique x hx_old
              have hℓ_old_eq : ℓ = oldℓ := hOldUnique ℓ hℓ_L
              exact hx_old_eq.trans hℓ_old_eq.symm
        have hDorm₁ : IsDormantConfig C₁ := by
          refine ⟨hAllR₁, hAllRc0₁, hUnique₁, ?_⟩
          intro x
          cases (C₁ x).1.leader <;> simp
        have hm_lt : (C₁ ℓ).1.delaytimer < k := by
          rw [hstep.2.2.1]
          omega
        obtain ⟨Ltail, hAwakeTail, hAllTail⟩ :=
          IH (C₁ ℓ).1.delaytimer hm_lt C₁ hDorm₁
            hstep.2.2.2.1 hstep.2.2.2.2.2.2.2
            hAllM₁ le_rfl
        refine ⟨[(ℓ, w)] ++ Ltail, ?_, ?_⟩
        · rw [runPairs_append]
          change IsAwakeningConfig (runPairs P C₁ Ltail)
          exact hAwakeTail
        · rw [runPairs_append]
          change ∀ x : Fin n, (runPairs P C₁ Ltail x).1.answer = m
          exact hAllTail

theorem dormant_to_FreshRankingStart_uniform_answer_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      (∀ w : Fin n, (C' w).1.answer = m) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨L₁, hAwake, hAll₁⟩ :=
    phase3a_to_awakening_uniform_answer_trank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m := m) hm hn4 hRmax hDmax C hDormant hAllM
  set C₁ : Config (AgentState n) Opinion n := runPairs P C L₁ with hC₁def
  obtain ⟨L₂, hFresh, hAll₂⟩ :=
    phase3bc_from_awakening_uniform_answer_trank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m := m) hm hn4 C₁
      (by simpa [C₁, hP] using hAwake)
      (by simpa [C₁, hP] using hAll₁)
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · rw [runPairs_append]
    simpa [C₁, hP] using hFresh
  · rw [runPairs_append]
    simpa [C₁, hP] using hAll₂

theorem dormant_uniform_to_FreshRankingStart_resAns_noPhi_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hDormant : IsDormantConfig C)
    (hm₀ : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      ResAns m₀ C' ∧
      (∀ w : Fin n, (C' w).1.answer ≠ .phi) ∧
      majorityAnswer C' = majorityAnswer C := by
  classical
  have hm_ne_phi : m₀ ≠ .phi := by
    rw [hm₀]
    exact majorityAnswer_ne_phi C
  obtain ⟨L, hFresh, hAllM⟩ :=
    dormant_to_FreshRankingStart_uniform_answer_trank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m := m₀) hm_ne_phi hn4 hRmax hDmax C hDormant hUniform
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · exact hFresh
  · intro w
    exact Or.inl (hAllM w)
  · intro w
    rw [hAllM w]
    exact hm_ne_phi
  · exact majorityAnswer_runPairs_eq_trank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) C L

theorem all_resetting_zero_unique_uniform_to_FreshRankingStart_resAns_noPhi_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllRc0 : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L)
    (hm₀ : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      ResAns m₀ C' ∧
      (∀ w : Fin n, (C' w).1.answer ≠ .phi) ∧
      majorityAnswer C' = majorityAnswer C := by
  have hDormant : IsDormantConfig C := by
    refine ⟨hAllReset, hAllRc0, hUniqueLeader, ?_⟩
    intro w
    cases (C w).1.leader <;> simp
  exact
    dormant_uniform_to_FreshRankingStart_resAns_noPhi_trank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax hDormant hm₀ hUniform

set_option maxHeartbeats 8000000 in
/-- Once the missing answer and unique-leader facts are supplied, the fresh
state enters the existing answer-preserving Phase-A bridge with only
`0 < Dmax`; the old `n <= Dmax` positive-resetcount budget is not used. -/
theorem fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L)
    (hm₀ : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      ResAns m₀ C' ∧
      (∀ w : Fin n, (C' w).1.answer ≠ .phi) ∧
      majorityAnswer C' = majorityAnswer C := by
  exact
    all_resetting_zero_unique_uniform_to_FreshRankingStart_resAns_noPhi_trank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := m₀) hn4 hRmax hDmax
      (all_resetting_of_all_fresh hFresh)
      (all_resetcount_zero_of_all_fresh hFresh)
      hUniqueLeader hm₀ hUniform

set_option maxHeartbeats 12000000 in
/-- Log-fueled answer-faithful reset growth reaches the fresh bridge without
any linear `n <= Dmax`, `n <= Rmax`, or `n <= Emax` carrier.  The fuel
constant is `2 * clog2 n + 2`: `clog2 n` for balanced growth, `clog2 n`
for the fueled leader tournament, and `2` for the final mutual drain. -/
theorem log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) (hDmax : 1 < Dmax)
    (hRmax : 0 < Rmax)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : 2 * Nat.clog 2 n + 2 ≤ (C r).1.resetcount)
    (hr_L : (C r).1.leader = .L)
    (hm₀ : m₀ = majorityAnswer C)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      FreshRankingStart C' ∧
      ResAns m₀ C' ∧
      (∀ w : Fin n, (C' w).1.answer ≠ .phi) ∧
      majorityAnswer C' = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨Lfresh, hFresh, hUniformMaj, hUnique, hMajFresh⟩ :=
    all_fresh_uniform_unique_from_log_seed
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (by omega : 2 ≤ n) C r hr_role hr_log hr_L hAllAns
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lfresh
  have hFresh₁ : ∀ w : Fin n, FreshResettingAt Dmax C₁ w := by
    simpa [C₁, hP] using hFresh
  have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L := by
    simpa [C₁, hP] using hUnique
  have hMaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, hP] using hMajFresh
  have hm₁ : m₀ = majorityAnswer C₁ := by
    rw [hMaj₁]
    exact hm₀
  have hUniform₁ : ∀ w : Fin n, (C₁ w).1.answer = m₀ := by
    intro w
    have hw : (C₁ w).1.answer = majorityAnswer C₁ := by
      simpa [C₁, hP] using hUniformMaj w
    rw [← hm₁] at hw
    exact hw
  obtain ⟨Ltail, hFreshStart, hRes, hNoPhi, hMajTail⟩ :=
    fresh_uniform_unique_to_FreshRankingStart_resAns_noPhi
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := m₀) hn4 hRmax (by omega : 0 < Dmax)
      (C := C₁) hFresh₁ hUnique₁ hm₁ hUniform₁
  refine ⟨Lfresh ++ Ltail, ?_, ?_, ?_, ?_⟩
  · rw [runPairs_append]
    exact hFreshStart
  · rw [runPairs_append]
    exact hRes
  · rw [runPairs_append]
    exact hNoPhi
  · rw [runPairs_append]
    rw [hMajTail]
    exact hMaj₁

end SSEM

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.LogRegimeConvergence
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BCFTrank
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.GenericTrank

namespace SSEM

variable {τ : ℕ}

set_option maxHeartbeats 20000000

/- ===== AUTO-GENERATED trank clones (Opus) v3 ===== -/

set_option maxHeartbeats 64000000 in
theorem transitionPEM_both_dormant_followers_dt_decrease_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : 1 < (C u).1.delaytimer) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.delaytimer = (C u).1.delaytimer - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.delaytimer = (C v).1.delaytimer - 1 ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_both_dormant_followers_dt_decrease
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
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

theorem both_dormant_followers_dt_step_followerDormantMeasure_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : 1 < (C u).1.delaytimer) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u v) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_both_dormant_followers_dt_decrease_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv
        hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    have hdelay_eq : (C u).1.delaytimer - 1 + 1 = (C u).1.delaytimer := by
      omega
    unfold followerDormantContribution
    rw [hstep.1, hstep.2.2.1, hu_res]
    simp [hdelay_eq]
  have hv_lt :
      followerDormantContribution (C' v).1 <
        followerDormantContribution (C v).1 := by
    have hdelay_eq : (C v).1.delaytimer - 1 + 1 = (C v).1.delaytimer := by
      omega
    unfold followerDormantContribution
    rw [hstep.2.2.2.2.1, hstep.2.2.2.2.2.2.1, hv_res]
    simp [hdelay_eq]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxv : x = v
      · subst x
        exact le_of_lt hv_lt
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hxu, hxv]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 64000000 in

set_option maxHeartbeats 64000000 in
theorem transitionPEM_both_dormant_followers_low_dt_unsettle_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : (C v).1.delaytimer ≤ 1) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Unsettled ∧ (C' v).1.role = .Unsettled := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_both_dormant_followers_low_dt
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2

theorem both_dormant_followers_low_dt_step_followerDormantMeasure_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : (C v).1.delaytimer ≤ 1) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u v) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_both_dormant_followers_low_dt_unsettle_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hv_le :
      followerDormantContribution (C' v).1 ≤
        followerDormantContribution (C v).1 := by
    unfold followerDormantContribution
    rw [hstep.2, hv_res]
    simp
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxv : x = v
      · subst x
        exact hv_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hxu, hxv]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 200000000 in

theorem transitionPEM_dormant_follower_with_nonresetting_partner_wakes_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u w
    (C' u).1.role = .Unsettled ∧
    (C' u).1.leader = .F ∧
    (C' w).1.role = (C w).1.role := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_follower_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hu_rc hu_F hw_not_reset
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C huw
  have h_snd := Config.step_snd_state P C huw huw.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.1
  · rw [h_snd]
    change
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C u, C w)).2.role = (C w).1.role
    rw [h_pass.2.2.2.2.2.2.1]
    exact congrArg AgentState.role h_rd.2.2

theorem dormant_follower_nonresetting_step_followerDormantMeasure_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u w) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u w
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_follower_with_nonresetting_partner_wakes_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w) huw hu_res hu_rc hu_F hw_not_reset)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hw_le :
      followerDormantContribution (C' w).1 ≤
        followerDormantContribution (C w).1 := by
    unfold followerDormantContribution
    rw [hstep.2.2]
    simp [hw_not_reset]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxw : x = w
      · subst x
        exact hw_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huw, hxu, hxw]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 64000000 in

theorem dormant_follower_step_resetFuel_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resetFuel (C.step P u w) < resetFuel C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u w
  have hstep :
      (C₁ u).1.role = .Unsettled ∧
      (C₁ u).1.leader = .F ∧
      (C₁ w).1.role = (C w).1.role := by
    simpa [P, C₁] using
      (transitionPEM_dormant_follower_with_nonresetting_partner_wakes_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w)
        huw hu_res hu_rc hu_F hw_not_reset)
  -- Package `nonResettingCount + contribution` into one per-agent summand.
  let g : Config (AgentState n) Opinion n → Fin n → ℕ :=
    fun D x =>
      (if (D x).1.role ≠ .Resetting then (1 : ℕ) else 0) +
        resetFuelContribution (D x).1
  have hFuel_as_sum :
      ∀ D : Config (AgentState n) Opinion n,
        resetFuel D = ∑ x : Fin n, g D x := by
    intro D
    have hN :
        nonResettingCount D =
          ∑ x : Fin n,
            (if (D x).1.role ≠ .Resetting then (1 : ℕ) else 0) := by
      unfold nonResettingCount
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    unfold resetFuel
    rw [hN]
    dsimp [g]
    rw [← Finset.sum_add_distrib]
  have hg_u_new : g C₁ u = 1 := by
    dsimp [g]
    simp [resetFuelContribution, hstep.1]
  have hg_u_old : g C u = 2 := by
    dsimp [g]
    simp [resetFuelContribution, hu_res, hu_rc]
  have hg_w_eq : g C₁ w = g C w := by
    dsimp [g, resetFuelContribution]
    rw [hstep.2.2]
    simp [hw_not_reset]
  have hothers :
      ∀ x : Fin n, x ≠ u → x ≠ w → C₁ x = C x := by
    intro x hxu hxw
    dsimp [C₁, P]
    simp [Config.step, huw, hxu, hxw]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)), g C₁ x ≤ g C x := by
    intro x _
    by_cases hxu : x = u
    · subst x
      rw [hg_u_new, hg_u_old]
      omega
    · by_cases hxw : x = w
      · subst x
        rw [hg_w_eq]
      · have hx_state : C₁ x = C x := hothers x hxu hxw
        dsimp [g]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)), g C₁ x < g C x := by
    refine ⟨u, Finset.mem_univ u, ?_⟩
    rw [hg_u_new, hg_u_old]
    omega
  change resetFuel C₁ < resetFuel C
  calc
    resetFuel C₁ = ∑ x : Fin n, g C₁ x := hFuel_as_sum C₁
    _ < ∑ x : Fin n, g C x :=
      Finset.sum_lt_sum hpointwise hstrict
    _ = resetFuel C := (hFuel_as_sum C).symm

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_follower_with_unsettled_partner_wakes_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_unsettled : (C w).1.role = .Unsettled) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u w
    (C' u).1.role = .Unsettled ∧
    (C' u).1.leader = .F ∧
    (C' w).1.role = .Unsettled := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_follower_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hu_rc hu_F (by rw [hw_unsettled]; decide)
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C huw
  have h_snd := Config.step_snd_state P C huw huw.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.role h_snd]
    change
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C u, C w)).2.role = .Unsettled
    rw [h_pass.2.2.2.2.2.2.1, h_rd.2.2]
    exact hw_unsettled

theorem dormant_follower_unsettled_step_followerDormantMeasure_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_unsettled : (C w).1.role = .Unsettled) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u w) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u w
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_follower_with_unsettled_partner_wakes_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w) huw hu_res hu_rc hu_F hw_unsettled)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hw_le :
      followerDormantContribution (C' w).1 ≤
        followerDormantContribution (C w).1 := by
    unfold followerDormantContribution
    rw [hstep.2.2, hw_unsettled]
    simp
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxw : x = w
      · subst x
        exact hw_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huw, hxu, hxw]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_followers_low_high_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Unsettled ∧
    (C' u).1.leader = .F ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.delaytimer = (C v).1.delaytimer - 1 ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_dormant_follower_low_high
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

theorem dormant_followers_low_high_step_followerDormantMeasure_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u v) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_followers_low_high_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv
        hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hv_le :
      followerDormantContribution (C' v).1 ≤
        followerDormantContribution (C v).1 := by
    have hdelay_eq : (C v).1.delaytimer - 1 + 1 = (C v).1.delaytimer := by
      omega
    unfold followerDormantContribution
    rw [hstep.2.2.1, hstep.2.2.2.2.1, hv_res]
    simp [hdelay_eq]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxv : x = v
      · subst x
        exact hv_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hxu, hxv]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

/-- trank-generalized `transitionPEM_prePhase4_dormant_leader_roles`: the
`trank` argument only feeds the Settled-timer and does not affect the roles. -/
theorem transitionPEM_prePhase4_dormant_leader_roles_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs_res : s.role = .Resetting)
    (hs_rc : s.resetcount = 0)
    (hs_L : s.leader = .L)
    (ht_not_res : t.role ≠ .Resetting) :
    let pre := transitionPEM_prePhase4 n τ
                (rankDeltaOSSR Rmax Emax Dmax hn) s t x y
    pre.1.role = .Settled ∧ pre.2.role = t.role := by
  have h_rd := rankDeltaOSSR_dormant_leader_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs_res hs_rc hs_L ht_not_res
  have h_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  refine ⟨?_, ?_⟩
  · show (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) s t x y).1.role
         = .Settled
    rw [h_struct.1, h_rd.1]
  · show (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) s t x y).2.role
         = t.role
    rw [h_struct.2.2.2.2.2.2.1]
    have h₂ : (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2 = t := h_rd.2.2.2.2
    exact congrArg AgentState.role h₂

set_option maxHeartbeats 8000000 in
/-- trank-generalized `transitionPEM_dormant_leader_nonresetting_bounce_or_nonresetting`.
The `trank` argument only feeds the Settled-timer; the wake/bounce disjunction
on roles/resetcount/leader is `trank`-independent. -/
theorem transitionPEM_dormant_leader_nonresetting_bounce_or_nonresetting_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs_res : s.role = .Resetting)
    (hs_rc : s.resetcount = 0)
    (hs_L : s.leader = .L)
    (ht_not_res : t.role ≠ .Resetting) :
    let out :=
      transitionPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) ((s, x), (t, y))
    (out.1.role ≠ .Resetting ∧ out.2.role ≠ .Resetting) ∨
    ((out.1.role = .Resetting ∧
        out.1.resetcount = Rmax ∧
        out.1.leader = .L) ∧
     (out.2.role = .Resetting ∧
        out.2.resetcount = Rmax ∧
        out.2.leader = .L)) := by
  classical
  have h_pre := transitionPEM_prePhase4_dormant_leader_roles_trank
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (s := s) (t := t) (x := x) (y := y)
    hs_res hs_rc hs_L ht_not_res
  by_cases ht_settled : t.role = .Settled
  · have hpre0 : (transitionPEM_prePhase4 n τ
                    (rankDeltaOSSR Rmax Emax Dmax hn) s t x y).1.role = .Settled := h_pre.1
    have hpre1 : (transitionPEM_prePhase4 n τ
                    (rankDeltaOSSR Rmax Emax Dmax hn) s t x y).2.role = .Settled := by
      rw [h_pre.2]; exact ht_settled
    have hphase :=
      transitionPEM_phase4_settled_pair (Rmax := Rmax)
        (a₀ := (transitionPEM_prePhase4 n τ
                  (rankDeltaOSSR Rmax Emax Dmax hn) s t x y).1)
        (a₁ := (transitionPEM_prePhase4 n τ
                  (rankDeltaOSSR Rmax Emax Dmax hn) s t x y).2)
        (x₀ := x) (x₁ := y) hpre0 hpre1
    show
      (let out := transitionPEM n τ Rmax
                    (rankDeltaOSSR Rmax Emax Dmax hn) ((s, x), (t, y))
       (out.1.role ≠ .Resetting ∧ out.2.role ≠ .Resetting) ∨
       ((out.1.role = .Resetting ∧ out.1.resetcount = Rmax ∧ out.1.leader = .L) ∧
        (out.2.role = .Resetting ∧ out.2.resetcount = Rmax ∧ out.2.leader = .L)))
    unfold transitionPEM
    exact hphase
  · have ht_unsettled : t.role = .Unsettled := by
      cases ht_role : t.role with
      | Resetting => exact absurd ht_role ht_not_res
      | Settled   => exact absurd ht_role ht_settled
      | Unsettled => rfl
    have h_rd := rankDeltaOSSR_dormant_leader_wakes
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hs_res hs_rc hs_L ht_not_res
    have h_not_both :
        ¬ ((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
            (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled) := by
      intro hboth
      have h₂ : (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2 = t := h_rd.2.2.2.2
      have : (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled := by
        rw [congrArg AgentState.role h₂]; exact ht_unsettled
      rw [this] at hboth
      exact Role.noConfusion hboth.2
    have h_pass := transitionPEM_structural_passthrough
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (x₀ := x) (x₁ := y) h_not_both
    left
    refine ⟨?_, ?_⟩
    · show (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              ((s, x), (t, y))).1.role ≠ .Resetting
      rw [h_pass.1, h_rd.1]; decide
    · show (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              ((s, x), (t, y))).2.role ≠ .Resetting
      rw [h_pass.2.2.2.2.2.2.1]
      have h₂ : (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2 = t := h_rd.2.2.2.2
      rw [congrArg AgentState.role h₂, ht_unsettled]
      decide

theorem dormant_leader_nonresetting_step_resetFuel_lt_or_seed_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C₁ := C.step P u w
    resetFuel C₁ < resetFuel C ∨
    ∃ r : Fin n,
      (C₁ r).1.role = .Resetting ∧
      (C₁ r).1.resetcount = Rmax ∧
      (C₁ r).1.leader = .L := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C₁ : Config (AgentState n) Opinion n := C.step P u w
  have h_trace :=
    transitionPEM_dormant_leader_nonresetting_bounce_or_nonresetting_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C u).1) (t := (C w).1) (x := (C u).2) (y := (C w).2)
      hu_res hu_rc hu_L hw_not_reset
  have h_fst := Config.step_fst_state P C huw
  have h_snd := Config.step_snd_state P C huw huw.symm
  rcases h_trace with h_no | h_bounce
  · -- Clean wake: both u and w end non-Resetting. Fuel argument identical
    -- to F-leader: at u, contribution drops 2 → 1 (count indicator +1, weight
    -- 2^1=2 removed); w's indicator stays 1 and contribution stays 0.
    left
    have hu_after_not_reset : (C₁ u).1.role ≠ .Resetting := by
      dsimp [C₁]
      rw [congrArg AgentState.role h_fst]; exact h_no.1
    have hw_after_not_reset : (C₁ w).1.role ≠ .Resetting := by
      dsimp [C₁]
      rw [congrArg AgentState.role h_snd]; exact h_no.2
    -- Package g = indicator + contribution, identical to F-leader.
    let g : Config (AgentState n) Opinion n → Fin n → ℕ := fun D x =>
      (if (D x).1.role ≠ .Resetting then (1 : ℕ) else 0) +
        resetFuelContribution (D x).1
    have hFuel_as_sum :
        ∀ D : Config (AgentState n) Opinion n,
          resetFuel D = ∑ x : Fin n, g D x := by
      intro D
      have hN : nonResettingCount D = ∑ x : Fin n,
                  (if (D x).1.role ≠ .Resetting then (1 : ℕ) else 0) := by
        unfold nonResettingCount
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      unfold resetFuel; rw [hN]; dsimp [g]
      rw [← Finset.sum_add_distrib]
    have hg_u_new : g C₁ u = 1 := by
      dsimp [g]
      rw [if_pos hu_after_not_reset]
      have : ¬ ((C₁ u).1.role = .Resetting) := hu_after_not_reset
      simp [resetFuelContribution, this]
    have hg_u_old : g C u = 2 := by
      dsimp [g]
      simp [resetFuelContribution, hu_res, hu_rc]
    have hg_w_new : g C₁ w = 1 := by
      dsimp [g]
      rw [if_pos hw_after_not_reset]
      have : ¬ ((C₁ w).1.role = .Resetting) := hw_after_not_reset
      simp [resetFuelContribution, this]
    have hg_w_old : g C w = 1 := by
      dsimp [g]
      rw [if_pos hw_not_reset]
      have : ¬ ((C w).1.role = .Resetting) := hw_not_reset
      simp [resetFuelContribution, this]
    have hothers : ∀ x : Fin n, x ≠ u → x ≠ w → C₁ x = C x := by
      intro x hxu hxw
      dsimp [C₁, P]
      simp [Config.step, huw, hxu, hxw]
    have hpointwise :
        ∀ x ∈ (Finset.univ : Finset (Fin n)), g C₁ x ≤ g C x := by
      intro x _
      by_cases hxu : x = u
      · subst x; rw [hg_u_new, hg_u_old]; omega
      · by_cases hxw : x = w
        · subst x; rw [hg_w_new, hg_w_old]
        · have hx_state : C₁ x = C x := hothers x hxu hxw
          dsimp [g]; rw [hx_state]
    have hstrict :
        ∃ x ∈ (Finset.univ : Finset (Fin n)), g C₁ x < g C x := by
      refine ⟨u, Finset.mem_univ u, ?_⟩
      rw [hg_u_new, hg_u_old]; omega
    change resetFuel C₁ < resetFuel C
    calc
      resetFuel C₁ = ∑ x : Fin n, g C₁ x := hFuel_as_sum C₁
      _ < ∑ x : Fin n, g C x := Finset.sum_lt_sum hpointwise hstrict
      _ = resetFuel C := (hFuel_as_sum C).symm
  · -- Bounce: both u and w end up Resetting with rc=Rmax, leader=L.
    right
    refine ⟨u, ?_, ?_, ?_⟩
    · dsimp [C₁]
      rw [congrArg AgentState.role h_fst]; exact h_bounce.1.1
    · dsimp [C₁]
      rw [congrArg AgentState.resetcount h_fst]; exact h_bounce.1.2.1
    · dsimp [C₁]
      rw [congrArg AgentState.leader h_fst]; exact h_bounce.1.2.2

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_FF_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .F ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      (C' u).1.leader = .F → (C' v).1.leader = .F →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        (runPairs P C' L u).1.role = .Resetting ∧
        (runPairs P C' L u).1.resetcount = 0 ∧
        (runPairs P C' L u).1.leader = .F ∧
        (runPairs P C' L v).1.role = .Resetting ∧
        (runPairs P C' L v).1.resetcount = 0 ∧
        (runPairs P C' L v).1.leader = .F ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc hu_F hv_F le_rfl
  intro k
  induction k with
  | zero =>
    intros C' _ _ hu_rc' _ _ _ hmax
    exfalso
    have : (C' u).1.resetcount ≤ Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
      Nat.le_max_left _ _
    omega
  | succ k ih =>
    intros C' hu_res' hv_res' hu_rc' hv_rc' hu_F' hv_F' hmax
    have h_step := step_both_rc_pos_FF_trank (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hDmax C' huv hu_res' hv_res' hu_rc' hv_rc' hu_F' hv_F'
    have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
    have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
    have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.1
    have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.2.1
    have hu_F₁ : (C'.step P u v u).1.leader = .F := h_step.2.2.2.2.1
    have hv_F₁ : (C'.step P u v v).1.leader = .F := h_step.2.2.2.2.2
    have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
      intro w hwu hwv
      simp [Config.step, huv, hwu, hwv]
    have hM_le : Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount)
                  ≤ k := by
      have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
        have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
        have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hpred :
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
        max_le hu_pred_le hv_pred_le
      rw [hu_rc₁_eq, hv_rc₁_eq]
      exact max_le hpred hpred
    by_cases hdone :
        Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
    · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
        have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
        have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] u).1.leader = .F
        simp [runPairs]; exact hu_F₁
      · show (runPairs P C' [(u, v)] v).1.role = .Resetting
        simp [runPairs]; exact hv_role₁
      · show (runPairs P C' [(u, v)] v).1.resetcount = 0
        simp [runPairs]; exact hv_zero
      · show (runPairs P C' [(u, v)] v).1.leader = .F
        simp [runPairs]; exact hv_F₁
      · intro w hwu hwv
        show runPairs P C' [(u, v)] w = C' w
        simp [runPairs]; exact h_others w hwu hwv
    · have hu_rc₁ : 0 < (C'.step P u v u).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      have hv_rc₁ : 0 < (C'.step P u v v).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_F_t, hv_role_t, hv_rc_t, hv_F_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hu_F₁ hv_F₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.leader = .F
        simp [runPairs]; exact hu_F_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.role = .Resetting
        simp [runPairs]; exact hv_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.resetcount = 0
        simp [runPairs]; exact hv_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.leader = .F
        simp [runPairs]; exact hv_F_t
      · intro w hwu hwv
        rw [runPairs_append]
        change runPairs P (C'.step P u v) Ltail w = C' w
        rw [h_others_t w hwu hwv]
        exact h_others w hwu hwv

set_option maxHeartbeats 8000000 in

set_option maxHeartbeats 8000000 in
theorem drain_F_pos_F_zero_to_zero_FF_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .F ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_F_pos_F_zero_trank
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_F hv_F hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_F₁ : (C₁ u).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .F
      simp [runPairs, C₁, P]
      exact hu_F₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_F_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_FF_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_F₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .F
      simp [runPairs]
      exact hu_F_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

set_option maxHeartbeats 8000000 in

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_LF_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      (C' u).1.leader = .L → (C' v).1.leader = .F →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        (runPairs P C' L u).1.role = .Resetting ∧
        (runPairs P C' L u).1.resetcount = 0 ∧
        (runPairs P C' L u).1.leader = .L ∧
        (runPairs P C' L v).1.role = .Resetting ∧
        (runPairs P C' L v).1.resetcount = 0 ∧
        (runPairs P C' L v).1.leader = .F ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc hu_L hv_F le_rfl
  intro k
  induction k with
  | zero =>
    intros C' _ _ hu_rc' _ _ _ hmax
    exfalso
    have : (C' u).1.resetcount ≤ Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
      Nat.le_max_left _ _
    omega
  | succ k ih =>
    intros C' hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F' hmax
    have h_step := step_both_rc_pos_LF_trank (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hDmax C' huv hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F'
    have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
    have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
    have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.1
    have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.2.1
    have hu_L₁ : (C'.step P u v u).1.leader = .L := h_step.2.2.2.2.1
    have hv_F₁ : (C'.step P u v v).1.leader = .F := h_step.2.2.2.2.2
    have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
      intro w hwu hwv
      simp [Config.step, huv, hwu, hwv]
    have hM_le : Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount)
                  ≤ k := by
      have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
        have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
        have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hpred :
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
        max_le hu_pred_le hv_pred_le
      rw [hu_rc₁_eq, hv_rc₁_eq]
      exact max_le hpred hpred
    by_cases hdone :
        Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
    · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
        have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
        have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] u).1.leader = .L
        simp [runPairs]; exact hu_L₁
      · show (runPairs P C' [(u, v)] v).1.role = .Resetting
        simp [runPairs]; exact hv_role₁
      · show (runPairs P C' [(u, v)] v).1.resetcount = 0
        simp [runPairs]; exact hv_zero
      · show (runPairs P C' [(u, v)] v).1.leader = .F
        simp [runPairs]; exact hv_F₁
      · intro w hwu hwv
        show runPairs P C' [(u, v)] w = C' w
        simp [runPairs]; exact h_others w hwu hwv
    · have hu_rc₁ : 0 < (C'.step P u v u).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      have hv_rc₁ : 0 < (C'.step P u v v).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hu_L₁ hv_F₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.leader = .L
        simp [runPairs]; exact hu_L_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.role = .Resetting
        simp [runPairs]; exact hv_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.resetcount = 0
        simp [runPairs]; exact hv_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.leader = .F
        simp [runPairs]; exact hv_F_t
      · intro w hwu hwv
        rw [runPairs_append]
        change runPairs P (C'.step P u v) Ltail w = C' w
        rw [h_others_t w hwu hwv]
        exact h_others w hwu hwv

set_option maxHeartbeats 8000000 in

set_option maxHeartbeats 8000000 in
theorem drain_L_pos_F_zero_to_zero_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_L_pos_F_zero_trank
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_F hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2.1
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

set_option maxHeartbeats 8000000 in

set_option maxHeartbeats 4000000 in
theorem step_L_pos_L_zero_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' v).1.delaytimer =
      (if (C u).1.resetcount = 1 then (C v).1.delaytimer - 1 else (C v).1.delaytimer) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_L_zero_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_L hv_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 8000000 in
theorem drain_L_pos_L_zero_to_zero_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_L_pos_L_zero_trank
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_L hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2.1
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

theorem drain_L_pos_any_zero_to_zero_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      exact drain_L_pos_L_zero_to_zero_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hv_dt
  | F =>
      exact drain_L_pos_F_zero_to_zero_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hv_dt

set_option maxHeartbeats 8000000 in

theorem follower_clean_to_no_reset_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerClean C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, (C' w).1.role ≠ .Resetting := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hne_of_fin (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  suffices rec :
      ∀ m (C₀ : Config (AgentState n) Opinion n),
        followerDormantMeasure C₀ = m →
        FollowerClean C₀ →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          ∀ w : Fin n, (C' w).1.role ≠ .Resetting by
    exact rec (followerDormantMeasure C) C rfl hClean
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
      intro C₀ hm hClean₀
      by_cases hNoReset : ∀ w : Fin n, (C₀ w).1.role ≠ .Resetting
      · refine ⟨[], ?_⟩
        simpa using hNoReset
      · push_neg at hNoReset
        obtain ⟨u, hu_res⟩ := hNoReset
        have hu_fields : (C₀ u).1.resetcount = 0 ∧ (C₀ u).1.leader = .F := by
          rcases hClean₀ u with hreset | hun
          · exact ⟨hreset.2.1, hreset.2.2⟩
          · rw [hun] at hu_res
            cases hu_res
        by_cases hAllReset : ∀ w : Fin n, (C₀ w).1.role = .Resetting
        · obtain ⟨v, hv_ne_u⟩ := hne_of_fin u
          have huv : u ≠ v := hv_ne_u.symm
          have hv_res : (C₀ v).1.role = .Resetting := hAllReset v
          have hv_fields : (C₀ v).1.resetcount = 0 ∧ (C₀ v).1.leader = .F := by
            rcases hClean₀ v with hreset | hun
            · exact ⟨hreset.2.1, hreset.2.2⟩
            · rw [hun] at hv_res
              cases hv_res
          by_cases hu_low : (C₀ u).1.delaytimer ≤ 1
          · by_cases hv_low : (C₀ v).1.delaytimer ≤ 1
            · let C₁ : Config (AgentState n) Opinion n := C₀.step P u v
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_both_dormant_followers_low_dt_unsettle_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_low hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (both_dormant_followers_low_dt_step_followerDormantMeasure_lt_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_low hv_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxu : x = u
                · subst x
                  exact Or.inr hstep.1
                · by_cases hxv : x = v
                  · subst x
                    exact Or.inr hstep.2
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, huv, hxu, hxv]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(u, v)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
            · have hv_high : 1 < (C₀ v).1.delaytimer := by omega
              let C₁ : Config (AgentState n) Opinion n := C₀.step P u v
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_dormant_followers_low_high_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (dormant_followers_low_high_step_followerDormantMeasure_lt_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxu : x = u
                · subst x
                  exact Or.inr hstep.1
                · by_cases hxv : x = v
                  · subst x
                    exact Or.inl ⟨hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.2⟩
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, huv, hxu, hxv]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(u, v)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
          · have hu_high : 1 < (C₀ u).1.delaytimer := by omega
            by_cases hv_low : (C₀ v).1.delaytimer ≤ 1
            · let C₁ : Config (AgentState n) Opinion n := C₀.step P v u
              have hvu : v ≠ u := hv_ne_u
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_dormant_followers_low_high_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := v) (v := u) hvu
                    hv_res hv_fields.1 hv_low hv_fields.2
                    hu_res hu_fields.1 hu_high hu_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (dormant_followers_low_high_step_followerDormantMeasure_lt_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := v) (v := u) hvu
                    hv_res hv_fields.1 hv_low hv_fields.2
                    hu_res hu_fields.1 hu_high hu_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxv : x = v
                · subst x
                  exact Or.inr hstep.1
                · by_cases hxu : x = u
                  · subst x
                    exact Or.inl ⟨hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.2⟩
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, hvu, hxv, hxu]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(v, u)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
            · have hv_high : 1 < (C₀ v).1.delaytimer := by omega
              let C₁ : Config (AgentState n) Opinion n := C₀.step P u v
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_both_dormant_followers_dt_decrease_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_high hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (both_dormant_followers_dt_step_followerDormantMeasure_lt_trank
                    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_high hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxu : x = u
                · subst x
                  exact Or.inl ⟨hstep.1, hstep.2.1, hstep.2.2.2.1⟩
                · by_cases hxv : x = v
                  · subst x
                    exact Or.inl ⟨hstep.2.2.2.2.1, hstep.2.2.2.2.2.1,
                      hstep.2.2.2.2.2.2.2⟩
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, huv, hxu, hxv]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(u, v)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
        · push_neg at hAllReset
          obtain ⟨w, hw_not_reset⟩ := hAllReset
          have hw_un : (C₀ w).1.role = .Unsettled := by
            rcases hClean₀ w with hreset | hun
            · exact False.elim (hw_not_reset hreset.1)
            · exact hun
          have huw : u ≠ w := by
            intro huw
            subst w
            exact hw_not_reset hu_res
          let C₁ : Config (AgentState n) Opinion n := C₀.step P u w
          have hstep := by
            simpa [P, C₁] using
              (transitionPEM_dormant_follower_with_unsettled_partner_wakes_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw
                hu_res hu_fields.1 hu_fields.2 hw_un)
          have hmeasure :
              followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
            simpa [P, C₁] using
              (dormant_follower_unsettled_step_followerDormantMeasure_lt_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw
                hu_res hu_fields.1 hu_fields.2 hw_un)
          have hClean₁ : FollowerClean C₁ := by
            intro x
            by_cases hxu : x = u
            · subst x
              exact Or.inr hstep.1
            · by_cases hxw : x = w
              · subst x
                exact Or.inr hstep.2.2
              · have hx_state : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, huw, hxu, hxw]
                rw [hx_state]
                exact hClean₀ x
          obtain ⟨Ltail, htail⟩ :=
            IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
          refine ⟨[(u, w)] ++ Ltail, ?_⟩
          rw [runPairs_append]
          change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
          exact htail

theorem follower_dormant_or_nonresetting_to_no_reset_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, (C' w).1.role ≠ .Resetting := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices rec :
      ∀ m (C₀ : Config (AgentState n) Opinion n),
        followerDormantMeasure C₀ = m →
        FollowerDormantOrNonResetting C₀ →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          ∀ w : Fin n, (C' w).1.role ≠ .Resetting by
    exact rec (followerDormantMeasure C) C rfl hClean
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
      intro C₀ hm hClean₀
      by_cases hNoReset : ∀ w : Fin n, (C₀ w).1.role ≠ .Resetting
      · refine ⟨[], ?_⟩
        simpa using hNoReset
      · push_neg at hNoReset
        obtain ⟨u, hu_res⟩ := hNoReset
        have hu_fields : (C₀ u).1.resetcount = 0 ∧ (C₀ u).1.leader = .F := by
          rcases hClean₀ u with hreset | hnot
          · exact ⟨hreset.2.1, hreset.2.2⟩
          · exact False.elim (hnot hu_res)
        by_cases hAllReset : ∀ w : Fin n, (C₀ w).1.role = .Resetting
        · have hFollower : FollowerClean C₀ := by
            intro x
            rcases hClean₀ x with hreset | hnot
            · exact Or.inl hreset
            · exact False.elim (hnot (hAllReset x))
          exact
            follower_clean_to_no_reset_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 C₀ hFollower
        · push_neg at hAllReset
          obtain ⟨w, hw_not_reset⟩ := hAllReset
          have huw : u ≠ w := by
            intro huw
            subst w
            exact hw_not_reset hu_res
          let C₁ : Config (AgentState n) Opinion n := C₀.step P u w
          have hstep := by
            simpa [P, C₁] using
              (transitionPEM_dormant_follower_with_nonresetting_partner_wakes_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw hu_res hu_fields.1 hu_fields.2
                hw_not_reset)
          have hmeasure :
              followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
            simpa [P, C₁] using
              (dormant_follower_nonresetting_step_followerDormantMeasure_lt_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw hu_res hu_fields.1 hu_fields.2
                hw_not_reset)
          have hClean₁ : FollowerDormantOrNonResetting C₁ := by
            intro x
            by_cases hxu : x = u
            · subst x
              exact Or.inr (by rw [hstep.1]; decide)
            · by_cases hxw : x = w
              · subst x
                exact Or.inr (by
                  rw [hstep.2.2]
                  exact hw_not_reset)
              · have hx_state : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, huw, hxu, hxw]
                rw [hx_state]
                exact hClean₀ x
          obtain ⟨Ltail, htail⟩ :=
            IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
          refine ⟨[(u, w)] ++ Ltail, ?_⟩
          rw [runPairs_append]
          change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
          exact htail

theorem propagate_reset_step_resetFuel_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resetFuel (C.step P r v) < resetFuel C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P r v
  have hpartner : (C₁ v).1.role = .Resetting ∧
                  (C₁ v).1.resetcount = (C r).1.resetcount - 1 := by
    simpa [P, C₁] using
      (propagate_reset_step_partner_rc_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
        C hrv hr_res hr_rc hv_not)
  have hsender : (C₁ r).1.role = .Resetting ∧
                 (C₁ r).1.resetcount = (C r).1.resetcount - 1 := by
    simpa [P, C₁] using
      (propagate_reset_step_sender_rc_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
        C hrv hr_res hr_rc hv_not)
  -- Per-agent summand packaging `nonResettingCount + resetFuelContribution`.
  let g : Config (AgentState n) Opinion n → Fin n → ℕ := fun D x =>
    (if (D x).1.role ≠ .Resetting then (1 : ℕ) else 0) +
      resetFuelContribution (D x).1
  have hFuel_as_sum :
      ∀ D : Config (AgentState n) Opinion n,
        resetFuel D = ∑ x : Fin n, g D x := by
    intro D
    have hN : nonResettingCount D = ∑ x : Fin n,
                (if (D x).1.role ≠ .Resetting then (1 : ℕ) else 0) := by
      unfold nonResettingCount
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    unfold resetFuel; rw [hN]; dsimp [g]
    rw [← Finset.sum_add_distrib]
  -- Split sum into r, v, and the unchanged tail.
  have hsum_decomp : ∀ D : Config (AgentState n) Opinion n,
      (∑ x : Fin n, g D x) =
        g D r + g D v +
          ∑ x ∈ ((Finset.univ : Finset (Fin n)).erase r).erase v, g D x := by
    intro D
    have hr_not_mem : r ∉ (Finset.univ : Finset (Fin n)).erase r := by
      simp
    have hv_mem : v ∈ (Finset.univ : Finset (Fin n)).erase r := by
      simp [hrv.symm]
    have hv_not_mem_tail :
        v ∉ ((Finset.univ : Finset (Fin n)).erase r).erase v := by
      simp
    calc
      (∑ x : Fin n, g D x)
          = ∑ x ∈ insert r ((Finset.univ : Finset (Fin n)).erase r),
              g D x := by
                rw [Finset.insert_erase (Finset.mem_univ r)]
      _ = g D r + ∑ x ∈ (Finset.univ : Finset (Fin n)).erase r, g D x := by
                rw [Finset.sum_insert hr_not_mem]
      _ = g D r +
            ∑ x ∈ insert v
                (((Finset.univ : Finset (Fin n)).erase r).erase v),
              g D x := by
                rw [Finset.insert_erase hv_mem]
      _ = g D r +
            (g D v +
              ∑ x ∈ (((Finset.univ : Finset (Fin n)).erase r).erase v),
                g D x) := by
                rw [Finset.sum_insert hv_not_mem_tail]
      _ = g D r + g D v +
            ∑ x ∈ (((Finset.univ : Finset (Fin n)).erase r).erase v),
              g D x := by rw [← add_assoc]
  have hsubadd : (C r).1.resetcount - 1 + 1 = (C r).1.resetcount := by omega
  have hg_r_old : g C r = 2 ^ ((C r).1.resetcount + 1) := by
    dsimp [g]
    simp [resetFuelContribution, hr_res]
  have hg_v_old : g C v = 1 := by
    dsimp [g]
    simp [resetFuelContribution, hv_not]
  have hg_r_new : g C₁ r = 2 ^ (C r).1.resetcount := by
    dsimp [g]
    simp [resetFuelContribution, hsender.1, hsender.2, hsubadd]
  have hg_v_new : g C₁ v = 2 ^ (C r).1.resetcount := by
    dsimp [g]
    simp [resetFuelContribution, hpartner.1, hpartner.2, hsubadd]
  have hpair : g C₁ r + g C₁ v + 1 = g C r + g C v := by
    rw [hg_r_new, hg_v_new, hg_r_old, hg_v_old, pow_succ]
    omega
  have hothers : ∀ x : Fin n, x ≠ r → x ≠ v → C₁ x = C x := by
    intro x hxr hxv
    dsimp [C₁, P]
    simp [Config.step, hrv, hxr, hxv]
  have htail_eq :
      (∑ x ∈ ((Finset.univ : Finset (Fin n)).erase r).erase v, g C₁ x) =
      (∑ x ∈ ((Finset.univ : Finset (Fin n)).erase r).erase v, g C x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx_ne_v : x ≠ v := (Finset.mem_erase.mp hx).1
    have hx_mem_er : x ∈ (Finset.univ : Finset (Fin n)).erase r :=
      (Finset.mem_erase.mp hx).2
    have hx_ne_r : x ≠ r := (Finset.mem_erase.mp hx_mem_er).1
    have hx_state : C₁ x = C x := hothers x hx_ne_r hx_ne_v
    dsimp [g]; rw [hx_state]
  have hsum_plus_one : (∑ x : Fin n, g C₁ x) + 1 = ∑ x : Fin n, g C x := by
    rw [hsum_decomp C₁, hsum_decomp C, htail_eq]
    omega
  change resetFuel C₁ < resetFuel C
  calc
    resetFuel C₁ = ∑ x : Fin n, g C₁ x := hFuel_as_sum C₁
    _ < ∑ x : Fin n, g C x := by omega
    _ = resetFuel C := (hFuel_as_sum C).symm

theorem ranking_goal_of_runPairs_ranking_goal_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {L : List (Fin n × Fin n)}
    (h :
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank
          (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t) ∧
        ((∀ μ : Fin n,
          (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t μ).1.rank.val + 1 = ceilHalf n →
          2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t μ).1.timer) ∨
         IsConsensusConfig
          (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t))) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨γ₁, t₁, hC₁⟩ :=
    exists_schedule_of_runPairs P C L
      (Goal := fun C' => C' = runPairs P C L)
      rfl
  obtain ⟨γ₂, t₂, hgoal⟩ := h
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  rw [execution_concat]
  rw [hC₁]
  simpa [P] using hgoal

theorem ranking_goal_of_step_ranking_goal_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (h :
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank
          (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t) ∧
        ((∀ μ : Fin n,
          (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t μ).1.rank.val + 1 = ceilHalf n →
          2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t μ).1.timer) ∨
         IsConsensusConfig
          (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t))) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨γ, t, hgoal⟩ := h
  refine ⟨concatScheduler (fun _ => (u, v)) 1 γ, 1 + t, ?_⟩
  rw [execution_concat]
  simpa [P] using hgoal

set_option maxHeartbeats 128000000 in

theorem transitionPEM_settled_meets_dormant_L_trace_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0)
    (hw_L : (C w).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank.val = 0 ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Settled ∧
    (C' w).1.rank.val = 0 ∧
    (C' w).1.children = 0 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let p :=
    transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
      (C ℓ).1 (C w).1 (C ℓ).2 (C w).2
  have h_rd :=
    rankDeltaOSSR_settled_meets_dormant_L_trace
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_settled hw_res hw_rc hw_L
  have hpre :=
    transitionPEM_prePhase4_structural
      (trank := τ)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C ℓ).1) (s₁ := (C w).1)
      (x₀ := (C ℓ).2) (x₁ := (C w).2)
  have hp₁_role : p.1.role = .Settled := by
    dsimp [p]
    rw [hpre.1, congrArg AgentState.role h_rd.1]
    exact hℓ_settled
  have hp₁_rank0 : p.1.rank.val = 0 := by
    dsimp [p]
    rw [hpre.2.2.1, congrArg AgentState.rank h_rd.1]
    exact hℓ_rank0
  have hp₁_children : p.1.children = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.1, congrArg AgentState.children h_rd.1]
    exact hℓ_children
  have hp₁_leader : p.1.leader = .L := by
    dsimp [p]
    rw [hpre.2.1, congrArg AgentState.leader h_rd.1]
    exact hℓ_L
  have hp₂_role : p.2.role = .Settled := by
    dsimp [p]
    rw [hpre.2.2.2.2.2.2.1]
    exact h_rd.2.1
  have hp₂_rank0 : p.2.rank.val = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.2.2.2.2.2.1, h_rd.2.2.1]
  have hp₂_children : p.2.children = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.2.2.2.2.2.2.1]
    exact h_rd.2.2.2
  have hphase :
      transitionPEM_phase4 n Rmax p (C ℓ).2 (C w).2 = p := by
    exact
      transitionPEM_phase4_rank0_pair_id
        (n := n) (Rmax := Rmax) hn4
        (a₀ := p.1) (a₁ := p.2)
        (x₀ := (C ℓ).2) (x₁ := (C w).2)
        hp₁_role hp₂_role hp₁_rank0 hp₂_rank0
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_role
  · rw [congrArg AgentState.rank h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_rank0
  · rw [congrArg AgentState.children h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.children = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_children
  · rw [congrArg AgentState.leader h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.leader = .L
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_leader
  · rw [congrArg AgentState.role h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.role = .Settled
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₂_role
  · rw [congrArg AgentState.rank h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.rank.val = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₂_rank0
  · rw [congrArg AgentState.children h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.children = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₂_children

theorem settled_root_dormant_step_resettingCount_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resettingCount (C.step P ℓ w) < resettingCount C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P ℓ w
  have hstep :
      (C' ℓ).1.role = .Settled ∧ (C' w).1.role ≠ .Resetting := by
    cases hw_leader : (C w).1.leader with
    | F =>
        have h :=
          transitionPEM_settled_meets_dormant_trace_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C) (ℓ := ℓ) (w := w) hℓw
            hℓ_settled hℓ_rank0 hℓ_children hℓ_L hw_res hw_rc hw_leader
        exact ⟨by simpa [C', P] using h.1, by
          intro hw_reset'
          have hw_unsettled : (C' w).1.role = .Unsettled := by
            simpa [C', P] using h.2.2.2.2.1
          rw [hw_unsettled] at hw_reset'
          cases hw_reset'⟩
    | L =>
        have h :=
          transitionPEM_settled_meets_dormant_L_trace_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C) (ℓ := ℓ) (w := w) hℓw
            hℓ_settled hℓ_rank0 hℓ_children hℓ_L hw_res hw_rc hw_leader
        exact ⟨by simpa [C', P] using h.1, by
          intro hw_reset'
          have hw_settled : (C' w).1.role = .Settled := by
            simpa [C', P] using h.2.2.2.2.1
          rw [hw_settled] at hw_reset'
          cases hw_reset'⟩
  set S := Finset.univ.filter (fun x : Fin n => (C x).1.role = .Resetting) with hS
  set S' := Finset.univ.filter (fun x : Fin n => (C' x).1.role = .Resetting) with hS'
  have hw_mem : w ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, hw_res⟩
  have hsub : S' ⊆ S.erase w := by
    intro x hx
    have hx_reset : (C' x).1.role = .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_w : x ≠ w := by
      intro hxw
      subst x
      exact hstep.2 hx_reset
    have hx_ne_ℓ : x ≠ ℓ := by
      intro hxℓ
      subst x
      rw [hstep.1] at hx_reset
      cases hx_reset
    have hx_old : C' x = C x := by
      dsimp [C', P]
      simp [Config.step, hℓw, hx_ne_ℓ, hx_ne_w]
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      rw [hx_old] at hx_reset
      exact ⟨Finset.mem_univ x, hx_reset⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_w, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase w).card := Finset.card_le_card hsub
  have herase : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hw_mem
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨w, hw_mem⟩
    omega
  have hS_card : S.card = resettingCount C := by
    rw [hS]
    rfl
  have hS'_card : S'.card = resettingCount C' := by
    rw [hS']
    rfl
  change resettingCount C' < resettingCount C
  simpa [hS_card, hS'_card] using hlt

set_option maxHeartbeats 64000000 in

set_option maxHeartbeats 64000000 in
theorem settled_root_zero_resetting_to_no_reset_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hResetZero : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount = 0) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      ∀ w : Fin n, (runPairs P C L w).1.role ≠ .Resetting := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        resettingCount C₀ = k →
        (C₀ ℓ).1.role = .Settled →
        (C₀ ℓ).1.rank.val = 0 →
        (C₀ ℓ).1.children = 0 →
        (C₀ ℓ).1.leader = .L →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting → (C₀ w).1.resetcount = 0) →
        ∃ L : List (Fin n × Fin n),
          ∀ w : Fin n, (runPairs P C₀ L w).1.role ≠ .Resetting by
    exact go (resettingCount C) C rfl hℓ_settled hℓ_rank0 hℓ_children hℓ_L hResetZero
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hk hroot_role hroot_rank hroot_children hroot_L hzero
    by_cases hk0 : k = 0
    · refine ⟨[], ?_⟩
      intro w hw_reset
      have hmem :
          w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role = .Resetting) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ w, hw_reset⟩
      have hcard_pos :
          0 < (Finset.univ.filter (fun x : Fin n => (C₀ x).1.role = .Resetting)).card :=
        Finset.card_pos.mpr ⟨w, hmem⟩
      unfold resettingCount at hk
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hcard_pos :
          0 < (Finset.univ.filter (fun x : Fin n => (C₀ x).1.role = .Resetting)).card := by
        unfold resettingCount at hk
        omega
      obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hcard_pos
      have hw_res : (C₀ w).1.role = .Resetting := by
        exact (Finset.mem_filter.mp hw_mem).2
      have hw_rc : (C₀ w).1.resetcount = 0 := hzero w hw_res
      have hℓw : ℓ ≠ w := by
        intro h
        subst w
        rw [hroot_role] at hw_res
        cases hw_res
      let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
      have hmeasure : resettingCount C₁ < resettingCount C₀ := by
        simpa [P, C₁] using
          (settled_root_dormant_step_resettingCount_lt_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
            hroot_role hroot_rank hroot_children hroot_L hw_res hw_rc)
      have hstep_root :
          (C₁ ℓ).1.role = .Settled ∧
          (C₁ ℓ).1.rank.val = 0 ∧
          (C₁ ℓ).1.children = 0 ∧
          (C₁ ℓ).1.leader = .L ∧
          (C₁ w).1.role ≠ .Resetting := by
        cases hw_leader : (C₀ w).1.leader with
        | F =>
            have h :=
              transitionPEM_settled_meets_dormant_trace_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
                hroot_role hroot_rank hroot_children hroot_L hw_res hw_rc hw_leader
            refine ⟨by simpa [C₁, P] using h.1,
              by simpa [C₁, P] using h.2.1,
              by simpa [C₁, P] using h.2.2.1,
              by simpa [C₁, P] using h.2.2.2.1, ?_⟩
            intro hw_reset'
            have hw_unsettled : (C₁ w).1.role = .Unsettled := by
              simpa [C₁, P] using h.2.2.2.2.1
            rw [hw_unsettled] at hw_reset'
            cases hw_reset'
        | L =>
            have h :=
              transitionPEM_settled_meets_dormant_L_trace_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
                hroot_role hroot_rank hroot_children hroot_L hw_res hw_rc hw_leader
            refine ⟨by simpa [C₁, P] using h.1,
              by simpa [C₁, P] using h.2.1,
              by simpa [C₁, P] using h.2.2.1,
              by simpa [C₁, P] using h.2.2.2.1, ?_⟩
            intro hw_reset'
            have hw_settled : (C₁ w).1.role = .Settled := by
              simpa [C₁, P] using h.2.2.2.2.1
            rw [hw_settled] at hw_reset'
            cases hw_reset'
      have hzero₁ :
          ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
        intro x hx_reset
        by_cases hxℓ : x = ℓ
        · subst x
          rw [hstep_root.1] at hx_reset
          cases hx_reset
        · by_cases hxw : x = w
          · subst x
            exact False.elim (hstep_root.2.2.2.2 hx_reset)
          · have hx_old : C₁ x = C₀ x := by
              dsimp [C₁, P]
              simp [Config.step, hℓw, hxℓ, hxw]
            have hx_old_reset : (C₀ x).1.role = .Resetting := by
              rw [← hx_old]
              exact hx_reset
            rw [hx_old]
            exact hzero x hx_old_reset
      obtain ⟨Ltail, htail⟩ :=
        IH (resettingCount C₁) (by omega) C₁ rfl
          hstep_root.1 hstep_root.2.1 hstep_root.2.2.1
          hstep_root.2.2.2.1 hzero₁
      refine ⟨[(ℓ, w)] ++ Ltail, ?_⟩
      intro x
      rw [runPairs_append]
      change (runPairs P C₁ Ltail x).1.role ≠ .Resetting
      exact htail x

set_option maxHeartbeats 4000000 in
theorem step_F_pos_F_zero_gt_one_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_F_zero_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_F
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
theorem step_F_pos_one_F_zero_low_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 1) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_low : (C v).1.delaytimer ≤ 1) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .F ∧
    (C' u).1.delaytimer = Dmax ∧
    (C' v).1.role = .Unsettled ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_one_F_zero_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_F hv_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
theorem step_L_pos_one_F_zero_low_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 1) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hv_low : (C v).1.delaytimer ≤ 1) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .L ∧
    (C' u).1.delaytimer = Dmax ∧
    (C' v).1.role = .Unsettled ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_one_F_zero_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F hv_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
theorem step_L_pos_one_L_zero_low_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 1) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hv_low : (C v).1.delaytimer ≤ 1) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .L ∧
    (C' u).1.delaytimer = Dmax ∧
    (C' v).1.role = .Settled ∧
    (C' v).1.rank.val = 0 ∧
    (C' v).1.children = 0 ∧
    (C' v).1.leader = .L := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_one_L_zero_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_L hv_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.rank h_snd]
    exact congrArg Fin.val (h_pass.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1)
  · rw [congrArg AgentState.children h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
theorem step_L_zero_F_pos_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hu_dt : 1 < (C u).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' u).1.delaytimer =
      (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_F hu_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
theorem step_L_zero_F_pos_one_low_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : (C v).1.resetcount = 1)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hu_low : (C u).1.delaytimer ≤ 1) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Settled ∧
    (C' u).1.rank.val = 0 ∧
    (C' u).1.children = 0 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.leader = .F ∧
    (C' v).1.delaytimer = Dmax := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_one_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F hu_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.2.2.2.2.1] at hboth
    exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact congrArg Fin.val (h_pass.2.2.1 ▸ h_rd.2.1)
  · rw [congrArg AgentState.children h_fst]; exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in

theorem step_leader_dedup_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L) (hw_L : (C w).1.leader = .L)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧ (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.leader = .L ∧ (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧
    (C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0 ∧
    (C' w).1.leader = .F ∧ (C' w).1.delaytimer = (C w).1.delaytimer - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_leader_dedup_step (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1

theorem step_leader_dedup_trace_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L) (hw_L : (C w).1.leader = .L)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧
    (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧
    (C' w).1.role = .Resetting ∧
    (C' w).1.resetcount = 0 ∧
    (C' w).1.leader = .F ∧
    (C' w).1.delaytimer = (C w).1.delaytimer - 1 ∧
    (∀ x : Fin n, x ≠ ℓ → x ≠ w → C' x = C x) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep :=
    step_leader_dedup_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (ℓ := ℓ) (w := w) hℓw
      hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
    hstep.2.2.2.2.1, hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2.1,
    hstep.2.2.2.2.2.2.2, ?_⟩
  intro x hxℓ hxw
  simp [Config.step, hℓw, hxℓ, hxw, P]

theorem step_leader_dedup_resetLeaderCount_lt_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L) (hw_L : (C w).1.leader = .L)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resetLeaderCount (C.step P ℓ w) < resetLeaderCount C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P ℓ w
  have hstep :=
    step_leader_dedup_trace_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (ℓ := ℓ) (w := w) hℓw
      hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  set S := Finset.univ.filter (fun x : Fin n =>
    (C x).1.role = .Resetting ∧ (C x).1.resetcount = 0 ∧ (C x).1.leader = .L) with hS
  set S' := Finset.univ.filter (fun x : Fin n =>
    (C' x).1.role = .Resetting ∧ (C' x).1.resetcount = 0 ∧ (C' x).1.leader = .L) with hS'
  have hw_mem : w ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, hw_res, hw_rc, hw_L⟩
  have hsub : S' ⊆ S.erase w := by
    intro x hx
    have hx_fields :
        (C' x).1.role = .Resetting ∧ (C' x).1.resetcount = 0 ∧
          (C' x).1.leader = .L := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_w : x ≠ w := by
      intro hxw
      subst x
      rw [show (C' w).1.leader = .F from hstep.2.2.2.2.2.2.1] at hx_fields
      cases hx_fields.2.2
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      by_cases hxℓ : x = ℓ
      · subst x
        exact ⟨Finset.mem_univ ℓ, hℓ_res, hℓ_rc, hℓ_L⟩
      · have hx_old : C' x = C x := hstep.2.2.2.2.2.2.2.2 x hxℓ hx_ne_w
        rw [hx_old] at hx_fields
        exact ⟨Finset.mem_univ x, hx_fields⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_w, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase w).card := Finset.card_le_card hsub
  have herase : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hw_mem
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨w, hw_mem⟩
    omega
  change resetLeaderCount C' < resetLeaderCount C
  unfold resetLeaderCount
  rw [← hS, ← hS']
  exact hlt


/-- Strong form of `CorrectResetSeed` for the log-regime re-entry:
the seed still has the exact reset fuel `Rmax`, and the existing answer
invariant is the one required by
`log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log`. -/
def CorrectResetSeedStrong
    (Rmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (∃ r : Fin n,
    (C r).1.role = .Resetting ∧
    (C r).1.resetcount = Rmax ∧
    (C r).1.leader = .L ∧
    (C r).1.answer = majorityAnswer C) ∧
  (∀ w : Fin n,
    (C w).1.role = .Resetting →
    0 < (C w).1.resetcount ∧
    (C w).1.answer = majorityAnswer C)

theorem CorrectResetSeedStrong.toCorrectResetSeed
    {Rmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hN_lt_Rmax : nonResettingCount C < Rmax)
    (hSeed : CorrectResetSeedStrong Rmax C) :
    CorrectResetSeed C := by
  rcases hSeed with ⟨⟨r, hr_role, hr_rc, hr_L, hr_ans⟩, hAllAns⟩
  refine ⟨⟨r, hr_role, ?_, hr_L, hr_ans⟩, ?_⟩
  · simpa [hr_rc] using hN_lt_Rmax
  · intro w hw
    exact hAllAns w hw

theorem CorrectResetSeedStrong_of_step_pair
    {Y : Type*} {P : Protocol (AgentState n) Opinion Y}
    {Rmax : ℕ} {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hRmax_pos : 0 < Rmax)
    (hC : InSrank C) (huv : u ≠ v)
    (hu_role : (C.step P u v u).1.role = .Resetting)
    (hu_rc : (C.step P u v u).1.resetcount = Rmax)
    (hu_L : (C.step P u v u).1.leader = .L)
    (hu_ans : (C.step P u v u).1.answer = majorityAnswer (C.step P u v))
    (_hv_role : (C.step P u v v).1.role = .Resetting)
    (hv_rc : (C.step P u v v).1.resetcount = Rmax)
    (hv_ans : (C.step P u v v).1.answer = majorityAnswer (C.step P u v)) :
    CorrectResetSeedStrong Rmax (C.step P u v) := by
  refine ⟨⟨u, hu_role, hu_rc, hu_L, hu_ans⟩, ?_⟩
  intro w hw
  by_cases hwu : w = u
  · subst w
    refine ⟨?_, hu_ans⟩
    rw [hu_rc]
    exact hRmax_pos
  · by_cases hwv : w = v
    · subst w
      refine ⟨?_, hv_ans⟩
      rw [hv_rc]
      exact hRmax_pos
    · have hw_old : C.step P u v w = C w := by
        unfold Config.step
        simp [huv, hwu, hwv]
      rw [hw_old] at hw
      rw [hC.allSettled w] at hw
      cases hw

theorem ranking_goal_of_runPairs_RankingEndpoint_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {L : List (Fin n × Fin n)}
    (hEndpoint :
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank
        (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 =
            ceilHalf n →
        2 ≤
          (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig
        (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    exists_schedule_of_runPairs
      (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n,
              (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      hEndpoint

set_option maxHeartbeats 12000000 in
theorem phase3a_to_awakening_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      IsAwakeningConfig (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
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
        (C₀ ℓ).1.delaytimer ≤ k →
        ∃ L : List (Fin n × Fin n), IsAwakeningConfig (runPairs P C₀ L) by
    exact wake (C ℓ).1.delaytimer C hDormant₀ hℓ_L₀ hw_F₀ le_rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hDorm hℓ_L hw_F hdt_le
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
      refine ⟨[(ℓ, w)], ?_⟩
      change IsAwakeningConfig C₁
      exact awakening_of_pair_trace
        (C := C₀) (C' := C₁) (ℓ := ℓ) (w := w)
        ⟨hAllR, hAllRc0, hUnique_saved, hLeaderCases⟩ hℓw hℓ_L
        hstep.2.2.2.1 hstep.1 (congrArg Fin.val hstep.2.1)
        hstep.2.2.1 hw_leader₁ hstep.2.2.2.2 hOthers₁
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
        have hstep₂ := by
          simpa [P, C₁] using
            (transitionPEM_dormant_leader_with_unsettled_follower_wakes_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (ℓ := ℓ) (w := w) hℓw
              hstep₁.1 hstep₁.2.1 hstep₁.2.2.2.1
              hstep₁.2.2.2.2.1 hstep₁.2.2.2.2.2)
        have hOthers₂ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₂ x = C₀ x := by
          intro x hxℓ hxw
          dsimp [C₂, C₁]
          simp [Config.step, hℓw, hxℓ, hxw]
        refine ⟨[(ℓ, w), (ℓ, w)], ?_⟩
        change IsAwakeningConfig C₂
        exact awakening_of_pair_trace
          (C := C₀) (C' := C₂) (ℓ := ℓ) (w := w)
          ⟨hAllR, hAllRc0, hUnique_saved, hLeaderCases⟩ hℓw hℓ_L
          hstep₂.2.2.2.1 hstep₂.1 (congrArg Fin.val hstep₂.2.1)
          hstep₂.2.2.1 hstep₂.2.2.2.2.2 (Or.inl hstep₂.2.2.2.2.1) hOthers₂
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
        obtain ⟨Ltail, htail⟩ :=
          IH (C₁ ℓ).1.delaytimer hm_lt C₁ hDorm₁ hstep.2.2.2.1
            hstep.2.2.2.2.2.2.2 le_rfl
        refine ⟨[(ℓ, w)] ++ Ltail, ?_⟩
        rw [runPairs_append]
        change IsAwakeningConfig (runPairs P C₁ Ltail)
        exact htail

set_option maxHeartbeats 12000000 in
theorem phase3bc_from_awakening_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    ∃ L : List (Fin n × Fin n),
      FreshRankingStart (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices sweep :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        IsAwakeningConfig C₀ →
        (awakeningResettingFollowers C₀).card = k →
        ∃ L : List (Fin n × Fin n), FreshRankingStart (runPairs P C₀ L) by
    exact sweep (awakeningResettingFollowers C).card C hAwake rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hAwake₀ hcard
    rcases hAwake₀ with ⟨hUnique, hLeaderOK, hFollowerOK⟩
    obtain ⟨root, hroot_L, hroot_unique⟩ := hUnique
    by_cases hk0 : k = 0
    · refine ⟨[], ?_⟩
      simp only [runPairs_nil]
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
    · have hpos : 0 < (awakeningResettingFollowers C₀).card := by
        rw [hcard]
        omega
      obtain ⟨w, hw_bad⟩ := Finset.card_pos.mp hpos
      have hw_F : (C₀ w).1.leader = .F := by
        exact (Finset.mem_filter.mp hw_bad).2.1
      have hw_res : (C₀ w).1.role = .Resetting := by
        exact (Finset.mem_filter.mp hw_bad).2.2
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
      have hsubset :
          awakeningResettingFollowers C₁ ⊆ (awakeningResettingFollowers C₀).erase w := by
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
      obtain ⟨Ltail, htail⟩ :=
        IH (awakeningResettingFollowers C₁).card hcard_lt C₁ hAwake₁ rfl
      refine ⟨[(root, w)] ++ Ltail, ?_⟩
      rw [runPairs_append]
      change FreshRankingStart (runPairs P C₁ Ltail)
      exact htail

lemma transitionPEM_recruit_ba_rank_children_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    let t := transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))
    t.1.rank.val = 2 * b.rank.val + b.children + 1 ∧
    t.1.children = 0 ∧
    t.2.rank = b.rank ∧
    t.2.children = b.children + 1 := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₁_children : p.1.children = 0 := by
    simpa [p, hrd] using hpre.2.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_children : p.2.children = b.children + 1 := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    have hv : p.1.rank.val < p.2.rank.val := by
      exact h.1
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) hv
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hprop := phase4_propagate_preserves_rank_children
    (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
  have ht :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprop.1, hdec.2.1, hp₁_rank]
  · rw [hprop.2.1, hdec.2.2.1, hp₁_children]
  · rw [hprop.2.2.1, hdec.2.2.2.2.1, hp₂_rank]
  · rw [hprop.2.2.2, hdec.2.2.2.2.2, hp₂_children]

set_option maxHeartbeats 1600000 in
/-- **prePhase4 of a recruit `(child Unsettled, parent Settled)` pair is
answer-inert.**  `rankDeltaOSSR_recruit_ba` keeps both `.answer` fields;
the prePhase4 phi-wipe fires only on a *fresh* `Resetting` (neither
endpoint becomes `Resetting`: both are `Settled`), the timer-init only
touches `timer`, and the phi-spread guard needs both `Resetting` (false
here).  Hence both prePhase4 output answers equal the inputs. -/
lemma prePhase4_recruit_ba_answer_preserved_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        a b x₀ x₁).1.answer = a.answer ∧
    (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
        a b x₀ x₁).2.answer = b.answer := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  -- The recruit `rankDeltaOSSR` output (explicit via `hrd`): child Settled
  -- with answer `a.answer`, parent Settled with answer `b.answer`.  No
  -- phi-wipe (both outputs `.Settled`, not `.Resetting`), timer-init only
  -- modifies `.timer`, phi-spread needs both `.Resetting`.
  unfold transitionPEM_prePhase4
  rw [hrd]
  simp only []
  refine ⟨?_, ?_⟩ <;>
    · split_ifs <;>
        simp_all [AgentState.answer]

set_option maxHeartbeats 1600000 in
/-- **A recruit `(child Unsettled, parent Settled)` `transitionPEM` step
is answer-inert when neither resulting agent lands at a median decision
rank.**  prePhase4 preserves answers (`prePhase4_recruit_ba_answer_
preserved`); both agents are `Settled` so Phase 4 fires, but
`phase4_swap` only reorders, `phase4_decide` writes `.answer` *only* at a
median rank (none here), and `phase4_propagate` only changes `timer`/role
unless an agent is at the median rank (none here).  Hence both output
answers equal the input answers. -/
lemma transitionPEM_recruit_ba_answer_inert_of_no_median_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (hchild_no_med : 2 * b.rank.val + b.children + 1 + 1 ≠ ceilHalf n)
    (hchild_no_lower : 2 * b.rank.val + b.children + 1 + 1 ≠ n / 2)
    (hchild_no_upper : 2 * b.rank.val + b.children + 1 + 1 ≠ n / 2 + 1)
    (hpar_no_med : b.rank.val + 1 ≠ ceilHalf n)
    (hpar_no_lower : b.rank.val + 1 ≠ n / 2)
    (hpar_no_upper : b.rank.val + 1 ≠ n / 2 + 1) :
    let t := transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))
    t.1.answer = a.answer ∧ t.2.answer = b.answer := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp_ans := prePhase4_recruit_ba_answer_preserved_trank
    (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := a) (b := b) (x₀ := x₀) (x₁ := x₁) ha hb hb_children h_valid
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  -- `phase4_decide` is the identity: neither rank is a median decision rank.
  have hp₁_rankv : p.1.rank.val = 2 * b.rank.val + b.children + 1 := by
    rw [hp₁_rank]
  have hp₂_rankv : p.2.rank.val = b.rank.val := by
    rw [hp₂_rank]
  -- Restate the no-median guards in terms of `p`'s ranks.
  have hc_med : p.1.rank.val + 1 ≠ ceilHalf n := by
    rw [hp₁_rankv]; exact hchild_no_med
  have hc_low : p.1.rank.val + 1 ≠ n / 2 := by
    rw [hp₁_rankv]; exact hchild_no_lower
  have hc_up : p.1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hp₁_rankv]; exact hchild_no_upper
  have hpar_med : p.2.rank.val + 1 ≠ ceilHalf n := by
    rw [hp₂_rankv]; exact hpar_no_med
  have hpar_low : p.2.rank.val + 1 ≠ n / 2 := by
    rw [hp₂_rankv]; exact hpar_no_lower
  have hpar_up : p.2.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hp₂_rankv]; exact hpar_no_upper
  -- The four median-decision guards of `phase4_decide` are all false.
  have hg_even1 : ¬ (p.1.rank.val + 1 = n / 2 ∧ p.2.rank.val + 1 = n / 2 + 1) := by
    rintro ⟨h, _⟩; exact hc_low h
  have hg_even2 : ¬ (p.2.rank.val + 1 = n / 2 ∧ p.1.rank.val + 1 = n / 2 + 1) := by
    rintro ⟨h, _⟩; exact hpar_low h
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec_id : q = (p.1, p.2) := by
    show phase4_decide n p.1 p.2 x₀ x₁ = (p.1, p.2)
    unfold phase4_decide
    by_cases hpar : n % 2 = 0
    · rw [if_pos hpar, if_neg hg_even1, if_neg hg_even2]
    · rw [if_neg hpar, if_neg hc_med, if_neg hpar_med]
  have hq₁ : q.1 = p.1 := by rw [hdec_id]
  have hq₂ : q.2 = p.2 := by rw [hdec_id]
  -- `phase4_propagate` only touches `timer`/role unless at the (ceilHalf)
  -- median rank; neither endpoint is there.
  have hprop_ans :
      (phase4_propagate n Rmax q.1 q.2).1.answer = p.1.answer ∧
      (phase4_propagate n Rmax q.1 q.2).2.answer = p.2.answer := by
    rw [hq₁, hq₂]
    unfold phase4_propagate
    rw [if_neg hc_med, if_neg hpar_med]
    exact ⟨rfl, rfl⟩
  have ht :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  refine ⟨?_, ?_⟩
  · rw [ht, hprop_ans.1]; exact hp_ans.1
  · rw [ht, hprop_ans.2]; exact hp_ans.2

lemma prePhase4_recruit_ba_child_timer_of_median_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁).1.rank.val + 1 =
      ceilHalf n →
    (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁).1.timer =
      7 * (τ + 4) := by
    intro hmed
    have hrd :=
      rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
    unfold transitionPEM_prePhase4 at hmed ⊢
    rw [hrd] at hmed ⊢
    simp [ha, hb] at hmed ⊢
    by_cases h : 2 * b.rank.val + b.children + 1 + 1 = ceilHalf n
    · simp [h]
    · have h' : 2 * b.rank.val + b.children + 1 + 1 = ceilHalf n := by
        simpa [h] using hmed
      exact False.elim (h h')

lemma prePhase4_recruit_ba_parent_timer_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁).2.timer =
      b.timer := by
    have hrd :=
      rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
    unfold transitionPEM_prePhase4
    simp [hrd, ha, hb]

set_option maxHeartbeats 8000000 in
lemma transitionPEM_recruit_ba_settled_rank_children_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (ht_parent : b.rank.val + 1 = ceilHalf n →
      (if 2 * b.rank.val + b.children + 1 + 1 = n then b.timer - 1 else b.timer) ≠ 0) :
    let t := transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))
    t.1.role = .Settled ∧ t.2.role = .Settled ∧
    t.1.rank.val = 2 * b.rank.val + b.children + 1 ∧
    t.1.children = 0 ∧
    t.2.rank = b.rank ∧
    t.2.children = b.children + 1 := by
  have hstruct :=
    transitionPEM_recruit_ba_rank_children_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hdt := phase4_decide_preserves_timer
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hq₁_role : q.1.role = .Settled := by
    rw [hdec.1, hp₁_role]
  have hq₂_role : q.2.role = .Settled := by
    rw [hdec.2.2.2.1, hp₂_role]
  have ht₀ : q.1.rank.val + 1 = ceilHalf n →
      (if q.2.rank.val + 1 = n then q.1.timer - 1 else q.1.timer) ≠ 0 := by
    intro hmed
    have hparent_not_max : q.2.rank.val + 1 ≠ n := by
      rw [hdec.2.2.2.2.1, hp₂_rank]
      omega
    simp [hparent_not_max]
    have hpmed : p.1.rank.val + 1 = ceilHalf n := by
      rwa [hdec.2.1] at hmed
    have hp_timer :=
      prePhase4_recruit_ba_child_timer_of_median_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
        ha hb hb_children h_valid hpmed
    rw [hdt.1, hp_timer]
    omega
  have ht₁ : q.2.rank.val + 1 = ceilHalf n →
      (if q.1.rank.val + 1 = n then q.2.timer - 1 else q.2.timer) ≠ 0 := by
    intro hmed
    have hpmed : b.rank.val + 1 = ceilHalf n := by
      rw [hdec.2.2.2.2.1, hp₂_rank] at hmed
      exact hmed
    have hp_timer :=
      prePhase4_recruit_ba_parent_timer_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
        ha hb hb_children h_valid
    rw [hdt.2, hp_timer, hdec.2.1, hp₁_rank]
    exact ht_parent hpmed
  have hroles :=
    phase4_propagate_settled_of_positive_median_timers
      (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
      hq₁_role hq₂_role ht₀ ht₁
  have ht :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  refine ⟨hroles.1, hroles.2, ?_, ?_, ?_, ?_⟩
  · simpa [ht] using hstruct.1
  · simpa [ht] using hstruct.2.1
  · simpa [ht] using hstruct.2.2.1
  · simpa [ht] using hstruct.2.2.2

lemma transitionPEM_recruit_ba_child_timer_ge_three_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (hmed : 2 * b.rank.val + b.children + 1 + 1 = ceilHalf n) :
    3 ≤
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((a, x₀), (b, x₁))).1.timer := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hdt := phase4_decide_preserves_timer
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hq₁_med : q.1.rank.val + 1 = ceilHalf n := by
    rw [hdec.2.1, hp₁_rank]
    exact hmed
  have hq₂_not_max : q.2.rank.val + 1 ≠ n := by
    rw [hdec.2.2.2.2.1, hp₂_rank]
    omega
  have hp_timer :=
    prePhase4_recruit_ba_child_timer_of_median_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid (by
        change p.1.rank.val + 1 = ceilHalf n
        rw [hp₁_rank]
        exact hmed)
  have ht :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  unfold phase4_propagate
  simp [hq₁_med, hq₂_not_max]
  split_ifs <;> rw [hdt.1, hp_timer] <;> omega

lemma transitionPEM_recruit_ba_parent_timer_bounds_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (htimer : b.rank.val + 1 = ceilHalf n → 3 ≤ b.timer) :
    (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))).2.rank.val + 1 = ceilHalf n →
      2 ≤
          (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
            ((a, x₀), (b, x₁))).2.timer ∧
        (2 * b.rank.val + b.children + 1 + 1 < n →
          3 ≤
            (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              ((a, x₀), (b, x₁))).2.timer) := by
  intro hmed_t
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hdt := phase4_decide_preserves_timer
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hp_timer :=
    prePhase4_recruit_ba_parent_timer_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid
  have hq₂_timer : q.2.timer = b.timer := by
    rw [hdt.2, hp_timer]
  have hq₁_rank : q.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    rw [hdec.2.1, hp₁_rank]
  have ht :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  have hq₂_med : q.2.rank.val + 1 = ceilHalf n := by
    rw [ht] at hmed_t
    unfold phase4_propagate at hmed_t
    by_cases hq₁_med : q.1.rank.val + 1 = ceilHalf n
    · simp [hq₁_med] at hmed_t
      split_ifs at hmed_t <;> simpa using hmed_t
    · simp [hq₁_med] at hmed_t
      by_cases hq₂_med : q.2.rank.val + 1 = ceilHalf n
      · exact hq₂_med
      · simp [hq₂_med] at hmed_t
  have hb_med : b.rank.val + 1 = ceilHalf n := by
    rw [hdec.2.2.2.2.1, hp₂_rank] at hq₂_med
    exact hq₂_med
  have hq₁_not_med : q.1.rank.val + 1 ≠ ceilHalf n := by
    rw [hdec.2.1, hp₁_rank]
    omega
  have hparent_timer : 3 ≤ b.timer := htimer hb_med
  rw [ht]
  unfold phase4_propagate
  simp [hq₁_not_med, hq₂_med]
  by_cases hmax : q.1.rank.val + 1 = n
  · simp [hmax]
    split_ifs <;> simp [hq₂_timer] <;> refine ⟨by omega, ?_⟩
    · intro hlt
      have hmax_child : 2 * b.rank.val + b.children + 1 + 1 = n := by
        simpa [hq₁_rank] using hmax
      omega
    · intro hlt
      have hmax_child : 2 * b.rank.val + b.children + 1 + 1 = n := by
        simpa [hq₁_rank] using hmax
      omega
  · simp [hmax]
    split_ifs <;> simp [hq₂_timer] <;> exact ⟨by omega, by intro hlt; omega⟩

set_option maxHeartbeats 24000000 in
theorem heapPrefix_recruit_step_trank [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {k : ℕ}
    (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    ∃ parent child : Fin n,
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C [(parent, child)]
      HeapPrefix C' (k + 1) ∧ SettledMedianTimerGood C' ∧
        (k + 1 < n → SettledMedianTimerStrong C') := by
  classical
  let pr := heapParent k
  have hpr_lt : pr < k := by
    simpa [pr] using heapParent_lt_self hk_pos
  rcases hHeap with ⟨hkn, hRankLt, hUnique, hRoles, hChildren⟩
  obtain ⟨v, hv_prop, hv_unique⟩ := hUnique pr hpr_lt
  have hv_settled : (C v).1.role = .Settled := hv_prop.1
  have hv_rank : (C v).1.rank.val = pr := hv_prop.2
  have hHeap_old : HeapPrefix C k :=
    ⟨hkn, hRankLt, hUnique, hRoles, hChildren⟩
  have hExistsUnsettled : ∃ u : Fin n, (C u).1.role = .Unsettled := by
    by_contra hnone
    push_neg at hnone
    have hall : ∀ w : Fin n, (C w).1.role = .Settled := by
      intro w
      rcases hRoles w with hs | hu
      · exact hs
      · exact False.elim (hnone w hu)
    exact heapPrefix_no_unsettled_contradiction hk_lt hHeap_old hall
  obtain ⟨u, hu_unsettled⟩ := hExistsUnsettled
  have huv : u ≠ v := by
    intro huv
    subst u
    rw [hv_settled] at hu_unsettled
    cases hu_unsettled
  have hv_children_old : (C v).1.children = heapChildIndex k := by
    have hchild := hChildren v hv_settled
    rw [hchild, hv_rank]
    exact heapChildrenBefore_parent hk_pos
  have hv_children_lt : (C v).1.children < 2 := by
    rw [hv_children_old]
    exact heapChildIndex_lt_two k
  have h_valid : 2 * (C v).1.rank.val + (C v).1.children + 1 < n := by
    rw [hv_rank, hv_children_old]
    have hp := heap_parent_rank hk_pos
    omega
  refine ⟨u, v, ?_⟩
  let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := runPairs P C [(u, v)]
  have ht_parent :
      (C v).1.rank.val + 1 = ceilHalf n →
      (if 2 * (C v).1.rank.val + (C v).1.children + 1 + 1 = n
       then (C v).1.timer - 1 else (C v).1.timer) ≠ 0 := by
    intro hmed
    have ht := hTimer v hv_settled hmed
    split_ifs <;> omega
  have hstep :=
    transitionPEM_recruit_ba_settled_rank_children_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := (C u).1) (b := (C v).1)
      (x₀ := (C u).2) (x₁ := (C v).2)
      hu_unsettled hv_settled hv_children_lt h_valid ht_parent
  have hfst :
      (C' u).1 =
        (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).1 := by
    simpa [C', P, protocolPEM] using Config.step_fst_state P C huv
  have hsnd :
      (C' v).1 =
        (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).2 := by
    simpa [C', P, protocolPEM] using Config.step_snd_state P C huv huv.symm
  have hother (w : Fin n) (hwu : w ≠ u) (hwv : w ≠ v) : C' w = C w := by
    simp [C', P, runPairs, Config.step, huv, hwu, hwv]
  have hu_settled' : (C' u).1.role = .Settled := by
    rw [congrArg AgentState.role hfst]
    exact hstep.1
  have hv_settled' : (C' v).1.role = .Settled := by
    rw [congrArg AgentState.role hsnd]
    exact hstep.2.1
  have hu_rank' : (C' u).1.rank.val = k := by
    rw [congrArg AgentState.rank hfst]
    have hr := hstep.2.2.1
    rw [hr, hv_rank, hv_children_old]
    exact heap_parent_rank hk_pos
  have hu_children' : (C' u).1.children = 0 := by
    rw [congrArg AgentState.children hfst]
    exact hstep.2.2.2.1
  have hv_rank' : (C' v).1.rank.val = pr := by
    rw [congrArg AgentState.rank hsnd]
    rw [hstep.2.2.2.2.1]
    exact hv_rank
  have hv_children' : (C' v).1.children = heapChildIndex k + 1 := by
    rw [congrArg AgentState.children hsnd]
    rw [hstep.2.2.2.2.2, hv_children_old]
  have hHeap' : HeapPrefix C' (k + 1) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · intro w hw_settled
      by_cases hwu : w = u
      · subst w
        rw [hu_rank']
        omega
      · by_cases hwv : w = v
        · subst w
          rw [hv_rank']
          omega
        · have hw_old_settled : (C w).1.role = .Settled := by
            have hw_eq := hother w hwu hwv
            simpa [hw_eq] using hw_settled
          have hr := hRankLt w hw_old_settled
          have hw_eq := hother w hwu hwv
          rw [hw_eq]
          omega
    · intro r hr
      by_cases hrk : r = k
      · subst r
        refine ⟨u, ⟨hu_settled', hu_rank'⟩, ?_⟩
        intro w hw
        by_cases hwu : w = u
        · exact hwu
        · by_cases hwv : w = v
          · subst w
            have hpr_ne : pr ≠ k := by omega
            exact False.elim (hpr_ne (by simpa [hv_rank'] using hw.2))
          · have hw_eq := hother w hwu hwv
            have hw_old_settled : (C w).1.role = .Settled := by
              simpa [hw_eq] using hw.1
            have hw_old_lt := hRankLt w hw_old_settled
            rw [hw_eq] at hw
            omega
      · have hr_lt_k : r < k := by omega
        obtain ⟨z, hz, hz_unique⟩ := hUnique r hr_lt_k
        have hzu : z ≠ u := by
          intro hzu
          subst z
          rw [hu_unsettled] at hz
          cases hz.1
        by_cases hzv : z = v
        · subst z
          refine ⟨v, ⟨hv_settled', by
            rw [hv_rank']
            rw [hv_rank] at hz
            exact hz.2⟩, ?_⟩
          intro w hw
          by_cases hwu : w = u
          · subst w
            omega
          · by_cases hwv : w = v
            · exact hwv
            · have hw_eq := hother w hwu hwv
              have hw_old : (C w).1.role = .Settled ∧ (C w).1.rank.val = r := by
                rw [hw_eq] at hw
                exact hw
              exact hz_unique w hw_old
        · refine ⟨z, ?_, ?_⟩
          · have hz_eq := hother z hzu hzv
            simpa [hz_eq] using hz
          · intro w hw
            by_cases hwu : w = u
            · subst w
              omega
            · by_cases hwv : w = v
              · subst w
                have hv_old : (C v).1.role = .Settled ∧ (C v).1.rank.val = r := by
                  have hpr_r : pr = r := by simpa [hv_rank'] using hw.2
                  exact ⟨hv_settled, by rw [hv_rank]; exact hpr_r⟩
                exact hz_unique v hv_old
              · have hw_eq := hother w hwu hwv
                have hw_old : (C w).1.role = .Settled ∧ (C w).1.rank.val = r := by
                  rw [hw_eq] at hw
                  exact hw
                exact hz_unique w hw_old
    · intro w
      by_cases hwu : w = u
      · subst w
        exact Or.inl hu_settled'
      · by_cases hwv : w = v
        · subst w
          exact Or.inl hv_settled'
        · have hw_eq := hother w hwu hwv
          simpa [hw_eq] using hRoles w
    · intro w hw_settled
      by_cases hwu : w = u
      · subst w
        rw [hu_children', hu_rank']
        exact (heapChildrenBefore_self_succ k).symm
      · by_cases hwv : w = v
        · subst w
          rw [hv_children', hv_rank']
          simpa [pr] using (heapChildrenBefore_succ_parent hk_pos).symm
        · have hw_eq := hother w hwu hwv
          have hw_old_settled : (C w).1.role = .Settled := by
            simpa [hw_eq] using hw_settled
          have hchild_old := hChildren w hw_old_settled
          have hr_ne : (C w).1.rank.val ≠ pr := by
            intro hr_eq
            have hw_old : (C w).1.role = .Settled ∧ (C w).1.rank.val = pr :=
              ⟨hw_old_settled, hr_eq⟩
            exact hwv (hv_unique w hw_old)
          rw [hw_eq, hchild_old]
          exact (heapChildrenBefore_succ_ne_parent hr_ne).symm
  have hTimerGood' : SettledMedianTimerGood C' := by
    intro μ hμ_settled hμ_med
    by_cases hμu : μ = u
    · subst μ
      rw [congrArg AgentState.timer hfst]
      have hchild_med :
          2 * (C v).1.rank.val + (C v).1.children + 1 + 1 = ceilHalf n := by
        rw [hu_rank'] at hμ_med
        rw [hv_rank, hv_children_old]
        have hp := heap_parent_rank hk_pos
        omega
      have hge3 :=
        transitionPEM_recruit_ba_child_timer_ge_three_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
      exact Nat.le_trans (show 2 ≤ 3 by omega) (by simpa using hge3)
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (a := (C u).1) (b := (C v).1)
            (x₀ := (C u).2) (x₁ := (C v).2)
            hu_unsettled hv_settled hv_children_lt h_valid
            (fun hmed => hTimer v hv_settled hmed)
        have hmed_t :
            (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).2.rank.val + 1 = ceilHalf n := by
          simpa [hsnd] using hμ_med
        exact (hbounds hmed_t).1
      · have hμ_eq := hother μ hμu hμv
        have hμ_old_settled : (C μ).1.role = .Settled := by
          simpa [hμ_eq] using hμ_settled
        have hμ_old_med : (C μ).1.rank.val + 1 = ceilHalf n := by
          rwa [hμ_eq] at hμ_med
        have ht := hTimer μ hμ_old_settled hμ_old_med
        rw [hμ_eq]
        omega
  have hTimerStrong' : k + 1 < n → SettledMedianTimerStrong C' := by
    intro hk_next μ hμ_settled hμ_med
    by_cases hμu : μ = u
    · subst μ
      rw [congrArg AgentState.timer hfst]
      have hchild_med :
          2 * (C v).1.rank.val + (C v).1.children + 1 + 1 = ceilHalf n := by
        rw [hu_rank'] at hμ_med
        rw [hv_rank, hv_children_old]
        have hp := heap_parent_rank hk_pos
        omega
      exact
        transitionPEM_recruit_ba_child_timer_ge_three_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds_trank
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (a := (C u).1) (b := (C v).1)
            (x₀ := (C u).2) (x₁ := (C v).2)
            hu_unsettled hv_settled hv_children_lt h_valid
            (fun hmed => hTimer v hv_settled hmed)
        have hmed_t :
            (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).2.rank.val + 1 = ceilHalf n := by
          simpa [hsnd] using hμ_med
        exact (hbounds hmed_t).2 (by
          rw [hv_rank, hv_children_old]
          have hp := heap_parent_rank hk_pos
          omega)
      · have hμ_eq := hother μ hμu hμv
        have hμ_old_settled : (C μ).1.role = .Settled := by
          simpa [hμ_eq] using hμ_settled
        have hμ_old_med : (C μ).1.rank.val + 1 = ceilHalf n := by
          rwa [hμ_eq] at hμ_med
        rw [hμ_eq]
        exact hTimer μ hμ_old_settled hμ_old_med
  exact ⟨hHeap', hTimerGood', hTimerStrong'⟩

set_option maxHeartbeats 16000000 in
theorem phase4_binary_tree_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hSeed : FreshRankingStart C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C') := by
    classical
    set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    have hHeap0 : HeapPrefix C 1 := FreshRankingStart.to_heapPrefix_one hSeed
    have hTimer0 : SettledMedianTimerStrong C :=
      FreshRankingStart.to_timerStrong hn4 hSeed
    have grow :
        ∀ fuel k (C₀ : Config (AgentState n) Opinion n),
          n - k ≤ fuel →
          1 ≤ k →
          k ≤ n →
          HeapPrefix C₀ k →
          SettledMedianTimerStrong C₀ →
          ∃ L : List (Fin n × Fin n),
            let C' := runPairs P C₀ L
            HeapPrefix C' n ∧ SettledMedianTimerGood C' := by
      intro fuel
      induction fuel with
      | zero =>
          intro k C₀ hfuel _hk_pos hk_le hHeap hTimer
          have hk_eq : k = n := by omega
          subst k
          refine ⟨[], ?_⟩
          simp only [runPairs_nil]
          exact ⟨hHeap, SettledMedianTimerStrong.toGood hTimer⟩
      | succ fuel IH =>
          intro k C₀ hfuel hk_pos hk_le hHeap hTimer
          by_cases hk_eq : k = n
          · subst k
            refine ⟨[], ?_⟩
            simp only [runPairs_nil]
            exact ⟨hHeap, SettledMedianTimerStrong.toGood hTimer⟩
          · have hk_lt : k < n := by omega
            obtain ⟨parent, child, hstep⟩ :=
              heapPrefix_recruit_step_trank
                (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hk_pos hk_lt C₀ hHeap hTimer
            let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ [(parent, child)]
            have hHeap₁ : HeapPrefix C₁ (k + 1) := by
              simpa [C₁, P] using hstep.1
            by_cases hlast : k + 1 = n
            · refine ⟨[(parent, child)], ?_⟩
              simp only [runPairs_cons, runPairs_nil]
              exact ⟨by simpa [hlast] using hHeap₁,
                by simpa [C₁, P, hlast] using hstep.2.1⟩
            · have hk_next_lt : k + 1 < n := by omega
              have hTimer₁ : SettledMedianTimerStrong C₁ := by
                simpa [C₁, P] using hstep.2.2 hk_next_lt
              have hfuel₁ : n - (k + 1) ≤ fuel := by omega
              obtain ⟨Ltail, htail⟩ :=
                IH (k + 1) C₁ hfuel₁ (by omega) (by omega) hHeap₁ hTimer₁
              refine ⟨[(parent, child)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change
                let C' := runPairs P C₁ Ltail
                HeapPrefix C' n ∧ SettledMedianTimerGood C'
              exact htail
    obtain ⟨L, hDone⟩ :=
      grow (n - 1) 1 C (by omega) (by omega) (by omega) hHeap0 hTimer0
    refine ⟨L, ?_⟩
    obtain ⟨hHeapN, hTimerN⟩ := hDone
    have hSrank : InSrank (runPairs P C L) := HeapPrefix.to_InSrank hHeapN
    exact ⟨hSrank, Or.inl (fun μ hμ_med => hTimerN μ (hSrank.allSettled μ) hμ_med)⟩

set_option maxHeartbeats 16000000 in
theorem phase34_rerank_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C') := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hAwake⟩ :=
    phase3a_to_awakening_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hSeed⟩ :=
    phase3bc_from_awakening_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C₁ (by simpa [C₁, P] using hAwake)
  let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
  obtain ⟨L₃, hRanked⟩ :=
    phase4_binary_tree_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C₂ (by simpa [C₂, P] using hSeed)
  refine ⟨(L₁ ++ L₂) ++ L₃, ?_⟩
  rw [runPairs_append]
  change
    let C' := runPairs P (runPairs P C (L₁ ++ L₂)) L₃
    InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C')
  rw [runPairs_append]
  change
    let C' := runPairs P C₂ L₃
    InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C')
  exact hRanked

theorem dormant_to_RankingEndpoint_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨L, hL⟩ :=
    phase34_rerank_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  exact ⟨L, hL⟩

theorem fresh_unique_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax) (hDmax_pos : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hFresh : ∀ w : Fin n, FreshResettingAt Dmax C w)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  have hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting := by
    intro w
    exact (hFresh w).1
  have hAllRc0 : ∀ w : Fin n, (C w).1.resetcount = 0 := by
    intro w
    exact (hFresh w).2.1
  have hDormant : IsDormantConfig C := by
    refine ⟨hAllReset, hAllRc0, hUnique, ?_⟩
    intro w
    cases (C w).1.leader <;> simp
  exact
    dormant_to_RankingEndpoint_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C hDormant

theorem reset_snapshot_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        Rmax ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hn2 : 2 ≤ n := by omega
  have hRmax_pos : 0 < Rmax := by omega
  have hDmax_pos : 0 < Dmax := by omega
  rcases hReset with ⟨r, hr_role, hr_rc, hr_L⟩
  obtain ⟨Lfresh, hFresh, hUnique⟩ :=
    all_fresh_unique_from_log_seed_no_answer
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax1 hn2 C r hr_role
      (Nat.le_trans hRlog hr_rc) hr_L
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lfresh
  obtain ⟨Lrank, hRank⟩ :=
    fresh_unique_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C₁
      (by simpa [C₁, P] using hFresh)
      (by simpa [C₁, P] using hUnique)
  refine ⟨Lfresh ++ Lrank, ?_⟩
  rw [runPairs_append]
  change RankingEndpoint (runPairs P C₁ Lrank)
  exact hRank

theorem step_reset_snapshot_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hStep :
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C ((u, v) :: L)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  change
    (C₁ u).1.role = .Resetting ∧ (C₁ u).1.resetcount = Rmax ∧
      (C₁ u).1.leader = .L ∧
    (C₁ v).1.role = .Resetting ∧ (C₁ v).1.resetcount = Rmax ∧
      (C₁ v).1.leader = .L ∧
    ∀ y : Fin n, (C₁ y).1.role = .Resetting →
      (C₁ y).1.resetcount = Rmax ∧ (C₁ y).1.leader = .L at hStep
  rcases hStep with ⟨hu_role, hu_rc, hu_L, _hv_role, _hv_rc, _hv_L, _hSnapshot⟩
  have hReset :
      ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        Rmax ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
    refine ⟨u, hu_role, ?_, hu_L⟩
    rw [hu_rc]
  obtain ⟨L, hEndpoint⟩ :=
    reset_snapshot_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C₁ hReset
  refine ⟨L, ?_⟩
  rw [runPairs_cons]
  change RankingEndpoint (runPairs P C₁ L)
  exact hEndpoint

theorem ranking_goal_of_step_reset_snapshot_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hStep :
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := u) (v := v) hStep
  exact
    ranking_goal_of_runPairs_RankingEndpoint_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := (u, v) :: L) hEndpoint

private theorem reset_snapshot_transport_step_eq
    {P Q : Protocol (AgentState n) Opinion Output}
    {Rmax : ℕ} {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hEq : C.step P u v = C.step Q u v)
    (h :
      let C' := C.step Q u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
      (C' u).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  rw [hEq]
  exact h

private theorem lower_max_timer_one_state_transport_step_eq
    {P Q : Protocol (AgentState n) Opinion Output}
    {C : Config (AgentState n) Opinion n} {μ v : Fin n}
    (hEq : C.step P μ v = C.step Q μ v)
    (h :
      let C' := C.step Q μ v
      C' μ = ({ (C μ).1 with timer := 0 }, (C μ).2) ∧
      C' v = C v ∧
      ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w) :
    let C' := C.step P μ v
    C' μ = ({ (C μ).1 with timer := 0 }, (C μ).2) ∧
    C' v = C v ∧
    ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
  rw [hEq]
  exact h

private theorem lower_max_timer_one_insswap_transport_step_eq
    {P Q : Protocol (AgentState n) Opinion Output}
    {C : Config (AgentState n) Opinion n} {μ v : Fin n}
    (hEq : C.step P μ v = C.step Q μ v)
    (h :
      let C' := C.step Q μ v
      InSswap C' ∧
        (C' μ).1.timer = 0 ∧
        (C' μ).1.answer = (C μ).1.answer ∧
        (C' μ).1.rank.val + 1 = n / 2) :
    let C' := C.step P μ v
    InSswap C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2 := by
  rw [hEq]
  exact h

private theorem max_timer_one_insrank_transport_step_eq
    {P Q : Protocol (AgentState n) Opinion Output}
    {C : Config (AgentState n) Opinion n} {μ v : Fin n}
    (hEq : C.step P μ v = C.step Q μ v)
    (h :
      let C' := C.step Q μ v
      InSrank C' ∧
        (C' μ).1.timer = 0 ∧
        (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
        (C' μ).1.rank.val + 1 = ceilHalf n) :
    let C' := C.step P μ v
    InSrank C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
      (C' μ).1.rank.val + 1 = ceilHalf n := by
  rw [hEq]
  exact h

theorem trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hC μ v)
  have hold :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  exact
    reset_snapshot_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (u := μ) (v := v) (Rmax := Rmax) hEq hold

theorem trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_not_lower : (C v).1.rank.val + 1 ≠ n / 2)
    (hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_diff : (C μ).1.answer ≠ (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hC μ v)
  have hold :=
    trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC hμv hpar hμ_lower hv_not_lower hv_not_upper h_timer h_no_swap h_post_diff
  exact
    reset_snapshot_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (u := μ) (v := v) (Rmax := Rmax) hEq hold

theorem trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_diff : (C μ).1.answer ≠ (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hC μ v)
  have hold :=
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_diff
  exact
    reset_snapshot_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (u := μ) (v := v) (Rmax := Rmax) hEq hold

theorem trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hC μ v)
  have hold :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  exact
    reset_snapshot_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (u := μ) (v := v) (Rmax := Rmax) hEq hold

theorem no_reset_even_lower_max_timer_one_step_state_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    C' μ = ({ (C μ).1 with timer := 0 }, (C μ).2) ∧
    C' v = C v ∧
    ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hC μ v)
  have hold :=
    no_reset_even_lower_max_timer_one_step_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  exact
    lower_max_timer_one_state_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (μ := μ) (v := v) hEq hold

theorem no_reset_even_lower_max_timer_one_step_InSswap_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hSwap : InSswap C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSswap C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2 := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hSwap.toInSrank μ v)
  have hold :=
    no_reset_even_lower_max_timer_one_step_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  exact
    lower_max_timer_one_insswap_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (μ := μ) (v := v) hEq hold

theorem no_reset_no_swap_max_timer_one_step_InSrank_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSrank C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
      (C' μ).1.rank.val + 1 = ceilHalf n := by
  have hEq :
      C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v =
        C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) μ v := by
    simpa [PEMProtocol, PEMProtocolCoupled] using
      (generic_step_eq_coupled_of_InSrank
        (trank := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn hC μ v)
  have hold :=
    no_reset_no_swap_max_timer_one_step_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_same
  exact
    max_timer_one_insrank_transport_step_eq
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Q := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (C := C) (μ := μ) (v := v) hEq hold

theorem InSrank_misorder_step_reset_snapshot_of_not_both_settled_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hnot :
      ¬ ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).1.role = .Settled ∧
           (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).2.role = .Settled)) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
      (C' u).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  classical
  obtain ⟨_, _, huv_rank⟩ := hMis
  have huv : u ≠ v := by
    intro h
    rw [h] at huv_rank
    exact (lt_irrefl _ huv_rank).elim
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C u).1.rank ≠ (C v).1.rank := ne_of_lt huv_rank
  have hRD :
      rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1) =
        ((C u).1, (C v).1) :=
    rankDeltaOSSR_satisfies_fix (C u).1 (C v).1 hsu hsv h_rank_ne
  have htr_eq :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v) =
        transitionPEM_phase4 n Rmax ((C u).1, (C v).1) (C u).2 (C v).2 := by
    unfold transitionPEM transitionPEM_prePhase4
    simp [hRD, hsu, hsv, role_settled_ne_resetting]
  have hphase_not :
      ¬ ((transitionPEM_phase4 n Rmax ((C u).1, (C v).1) (C u).2 (C v).2).1.role =
            .Settled ∧
          (transitionPEM_phase4 n Rmax ((C u).1, (C v).1) (C u).2 (C v).2).2.role =
            .Settled) := by
    intro hphase
    apply hnot
    simpa [htr_eq] using hphase
  have hphase_reset :=
    transitionPEM_phase4_reset_both_of_not_both_settled
      (n := n) (Rmax := Rmax) (a := ((C u).1, (C v).1))
      (x₀ := (C u).2) (x₁ := (C v).2) hsu hsv hphase_not
  have hphase_rc :=
    phase4_resetting_resetcount
      (n := n) (Rmax := Rmax) (a := ((C u).1, (C v).1))
      (x₀ := (C u).2) (x₁ := (C v).2) hsu hsv
  have hphase_leader :=
    phase4_resetting_leader
      (n := n) (Rmax := Rmax) (a := ((C u).1, (C v).1))
      (x₀ := (C u).2) (x₁ := (C v).2) hsu hsv
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hfst := Config.step_fst_state P C huv
  have hsnd := Config.step_snd_state P C huv huv.symm
  have hu_role : (C' u).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).1.role = .Resetting
    simpa [htr_eq] using hphase_reset.1
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).2.role = .Resetting
    simpa [htr_eq] using hphase_reset.2
  have hu_rc : (C' u).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).1.resetcount = Rmax
    simpa [htr_eq] using hphase_rc.1 hphase_reset.1
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).2.resetcount = Rmax
    simpa [htr_eq] using hphase_rc.2 hphase_reset.2
  have hu_leader : (C' u).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).1.leader = .L
    simpa [htr_eq] using hphase_leader.1 hphase_reset.1
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).2.leader = .L
    simpa [htr_eq] using hphase_leader.2 hphase_reset.2
  refine ⟨hu_role, hu_rc, hu_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy
  by_cases hyu : y = u
  · subst y
    exact ⟨hu_rc, hu_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_reset_C : (C y).1.role = .Resetting := by
        simpa [C', P, Config.step, huv, hyu, hyv] using hy
      rw [hC.allSettled y] at hy_reset_C
      cases hy_reset_C

theorem InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v)) :
    (∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C ((u, v) :: L))) ∨
    (InSrank
        (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
      misorderedCount
        (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) <
      misorderedCount C) := by
  by_cases hrole :
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).1.role = .Settled ∧
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).2.role = .Settled
  · exact Or.inr
      (swap_step_decreases_at_misorder_of_role_settled
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        rankDeltaOSSR_satisfies_fix hC hMis hrole)
  · have hstep :=
      InSrank_misorder_step_reset_snapshot_of_not_both_settled_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC hMis hrole
    obtain ⟨L, hEndpoint⟩ :=
      step_reset_snapshot_to_RankingEndpoint_log
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog (C := C) (u := u) (v := v) hstep
    exact Or.inl ⟨L, hEndpoint⟩

theorem InSrank_reaches_RankingEndpoint_or_InSswap_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C) :
    (∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) ∨
    (∃ L : List (Fin n × Fin n),
      InSswap
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let motive : ℕ → Prop := fun k =>
    ∀ C : Config (AgentState n) Opinion n,
      InSrank C →
      misorderedCount C = k →
      (∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L)) ∨
      (∃ L : List (Fin n × Fin n), InSswap (runPairs P C L))
  have hmain : ∀ k, motive k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hC hcount
      by_cases hk0 : k = 0
      · have hzero : misorderedCount C = 0 := by
          rw [hcount, hk0]
        exact Or.inr ⟨[], by
          simpa [P] using
            (InSswap_of_InSrank_of_count_zero hC hzero)⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hpos : 0 < misorderedCount C := by
          rw [hcount]
          exact hkpos
        obtain ⟨u, v, hMis⟩ := exists_misordered_of_pos_count hpos
        have hstep :=
          InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease_log
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog hC hMis
        rcases hstep with hEndpoint | hDec
        · rcases hEndpoint with ⟨L, hEndpoint⟩
          exact Or.inl ⟨(u, v) :: L, by
            simpa [P] using hEndpoint⟩
        · rcases hDec with ⟨hCstep, hlt⟩
          let Cstep : Config (AgentState n) Opinion n := C.step P u v
          have hlt_k : misorderedCount Cstep < k := by
            dsimp [Cstep, P]
            rw [← hcount]
            exact hlt
          have hrec := ih (misorderedCount Cstep) hlt_k Cstep hCstep rfl
          rcases hrec with hEndpoint | hSwap
          · rcases hEndpoint with ⟨L, hEndpoint⟩
            exact Or.inl ⟨(u, v) :: L, by
              change RankingEndpoint (runPairs P (C.step P u v) L)
              exact hEndpoint⟩
          · rcases hSwap with ⟨L, hSwap⟩
            exact Or.inr ⟨(u, v) :: L, by
              change InSswap (runPairs P (C.step P u v) L)
              exact hSwap⟩
  have h := hmain (misorderedCount C) C hC rfl
  simpa [P] using h

theorem InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧
      (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ w : Fin n} (hμw : μ ≠ w)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hw_not_lower : (C w).1.rank.val + 1 ≠ n / 2 := by
    intro hw_lower
    apply hμw
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = n / 2 - 1 := by omega
    have hw_val : (C w).1.rank.val = n / 2 - 1 := by omega
    exact hμ_val.trans hw_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C w).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
    hSwap.swap_condition_false μ w
  have hdiff : (C μ).1.answer ≠ (C w).1.answer := by
    intro hsame
    exact hw_wrong (by rw [← hsame, hμ_correct])
  have hstep :=
    trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hμw hpar hμ_lower hw_not_lower hw_not_upper h_timer
      h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := w) hstep
  exact ⟨(μ, w) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_correct : (C v).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_same : (C μ).1.answer = (C v).1.answer := by
    rw [hμ_correct, hv_correct]
  obtain ⟨hμ_state, hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap_pack :=
    no_reset_even_lower_max_timer_one_step_InSswap_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap : InSswap C₁ := by
    simpa [C₁, P] using hC₁_swap_pack.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := by
    simpa [C₁, P] using hC₁_swap_pack.2.1
  have hμ_lower₁ : (C₁ μ).1.rank.val + 1 = n / 2 := by
    simpa [C₁, P] using hC₁_swap_pack.2.2.2
  have hw_state₁ : C₁ w = C w := by
    simpa [C₁, P] using hothers w hμw.symm hwv
  have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, P] using
      (majorityAnswer_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hμ_correct₁ : (C₁ μ).1.answer = majorityAnswer C₁ := by
    rw [hmaj₁]
    simpa [C₁, P] using hC₁_swap_pack.2.2.1.trans hμ_correct
  have hw_not_upper₁ : (C₁ w).1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hw_state₁]
    exact hw_not_upper
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    rw [hw_state₁, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hEndpoint⟩ :=
    InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hC₁_swap hpar hμw hμ_lower₁ hw_not_upper₁
      hμ_timer₁ hμ_correct₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have hdiff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hstep :=
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_bad_even_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let motive : ℕ → Prop := fun k =>
    ∀ C : Config (AgentState n) Opinion n,
      BadRankingStart C →
      InSswap C →
      wrongAnswerCount C = k →
      ∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L)
  have hmain : ∀ k, motive k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hbad hSwap hcount
      by_cases hk0 : k = 0
      · have hzero : wrongAnswerCount C = 0 := by
          rw [hcount, hk0]
        have hConsensus :=
          isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hSwap hzero
        exact ⟨[], by
          simp only [runPairs_nil]
          exact ⟨hSwap.toInSrank, Or.inr hConsensus⟩⟩
      · obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
        have hceil : ceilHalf n = n / 2 := by
          unfold ceilHalf
          omega
        have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
          rwa [hceil] at hμ_med
        have h_upper_lt : n / 2 < n := by omega
        obtain ⟨ν, hν_rank⟩ :=
          hSwap.toInSrank.exists_at_rank (by omega) (⟨n / 2, h_upper_lt⟩ : Fin n)
        have hν_upper : (C ν).1.rank.val + 1 = n / 2 + 1 := by
          rw [hν_rank]
        have hμν : μ ≠ ν := by
          intro h
          subst ν
          omega
        have hdecision
            (hwrong_pair :
              (C μ).1.answer ≠ majorityAnswer C ∨
                (C ν).1.answer ≠ majorityAnswer C) :
            ∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L) := by
          let C₁ : Config (AgentState n) Opinion n := C.step P μ ν
          have hdec :=
            InSswap_even_median_pair_decision_decreases
              (trank := τ) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
              rankDeltaOSSR_satisfies_fix hSwap hμν hpar hμ_lower hν_upper hn4
              hwrong_pair
          have hC₁_swap : InSswap C₁ := by
            simpa [C₁, P] using hdec.1
          have hlt : wrongAnswerCount C₁ < k := by
            rw [← hcount]
            simpa [C₁, P] using hdec.2
          by_cases hDone : RankingEndpoint C₁
          · exact ⟨[(μ, ν)], by
              simp only [runPairs_cons, runPairs_nil]
              change RankingEndpoint C₁
              exact hDone⟩
          · have hbad₁ : BadRankingStart C₁ := ⟨hC₁_swap.toInSrank, hDone⟩
            obtain ⟨Ltail, htail⟩ := ih (wrongAnswerCount C₁) hlt C₁ hbad₁ hC₁_swap rfl
            exact ⟨(μ, ν) :: Ltail, by
              change RankingEndpoint (runPairs P (C.step P μ ν) Ltail)
              exact htail⟩
        by_cases hμ_wrong : (C μ).1.answer ≠ majorityAnswer C
        · exact hdecision (Or.inl hμ_wrong)
        · have hμ_correct : (C μ).1.answer = majorityAnswer C := not_not.mp hμ_wrong
          obtain ⟨w, hw_wrong⟩ := hbad.exists_wrong_answer_of_InSswap hSwap
          rcases htimer with htimer0 | htimer1
          · by_cases hw_upper : (C w).1.rank.val + 1 = n / 2 + 1
            · have hw_eq_ν : w = ν := by
                apply hSwap.ranks_inj
                apply Fin.eq_of_val_eq
                have hw_val : (C w).1.rank.val = n / 2 := by omega
                have hν_val : (C ν).1.rank.val = n / 2 := by omega
                exact hw_val.trans hν_val.symm
              subst w
              exact hdecision (Or.inr hw_wrong)
            · have hμw : μ ≠ w := by
                intro h
                subst w
                exact hw_wrong hμ_correct
              exact
                InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_log
                  (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog hSwap hpar hμw hμ_lower hw_upper htimer0
                  hμ_correct hw_wrong
          · obtain ⟨ρ, hμρ, hρ_max⟩ :=
              hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
            by_cases hρ_wrong : (C ρ).1.answer ≠ majorityAnswer C
            · exact
                InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint_log
                  (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog hSwap hpar hμρ hμ_lower hρ_max htimer1
                  hμ_correct hρ_wrong
            · have hρ_correct : (C ρ).1.answer = majorityAnswer C := not_not.mp hρ_wrong
              by_cases hw_upper : (C w).1.rank.val + 1 = n / 2 + 1
              · have hw_eq_ν : w = ν := by
                  apply hSwap.ranks_inj
                  apply Fin.eq_of_val_eq
                  have hw_val : (C w).1.rank.val = n / 2 := by omega
                  have hν_val : (C ν).1.rank.val = n / 2 := by omega
                  exact hw_val.trans hν_val.symm
                subst w
                exact hdecision (Or.inr hw_wrong)
              · have hμw : μ ≠ w := by
                  intro h
                  subst w
                  exact hw_wrong hμ_correct
                have hwρ : w ≠ ρ := by
                  intro h
                  subst w
                  exact hw_wrong hρ_correct
                exact
                  InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint_log
                    (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax1 hRlog hSwap hpar hμρ hμw hwρ hμ_lower hρ_max
                    hw_upper htimer1 hμ_correct hρ_correct hw_wrong
  simpa [P, motive] using hmain (wrongAnswerCount C) C hbad hSwap rfl

theorem BadRankingStart_even_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hbad.1
  rcases hReach with hEndpoint | hSwapReach
  · exact hEndpoint
  · obtain ⟨L₁, hSwap₁⟩ := hSwapReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    by_cases hDone : RankingEndpoint C₁
    · exact ⟨L₁, by simpa [C₁, P] using hDone⟩
    · have hbad₁ : BadRankingStart C₁ := by
        exact ⟨by simpa [C₁, P] using hSwap₁.toInSrank, hDone⟩
      have hSwapC₁ : InSswap C₁ := by
        simpa [C₁, P] using hSwap₁
      obtain ⟨L₂, hEndpoint₂⟩ :=
        InSswap_bad_even_to_RankingEndpoint_log
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ w : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hμw : μ ≠ w := by
    intro h
    subst w
    exact hw_no_med hμ_med
  have h_no_swap :
      ¬((C μ).1.rank < (C w).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
    hSwap.swap_condition_false μ w
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C w).1.answer := by
    rw [opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar]
    exact hw_wrong.symm
  exact
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hbad.1 hμw hμ_med hw_no_med h_timer
      h_no_swap hpar h_post_diff

theorem InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0)
    (hOnlyMedianWrong :
      ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hcard : 1 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨v, hv_ne_mu⟩ := Fintype.exists_ne_of_one_lt_card hcard μ
  have hμv : μ ≠ v := fun h => hv_ne_mu h.symm
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    intro hv_med
    apply hμv
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
    have hv_val : (C v).1.rank.val = ceilHalf n - 1 := by omega
    exact hμ_val.trans hv_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  have hv_correct : (C v).1.answer = majorityAnswer C :=
    hOnlyMedianWrong v hv_ne_mu
  have h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer := by
    rw [h_median_correct, hv_correct]
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    transitionPEM_timer_zero_no_swap_same_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hSwap.toInSrank hμv hμ_med hv_no_med h_timer
      h_no_swap hpar h_post_same
  have hC'_eq : C' =
      fun w => if w = μ then ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C μ).2)
        else if w = v then C v
        else C w := by
    funext w
    dsimp [C', P]
    unfold Config.step
    simp only [if_neg hμv]
    change
      (if w = μ then
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1, (C μ).2)
        else if w = v then
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2, (C v).2)
        else C w) =
      (if w = μ then ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C μ).2)
        else if w = v then C v
        else C w)
    rw [htr]
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P] using
      (majorityAnswer_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hConsensus : IsConsensusConfig C' := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_
        allAnswerCorrect := ?_ }
    · intro w
      have hw_state := congrFun hC'_eq w
      rw [hw_state]
      by_cases hwμ : w = μ
      · simp [hwμ, hSwap.allSettled μ]
      · by_cases hwv : w = v
        · simp [hwμ, hwv, hv_ne_mu, hSwap.allSettled v]
        · simp [hwμ, hwv, hSwap.allSettled w]
    · intro w₁ w₂ heq
      apply hSwap.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hSwap.input_rank w
    · intro w
      rw [hmaj]
      by_cases hwμ : w = μ
      · subst w
        have hμ_state := congrFun hC'_eq μ
        rw [hμ_state]
        simp [h_median_correct]
      · have hw_state := congrFun hC'_eq w
        rw [hw_state]
        by_cases hwv : w = v
        · subst w
          simp [hv_ne_mu, hv_correct]
        · simp [hwμ, hwv, hOnlyMedianWrong w hwμ]
  refine ⟨[(μ, v)], ?_⟩
  simp only [runPairs_cons, runPairs_nil]
  change RankingEndpoint C'
  exact ⟨⟨hConsensus.allSettled, hConsensus.ranks_inj⟩, Or.inr hConsensus⟩

theorem InSswap_bad_timer_zero_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
  · exact
      InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hSwap hμ_med h_timer hpar hOnly
  · push_neg at hOnly
    obtain ⟨w, hwm, hw_wrong⟩ := hOnly
    have hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n := by
      intro hw_med
      apply hwm
      apply hSwap.ranks_inj
      apply Fin.eq_of_val_eq
      have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
      have hw_val : (C w).1.rank.val = ceilHalf n - 1 := by omega
      exact hw_val.trans hμ_val.symm
    exact
      InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint_log
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad hSwap hμ_med hw_no_med h_timer hpar hw_wrong

theorem InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧
      (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap_max : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_no_swap_w : ¬((C μ).1.rank < (C w).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer)
    (h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have hstep :=
    no_reset_no_swap_max_timer_one_step_InSrank_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap_max hpar h_post_same_max
  have hC₁ : InSrank C₁ := hstep.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := hstep.2.1
  have hμ_med₁ : (C₁ μ).1.rank.val + 1 = ceilHalf n := hstep.2.2.2
  have hw_state₁ : C₁ w = C w := by
    dsimp [C₁, P]
    simp [Config.step, hμv, hμw.symm, hwv]
  have hμ_input₁ : (C₁ μ).2 = (C μ).2 := by
    dsimp [C₁, P]
    simp [Config.step, hμv]
  have hμ_rank₁ : (C₁ μ).1.rank = (C μ).1.rank := by
    have htrace :=
      no_reset_no_swap_max_timer_one_trace
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap_max hpar h_post_same_max
    have hfst := Config.step_fst_state P C hμv
    dsimp [C₁]
    rw [hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.rank =
      (C μ).1.rank
    rw [htrace]
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hw_state₁]
    exact hw_no_med
  have h_no_swap_w₁ :
      ¬((C₁ μ).1.rank < (C₁ w).1.rank ∧
        (C₁ μ).2 = Opinion.B ∧ (C₁ w).2 = Opinion.A) := by
    rintro ⟨hrank, hB, hA⟩
    exact h_no_swap_w ⟨by rwa [hμ_rank₁, hw_state₁] at hrank,
      by rwa [hμ_input₁] at hB,
      by rwa [hw_state₁] at hA⟩
  have h_post_diff_w₁ : opinionToAnswer (C₁ μ).2 ≠ (C₁ w).1.answer := by
    rw [hμ_input₁, hw_state₁]
    exact h_post_diff_w
  obtain ⟨Ltail, hEndpoint⟩ :=
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hC₁ hμw hμ_med₁ hw_no_med₁ hμ_timer₁
      h_no_swap_w₁ hpar h_post_diff_w₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (hpar : ¬ n % 2 = 0)
    (hOnlyMedianWrong :
      ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨v, hμv, hv_max⟩ :=
    hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
  have hv_ne_mu : v ≠ μ := hμv.symm
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    intro hv_med
    apply hμv
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
    have hv_val : (C v).1.rank.val = ceilHalf n - 1 := by omega
    exact hμ_val.trans hv_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  have hv_correct : (C v).1.answer = majorityAnswer C :=
    hOnlyMedianWrong v hv_ne_mu
  have h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer := by
    rw [h_median_correct, hv_correct]
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_no_swap_max_timer_one_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hSwap.toInSrank hn4 hμv hμ_med hv_max h_timer
      h_no_swap hpar h_post_same
  have hC'_eq : C' =
      fun w => if w = μ then
          ({ (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 }, (C μ).2)
        else if w = v then C v
        else C w := by
    funext w
    dsimp [C', P]
    unfold Config.step
    simp only [if_neg hμv]
    change
      (if w = μ then
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1, (C μ).2)
        else if w = v then
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2, (C v).2)
        else C w) =
      (if w = μ then
          ({ (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 }, (C μ).2)
        else if w = v then C v
        else C w)
    rw [htr]
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P] using
      (majorityAnswer_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hConsensus : IsConsensusConfig C' := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_
        allAnswerCorrect := ?_ }
    · intro w
      have hw_state := congrFun hC'_eq w
      rw [hw_state]
      by_cases hwμ : w = μ
      · simp [hwμ, hSwap.allSettled μ]
      · by_cases hwv : w = v
        · simp [hwμ, hwv, hv_ne_mu, hSwap.allSettled v]
        · simp [hwμ, hwv, hSwap.allSettled w]
    · intro w₁ w₂ heq
      apply hSwap.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hSwap.input_rank w
    · intro w
      rw [hmaj]
      by_cases hwμ : w = μ
      · subst w
        have hμ_state := congrFun hC'_eq μ
        rw [hμ_state]
        simp [h_median_correct]
      · have hw_state := congrFun hC'_eq w
        rw [hw_state]
        by_cases hwv : w = v
        · subst w
          simp [hv_ne_mu, hv_correct]
        · simp [hwμ, hwv, hOnlyMedianWrong w hwμ]
  refine ⟨[(μ, v)], ?_⟩
  simp only [runPairs_cons, runPairs_nil]
  change RankingEndpoint C'
  exact ⟨⟨hConsensus.allSettled, hConsensus.ranks_inj⟩, Or.inr hConsensus⟩

theorem InSswap_bad_timer_one_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  obtain ⟨v, hμv, hv_max⟩ :=
    hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
  have h_no_swap_max :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  by_cases hv_wrong : (C v).1.answer ≠ majorityAnswer C
  · have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
      rw [h_median_correct]
      exact hv_wrong.symm
    exact
      InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint_log
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad.1 hμv hμ_med hv_max h_timer
        h_no_swap_max hpar h_post_diff
  · have hv_correct : (C v).1.answer = majorityAnswer C := by
      exact not_not.mp hv_wrong
    by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
    · exact
        InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSwap hμ_med h_timer hpar hOnly
    · push_neg at hOnly
      obtain ⟨w, hwm, hw_wrong⟩ := hOnly
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n := by
        intro hw_med
        apply hwm
        apply hSwap.ranks_inj
        apply Fin.eq_of_val_eq
        have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
        have hw_val : (C w).1.rank.val = ceilHalf n - 1 := by omega
        exact hw_val.trans hμ_val.symm
      have h_no_swap_w :
          ¬((C μ).1.rank < (C w).1.rank ∧
            (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
        hSwap.swap_condition_false μ w
      have h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer := by
        rw [h_median_correct, hv_correct]
      have h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer := by
        rw [h_median_correct]
        exact hw_wrong.symm
      exact
        InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint_log
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad.1 hμv hwm.symm hwv hμ_med hv_max hw_no_med h_timer
          h_no_swap_max h_no_swap_w hpar h_post_same_max h_post_diff_w

theorem InSswap_bad_odd_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
  rcases htimer with htimer0 | htimer1
  · exact
      InSswap_bad_timer_zero_to_RankingEndpoint_log
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad hSwap hμ_med htimer0 hpar
  · exact
      InSswap_bad_timer_one_to_RankingEndpoint_log
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog hbad hSwap hμ_med htimer1 hpar

theorem BadRankingStart_odd_to_RankingEndpoint_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap_log
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hbad.1
  rcases hReach with hEndpoint | hSwapReach
  · exact hEndpoint
  · obtain ⟨L₁, hSwap₁⟩ := hSwapReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    by_cases hDone : RankingEndpoint C₁
    · exact ⟨L₁, by simpa [C₁, P] using hDone⟩
    · have hbad₁ : BadRankingStart C₁ := by
        exact ⟨by simpa [C₁, P] using hSwap₁.toInSrank, hDone⟩
      have hSwapC₁ : InSswap C₁ := by
        simpa [C₁, P] using hSwap₁
      obtain ⟨L₂, hEndpoint₂⟩ :=
        InSswap_bad_odd_to_RankingEndpoint_log
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem ranking_from_InSrank_by_parity_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hDone : RankingEndpoint C
  · exact
      ranking_goal_of_runPairs_RankingEndpoint_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := [])
        (by simpa using hDone)
  · have hbad : BadRankingStart C := ⟨hSrank, hDone⟩
    by_cases hpar : n % 2 = 0
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_even_to_RankingEndpoint_log
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_odd_to_RankingEndpoint_log
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint

theorem transitionPEM_unsettled_one_step_progress_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n}
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let r : AgentState n × AgentState n :=
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
    (r.1.role = .Resetting ∨ r.2.role = .Resetting) ∨
    (r.1.role ≠ .Resetting ∧
     r.2.role ≠ .Resetting ∧
     (if r.1.role == .Unsettled then r.1.errorcount + 1 else 0) <
       (if (C w).1.role == .Unsettled then (C w).1.errorcount + 1 else 0) ∧
     (if r.2.role == .Unsettled then r.2.errorcount + 1 else 0) ≤
       (if (C v).1.role == .Unsettled then (C v).1.errorcount + 1 else 0)) := by
  have hrd :=
    rankDeltaOSSR_unsettled_no_resetting_progress
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C w).1) (t := (C v).1) hw_unsettled (hNoReset v)
  dsimp at hrd ⊢
  rcases hrd with hrd_reset | hrd_prog
  · have h_not_both :
        ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).2.role = .Settled) := by
      intro hboth
      rcases hrd_reset with hreset | hreset
      · rw [hreset] at hboth
        exact Role.noConfusion hboth.1
      · rw [hreset] at hboth
        exact Role.noConfusion hboth.2
    have hpass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
      (h := h_not_both)
    rcases hpass with ⟨hrole₁, _, _, _, _, _, hrole₂, _, _, _, _, _, _, _⟩
    rcases hrd_reset with hreset | hreset
    · exact Or.inl (Or.inl (by rw [hrole₁]; exact hreset))
    · exact Or.inl (Or.inr (by rw [hrole₂]; exact hreset))
  · by_cases hboth :
        (rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).2.role = .Settled
    · by_cases hreset :
          (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1.role = .Resetting ∨
          (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2.role = .Resetting
      · exact Or.inl hreset
      · push_neg at hreset
        have hpre_struct := transitionPEM_prePhase4_structural
          (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        have hpre₁ :
            (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
              (C w).1 (C v).1 (C w).2 (C v).2).1.role = .Settled := by
          rw [hpre_struct.1]
          exact hboth.1
        have hpre₂ :
            (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
              (C w).1 (C v).1 (C w).2 (C v).2).2.role = .Settled := by
          rw [hpre_struct.2.2.2.2.2.2.1]
          exact hboth.2
        have hnotU :=
          transitionPEM_phase4_not_unsettled_of_both_settled
            (n := n) (Rmax := Rmax)
            (a := transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
              (C w).1 (C v).1 (C w).2 (C v).2)
            (x₀ := (C w).2) (x₁ := (C v).2) hpre₁ hpre₂
        refine Or.inr ⟨hreset.1, hreset.2, ?_, ?_⟩
        · have hpos : 0 < (C w).1.errorcount + 1 := Nat.succ_pos _
          simpa [transitionPEM, hnotU.1, hw_unsettled] using hpos
        · simp [transitionPEM, hnotU.2]
    · have hpass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        (h := hboth)
      rcases hpass with
        ⟨hrole₁, _, _, _, _, _, hrole₂, _, _, _, _, _, herr₁, herr₂⟩
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · rw [hrole₁]
        exact hrd_prog.1
      · rw [hrole₂]
        exact hrd_prog.2.1
      · simpa [hrole₁, hrole₂, herr₁, herr₂, hw_unsettled] using hrd_prog.2.2.1
      · simpa [hrole₁, hrole₂, herr₁, herr₂] using hrd_prog.2.2.2

theorem transitionPEM_unsettled_one_step_resetcount_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n}
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let r : AgentState n × AgentState n :=
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
    (r.1.role = .Resetting → r.1.resetcount = Rmax) ∧
    (r.2.role = .Resetting → r.2.resetcount = Rmax) := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let p :=
    transitionPEM_prePhase4 n τ rankDelta (C w).1 (C v).1 (C w).2 (C v).2
  have hrd_rc :=
    rankDeltaOSSR_unsettled_no_resetting_resetcount
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C w).1) (t := (C v).1) hw_unsettled (hNoReset v)
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDelta)
    (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
  by_cases hboth :
      (rankDelta ((C w).1, (C v).1)).1.role = .Settled ∧
      (rankDelta ((C w).1, (C v).1)).2.role = .Settled
  · have hp₁ : p.1.role = .Settled := by
      simpa [p] using hpre.1.trans hboth.1
    have hp₂ : p.2.role = .Settled := by
      simpa [p] using hpre.2.2.2.2.2.2.1.trans hboth.2
    have hphase :=
      phase4_resetting_resetcount
        (n := n) (Rmax := Rmax) (a := p) (x₀ := (C w).2) (x₁ := (C v).2)
        hp₁ hp₂
    simpa [transitionPEM, rankDelta, p] using hphase
  · have hpass :=
      transitionPEM_structural_passthrough
        (n := n) (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDelta)
        (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        hboth
    dsimp [rankDelta] at hrd_rc
    rcases hpass with
      ⟨hrole₁, _, _, _, hrc₁, _, hrole₂, _, _, _, hrc₂, _, _, _⟩
    refine ⟨?_, ?_⟩
    · intro hreset
      rw [hrc₁]
      exact hrd_rc.1 (by
        rw [← hrole₁]
        exact hreset)
    · intro hreset
      rw [hrc₂]
      exact hrd_rc.2 (by
        rw [← hrole₂]
        exact hreset)

theorem transitionPEM_unsettled_one_step_reset_leader_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n}
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let r : AgentState n × AgentState n :=
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
    (r.1.role = .Resetting → r.1.leader = .L) ∧
    (r.2.role = .Resetting → r.2.leader = .L) := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let p :=
    transitionPEM_prePhase4 n τ rankDelta (C w).1 (C v).1 (C w).2 (C v).2
  have hrd_leader :=
    rankDeltaOSSR_unsettled_no_resetting_reset_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C w).1) (t := (C v).1) hw_unsettled (hNoReset v)
  have hpre := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDelta)
    (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
  by_cases hboth :
      (rankDelta ((C w).1, (C v).1)).1.role = .Settled ∧
      (rankDelta ((C w).1, (C v).1)).2.role = .Settled
  · have hp₁ : p.1.role = .Settled := by
      simpa [p] using hpre.1.trans hboth.1
    have hp₂ : p.2.role = .Settled := by
      simpa [p] using hpre.2.2.2.2.2.2.1.trans hboth.2
    have hphase :=
      phase4_resetting_leader
        (n := n) (Rmax := Rmax) (a := p) (x₀ := (C w).2) (x₁ := (C v).2)
        hp₁ hp₂
    simpa [transitionPEM, rankDelta, p] using hphase
  · have hpass :=
      transitionPEM_structural_passthrough
        (n := n) (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDelta)
        (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        hboth
    dsimp [rankDelta] at hrd_leader
    rcases hpass with
      ⟨hrole₁, hleader₁, _, _, _, _, hrole₂, hleader₂, _, _, _, _, _, _⟩
    refine ⟨?_, ?_⟩
    · intro hreset
      rw [hleader₁]
      exact hrd_leader.1 (by
        rw [← hrole₁]
        exact hreset)
    · intro hreset
      rw [hleader₂]
      exact hrd_leader.2 (by
        rw [← hrole₂]
        exact hreset)

theorem unsettled_one_step_progress_reset_snapshot_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting ∧
      (C' x).1.resetcount = Rmax ∧ (C' x).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C' := runPairs P C [(w, v)]
  have hC' : C' = C.step P w v := by
    simp [C', runPairs]
  have hstep :=
    transitionPEM_unsettled_one_step_progress_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hrc :=
    transitionPEM_unsettled_one_step_resetcount_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hleader :=
    transitionPEM_unsettled_one_step_reset_leader_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  dsimp at hstep hrc hleader
  have hfst : (C' w).1 =
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_fst_state P C hwv.symm
  have hsnd : (C' v).1 =
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_snd_state P C hwv.symm hwv
  have hreset_fields :
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    intro y hy_reset
    by_cases hyw : y = w
    · subst y
      rw [congrArg AgentState.resetcount hfst, congrArg AgentState.leader hfst]
      exact ⟨hrc.1 (by rw [← hfst]; exact hy_reset),
        hleader.1 (by rw [← hfst]; exact hy_reset)⟩
    · by_cases hyv : y = v
      · subst y
        rw [congrArg AgentState.resetcount hsnd, congrArg AgentState.leader hsnd]
        exact ⟨hrc.2 (by rw [← hsnd]; exact hy_reset),
          hleader.2 (by rw [← hsnd]; exact hy_reset)⟩
      · exfalso
        rw [hC'] at hy_reset
        unfold Config.step at hy_reset
        simp [hwv.symm, hyw, hyv, hNoReset y] at hy_reset
  rcases hstep with hreset | hprogress
  · rcases hreset with hreset | hreset
    · refine Or.inl ⟨w, ?_, ?_, ?_, hreset_fields⟩
      · rw [hfst]
        exact hreset
      · rw [congrArg AgentState.resetcount hfst]
        exact hrc.1 hreset
      · rw [congrArg AgentState.leader hfst]
        exact hleader.1 hreset
    · refine Or.inl ⟨v, ?_, ?_, ?_, hreset_fields⟩
      · rw [hsnd]
        exact hreset
      · rw [congrArg AgentState.resetcount hsnd]
        exact hrc.2 hreset
      · rw [congrArg AgentState.leader hsnd]
        exact hleader.2 hreset
  · have hNoReset' : ∀ x : Fin n, (C' x).1.role ≠ .Resetting := by
      intro x
      by_cases hxw : x = w
      · subst x
        rw [hfst]
        exact hprogress.1
      · by_cases hxv : x = v
        · subst x
          rw [hsnd]
          exact hprogress.2.1
        · rw [hC']
          unfold Config.step
          simp [hwv.symm, hxw, hxv, hNoReset x]
    have hw_lt :
        unsettledContribution (C' w).1 < unsettledContribution (C w).1 := by
      rw [hfst]
      simpa [unsettledContribution] using hprogress.2.2.1
    have hv_le :
        unsettledContribution (C' v).1 ≤ unsettledContribution (C v).1 := by
      rw [hsnd]
      simpa [unsettledContribution] using hprogress.2.2.2
    have hpointwise :
        ∀ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 ≤ unsettledContribution (C x).1 := by
      intro x _
      by_cases hxw : x = w
      · subst x
        exact le_of_lt hw_lt
      · by_cases hxv : x = v
        · simpa [hxv] using hv_le
        · have hx_state : (C' x).1 = (C x).1 := by
            rw [hC']
            unfold Config.step
            simp [hwv.symm, hxw, hxv]
          rw [hx_state]
    have hstrict :
        ∃ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 < unsettledContribution (C x).1 :=
      ⟨w, Finset.mem_univ w, hw_lt⟩
    refine Or.inr ⟨hNoReset', ?_⟩
    unfold unsettledMass
    exact Finset.sum_lt_sum hpointwise hstrict

theorem unsettled_branch_eventually_reset_snapshot_or_allSettled_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax ∧
        (runPairs P C L w).1.leader = .L ∧
        ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
          (runPairs P C L y).1.resetcount = Rmax ∧
          (runPairs P C L y).1.leader = .L) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax ∧
        (runPairs P C L w).1.leader = .L ∧
        ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
          (runPairs P C L y).1.resetcount = Rmax ∧
          (runPairs P C L y).1.leader = .L) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled)
  have hne_of_fin (w : Fin n) : ∃ v : Fin n, v ≠ w := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard w
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        unsettledMass C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role ≠ .Resetting) →
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting ∧
            (runPairs P C₀ L w).1.resetcount = Rmax ∧
            (runPairs P C₀ L w).1.leader = .L ∧
            ∀ y : Fin n, (runPairs P C₀ L y).1.role = .Resetting →
              (runPairs P C₀ L y).1.resetcount = Rmax ∧
              (runPairs P C₀ L y).1.leader = .L) ∨
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Settled) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hmass hNoReset₀
      by_cases hUn : ∃ w : Fin n, (C₀ w).1.role = .Unsettled
      · rcases hUn with ⟨w, hw_unsettled⟩
        rcases hne_of_fin w with ⟨v, hvw⟩
        have hstep :=
          unsettled_one_step_progress_reset_snapshot_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C₀ (w := w) (v := v) hvw hw_unsettled hNoReset₀
        set C₁ := runPairs P C₀ [(w, v)]
        have hC₁ :
            C₁ =
              runPairs
                (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
                C₀ [(w, v)] := by
          simp [C₁, P]
        rcases hstep with hreset | hprogress
        · refine ⟨[(w, v)], Or.inl ?_⟩
          simpa [P] using hreset
        · have hNoReset₁ : ∀ x : Fin n, (C₁ x).1.role ≠ .Resetting := by
            intro x
            rw [hC₁]
            exact hprogress.1 x
          have hlt : unsettledMass C₁ < k := by
            rw [hC₁]
            rw [← hmass]
            exact hprogress.2
          have htail := ih (unsettledMass C₁) hlt C₁ rfl hNoReset₁
          rcases htail with ⟨Ltail, htail⟩
          refine ⟨(w, v) :: Ltail, ?_⟩
          simp only [runPairs_cons]
          change
            (∃ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Resetting ∧
              (runPairs P C₁ Ltail x).1.resetcount = Rmax ∧
              (runPairs P C₁ Ltail x).1.leader = .L ∧
              ∀ y : Fin n, (runPairs P C₁ Ltail y).1.role = .Resetting →
                (runPairs P C₁ Ltail y).1.resetcount = Rmax ∧
                (runPairs P C₁ Ltail y).1.leader = .L) ∨
            (∀ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Settled)
          exact htail
      · refine ⟨[], Or.inr ?_⟩
        intro w
        simp only [runPairs_nil]
        have hnotU : (C₀ w).1.role ≠ .Unsettled := by
          intro hw
          exact hUn ⟨w, hw⟩
        have hnotR : (C₀ w).1.role ≠ .Resetting := hNoReset₀ w
        cases hrole : (C₀ w).1.role with
        | Resetting => exact False.elim (hnotR hrole)
        | Settled => rfl
        | Unsettled => exact False.elim (hnotU hrole)
  exact hrec (unsettledMass C) C rfl hNoReset

/-- Trank-parametric version of `trigger_reset_from_all_settled_non_InSrank_with_leader`.
The collision-reset transition is trank-independent (both colliding Settled
agents become Resetting with `resetcount = Rmax` and `leader = L`, regardless of
the timer-init parameter `τ`), so the statement holds verbatim for any `τ`. -/
theorem trigger_reset_from_all_settled_non_InSrank_with_leader_trank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C₀ : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C₀ v).1.role = .Settled)
    (hNotInSrank : ¬ InSrank C₀) :
    ∃ u v : Fin n, u ≠ v ∧
      let C' := C₀.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
      (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L := by
  have hNotInj : ¬ Function.Injective (fun v : Fin n => (C₀ v).1.rank) := by
    intro hInj
    exact hNotInSrank ⟨hSettled, hInj⟩
  obtain ⟨u, v, huv, h_same⟩ := exists_collision_of_not_inj hSettled hNotInj
  refine ⟨u, v, huv, ?_⟩
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_tr := transitionPEM_collision_both_resetting (trank := τ) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) (C := C₀) (u := u) (v := v)
    (hSettled u) (hSettled v) h_same
  have h_leader := transitionPEM_collision_both_resetting_leader (trank := τ) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) (C := C₀) (u := u) (v := v)
    (hSettled u) (hSettled v) h_same
  have h_fst := Config.step_fst_state P C₀ huv
  have h_snd := Config.step_snd_state P C₀ huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.role = .Resetting
    exact h_tr.1
  · rw [congrArg AgentState.resetcount h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.resetcount = Rmax
    exact h_tr.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.leader = .L
    exact h_leader.1
  · rw [congrArg AgentState.role h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.role = .Resetting
    exact h_tr.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.resetcount = Rmax
    exact h_tr.2.2.2
  · rw [congrArg AgentState.leader h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.leader = .L
    exact h_leader.2

theorem phase1_no_reset_trigger_snapshot_or_InSrank_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L ∧
          ∀ y : Fin n, (C' y).1.role = .Resetting →
            (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L ∧
          ∀ y : Fin n, (C' y).1.role = .Resetting →
            (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L)
  have hReach :
      ∃ L : List (Fin n × Fin n),
        (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
          (runPairs P C L w).1.resetcount = Rmax ∧
          (runPairs P C L w).1.leader = .L ∧
          ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
            (runPairs P C L y).1.resetcount = Rmax ∧
            (runPairs P C L y).1.leader = .L) ∨
        (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
    by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
    · simpa [P] using
        unsettled_branch_eventually_reset_snapshot_or_allSettled_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 C hUn hNoReset
    · refine ⟨[], Or.inr ?_⟩
      intro w
      simp only [runPairs_nil]
      have hnotU : (C w).1.role ≠ .Unsettled := by
        intro hw
        exact hUn ⟨w, hw⟩
      have hnotR : (C w).1.role ≠ .Resetting := hNoReset w
      cases hrole : (C w).1.role with
      | Resetting => exact False.elim (hnotR hrole)
      | Settled => rfl
      | Unsettled => exact False.elim (hnotU hrole)
  rcases hReach with ⟨L₀, hReach⟩
  rcases hReach with hResetAfter | hAllSettled
  · refine ⟨L₀, ?_⟩
    exact Or.inr hResetAfter
  · set C₀ := runPairs P C L₀
    have hAllSettled₀ : ∀ w : Fin n, (C₀ w).1.role = .Settled := by
      intro w
      simpa [C₀] using hAllSettled w
    by_cases hSrank : InSrank C₀
    · refine ⟨L₀, ?_⟩
      exact Or.inl hSrank
    · obtain ⟨u, v, huv, hcol⟩ :=
        trigger_reset_from_all_settled_non_InSrank_with_leader_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C₀ := C₀) hAllSettled₀ hSrank
      have hsnap :
          ∀ y : Fin n, (runPairs P C₀ [(u, v)] y).1.role = .Resetting →
            (runPairs P C₀ [(u, v)] y).1.resetcount = Rmax ∧
            (runPairs P C₀ [(u, v)] y).1.leader = .L := by
        intro y hy_reset
        by_cases hyu : y = u
        · subst y
          exact ⟨by simpa [P, runPairs] using hcol.2.1,
            by simpa [P, runPairs] using hcol.2.2.1⟩
        · by_cases hyv : y = v
          · subst y
            exact ⟨by simpa [P, runPairs] using hcol.2.2.2.2.1,
              by simpa [P, runPairs] using hcol.2.2.2.2.2⟩
          · have hy_state : runPairs P C₀ [(u, v)] y = C₀ y := by
              simp [runPairs, Config.step, huv, hyu, hyv]
            have hy_settled : (runPairs P C₀ [(u, v)] y).1.role = .Settled := by
              rw [hy_state]
              exact hAllSettled₀ y
            rw [hy_settled] at hy_reset
            cases hy_reset
      refine ⟨L₀ ++ [(u, v)], ?_⟩
      rw [runPairs_append]
      refine Or.inr ⟨u, ?_, ?_, ?_, ?_⟩
      · change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        simpa [P, runPairs] using hcol.1
      · change (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax
        simpa [P, runPairs] using hcol.2.1
      · change (runPairs P C₀ [(u, v)] u).1.leader = .L
        simpa [P, runPairs] using hcol.2.2.1
      · intro y hy_reset
        change (runPairs P C₀ [(u, v)] y).1.resetcount = Rmax ∧
          (runPairs P C₀ [(u, v)] y).1.leader = .L
        exact hsnap y hy_reset

theorem ranking_of_no_reset_with_bad_start_handler_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting)
    (hBad :
      ∀ Cbad : Config (AgentState n) Opinion n,
        BadRankingStart Cbad →
        ∃ L : List (Fin n × Fin n),
          RankingEndpoint
            (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) Cbad L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase1_no_reset_trigger_snapshot_or_InSrank_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hSnapshot
  · by_cases hDone : RankingEndpoint C₁
    · exact
        ranking_goal_of_runPairs_RankingEndpoint_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁) (by simpa [C₁, P] using hDone)
    · obtain ⟨L₂, hEndpoint₂⟩ := hBad C₁ ⟨by simpa [C₁, P] using hSrank, hDone⟩
      have hEndpoint_total :
          RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
        rw [runPairs_append]
        change RankingEndpoint (runPairs P C₁ L₂)
        exact hEndpoint₂
      exact
        ranking_goal_of_runPairs_RankingEndpoint_trank
          (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂) hEndpoint_total
  · rcases hSnapshot with ⟨r, hr_role, hr_rc, hr_L, _hAllSnapshot⟩
    have hReset :
        ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
          Rmax ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
      refine ⟨r, ?_, ?_, ?_⟩
      · simpa [C₁, P] using hr_role
      · have hrc : (C₁ r).1.resetcount = Rmax := by
          simpa [C₁, P] using hr_rc
        rw [hrc]
      · simpa [C₁, P] using hr_L
    obtain ⟨L₂, hEndpoint₂⟩ :=
      reset_snapshot_to_RankingEndpoint_log
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₁ hReset
    have hEndpoint_total :
        RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem ranking_of_no_reset_by_parity_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hpar : n % 2 = 0
  · exact
      ranking_of_no_reset_with_bad_start_handler_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hNoReset
        (fun Cbad hbad =>
          BadRankingStart_even_to_RankingEndpoint_log
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog hbad hpar)
  · exact
      ranking_of_no_reset_with_bad_start_handler_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hNoReset
        (fun Cbad hbad =>
          BadRankingStart_odd_to_RankingEndpoint_log
            (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog hbad hpar)

theorem follower_dormant_or_nonresetting_to_ranking_goal_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    follower_dormant_or_nonresetting_to_no_reset_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hClean
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨γ₂, t₂, hgoal₂⟩ :=
    ranking_of_no_reset_by_parity_log
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C₁ hNoResetC₁
  exact
    exists_schedule_after_runPairs
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      P C L₁ ⟨γ₂, t₂, by simpa [C₁, P] using hgoal₂⟩

theorem ranking_from_settled_root_zero_resetting_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hResetZero : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    settled_root_zero_resetting_to_no_reset_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hℓ_settled hℓ_rank0 hℓ_children hℓ_L hResetZero
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨γ₂, t₂, hgoal₂⟩ :=
    ranking_of_no_reset_by_parity_log
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C₁ hNoResetC₁
  exact
    exists_schedule_after_runPairs
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      P C L₁ ⟨γ₂, t₂, by simpa [C₁, P] using hgoal₂⟩

theorem ranking_from_all_resetting_zero_no_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hClean : FollowerDormantOrNonResetting C := by
    intro w
    refine Or.inl ⟨hAllReset w, hAllZero w, ?_⟩
    cases hleader : (C w).1.leader with
    | L => exact False.elim ((hNoLeader w) hleader)
    | F => rfl
  exact
    follower_dormant_or_nonresetting_to_ranking_goal_log
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog C hClean

theorem ranking_from_all_resetting_zero_unique_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax_pos : 0 < Dmax) (hRmax_pos : 0 < Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hDormant : IsDormantConfig C := by
    refine ⟨hAllReset, hAllZero, hUniqueLeader, ?_⟩
    intro w
    cases (C w).1.leader <;> simp
  obtain ⟨L, hEndpoint⟩ :=
    dormant_to_RankingEndpoint_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C hDormant
  exact
    ranking_goal_of_runPairs_RankingEndpoint_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

set_option maxHeartbeats 32000000 in
/-- trank-generalized `transitionPEM_dormant_leader_low_dt_L_partner_wakes`.
The `trank` argument only feeds the Settled-timer; the conclusions about
role/rank/children/leader/resetcount are `trank`-independent. -/
theorem transitionPEM_dormant_leader_low_dt_L_partner_wakes_trank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : (C ℓ).1.delaytimer ≤ 1) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_L : (C w).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank.val = 0 ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    ((C' w).1.role = .Settled ∨
      ((C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0 ∧
        (C' w).1.leader = .L)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let p :=
    transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
      (C ℓ).1 (C w).1 (C ℓ).2 (C w).2
  have h_rd :=
    rankDeltaOSSR_dormant_leader_low_dt_L_partner_wakes
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_L
  have hpre :=
    transitionPEM_prePhase4_structural
      (trank := τ)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C ℓ).1) (s₁ := (C w).1)
      (x₀ := (C ℓ).2) (x₁ := (C w).2)
  have hp₁_role : p.1.role = .Settled := by
    dsimp [p]
    rw [hpre.1]
    exact h_rd.1
  have hp₁_rank0 : p.1.rank.val = 0 := by
    dsimp [p]
    rw [hpre.2.2.1, h_rd.2.1]
  have hp₁_children : p.1.children = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.1]
    exact h_rd.2.2.1
  have hp₁_leader : p.1.leader = .L := by
    dsimp [p]
    rw [hpre.2.1]
    exact h_rd.2.2.2.1
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  rcases h_rd.2.2.2.2 with hsettled | hreset
  · have hp₂_role : p.2.role = .Settled := by
      dsimp [p]
      rw [hpre.2.2.2.2.2.2.1]
      exact hsettled.1
    have hp₂_rank0 : p.2.rank.val = 0 := by
      dsimp [p]
      rw [hpre.2.2.2.2.2.2.2.2.1, hsettled.2.1]
    have hphase :
        transitionPEM_phase4 n Rmax p (C ℓ).2 (C w).2 = p := by
      exact
        transitionPEM_phase4_rank0_pair_id
          (n := n) (Rmax := Rmax) hn4
          (a₀ := p.1) (a₁ := p.2)
          (x₀ := (C ℓ).2) (x₁ := (C w).2)
          hp₁_role hp₂_role hp₁_rank0 hp₂_rank0
    refine ⟨?_, ?_, ?_, ?_, Or.inl ?_⟩
    · rw [congrArg AgentState.role h_fst]
      change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_role
    · rw [congrArg AgentState.rank h_fst]
      change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_rank0
    · rw [congrArg AgentState.children h_fst]
      change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.children = 0
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_children
    · rw [congrArg AgentState.leader h_fst]
      change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.leader = .L
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_leader
    · rw [congrArg AgentState.role h_snd]
      change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.role = .Settled
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₂_role
  · have h_not_both :
        ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
      intro hboth
      rw [hreset.1] at hboth
      exact Role.noConfusion hboth.2
    have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
    refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [congrArg AgentState.role h_fst]
      exact h_pass.1 ▸ h_rd.1
    · rw [congrArg AgentState.rank h_fst]
      exact congrArg Fin.val (h_pass.2.2.1 ▸ h_rd.2.1)
    · rw [congrArg AgentState.children h_fst]
      exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
    · rw [congrArg AgentState.leader h_fst]
      exact h_pass.2.1 ▸ h_rd.2.2.2.1
    · rw [congrArg AgentState.role h_snd]
      exact h_pass.2.2.2.2.2.2.1 ▸ hreset.1
    · rw [congrArg AgentState.resetcount h_snd]
      exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ hreset.2.1
    · rw [congrArg AgentState.leader h_snd]
      exact h_pass.2.2.2.2.2.2.2.1 ▸ hreset.2.2

set_option maxHeartbeats 8000000 in
theorem ranking_from_all_resetting_zero_with_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hRmax_pos : 0 < Rmax := by omega
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        resetLeaderCount C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (∀ w : Fin n, (C₀ w).1.resetcount = 0) →
        (∃ ℓ : Fin n, (C₀ ℓ).1.leader = .L) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using go (resetLeaderCount C) C rfl hAllReset hAllZero hHasLeader
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hk hAllR hAll0 hHasL
    by_cases hUnique : ∃! ℓ : Fin n, (C₀ ℓ).1.leader = .L
    · simpa [P] using
        ranking_from_all_resetting_zero_unique_leader_log
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax_pos hRmax_pos C₀ hAllR hAll0 hUnique
    · obtain ⟨ℓ, hℓ_L⟩ := hHasL
      have hOther : ∃ w : Fin n, w ≠ ℓ ∧ (C₀ w).1.leader = .L := by
        by_contra hnone
        push_neg at hnone
        apply hUnique
        refine ⟨ℓ, hℓ_L, ?_⟩
        intro y hyL
        by_contra hy_ne
        exact hnone y hy_ne hyL
      obtain ⟨w, hw_ne_ℓ, hw_L⟩ := hOther
      have hℓw : ℓ ≠ w := hw_ne_ℓ.symm
      by_cases hℓ_high : 1 < (C₀ ℓ).1.delaytimer
      · by_cases hw_high : 1 < (C₀ w).1.delaytimer
        · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
          have hstep :=
            step_leader_dedup_trace_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
              hℓ_high hw_high
          have hAllR₁ : ∀ x : Fin n, (C₁ x).1.role = .Resetting := by
            intro x
            by_cases hxℓ : x = ℓ
            · subst x
              exact hstep.1
            · by_cases hxw : x = w
              · subst x
                exact hstep.2.2.2.2.1
              · rw [show C₁ x = C₀ x from hstep.2.2.2.2.2.2.2.2 x hxℓ hxw]
                exact hAllR x
          have hAll0₁ : ∀ x : Fin n, (C₁ x).1.resetcount = 0 := by
            intro x
            by_cases hxℓ : x = ℓ
            · subst x
              exact hstep.2.1
            · by_cases hxw : x = w
              · subst x
                exact hstep.2.2.2.2.2.1
              · rw [show C₁ x = C₀ x from hstep.2.2.2.2.2.2.2.2 x hxℓ hxw]
                exact hAll0 x
          have hHasL₁ : ∃ x : Fin n, (C₁ x).1.leader = .L :=
            ⟨ℓ, hstep.2.2.1⟩
          have hcount_lt : resetLeaderCount C₁ < resetLeaderCount C₀ := by
            simpa [P, C₁] using
              (step_leader_dedup_resetLeaderCount_lt_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (ℓ := ℓ) (w := w) hℓw
                (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
                hℓ_high hw_high)
          have hgoal₁ :=
            IH (resetLeaderCount C₁) (by omega) C₁ rfl hAllR₁ hAll0₁ hHasL₁
          exact
            ranking_goal_of_step_ranking_goal_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := ℓ) (v := w)
              (by simpa [P, C₁] using hgoal₁)
        · have hw_low : (C₀ w).1.delaytimer ≤ 1 := by omega
          let C₁ : Config (AgentState n) Opinion n := C₀.step P w ℓ
          have hstep :=
            transitionPEM_dormant_leader_low_dt_L_partner_wakes_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 (C := C₀) (ℓ := w) (w := ℓ) hw_ne_ℓ
              (hAllR w) (hAll0 w) hw_low hw_L (hAllR ℓ) (hAll0 ℓ) hℓ_L
          have hResetZero₁ :
              ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
            intro x hx_reset
            by_cases hxw : x = w
            · subst x
              rw [hstep.1] at hx_reset
              cases hx_reset
            · by_cases hxℓ : x = ℓ
              · subst x
                rcases hstep.2.2.2.2 with hsettled | hreset
                · rw [hsettled] at hx_reset
                  cases hx_reset
                · exact hreset.2.1
              · have hx_old : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, hw_ne_ℓ, hxw, hxℓ]
                rw [hx_old] at hx_reset ⊢
                exact hAll0 x
          have hgoal₁ :=
            ranking_from_settled_root_zero_resetting_log
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₁
              (ℓ := w) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
          exact
            ranking_goal_of_step_ranking_goal_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := w) (v := ℓ)
              (by simpa [P, C₁] using hgoal₁)
      · have hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1 := by omega
        let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        have hstep :=
          transitionPEM_dormant_leader_low_dt_L_partner_wakes_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAll0 ℓ) hℓ_low hℓ_L (hAllR w) (hAll0 w) hw_L
        have hResetZero₁ :
            ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
          intro x hx_reset
          by_cases hxℓ : x = ℓ
          · subst x
            rw [hstep.1] at hx_reset
            cases hx_reset
          · by_cases hxw : x = w
            · subst x
              rcases hstep.2.2.2.2 with hsettled | hreset
              · rw [hsettled] at hx_reset
                cases hx_reset
              · exact hreset.2.1
            · have hx_old : C₁ x = C₀ x := by
                dsimp [C₁, P]
                simp [Config.step, hℓw, hxℓ, hxw]
              rw [hx_old] at hx_reset ⊢
              exact hAll0 x
        have hgoal₁ :=
          ranking_from_settled_root_zero_resetting_log
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog C₁
            (ℓ := ℓ) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
        exact
          ranking_goal_of_step_ranking_goal_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (u := ℓ) (v := w)
            (by simpa [P, C₁] using hgoal₁)

theorem ranking_from_all_resetting_zero_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L
  · exact
      ranking_from_all_resetting_zero_with_leader_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hAllReset hAllZero hHasLeader
  · exact
      ranking_from_all_resetting_zero_no_leader_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hAllReset hAllZero
        (by
          intro w hwL
          exact hHasLeader ⟨w, hwL⟩)

set_option maxHeartbeats 16000000 in
theorem ranking_from_all_resetting_single_pos_leader_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v hℓv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, _hℓ_L₁, hv_role₁, hv_rc₁, _hv_F₁, hothers₁⟩ :=
      drain_L_pos_any_zero_to_zero_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_pos hv_zero hℓ_L hv_high
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hℓ_role₁
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hv_role₁
        · dsimp [C₁]
          rw [hothers₁ w hwℓ hwv]
          exact hAllReset w
    have hAllZero₁ : ∀ w : Fin n, (C₁ w).1.resetcount = 0 := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hℓ_rc₁
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hv_rc₁
        · dsimp [C₁]
          rw [hothers₁ w hwℓ hwv]
          exact hOnlyPos w hwℓ
    have hgoal₁ :=
      ranking_from_all_resetting_zero_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₁ hAllReset₁ hAllZero₁
    exact
      ranking_goal_of_runPairs_ranking_goal_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁)
        (by simpa [C₁, P] using hgoal₁)
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    by_cases hgt : 1 < (C ℓ).1.resetcount
    · have hstep :=
        step_L_pos_any_zero_gt_one_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C hℓv (hAllReset ℓ) (hAllReset v) hgt hv_zero hℓ_L
      let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
      have hℓ_role₁ : (C₁ ℓ).1.role = .Resetting := by
        simpa [C₁, P] using hstep.1
      have hv_role₁ : (C₁ v).1.role = .Resetting := by
        simpa [C₁, P] using hstep.2.1
      have hℓ_rc₁ : (C₁ ℓ).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      have hv_rc₁ : (C₁ v).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
        rw [hℓ_rc₁]; omega
      have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
        rw [hv_rc₁]; omega
      obtain ⟨L₂, hℓ_fresh₂, hv_fresh₂, hothers₂⟩ :=
        drain_pair_rc_with_both_delay
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax1 C₁ hℓv hℓ_role₁ hv_role₁ hℓ_pos₁ hv_pos₁
      let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
      have hothers_step : ∀ w : Fin n, w ≠ ℓ → w ≠ v → C₁ w = C w := by
        intro w hwℓ hwv
        simp [C₁, Config.step, P, hℓv, hwℓ, hwv]
      have hAllReset₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          exact hℓ_fresh₂.1
        · by_cases hwv : w = v
          · subst w
            exact hv_fresh₂.1
          · dsimp [C₂]
            rw [hothers₂ w hwℓ hwv, hothers_step w hwℓ hwv]
            exact hAllReset w
      have hAllZero₂ : ∀ w : Fin n, (C₂ w).1.resetcount = 0 := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          exact hℓ_fresh₂.2.1
        · by_cases hwv : w = v
          · subst w
            exact hv_fresh₂.2.1
          · dsimp [C₂]
            rw [hothers₂ w hwℓ hwv, hothers_step w hwℓ hwv]
            exact hOnlyPos w hwℓ
      have hgoal₂ :=
        ranking_from_all_resetting_zero_log
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₂ hAllReset₂ hAllZero₂
      have hgoal₁ :=
        ranking_goal_of_runPairs_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C₁) (L := L₂)
          (by simpa [C₂, P] using hgoal₂)
      exact
        ranking_goal_of_step_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := ℓ) (v := v)
          (by simpa [C₁, P] using hgoal₁)
    · have hℓ_one : (C ℓ).1.resetcount = 1 := by omega
      cases hv_leader : (C v).1.leader with
      | L =>
          have hstep :=
            step_L_pos_one_L_zero_low_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
              hℓ_L hv_leader hv_low
          let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
          have hResetZero₁ :
              ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
            intro w hw_reset
            by_cases hwℓ : w = ℓ
            · subst w
              simpa [C₁, P] using hstep.2.1
            · by_cases hwv : w = v
              · subst w
                have hv_settled : (C₁ v).1.role = .Settled := by
                  simpa [C₁, P] using hstep.2.2.2.2.1
                rw [hv_settled] at hw_reset
                cases hw_reset
              · have hw_old : C₁ w = C w := by
                  dsimp [C₁, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                rw [hw_old] at hw_reset ⊢
                exact hOnlyPos w hwℓ
          have hgoal₁ :=
            ranking_from_settled_root_zero_resetting_log
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₁ (ℓ := v)
              (by simpa [C₁, P] using hstep.2.2.2.2.1)
              (by simpa [C₁, P] using hstep.2.2.2.2.2.1)
              (by simpa [C₁, P] using hstep.2.2.2.2.2.2.1)
              (by simpa [C₁, P] using hstep.2.2.2.2.2.2.2)
              hResetZero₁
          exact
            ranking_goal_of_step_ranking_goal_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C) (u := ℓ) (v := v)
              (by simpa [C₁, P] using hgoal₁)
      | F =>
          have hstep₁ :=
            step_L_pos_one_F_zero_low_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
              hℓ_L hv_leader hv_low
          let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
          have hstep₂ :=
            transitionPEM_dormant_leader_with_unsettled_follower_wakes_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (ℓ := ℓ) (w := v) hℓv
              (by simpa [C₁, P] using hstep₁.1)
              (by simpa [C₁, P] using hstep₁.2.1)
              (by simpa [C₁, P] using hstep₁.2.2.1)
              (by simpa [C₁, P] using hstep₁.2.2.2.2.1)
              (by simpa [C₁, P] using hstep₁.2.2.2.2.2)
          let C₂ : Config (AgentState n) Opinion n := C₁.step P ℓ v
          have hResetZero₂ :
              ∀ w : Fin n, (C₂ w).1.role = .Resetting → (C₂ w).1.resetcount = 0 := by
            intro w hw_reset
            by_cases hwℓ : w = ℓ
            · subst w
              have hsettled : (C₂ ℓ).1.role = .Settled := by
                simpa [C₂, P] using hstep₂.1
              rw [hsettled] at hw_reset
              cases hw_reset
            · by_cases hwv : w = v
              · subst w
                have hun : (C₂ v).1.role = .Unsettled := by
                  simpa [C₂, P] using hstep₂.2.2.2.2.1
                rw [hun] at hw_reset
                cases hw_reset
              · have hw_old₂ : C₂ w = C₁ w := by
                  dsimp [C₂, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                have hw_old₁ : C₁ w = C w := by
                  dsimp [C₁, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                rw [hw_old₂, hw_old₁] at hw_reset ⊢
                exact hOnlyPos w hwℓ
          have hgoal₂ :=
            ranking_from_settled_root_zero_resetting_log
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₂ (ℓ := ℓ)
              (by simpa [C₂, P] using hstep₂.1)
              (by
                have hrank : (C₂ ℓ).1.rank = ⟨0, hn⟩ := by
                  simpa [C₂, P] using hstep₂.2.1
                rw [hrank])
              (by simpa [C₂, P] using hstep₂.2.2.1)
              (by simpa [C₂, P] using hstep₂.2.2.2.1)
              hResetZero₂
          have hgoal₁ :=
            ranking_goal_of_step_ranking_goal_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (u := ℓ) (v := v)
              (by simpa [C₂, P] using hgoal₂)
          exact
            ranking_goal_of_step_ranking_goal_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C) (u := ℓ) (v := v)
              (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 16000000 in
theorem ranking_from_all_resetting_single_pos_follower_F_partner_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {u v : Fin n}
    (huv : u ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllF : ∀ w : Fin n, (C w).1.leader = .F)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hu_pos : 0 < (C u).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ u → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v huv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · obtain ⟨L₁, hu_role₁, hu_rc₁, hu_F₁, hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
      drain_F_pos_F_zero_to_zero_FF_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_pos C huv (hAllReset u) (hAllReset v) hu_pos hv_zero
        hu_F hv_F hv_high
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hClean₁ : FollowerDormantOrNonResetting C₁ := by
      intro w
      by_cases hwu : w = u
      · subst w
        exact Or.inl ⟨by simpa [C₁, P] using hu_role₁,
          by simpa [C₁, P] using hu_rc₁,
          by simpa [C₁, P] using hu_F₁⟩
      · by_cases hwv : w = v
        · subst w
          exact Or.inl ⟨by simpa [C₁, P] using hv_role₁,
            by simpa [C₁, P] using hv_rc₁,
            by simpa [C₁, P] using hv_F₁⟩
        · dsimp [C₁]
          rw [hothers₁ w hwu hwv]
          exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
    have hgoal₁ :=
      follower_dormant_or_nonresetting_to_ranking_goal_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₁ hClean₁
    exact
      ranking_goal_of_runPairs_ranking_goal_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁)
        (by simpa [C₁, P] using hgoal₁)
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    by_cases hu_gt : 1 < (C u).1.resetcount
    · have hstep :=
        step_F_pos_F_zero_gt_one_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C huv (hAllReset u) (hAllReset v) hu_gt hv_zero hu_F hv_F
      let C₁ : Config (AgentState n) Opinion n := C.step P u v
      have hu_role₁ : (C₁ u).1.role = .Resetting := by
        simpa [C₁, P] using hstep.1
      have hv_role₁ : (C₁ v).1.role = .Resetting := by
        simpa [C₁, P] using hstep.2.1
      have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
        rw [hu_rc₁]; omega
      have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
        rw [hv_rc₁]; omega
      obtain ⟨L₂, hu_role₂, hu_rc₂, hu_F₂, hv_role₂, hv_rc₂, hv_F₂, hothers₂⟩ :=
        drain_pair_rc_FF_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁
          (by simpa [C₁, P] using hstep.2.2.2.2.1)
          (by simpa [C₁, P] using hstep.2.2.2.2.2)
      let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
      have hothers_step : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
        intro w hwu hwv
        simp [C₁, Config.step, P, huv, hwu, hwv]
      have hClean₂ : FollowerDormantOrNonResetting C₂ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₂, P] using hu_role₂,
            by simpa [C₂, P] using hu_rc₂,
            by simpa [C₂, P] using hu_F₂⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inl ⟨by simpa [C₂, P] using hv_role₂,
              by simpa [C₂, P] using hv_rc₂,
              by simpa [C₂, P] using hv_F₂⟩
          · dsimp [C₂]
            rw [hothers₂ w hwu hwv, hothers_step w hwu hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₂ :=
        follower_dormant_or_nonresetting_to_ranking_goal_log
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₂ hClean₂
      have hgoal₁ :=
        ranking_goal_of_runPairs_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C₁) (L := L₂)
          (by simpa [C₂, P] using hgoal₂)
      exact
        ranking_goal_of_step_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)
    · have hu_one : (C u).1.resetcount = 1 := by omega
      have hstep :=
        step_F_pos_one_F_zero_low_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C huv (hAllReset u) (hAllReset v) hu_one hv_zero hu_F hv_F hv_low
      let C₁ : Config (AgentState n) Opinion n := C.step P u v
      have hClean₁ : FollowerDormantOrNonResetting C₁ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₁, P] using hstep.1,
            by simpa [C₁, P] using hstep.2.1,
            by simpa [C₁, P] using hstep.2.2.1⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inr (by
              intro hv_reset
              have hv_un : (C₁ v).1.role = .Unsettled := by
                simpa [C₁, P] using hstep.2.2.2.2.1
              rw [hv_un] at hv_reset
              cases hv_reset)
          · dsimp [C₁]
            simp [Config.step, P, huv, hwu, hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₁ :=
        follower_dormant_or_nonresetting_to_ranking_goal_log
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₁ hClean₁
      exact
        ranking_goal_of_step_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 16000000 in
theorem ranking_from_all_resetting_single_pos_follower_L_partner_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {u ℓ : Fin n}
    (hℓu : ℓ ≠ u)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hu_F : (C u).1.leader = .F) (hℓ_L : (C ℓ).1.leader = .L)
    (hu_pos : 0 < (C u).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ u → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hℓ_zero : (C ℓ).1.resetcount = 0 := hOnlyPos ℓ hℓu
  by_cases hu_gt : 1 < (C u).1.resetcount
  · have hstep :=
      step_L_zero_F_pos_gt_one_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hℓu (hAllReset ℓ) (hAllReset u) hℓ_zero hu_gt hℓ_L hu_F
    let C₁ : Config (AgentState n) Opinion n := C.step P ℓ u
    have hℓ_role₁ : (C₁ ℓ).1.role = .Resetting := by
      simpa [C₁, P] using hstep.1
    have hu_role₁ : (C₁ u).1.role = .Resetting := by
      simpa [C₁, P] using hstep.2.1
    have hℓ_rc₁ : (C₁ ℓ).1.resetcount = (C u).1.resetcount - 1 := by
      simpa [C₁, P] using hstep.2.2.1
    have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
      simpa [C₁, P] using hstep.2.2.2.1
    have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
      rw [hℓ_rc₁]; omega
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]; omega
    obtain ⟨L₂, hℓ_fresh₂, hu_fresh₂, hothers₂⟩ :=
      drain_pair_rc_with_both_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax1 C₁ hℓu hℓ_role₁ hu_role₁ hℓ_pos₁ hu_pos₁
    let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
    have hothers_step : ∀ w : Fin n, w ≠ ℓ → w ≠ u → C₁ w = C w := by
      intro w hwℓ hwu
      simp [C₁, Config.step, P, hℓu, hwℓ, hwu]
    have hAllReset₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        exact hℓ_fresh₂.1
      · by_cases hwu : w = u
        · subst w
          exact hu_fresh₂.1
        · dsimp [C₂]
          rw [hothers₂ w hwℓ hwu, hothers_step w hwℓ hwu]
          exact hAllReset w
    have hAllZero₂ : ∀ w : Fin n, (C₂ w).1.resetcount = 0 := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        exact hℓ_fresh₂.2.1
      · by_cases hwu : w = u
        · subst w
          exact hu_fresh₂.2.1
        · dsimp [C₂]
          rw [hothers₂ w hwℓ hwu, hothers_step w hwℓ hwu]
          exact hOnlyPos w hwu
    have hgoal₂ :=
      ranking_from_all_resetting_zero_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C₂ hAllReset₂ hAllZero₂
    have hgoal₁ :=
      ranking_goal_of_runPairs_ranking_goal_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C₁) (L := L₂)
        (by simpa [C₂, P] using hgoal₂)
    exact
      ranking_goal_of_step_ranking_goal_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := ℓ) (v := u)
        (by simpa [C₁, P] using hgoal₁)
  · have hu_one : (C u).1.resetcount = 1 := by omega
    by_cases hℓ_high : 1 < (C ℓ).1.delaytimer
    · have hstep :=
        step_L_zero_F_pos_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C hℓu (hAllReset ℓ) (hAllReset u)
          hℓ_zero hu_pos hℓ_L hu_F hℓ_high
      let C₁ : Config (AgentState n) Opinion n := C.step P ℓ u
      have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          simpa [C₁, P] using hstep.1
        · by_cases hwu : w = u
          · subst w
            simpa [C₁, P] using hstep.2.1
          · dsimp [C₁]
            simp [Config.step, P, hℓu, hwℓ, hwu]
            exact hAllReset w
      have hAllZero₁ : ∀ w : Fin n, (C₁ w).1.resetcount = 0 := by
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          have hrc : (C₁ ℓ).1.resetcount = (C u).1.resetcount - 1 := by
            simpa [C₁, P] using hstep.2.2.1
          rw [hrc, hu_one]
        · by_cases hwu : w = u
          · subst w
            have hrc : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
              simpa [C₁, P] using hstep.2.2.2.1
            rw [hrc, hu_one]
          · dsimp [C₁]
            simp [Config.step, P, hℓu, hwℓ, hwu]
            exact hOnlyPos w hwu
      have hgoal₁ :=
        ranking_from_all_resetting_zero_log
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₁ hAllReset₁ hAllZero₁
      exact
        ranking_goal_of_step_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := ℓ) (v := u)
          (by simpa [C₁, P] using hgoal₁)
    · have hℓ_low : (C ℓ).1.delaytimer ≤ 1 := by omega
      have hstep :=
        step_L_zero_F_pos_one_low_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C hℓu (hAllReset ℓ) (hAllReset u)
          hℓ_zero hu_one hℓ_L hu_F hℓ_low
      let C₁ : Config (AgentState n) Opinion n := C.step P ℓ u
      have hResetZero₁ :
          ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
        intro w hw_reset
        by_cases hwℓ : w = ℓ
        · subst w
          have hsettled : (C₁ ℓ).1.role = .Settled := by
            simpa [C₁, P] using hstep.1
          rw [hsettled] at hw_reset
          cases hw_reset
        · by_cases hwu : w = u
          · subst w
            simpa [C₁, P] using hstep.2.2.2.2.2.1
          · have hw_old : C₁ w = C w := by
              dsimp [C₁, P]
              simp [Config.step, hℓu, hwℓ, hwu]
            rw [hw_old] at hw_reset ⊢
            exact hOnlyPos w hwu
      have hgoal₁ :=
        ranking_from_settled_root_zero_resetting_log
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax1 hRlog C₁ (ℓ := ℓ)
          (by simpa [C₁, P] using hstep.1)
          (by simpa [C₁, P] using hstep.2.1)
          (by simpa [C₁, P] using hstep.2.2.1)
          (by simpa [C₁, P] using hstep.2.2.2.1)
          hResetZero₁
      exact
        ranking_goal_of_step_ranking_goal_trank
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := ℓ) (v := u)
          (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 32000000 in
theorem ranking_from_all_resetting_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcAgents C₀).card = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using go (positiveRcAgents C).card C rfl hAllReset
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
      intro C₀ hcard hAllReset₀
      by_cases hcard0 : k = 0
      · have hAllZero₀ : ∀ w : Fin n, (C₀ w).1.resetcount = 0 := by
          apply positiveRcAgents_eq_zero_iff.mp
          rw [hcard, hcard0]
        simpa [P] using
          ranking_from_all_resetting_zero_log
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 hRlog C₀ hAllReset₀ hAllZero₀
      · have hcard_pos : 0 < (positiveRcAgents C₀).card := by
          rw [hcard]
          omega
        obtain ⟨u, hu_pos⟩ :=
          positiveRcAgents_exists_of_card_pos (C := C₀) hcard_pos
        by_cases hSecond : ∃ v : Fin n, v ≠ u ∧ 0 < (C₀ v).1.resetcount
        · obtain ⟨v, hv_ne, hv_pos⟩ := hSecond
          have huv : u ≠ v := hv_ne.symm
          obtain ⟨L₁, hu_fresh₁, hv_fresh₁, hothers₁⟩ :=
            drain_pair_rc_with_both_delay
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax1 C₀ huv (hAllReset₀ u) (hAllReset₀ v) hu_pos hv_pos
          let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ L₁
          have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
            intro w
            by_cases hwu : w = u
            · subst w
              exact hu_fresh₁.1
            · by_cases hwv : w = v
              · subst w
                exact hv_fresh₁.1
              · dsimp [C₁]
                rw [hothers₁ w hwu hwv]
                exact hAllReset₀ w
          have hsub : positiveRcAgents C₁ ⊆ (positiveRcAgents C₀).erase u := by
            intro w hw_mem
            rw [positiveRcAgents, Finset.mem_filter] at hw_mem
            have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hwu
              subst w
              rw [hu_fresh₁.2.1] at hw_pos
              omega
            · rw [positiveRcAgents, Finset.mem_filter]
              by_cases hwv : w = v
              · subst w
                rw [hv_fresh₁.2.1] at hw_pos
                omega
              · have hwu : w ≠ u := by
                  intro hwu
                  subst w
                  rw [hu_fresh₁.2.1] at hw_pos
                  omega
                have hw_old : C₁ w = C₀ w := hothers₁ w hwu hwv
                have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                  rwa [hw_old] at hw_pos
                exact ⟨Finset.mem_univ w, hw_old_pos⟩
          have hu_mem_old : u ∈ positiveRcAgents C₀ := by
            rw [positiveRcAgents, Finset.mem_filter]
            exact ⟨Finset.mem_univ u, hu_pos⟩
          have hcard₁_lt : (positiveRcAgents C₁).card < k := by
            have hle := Finset.card_le_card hsub
            have herase :
                ((positiveRcAgents C₀).erase u).card =
                  (positiveRcAgents C₀).card - 1 :=
              Finset.card_erase_of_mem hu_mem_old
            rw [herase, hcard] at hle
            omega
          have hgoal₁ :=
            IH (positiveRcAgents C₁).card hcard₁_lt C₁ rfl hAllReset₁
          exact
            ranking_goal_of_runPairs_ranking_goal_trank
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (L := L₁)
              (by simpa [C₁, P] using hgoal₁)
        · push_neg at hSecond
          have hOnlyPos : ∀ w : Fin n, w ≠ u → (C₀ w).1.resetcount = 0 := by
            intro w hw
            have hle : (C₀ w).1.resetcount ≤ 0 := hSecond w hw
            omega
          have hcard_fin : 1 < Fintype.card (Fin n) := by
            rw [Fintype.card_fin]
            omega
          obtain ⟨v, hv_ne_u⟩ := Fintype.exists_ne_of_one_lt_card hcard_fin u
          cases hu_leader : (C₀ u).1.leader with
          | L =>
              simpa [P] using
                ranking_from_all_resetting_single_pos_leader_log
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog C₀ hv_ne_u.symm hAllReset₀ hu_leader hu_pos
                  hOnlyPos
          | F =>
              by_cases hHasLeader : ∃ ℓ : Fin n, (C₀ ℓ).1.leader = .L
              · obtain ⟨ℓ, hℓ_L⟩ := hHasLeader
                have hℓu : ℓ ≠ u := by
                  intro h
                  subst ℓ
                  rw [hu_leader] at hℓ_L
                  cases hℓ_L
                simpa [P] using
                  ranking_from_all_resetting_single_pos_follower_L_partner_log
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax1 hRlog C₀ hℓu hAllReset₀ hu_leader hℓ_L hu_pos
                    hOnlyPos
              · have hAllF : ∀ w : Fin n, (C₀ w).1.leader = .F := by
                  intro w
                  cases hw_leader : (C₀ w).1.leader with
                  | L => exact False.elim (hHasLeader ⟨w, hw_leader⟩)
                  | F => rfl
                simpa [P] using
                  ranking_from_all_resetting_single_pos_follower_F_partner_log
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax1 hRlog C₀ hv_ne_u.symm hAllReset₀ hAllF
                    hu_leader (hAllF v) hu_pos hOnlyPos

set_option maxHeartbeats 32000000 in
theorem partial_resetting_to_ranking_goal_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSomeReset : ∃ r : Fin n, (C r).1.role = .Resetting)
    (hNotAllReset : ¬ ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices h_aux :
      ∀ k : ℕ, ∀ C' : Config (AgentState n) Opinion n,
        resetFuel C' ≤ k →
        (∃ r : Fin n, (C' r).1.role = .Resetting) →
        (¬ ∀ w : Fin n, (C' w).1.role = .Resetting) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C' γ t) ∧
          ((∀ μ : Fin n,
            (execution P C' γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C' γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C' γ t)) by
    simpa [P] using h_aux (resetFuel C) C le_rfl hSomeReset hNotAllReset
  intro k
  induction k with
  | zero =>
      intro C' hF hSome _hNot
      obtain ⟨r, hr⟩ := hSome
      have hcontrib_pos : 0 < resetFuelContribution (C' r).1 := by
        unfold resetFuelContribution
        rw [if_pos hr]
        exact Nat.pow_pos (by decide : (0 : ℕ) < 2)
      have hsum_pos :
          0 < ∑ w : Fin n, resetFuelContribution (C' w).1 := by
        refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ?_
        exact ⟨r, Finset.mem_univ r, hcontrib_pos⟩
      have hf_pos : 0 < resetFuel C' := by
        unfold resetFuel
        omega
      omega
  | succ k ih =>
      intro C' hF hSome hNot
      obtain ⟨r, hr_res⟩ := hSome
      push_neg at hNot
      obtain ⟨v, hv_not⟩ := hNot
      have hrv : r ≠ v := fun heq => by
        subst heq
        exact hv_not hr_res
      let C₁ : Config (AgentState n) Opinion n := C'.step P r v
      have dispatch_after_step :
          resetFuel C₁ < resetFuel C' →
          ∃ (γ : DetScheduler n) (t : ℕ),
            InSrank (execution P C₁ γ t) ∧
            ((∀ μ : Fin n,
              (execution P C₁ γ t μ).1.rank.val + 1 = ceilHalf n →
              2 ≤ (execution P C₁ γ t μ).1.timer) ∨
             IsConsensusConfig (execution P C₁ γ t)) := by
        intro h_dec
        have hF1 : resetFuel C₁ ≤ k := by omega
        by_cases hAllRes : ∀ w, (C₁ w).1.role = .Resetting
        · simpa [P] using
            ranking_from_all_resetting_log
              (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hDmax1 hRlog C₁ hAllRes
        · by_cases hNoRes : ∀ w, (C₁ w).1.role ≠ .Resetting
          · simpa [P] using
              ranking_of_no_reset_by_parity_log
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hn4 hDmax1 hRlog C₁ hNoRes
          · have hSomeC1 : ∃ r' : Fin n, (C₁ r').1.role = .Resetting := by
              push_neg at hNoRes
              exact hNoRes
            exact ih C₁ hF1 hSomeC1 hAllRes
      by_cases hr_rc : (C' r).1.resetcount = 0
      · cases hr_leader : (C' r).1.leader with
        | F =>
            have h_dec :=
              dormant_follower_step_resetFuel_lt_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hrv hr_res hr_rc hr_leader hv_not
            have h_dec' : resetFuel C₁ < resetFuel C' := by
              simpa [C₁, P] using h_dec
            obtain ⟨γ, t, hgoal⟩ := dispatch_after_step h_dec'
            exact
              ranking_goal_of_step_ranking_goal_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C') (u := r) (v := v)
                (by simpa [C₁, P] using ⟨γ, t, hgoal⟩)
        | L =>
            rcases
              dormant_leader_nonresetting_step_resetFuel_lt_or_seed_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hrv hr_res hr_rc hr_leader hv_not
              with h_dec | ⟨r_seed, hseed_res, hseed_rc, hseed_L⟩
            · have h_dec' : resetFuel C₁ < resetFuel C' := by
                simpa [C₁, P] using h_dec
              obtain ⟨γ, t, hgoal⟩ := dispatch_after_step h_dec'
              exact
                ranking_goal_of_step_ranking_goal_trank
                  (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C') (u := r) (v := v)
                  (by simpa [C₁, P] using ⟨γ, t, hgoal⟩)
            · have hReset :
                  ∃ q : Fin n, (C₁ q).1.role = .Resetting ∧
                    Rmax ≤ (C₁ q).1.resetcount ∧ (C₁ q).1.leader = .L := by
                refine ⟨r_seed, ?_, ?_, ?_⟩
                · simpa [C₁, P] using hseed_res
                · have hrc : (C₁ r_seed).1.resetcount = Rmax := by
                    simpa [C₁, P] using hseed_rc
                  rw [hrc]
                · simpa [C₁, P] using hseed_L
              obtain ⟨Ltail, hEndpoint⟩ :=
                reset_snapshot_to_RankingEndpoint_log
                  (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax1 hRlog C₁ hReset
              have hgoal₁ :=
                ranking_goal_of_runPairs_RankingEndpoint_trank
                  (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₁) (L := Ltail) hEndpoint
              exact
                ranking_goal_of_step_ranking_goal_trank
                  (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C') (u := r) (v := v)
                  (by simpa [C₁, P] using hgoal₁)
      · have hr_rc_pos : 0 < (C' r).1.resetcount := Nat.pos_of_ne_zero hr_rc
        have h_dec :=
          propagate_reset_step_resetFuel_lt_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax1 C' hrv hr_res hr_rc_pos hv_not
        have h_dec' : resetFuel C₁ < resetFuel C' := by
          simpa [C₁, P] using h_dec
        obtain ⟨γ, t, hgoal⟩ := dispatch_after_step h_dec'
        exact
          ranking_goal_of_step_ranking_goal_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C') (u := r) (v := v)
            (by simpa [C₁, P] using ⟨γ, t, hgoal⟩)

theorem resetting_exists_to_ranking_goal_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting
  · exact
      ranking_from_all_resetting_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hAllReset
  · exact
      partial_resetting_to_ranking_goal_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hReset hAllReset

theorem ranking_field_proof_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (C : Config (AgentState n) Opinion n) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hReset : ∃ r : Fin n, (C r).1.role = .Resetting
  · exact
      resetting_exists_to_ranking_goal_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hReset
  · have hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting := by
      intro w hw
      exact hReset ⟨w, hw⟩
    exact
      ranking_of_no_reset_by_parity_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRlog C hNoReset

set_option maxHeartbeats 8000000 in
-- The log-regime replacement for the old positive-resetcount re-entry:
-- strong seed -> fresh uniform unique endpoint -> ranking -> swap.
theorem correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeedStrong Rmax C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      let E := execution
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t
      InSswap E ∧ ResAns (majorityAnswer E) E ∧ phiCount E = 0 := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  rcases hSeed with ⟨⟨r, hr_role, hr_rc, hr_L, _hr_ans⟩, hAllResetAns⟩
  have hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C := by
    intro w hw
    exact (hAllResetAns w hw).2
  obtain ⟨L0, hFresh0, hRes0, hNoPhi0, hMaj0⟩ :=
    log_seed_uniform_leader_to_FreshRankingStart_resAns_noPhi_log
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := majorityAnswer C)
      hn4 hDmax1 hRmax_pos C r hr_role
      (by simpa [hr_rc] using hRlog) hr_L rfl hAllAns
  let C1 : Config (AgentState n) Opinion n := runPairs P C L0
  have hFresh1 : FreshRankingStart C1 := by
    simpa [C1, hP] using hFresh0
  have hRes1 : ResAns (majorityAnswer C) C1 := by
    simpa [C1, hP] using hRes0
  have hNoPhi1 : ∀ w : Fin n, (C1 w).1.answer ≠ .phi := by
    simpa [C1, hP] using hNoPhi0
  have hMaj1 : majorityAnswer C1 = majorityAnswer C := by
    simpa [C1, hP] using hMaj0
  have hm1 : majorityAnswer C = majorityAnswer C1 := hMaj1.symm
  obtain ⟨L1, hSrank1, hResRank, hNoPhiRank, hTimerRank, hMajRank⟩ :=
    fresh_start_to_InSrank_ResAns_by_parity_BCF_tau
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C1 (majorityAnswer C) hm1 hFresh1 hRes1 hNoPhi1
  let C2 : Config (AgentState n) Opinion n := runPairs P C1 L1
  have hSrank2 : InSrank C2 := by
    simpa [C2, hP] using hSrank1
  have hRes2 : ResAns (majorityAnswer C) C2 := by
    simpa [C2, hP] using hResRank
  have hNoPhi2 : ∀ w : Fin n, (C2 w).1.answer ≠ .phi := by
    simpa [C2, hP] using hNoPhiRank
  have hTimer2 :
      ∀ μ : Fin n, (C2 μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (C2 μ).1.timer := by
    simpa [C2, hP] using hTimerRank
  have hMaj2 : majorityAnswer C2 = majorityAnswer C1 := by
    simpa [C2, hP] using hMajRank
  have hm2 : majorityAnswer C = majorityAnswer C2 := by
    rw [hMaj2, hMaj1]
  obtain ⟨L2, hSswap2, hResSwap, hNoPhiSwap, hMajSwap⟩ :=
    InSrank_to_InSswap_ResAns_with_inv_tau
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m₀ := majorityAnswer C) hn4 hSrank2 hRes2 hNoPhi2 hm2 hTimer2
  let E : Config (AgentState n) Opinion n := runPairs P C2 L2
  have hSswapE : InSswap E := by
    simpa [E, hP] using hSswap2
  have hResE0 : ResAns (majorityAnswer C) E := by
    simpa [E, hP] using hResSwap
  have hNoPhiE : ∀ w : Fin n, (E w).1.answer ≠ .phi := by
    simpa [E, hP] using hNoPhiSwap
  have hMajE_to_C2 : majorityAnswer E = majorityAnswer C2 := by
    simpa [E, hP] using hMajSwap
  exact
    exists_schedule_after_runPairs
      (Goal := fun E =>
        InSswap E ∧ ResAns (majorityAnswer E) E ∧ phiCount E = 0)
      P C (L0 ++ L1 ++ L2) ⟨fun _ => default, 0, by
        have hRun : runPairs P C (L0 ++ L1 ++ L2) = E := by
          simp [runPairs_append, C1, C2, E, hP]
        rw [hRun]
        simp only [execution]
        refine ⟨hSswapE, ?_, ?_⟩
        · have hMajE : majorityAnswer E = majorityAnswer C := by
            rw [hMajE_to_C2, hMaj2, hMaj1]
          rw [hMajE]
          exact hResE0
        · exact (phiCount_eq_zero_iff E).mpr hNoPhiE⟩

/-- Log-regime strong version of the entry seed-prefix obligation. -/
def MedCorrectLiveProducesStrongSeedOrProgress
    [Inhabited (Fin n × Fin n)]
    (Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (D μ).1.timer) →
    0 < wrongAnswerCount D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D) →
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C')

/-- Log-regime strong version of the reset-leaf seed-prefix obligation. -/
def ReservoirCaseProducesStrongSeedOrProgress
    [Inhabited (Fin n × Fin n)]
    (Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    ResAns (majorityAnswer D) D →
    0 < phiCount D →
    ((∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
        (D μ).1.answer = majorityAnswer D) ∨
     (∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
        (D μ).1.timer = 0)) →
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D)

theorem correctResetSeedStrong_of_odd_timer_one_max_no_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have hsnap :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC.toInSrank hn4 hμv hμ_med hv_max h_timer
      h_no_swap hpar h_post_diff
  have htr :=
    propagation_reset_fires_no_swap_max_timer_one_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hn4 hμv hμ_med hv_max h_timer
      h_no_swap hpar h_post_diff
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hfst]
    change (transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hsnd]
    change (transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
    hsnap
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact
    CorrectResetSeedStrong_of_step_pair
      (P := P) hRmax_pos hC.toInSrank hμv
      (by simpa [C'] using hμ_role)
      (by simpa [C'] using hμ_rc)
      (by simpa [C'] using hμ_leader)
      (by simpa [C'] using hμ_ans')
      (by simpa [C'] using hv_role)
      (by simpa [C'] using hv_rc)
      (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_even_lower_timer_one_max_wrong
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hsnap :=
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
      h_no_swap h_post_diff
  have htr :=
    propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
      h_no_swap h_post_diff
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hfst]
    change (transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
      majorityAnswer C
    rw [htr, hμ_correct]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hsnd]
    change (transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
      majorityAnswer C
    rw [htr, hμ_correct]
  obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
    hsnap
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact
    CorrectResetSeedStrong_of_step_pair
      (P := P) hRmax_pos hC.toInSrank hμv
      (by simpa [C'] using hμ_role)
      (by simpa [C'] using hμ_rc)
      (by simpa [C'] using hμ_leader)
      (by simpa [C'] using hμ_ans')
      (by simpa [C'] using hv_role)
      (by simpa [C'] using hv_rc)
      (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_timer_zero_wrong_nonupper
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (_hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_ans : (C μ).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil] at hμ_med
    have hv_not_lower : (C v).1.rank.val + 1 ≠ n / 2 := by
      rwa [← hceil]
    have h_no_swap :
        ¬((C μ).1.rank < (C v).1.rank ∧
          (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
      hC.swap_condition_false μ v
    have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
      intro hsame
      exact h_wrong (by rw [← hsame, hμ_ans])
    have hsnap :=
      trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC.toInSrank hμv hpar hμ_lower hv_not_lower hv_no_upper h_timer
        h_no_swap h_post_diff
    have htr :=
      propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hμv hpar hμ_lower hv_not_lower hv_no_upper
        h_timer h_no_swap h_post_diff
    have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hfst]
      change (transitionPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
        majorityAnswer C
      rw [htr, hμ_ans]
    have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hsnd]
      change (transitionPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
        majorityAnswer C
      rw [htr, hμ_ans]
    obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
      hsnap
    refine ⟨[(μ, v)], ?_⟩
    have hRun : runPairs P C [(μ, v)] = C' := by
      simp only [runPairs_cons, runPairs_nil, C']
    rw [hRun]
    exact
      CorrectResetSeedStrong_of_step_pair
        (P := P) hRmax_pos hC.toInSrank hμv
        (by simpa [C'] using hμ_role)
        (by simpa [C'] using hμ_rc)
        (by simpa [C'] using hμ_leader)
        (by simpa [C'] using hμ_ans')
        (by simpa [C'] using hv_role)
        (by simpa [C'] using hv_rc)
        (by simpa [C'] using hv_ans')
  · have h_no_swap :
        ¬((C μ).1.rank < (C v).1.rank ∧
          (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
      hC.swap_condition_false μ v
    have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
      opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
    have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
      rw [hμ_majority]
      exact h_wrong.symm
    have hsnap :=
      trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_trank
        (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer h_no_swap
        hpar h_post_diff
    have htr :=
      propagation_reset_fires_no_swap_trace
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer
        h_no_swap hpar h_post_diff
    have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hfst]
      change (transitionPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
        majorityAnswer C
      rw [htr, hμ_majority]
    have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
      rw [hmaj_step]
      dsimp [C']
      rw [congrArg AgentState.answer hsnd]
      change (transitionPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
        majorityAnswer C
      rw [htr, hμ_majority]
    obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
      hsnap
    refine ⟨[(μ, v)], ?_⟩
    have hRun : runPairs P C [(μ, v)] = C' := by
      simp only [runPairs_cons, runPairs_nil, C']
    rw [hRun]
    exact
      CorrectResetSeedStrong_of_step_pair
        (P := P) hRmax_pos hC.toInSrank hμv
        (by simpa [C'] using hμ_role)
        (by simpa [C'] using hμ_rc)
        (by simpa [C'] using hμ_leader)
        (by simpa [C'] using hμ_ans')
        (by simpa [C'] using hv_role)
        (by simpa [C'] using hv_rc)
        (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_timer_zero_wrong_nonexceptional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_ans : (C μ).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' :=
  correctResetSeedStrong_of_timer_zero_wrong_nonupper
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hRmax_pos hC hμv hμ_med hv_no_med hv_no_upper h_timer
    hμ_ans h_wrong

theorem correctResetSeedStrong_of_odd_timer_zero_wrong_nonmedian
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
    rw [hμ_majority]
    exact h_wrong.symm
  have hsnap :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer h_no_swap
      hpar h_post_diff
  have htr :=
    propagation_reset_fires_no_swap_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer
      h_no_swap hpar h_post_diff
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hfst]
    change (transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj_step]
    dsimp [C']
    rw [congrArg AgentState.answer hsnd]
    change (transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer =
      majorityAnswer C
    rw [htr, hμ_majority]
  obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, _hv_leader, _hAll⟩ :=
    hsnap
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact
    CorrectResetSeedStrong_of_step_pair
      (P := P) hRmax_pos hC.toInSrank hμv
      (by simpa [C'] using hμ_role)
      (by simpa [C'] using hμ_rc)
      (by simpa [C'] using hμ_leader)
      (by simpa [C'] using hμ_ans')
      (by simpa [C'] using hv_role)
      (by simpa [C'] using hv_rc)
      (by simpa [C'] using hv_ans')

theorem correctResetSeedStrong_of_odd_timer_one_max_same_then_zero_wrong_nonmedian
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  obtain ⟨hS₁, htimer₁, _hans₁, hmed₁, _hvmax₁, hothers₁, _hinputs₁⟩ :=
    step_at_median_max_timer_one_no_reset_explicit
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      rankDeltaOSSR_satisfies_fix hC hn4 hμv hμ_med hv_max hpar
      h_no_swap h_timer h_post_same
  have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, P] using
      (majorityAnswer_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [show C₁ w = C w from hothers₁ w hμw.symm hwv]
    exact hw_no_med
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    rw [show C₁ w = C w from hothers₁ w hμw.symm hwv, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hSeedTail⟩ :=
    correctResetSeedStrong_of_odd_timer_zero_wrong_nonmedian
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hRmax_pos hS₁ hμw hpar hmed₁ hw_no_med₁ htimer₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change
    let C' := runPairs P (C.step P μ v) Ltail
    CorrectResetSeedStrong Rmax C'
  exact hSeedTail

theorem correctResetSeedStrong_of_even_lower_timer_one_same_then_zero_wrong_nonupper
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hpar : n % 2 = 0)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_correct : (C v).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_same : (C μ).1.answer = (C v).1.answer := by
    rw [hμ_correct, hv_correct]
  obtain ⟨_hμ_state, _hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state_trank
      (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_pack :=
    insswap_drain_median_timer_one_step_tau
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap : InSswap C₁ := by
    simpa [C₁, P] using hC₁_pack.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := by
    simpa [C₁, P] using hC₁_pack.2.1
  have hμ_lower₁ : (C₁ μ).1.rank.val + 1 = n / 2 := by
    simpa [C₁, P] using hC₁_pack.2.2.2
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have hμ_med₁ : (C₁ μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower₁
  have hμ_correct₁ : (C₁ μ).1.answer = majorityAnswer C₁ := by
    have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
      simpa [C₁, P] using
        (majorityAnswer_step_eq
          (trank := τ) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
    rw [hmaj₁]
    simpa [C₁, P] using hC₁_pack.2.2.1.trans hμ_correct
  have hw_state₁ : C₁ w = C w := by
    simpa [C₁, P] using hothers w hμw.symm hwv
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hw_state₁, hceil]
    intro hw_lower
    apply hμw
    apply hC.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = n / 2 - 1 := by omega
    have hw_val : (C w).1.rank.val = n / 2 - 1 := by omega
    exact hμ_val.trans hw_val.symm
  have hw_not_upper₁ : (C₁ w).1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hw_state₁]
    exact hw_not_upper
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
      simpa [C₁, P] using
        (majorityAnswer_step_eq
          (trank := τ) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
    rw [hw_state₁, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hSeedTail⟩ :=
    correctResetSeedStrong_of_timer_zero_wrong_nonupper
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hC₁_swap hμw hμ_med₁ hw_no_med₁ hw_not_upper₁
      hμ_timer₁ hμ_correct₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change
    let C' := runPairs P (C.step P μ v) Ltail
    CorrectResetSeedStrong Rmax C'
  exact hSeedTail

theorem correctResetSeedStrong_of_median_correct_timer_zero_wrong_nonexceptional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hMedCorrect : ∀ η : Fin n, (C η).1.rank.val + 1 = ceilHalf n →
      (C η).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' := by
  classical
  have hμv : μ ≠ v := by
    intro h
    subst v
    exact hv_no_med hμ_med
  exact
    correctResetSeedStrong_of_timer_zero_wrong_nonexceptional
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hC hμv hμ_med hv_no_med hv_no_upper h_timer
      (hMedCorrect μ hμ_med) h_wrong

theorem med_correct_timer_zero_strong_seed_or_wrong_exceptional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpos : 0 < wrongAnswerCount C)
    (hMedCorrect : ∀ η : Fin n, (C η).1.rank.val + 1 = ceilHalf n →
      (C η).1.answer = majorityAnswer C) :
    (∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C') ∨
    (∃ v : Fin n,
      (C v).1.rank.val + 1 ≠ ceilHalf n ∧
      (C v).1.answer ≠ majorityAnswer C ∧
      (C v).1.rank.val + 1 = n / 2 + 1) := by
  classical
  obtain ⟨v, hv_no_med, hv_wrong⟩ :=
    exists_wrong_nonmedian_of_med_correct hpos hMedCorrect
  by_cases hv_upper : (C v).1.rank.val + 1 = n / 2 + 1
  · exact Or.inr ⟨v, hv_no_med, hv_wrong, hv_upper⟩
  · exact Or.inl
      (by
        have hμv : μ ≠ v := by
          intro h
          subst v
          exact hv_no_med hμ_med
        exact
          correctResetSeedStrong_of_timer_zero_wrong_nonupper
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hC hμv hμ_med hv_no_med hv_upper h_timer
            (hMedCorrect μ hμ_med) hv_wrong)

theorem med_correct_live_timer_one_strong_seed_or_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hWrongPos : 0 < wrongAnswerCount D)
    (hMedCorrect : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (D μ).1.timer = 1) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C') := by
  classical
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil] at hμ_med
    by_cases hNonupperWrong :
        ∃ w : Fin n,
          (D w).1.answer ≠ majorityAnswer D ∧
          (D w).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨w, hw_wrong, hw_not_upper⟩ := hNonupperWrong
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
      · obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_max_wrong
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hμv hpar hμ_lower hv_max h_timer
            (hMedCorrect μ hμ_med) hv_wrong
        exact ⟨L, Or.inl hSeed⟩
      · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
        have hμw : μ ≠ w := by
          intro h
          subst w
          exact hw_wrong (hMedCorrect μ hμ_med)
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw_wrong hv_correct
        obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_same_then_zero_wrong_nonupper
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hpar hμv hμw hwv hμ_lower hv_max
            hw_not_upper h_timer (hMedCorrect μ hμ_med) hv_correct hw_wrong
        exact ⟨L, Or.inl hSeed⟩
    · push_neg at hNonupperWrong
      obtain ⟨w, hw_no_med, hw_wrong⟩ :=
        exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
      have hw_upper : (D w).1.rank.val + 1 = n / 2 + 1 :=
        hNonupperWrong w hw_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      obtain ⟨L, hProg⟩ :=
        even_upper_only_wrong_decision_InSswap_ResAns_tau
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hμw hpar hμ_lower hw_upper hw_wrong hNonupperWrong
      exact ⟨L, Or.inr hProg⟩
  · obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    obtain ⟨v, hμv, hv_max⟩ :=
      hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
    have h_no_swap :
        ¬((D μ).1.rank < (D v).1.rank ∧
          (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
      hSswap.swap_condition_false μ v
    have hμ_input :
        opinionToAnswer (D μ).2 = majorityAnswer D :=
      opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
    by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
    · have hpost :
          opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
        rw [hμ_input]
        exact hv_wrong.symm
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_no_swap_diff
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμ_med hv_max h_timer h_no_swap hpar hpost
      exact ⟨L, Or.inl hSeed⟩
    · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hpost :
          opinionToAnswer (D μ).2 = (D v).1.answer := by
        rw [hμ_input, hv_correct]
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_same_then_zero_wrong_nonmedian
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμw hwv hpar hμ_med hv_max
          hw_no_med h_timer hpost hw_wrong
      exact ⟨L, Or.inl hSeed⟩

theorem medCorrectLiveProducesStrongSeedOrProgress_holds
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax) :
    MedCorrectLiveProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn := by
  classical
  intro D hSswap hTimer hWrongPos hMedCorrect
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨μ, hμ_rank⟩ :=
    hSswap.toInSrank.exists_at_rank
      (by omega : 0 < n) (⟨ceilHalf n - 1, by
        unfold ceilHalf
        omega⟩ : Fin n)
  have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
    have hv : (D μ).1.rank.val = ceilHalf n - 1 := by
      exact congrArg Fin.val hμ_rank
    have hceil_pos : 0 < ceilHalf n := by
      unfold ceilHalf
      omega
    omega
  by_cases htimer1 : (D μ).1.timer = 1
  · exact
      med_correct_live_timer_one_strong_seed_or_progress
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hWrongPos hMedCorrect hμ_med htimer1
  · have htimer2 : 2 ≤ (D μ).1.timer := by
      have hpos := hTimer μ hμ_med
      omega
    obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    have hμw : μ ≠ w := by
      intro h
      subst w
      exact hw_no_med hμ_med
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rwa [hceil] at hμ_med
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        even_lower_timer_descent_to_one_with_states
          (trank := τ) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap hn4 hpar hμv hμ_lower hv_max
          h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = n / 2 ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = (D μ).1.answer ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = n / 2 ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = (D μ).1.answer ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtLower, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq_tau
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hCtMed : (Ct μ).1.rank.val + 1 = ceilHalf n := by
        rw [hceil]
        exact hCtLower
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hCtμAns, hMajCt]
        exact hMedCorrect μ hμ_med
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        have hw_wrong_Ct : (Ct w).1.answer ≠ majorityAnswer Ct := by
          rw [hMajCt]
          by_cases hwv : w = v
          · subst w
            rw [hCtvState]
            exact hw_wrong
          · rw [hCtOthers w hμw.symm hwv]
            exact hw_wrong
        unfold wrongAnswerCount
        exact Finset.card_pos.mpr ⟨w, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ w, hw_wrong_Ct⟩⟩
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_progress
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hCtWrongPos hCtMedCorrect hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      simpa [Ct, hP] using hTail
    · obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        odd_timer_descent_to_one_explicit_with_states
          (trank := τ) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap (by omega : 2 ≤ n) hpar hμv
          hμ_med hv_max h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = ceilHalf n ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = ceilHalf n ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtMed, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq_tau
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hμ_input :
          opinionToAnswer (D μ).2 = majorityAnswer D :=
        opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hCtμAns, hμ_input, hMajCt]
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        have hw_wrong_Ct : (Ct w).1.answer ≠ majorityAnswer Ct := by
          rw [hMajCt]
          by_cases hwv : w = v
          · subst w
            rw [hCtvState]
            exact hw_wrong
          · rw [hCtOthers w hμw.symm hwv]
            exact hw_wrong
        unfold wrongAnswerCount
        exact Finset.card_pos.mpr ⟨w, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ w, hw_wrong_Ct⟩⟩
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_progress
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hCtWrongPos hCtMedCorrect hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      simpa [Ct, hP] using hTail

/-- τ-generic version of `even_upper_wrong_decision_resAns_phi_decrease`.
The coupled proof only ever instantiates genuinely `trank`-parametric step
lemmas at `(trank := Rmax)`; re-instantiating them at `(trank := τ)` gives the
identical argument over `protocolPEM n τ Rmax`. -/
theorem even_upper_wrong_decision_resAns_phi_decrease_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
        phiCount C' < phiCount C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have hRfix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hdec :=
    InSswap_even_median_pair_decision_decreases
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      hRfix hC hμv hpar hμ_lower hv_upper hn4 (Or.inr hv_wrong)
  have hSswap' : InSswap C' := by
    simpa [C', P] using hdec.1
  have hRes' : ResAns (majorityAnswer C') C' := by
    rw [hmaj_step]
    by_cases hTie : nAOf C = nBOf C
    · have hdis :=
        InSswap_even_median_pair_inputs_disagree_of_tie
          hC hpar hTie hμ_lower hv_upper
      have hsu := hC.allSettled μ
      have hsv := hC.allSettled v
      have h_no_swap : ¬((C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
        intro h
        rcases h with ⟨hμB, _hvA⟩
        have hsum := nAOf_add_nBOf C
        have hμA : (C μ).2 = Opinion.A := (hC.input_rank μ).mpr (by omega)
        rw [hμA] at hμB
        exact Opinion.noConfusion hμB
      obtain ⟨h_μ, h_v, h_others, _⟩ :=
        step_at_median_pair_even_disagreed_inputs
          (trank := τ) (Rmax := Rmax)
          hRfix hμv hsu hsv hpar hμ_lower hv_upper hdis h_no_swap hn4
      have h_outT : majorityAnswer C = .outT :=
        majorityAnswer_eq_outT_of_tie hTie
      intro w
      by_cases hwμ : w = μ
      · subst w
        left
        dsimp [C']
        rw [h_μ, h_outT]
      · by_cases hwv : w = v
        · subst w
          left
          dsimp [C']
          rw [h_v, h_outT]
        · have hww : C' w = C w := by
            dsimp [C']
            exact h_others w hwμ hwv
          rw [hww]
          exact hRes w
    · have hagree :=
        InSswap_even_median_pair_inputs_agree_of_strict
          hC hpar hTie hμ_lower hv_upper
      have hsu := hC.allSettled μ
      have hsv := hC.allSettled v
      have hC'_eq :=
        step_at_median_pair_even_agreed_inputs
          (trank := τ) (Rmax := Rmax)
          hRfix hμv hsu hsv hpar hμ_lower hv_upper hagree hn4
      have h_correct : opinionToAnswer (C μ).2 = majorityAnswer C :=
        opinionToAnswer_lower_median_eq_majorityAnswer_even hC hμ_lower hpar hTie
      intro w
      have hval := congrFun hC'_eq w
      by_cases hwμ : w = μ
      · left
        dsimp [C']
        rw [hval, if_pos hwμ, h_correct]
      · by_cases hwv : w = v
        · left
          dsimp [C']
          rw [hval, if_neg hwμ, if_pos hwv, h_correct]
        · dsimp [C']
          rw [hval, if_neg hwμ, if_neg hwv]
          exact hRes w
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  refine ⟨hSswap', hRes', ?_⟩
  rw [phiCount_eq_wrongAnswerCount_of_resAns hRes',
    phiCount_eq_wrongAnswerCount_of_resAns hRes]
  simpa [C', P] using hdec.2

/-- τ-generic version of `even_median_pair_wrong_decision_resAns_phi_decrease`. -/
theorem even_median_pair_wrong_decision_resAns_phi_decrease_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hwrong :
      (C μ).1.answer ≠ majorityAnswer C ∨
        (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
        phiCount C' < phiCount C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have hRfix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
  have hmaj_step : majorityAnswer C' = majorityAnswer C := by
    dsimp [C', P]
    exact majorityAnswer_step_eq C μ v
  have hdec :=
    InSswap_even_median_pair_decision_decreases
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      hRfix hC hμv hpar hμ_lower hv_upper hn4 hwrong
  have hSswap' : InSswap C' := by
    simpa [C', P] using hdec.1
  have hRes' : ResAns (majorityAnswer C') C' := by
    rw [hmaj_step]
    by_cases hTie : nAOf C = nBOf C
    · have hdis :=
        InSswap_even_median_pair_inputs_disagree_of_tie
          hC hpar hTie hμ_lower hv_upper
      have hsu := hC.allSettled μ
      have hsv := hC.allSettled v
      have h_no_swap : ¬((C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
        intro h
        rcases h with ⟨hμB, _hvA⟩
        have hsum := nAOf_add_nBOf C
        have hμA : (C μ).2 = Opinion.A := (hC.input_rank μ).mpr (by omega)
        rw [hμA] at hμB
        exact Opinion.noConfusion hμB
      obtain ⟨h_μ, h_v, h_others, _⟩ :=
        step_at_median_pair_even_disagreed_inputs
          (trank := τ) (Rmax := Rmax)
          hRfix hμv hsu hsv hpar hμ_lower hv_upper hdis h_no_swap hn4
      have h_outT : majorityAnswer C = .outT :=
        majorityAnswer_eq_outT_of_tie hTie
      intro w
      by_cases hwμ : w = μ
      · subst w
        left
        dsimp [C']
        rw [h_μ, h_outT]
      · by_cases hwv : w = v
        · subst w
          left
          dsimp [C']
          rw [h_v, h_outT]
        · have hww : C' w = C w := by
            dsimp [C']
            exact h_others w hwμ hwv
          rw [hww]
          exact hRes w
    · have hagree :=
        InSswap_even_median_pair_inputs_agree_of_strict
          hC hpar hTie hμ_lower hv_upper
      have hsu := hC.allSettled μ
      have hsv := hC.allSettled v
      have hC'_eq :=
        step_at_median_pair_even_agreed_inputs
          (trank := τ) (Rmax := Rmax)
          hRfix hμv hsu hsv hpar hμ_lower hv_upper hagree hn4
      have h_correct : opinionToAnswer (C μ).2 = majorityAnswer C :=
        opinionToAnswer_lower_median_eq_majorityAnswer_even hC hμ_lower hpar hTie
      intro w
      have hval := congrFun hC'_eq w
      by_cases hwμ : w = μ
      · left
        dsimp [C']
        rw [hval, if_pos hwμ, h_correct]
      · by_cases hwv : w = v
        · left
          dsimp [C']
          rw [hval, if_neg hwμ, if_pos hwv, h_correct]
        · dsimp [C']
          rw [hval, if_neg hwμ, if_neg hwv]
          exact hRes w
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  refine ⟨hSswap', hRes', ?_⟩
  rw [phiCount_eq_wrongAnswerCount_of_resAns hRes',
    phiCount_eq_wrongAnswerCount_of_resAns hRes]
  simpa [C', P] using hdec.2

/-- τ-generic version of `odd_timer_zero_only_median_wrong_resAns_phi_decrease`. -/
theorem odd_timer_zero_only_median_wrong_resAns_phi_decrease_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (hPhiPos : 0 < phiCount C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hOnlyMedianWrong :
      ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
        phiCount C' < phiCount C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have hcard : 1 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨v, hv_ne_mu⟩ := Fintype.exists_ne_of_one_lt_card hcard μ
  have hμv : μ ≠ v := fun h => hv_ne_mu h.symm
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    intro hv_med
    apply hμv
    apply hC.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
    have hv_val : (C v).1.rank.val = ceilHalf n - 1 := by omega
    exact hμ_val.trans hv_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have hv_correct : (C v).1.answer = majorityAnswer C :=
    hOnlyMedianWrong v hv_ne_mu
  have h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer := by
    rw [h_median_correct, hv_correct]
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    transitionPEM_timer_zero_no_swap_same_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC.toInSrank hμv hμ_med hv_no_med h_timer
      h_no_swap hpar h_post_same
  have hC'_eq : C' =
      fun w => if w = μ then
          ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C μ).2)
        else if w = v then C v
        else C w := by
    funext w
    dsimp [C', P]
    unfold Config.step
    simp only [if_neg hμv]
    change
      (if w = μ then
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C μ, C v)).1, (C μ).2)
        else if w = v then
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C μ, C v)).2, (C v).2)
        else C w) =
      (if w = μ then
          ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C μ).2)
        else if w = v then C v
        else C w)
    rw [htr]
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P] using
      (majorityAnswer_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hSswap' : InSswap C' := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_ }
    · intro w
      have hw_state := congrFun hC'_eq w
      rw [hw_state]
      by_cases hwμ : w = μ
      · simp [hwμ, hC.allSettled μ]
      · by_cases hwv : w = v
        · simp [hwμ, hwv, hv_ne_mu, hC.allSettled v]
        · simp [hwμ, hwv, hC.allSettled w]
    · intro w₁ w₂ heq
      apply hC.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hC.input_rank w
  have hAllCorrect : ∀ w : Fin n, (C' w).1.answer = majorityAnswer C' := by
    intro w
    rw [hmaj]
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ, h_median_correct]
    · by_cases hwv : w = v
      · subst w
        simp [hv_ne_mu, hv_correct]
      · simp [hwμ, hwv, hOnlyMedianWrong w hwμ]
  have hRes' : ResAns (majorityAnswer C') C' := by
    intro w
    exact Or.inl (hAllCorrect w)
  have hPhiZero : phiCount C' = 0 := by
    rw [phiCount_eq_zero_iff]
    intro w
    rw [hAllCorrect w]
    unfold majorityAnswer
    split_ifs <;> decide
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  refine ⟨hSswap', hRes', ?_⟩
  rw [hPhiZero]
  exact hPhiPos

theorem med_correct_live_timer_one_strong_seed_or_phi_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hWrongPos : 0 < wrongAnswerCount D)
    (hMedCorrect : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (D μ).1.timer = 1) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D) := by
  classical
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil] at hμ_med
    by_cases hNonupperWrong :
        ∃ w : Fin n,
          (D w).1.answer ≠ majorityAnswer D ∧
          (D w).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨w, hw_wrong, hw_not_upper⟩ := hNonupperWrong
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
      · obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_max_wrong
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hμv hpar hμ_lower hv_max h_timer
            (hMedCorrect μ hμ_med) hv_wrong
        exact ⟨L, Or.inl hSeed⟩
      · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
        have hμw : μ ≠ w := by
          intro h
          subst w
          exact hw_wrong (hMedCorrect μ hμ_med)
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw_wrong hv_correct
        obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_even_lower_timer_one_same_then_zero_wrong_nonupper
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hRmax_pos hSswap hpar hμv hμw hwv hμ_lower hv_max
            hw_not_upper h_timer (hMedCorrect μ hμ_med) hv_correct hw_wrong
        exact ⟨L, Or.inl hSeed⟩
    · push_neg at hNonupperWrong
      obtain ⟨w, hw_no_med, hw_wrong⟩ :=
        exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
      have hw_upper : (D w).1.rank.val + 1 = n / 2 + 1 :=
        hNonupperWrong w hw_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      obtain ⟨L, hProg⟩ :=
        even_upper_wrong_decision_resAns_phi_decrease_tau
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hRes hμw hpar hμ_lower hw_upper hw_wrong
      exact ⟨L, Or.inr hProg⟩
  · obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    obtain ⟨v, hμv, hv_max⟩ :=
      hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
    have h_no_swap :
        ¬((D μ).1.rank < (D v).1.rank ∧
          (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
      hSswap.swap_condition_false μ v
    have hμ_input :
        opinionToAnswer (D μ).2 = majorityAnswer D :=
      opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
    by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
    · have hpost :
          opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
        rw [hμ_input]
        exact hv_wrong.symm
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_no_swap_diff
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμ_med hv_max h_timer h_no_swap hpar hpost
      exact ⟨L, Or.inl hSeed⟩
    · have hv_correct : (D v).1.answer = majorityAnswer D := not_not.mp hv_wrong
      have hμw : μ ≠ w := by
        intro h
        subst w
        exact hw_no_med hμ_med
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hpost :
          opinionToAnswer (D μ).2 = (D v).1.answer := by
        rw [hμ_input, hv_correct]
      obtain ⟨L, hSeed⟩ :=
        correctResetSeedStrong_of_odd_timer_one_max_same_then_zero_wrong_nonmedian
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hμv hμw hwv hpar hμ_med hv_max
          hw_no_med h_timer hpost hw_wrong
      exact ⟨L, Or.inl hSeed⟩

theorem med_correct_live_strong_seed_or_phi_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hTimer : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (D μ).1.timer)
    (hWrongPos : 0 < wrongAnswerCount D)
    (hMedCorrect : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨μ, hμ_rank⟩ :=
    hSswap.toInSrank.exists_at_rank
      (by omega : 0 < n) (⟨ceilHalf n - 1, by
        unfold ceilHalf
        omega⟩ : Fin n)
  have hμ_med : (D μ).1.rank.val + 1 = ceilHalf n := by
    have hv : (D μ).1.rank.val = ceilHalf n - 1 := by
      exact congrArg Fin.val hμ_rank
    have hceil_pos : 0 < ceilHalf n := by
      unfold ceilHalf
      omega
    omega
  by_cases htimer1 : (D μ).1.timer = 1
  · exact
      med_correct_live_timer_one_strong_seed_or_phi_progress
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hRes hWrongPos hMedCorrect hμ_med htimer1
  · have htimer2 : 2 ≤ (D μ).1.timer := by
      have hpos := hTimer μ hμ_med
      omega
    obtain ⟨w, hw_no_med, hw_wrong⟩ :=
      exists_wrong_nonmedian_of_med_correct hWrongPos hMedCorrect
    have hμw : μ ≠ w := by
      intro h
      subst w
      exact hw_no_med hμ_med
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rwa [hceil] at hμ_med
      obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        even_lower_timer_descent_to_one_with_states
          (trank := τ) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap hn4 hpar hμv hμ_lower hv_max
          h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = n / 2 ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = (D μ).1.answer ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hlower, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = n / 2 ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = (D μ).1.answer ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtLower, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq_tau
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hAnsEq : ∀ x : Fin n, (Ct x).1.answer = (D x).1.answer := by
        intro x
        by_cases hxμ : x = μ
        · subst x
          exact hCtμAns
        · by_cases hxv : x = v
          · subst x
            exact congrArg AgentState.answer hCtvState
          · rw [hCtOthers x hxμ hxv]
      have hResCt : ResAns (majorityAnswer Ct) Ct := by
        rw [hMajCt]
        intro x
        rw [hAnsEq x]
        exact hRes x
      have hPhiCt : phiCount Ct = phiCount D := by
        unfold phiCount
        congr 1
        apply Finset.filter_congr
        intro x _
        rw [hAnsEq x]
      have hCtMed : (Ct μ).1.rank.val + 1 = ceilHalf n := by
        rw [hceil]
        exact hCtLower
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hAnsEq μ, hMajCt]
        exact hMedCorrect μ hμ_med
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        rw [← phiCount_eq_wrongAnswerCount_of_resAns hResCt, hPhiCt,
          phiCount_eq_wrongAnswerCount_of_resAns hRes]
        exact hWrongPos
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_phi_progress
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hResCt hCtWrongPos hCtMedCorrect
          hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      have hTail' :
          CorrectResetSeedStrong Rmax (runPairs P Ct Ltail) ∨
            (InSswap (runPairs P Ct Ltail) ∧
              ResAns (majorityAnswer (runPairs P Ct Ltail)) (runPairs P Ct Ltail) ∧
              phiCount (runPairs P Ct Ltail) < phiCount Ct) := by
        simpa [Ct, hP] using hTail
      rcases hTail' with hSeed | hProg
      · exact Or.inl hSeed
      · rcases hProg with ⟨hI, hR, hlt⟩
        exact Or.inr ⟨hI, hR, by rwa [hPhiCt] at hlt⟩
    · obtain ⟨v, hμv, hv_max⟩ :=
        hSswap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
      have h_no_swap :
          ¬ ((D μ).1.rank < (D v).1.rank ∧
            (D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) :=
        hSswap.swap_condition_false μ v
      obtain ⟨γ, t, hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩ :=
        odd_timer_descent_to_one_explicit_with_states
          (trank := τ) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          rankDeltaOSSR_satisfies_fix hSswap (by omega : 2 ≤ n) hpar hμv
          hμ_med hv_max h_no_swap htimer2
      obtain ⟨L0, hpack⟩ :=
        exists_runPairs_of_execution_bcf
          (P := P) (C := D)
          (Goal := fun Ct : Config (AgentState n) Opinion n =>
            InSswap Ct ∧
            (Ct μ).1.timer = 1 ∧
            (Ct μ).1.rank.val + 1 = ceilHalf n ∧
            (Ct v).1.rank.val + 1 = n ∧
            (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
            (Ct v).1 = (D v).1 ∧
            (Ct μ).2 = (D μ).2 ∧
            (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x))
          γ t ⟨hS, ht, hmedCt, hvmax, hμans, hvstate, hinput, hothers⟩
      set Ct : Config (AgentState n) Opinion n := runPairs P D L0 with hCt
      have hpack' :
          InSswap Ct ∧
          (Ct μ).1.timer = 1 ∧
          (Ct μ).1.rank.val + 1 = ceilHalf n ∧
          (Ct v).1.rank.val + 1 = n ∧
          (Ct μ).1.answer = opinionToAnswer (D μ).2 ∧
          (Ct v).1 = (D v).1 ∧
          (Ct μ).2 = (D μ).2 ∧
          (∀ x : Fin n, x ≠ μ → x ≠ v → Ct x = D x) := by
        simpa [Ct, hP] using hpack
      rcases hpack' with ⟨hCtS, hCtTimer, hCtMed, _hvmaxCt,
        hCtμAns, hCtvState, _hCtInput, hCtOthers⟩
      have hMajCt : majorityAnswer Ct = majorityAnswer D := by
        simpa [Ct, hP] using
          (majorityAnswer_runPairs_eq_tau
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) D L0)
      have hμ_input :
          opinionToAnswer (D μ).2 = majorityAnswer D :=
        opinionToAnswer_median_eq_majorityAnswer_odd hSswap hμ_med hpar
      have hAnsEq : ∀ x : Fin n, (Ct x).1.answer = (D x).1.answer := by
        intro x
        by_cases hxμ : x = μ
        · subst x
          rw [hCtμAns, hμ_input]
          exact (hMedCorrect μ hμ_med).symm
        · by_cases hxv : x = v
          · subst x
            exact congrArg AgentState.answer hCtvState
          · rw [hCtOthers x hxμ hxv]
      have hResCt : ResAns (majorityAnswer Ct) Ct := by
        rw [hMajCt]
        intro x
        rw [hAnsEq x]
        exact hRes x
      have hPhiCt : phiCount Ct = phiCount D := by
        unfold phiCount
        congr 1
        apply Finset.filter_congr
        intro x _
        rw [hAnsEq x]
      have hCtMedCorrect :
          ∀ η : Fin n, (Ct η).1.rank.val + 1 = ceilHalf n →
            (Ct η).1.answer = majorityAnswer Ct := by
        intro η hη
        have hημ : η = μ := by
          apply hCtS.ranks_inj
          apply Fin.eq_of_val_eq
          have hηv : (Ct η).1.rank.val = ceilHalf n - 1 := by omega
          have hμv' : (Ct μ).1.rank.val = ceilHalf n - 1 := by omega
          exact hηv.trans hμv'.symm
        subst η
        rw [hAnsEq μ, hMajCt]
        exact hMedCorrect μ hμ_med
      have hCtWrongPos : 0 < wrongAnswerCount Ct := by
        rw [← phiCount_eq_wrongAnswerCount_of_resAns hResCt, hPhiCt,
          phiCount_eq_wrongAnswerCount_of_resAns hRes]
        exact hWrongPos
      obtain ⟨Ltail, hTail⟩ :=
        med_correct_live_timer_one_strong_seed_or_phi_progress
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hCtS hResCt hCtWrongPos hCtMedCorrect
          hCtMed hCtTimer
      refine ⟨L0 ++ Ltail, ?_⟩
      rw [runPairs_append]
      have hTail' :
          CorrectResetSeedStrong Rmax (runPairs P Ct Ltail) ∨
            (InSswap (runPairs P Ct Ltail) ∧
              ResAns (majorityAnswer (runPairs P Ct Ltail)) (runPairs P Ct Ltail) ∧
              phiCount (runPairs P Ct Ltail) < phiCount Ct) := by
        simpa [Ct, hP] using hTail
      rcases hTail' with hSeed | hProg
      · exact Or.inl hSeed
      · rcases hProg with ⟨hI, hR, hlt⟩
        exact Or.inr ⟨hI, hR, by rwa [hPhiCt] at hlt⟩

theorem reservoir_med_correct_timer_zero_strong_seed_or_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (hPhiPos : 0 < phiCount C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hMedCorrect : ∀ η : Fin n, (C η).1.rank.val + 1 = ceilHalf n →
      (C η).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount C) := by
  classical
  have hWrongPos : 0 < wrongAnswerCount C := by
    rw [← phiCount_eq_wrongAnswerCount_of_resAns hRes]
    exact hPhiPos
  rcases med_correct_timer_zero_strong_seed_or_wrong_exceptional
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hC hμ_med h_timer hWrongPos hMedCorrect with
    hSeed | hUpper
  · obtain ⟨L, hL⟩ := hSeed
    exact ⟨L, Or.inl hL⟩
  · obtain ⟨v, hv_no_med, hv_wrong, hv_upper⟩ := hUpper
    have hpar : n % 2 = 0 := by
      by_contra hodd
      have hceil : ceilHalf n = n / 2 + 1 := by
        unfold ceilHalf
        omega
      exact hv_no_med (by rw [hceil]; exact hv_upper)
    have hceil_even : ceilHalf n = n / 2 := by
      exact ceilHalf_eq_half_of_even hpar
    have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
      rwa [hceil_even] at hμ_med
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact hv_no_med hμ_med
    obtain ⟨L, hProg⟩ :=
      even_upper_wrong_decision_resAns_phi_decrease_tau
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hC hRes hμv hpar hμ_lower hv_upper hv_wrong
    exact ⟨L, Or.inr hProg⟩

theorem reservoir_timer_zero_strong_seed_or_progress_core
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hSswap : InSswap D)
    (hRes : ResAns (majorityAnswer D) D)
    (hPhi : 0 < phiCount D)
    {μ : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D) := by
  classical
  by_cases hMedCorrect :
      ∀ η : Fin n, (D η).1.rank.val + 1 = ceilHalf n →
        (D η).1.answer = majorityAnswer D
  · exact
      reservoir_med_correct_timer_zero_strong_seed_or_progress
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hRes hPhi hμ_med hμ_timer hMedCorrect
  · push_neg at hMedCorrect
    obtain ⟨η, hη_med, hη_wrong⟩ := hMedCorrect
    by_cases hpar : n % 2 = 0
    · have hceil_even : ceilHalf n = n / 2 := by
        exact ceilHalf_eq_half_of_even hpar
      have hη_lower : (D η).1.rank.val + 1 = n / 2 := by
        rwa [hceil_even] at hη_med
      obtain ⟨v, hv_rank⟩ :=
        hSswap.toInSrank.exists_at_rank
          (by omega : 0 < n) (⟨n / 2, by omega⟩ : Fin n)
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 := by
        rw [hv_rank]
      have hηv : η ≠ v := by
        intro h
        subst v
        omega
      obtain ⟨L, hProg⟩ :=
        even_median_pair_wrong_decision_resAns_phi_decrease_tau
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hRes hηv hpar hη_lower hv_upper (Or.inl hη_wrong)
      exact ⟨L, Or.inr hProg⟩
    · have hη_eq_μ : η = μ := by
        apply hSswap.ranks_inj
        apply Fin.eq_of_val_eq
        have hη_val : (D η).1.rank.val = ceilHalf n - 1 := by omega
        have hμ_val : (D μ).1.rank.val = ceilHalf n - 1 := by omega
        exact hη_val.trans hμ_val.symm
      subst η
      by_cases hNonmedWrong :
          ∃ v : Fin n,
            (D v).1.rank.val + 1 ≠ ceilHalf n ∧
              (D v).1.answer ≠ majorityAnswer D
      · obtain ⟨v, hv_no_med, hv_wrong⟩ := hNonmedWrong
        have hμv : μ ≠ v := by
          intro h
          subst v
          exact hv_no_med hμ_med
        obtain ⟨L, hSeed⟩ :=
          correctResetSeedStrong_of_odd_timer_zero_wrong_nonmedian
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hRmax_pos hSswap hμv hpar hμ_med hv_no_med hμ_timer hv_wrong
        exact ⟨L, Or.inl hSeed⟩
      · push_neg at hNonmedWrong
        have hOnly : ∀ w : Fin n, w ≠ μ →
            (D w).1.answer = majorityAnswer D := by
          intro w hwμ
          exact hNonmedWrong w (by
            intro hw_med
            apply hwμ
            apply hSswap.ranks_inj
            apply Fin.eq_of_val_eq
            have hw_val : (D w).1.rank.val = ceilHalf n - 1 := by omega
            have hμ_val : (D μ).1.rank.val = ceilHalf n - 1 := by omega
            exact hw_val.trans hμ_val.symm)
        obtain ⟨L, hProg⟩ :=
          odd_timer_zero_only_median_wrong_resAns_phi_decrease_tau
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hSswap hRes hPhi hpar hμ_med hμ_timer hOnly
        exact ⟨L, Or.inr hProg⟩

theorem reservoirCaseProducesStrongSeedOrProgress_holds
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax) :
    ReservoirCaseProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn := by
  classical
  intro D hSswap hRes hPhi hCase
  rcases hCase with hMedCorrect | hTimerZero
  · have hWrongPos : 0 < wrongAnswerCount D := by
      rw [← phiCount_eq_wrongAnswerCount_of_resAns hRes]
      exact hPhi
    by_cases hTimer :
        ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
          1 ≤ (D μ).1.timer
    · exact
        med_correct_live_strong_seed_or_phi_progress
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hRes hTimer hWrongPos hMedCorrect
    · push_neg at hTimer
      obtain ⟨μ, hμ_med, hμ_timer_lt⟩ := hTimer
      have hμ_timer : (D μ).1.timer = 0 := by omega
      exact
        reservoir_timer_zero_strong_seed_or_progress_core
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hRmax_pos hSswap hRes hPhi hμ_med hμ_timer
  · obtain ⟨μ, hμ_med, hμ_timer⟩ := hTimerZero
    exact
      reservoir_timer_zero_strong_seed_or_progress_core
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hSswap hRes hPhi hμ_med hμ_timer

set_option maxHeartbeats 8000000 in
-- Re-entry consumer with the strong seed disjunct routed through the log
-- fresh bridge instead of the old positive-resetcount path.
theorem med_correct_live_InSswap_to_reservoir_entry_from_strong_seed_and_reentry_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hSeedPrefix :
      MedCorrectLiveProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn) :
    MedCorrectLiveInSswapToReservoirEntry_tau (τ := τ) Rmax Emax Dmax hn := by
  classical
  intro D hSswap hTimer hWrongPos hMedCorrect
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨L0, hCase⟩ :=
    hSeedPrefix D hSswap hTimer hWrongPos hMedCorrect
  set C0 : Config (AgentState n) Opinion n := runPairs P D L0 with hC0def
  have hCase' :
      CorrectResetSeedStrong Rmax C0 ∨
      (InSswap C0 ∧ ResAns (majorityAnswer C0) C0) := by
    simpa [C0, hP] using hCase
  rcases hCase' with hSeed0 | hProg
  · obtain ⟨γ1, t1, hFinal⟩ :=
      correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hSeed0
    exact
      exists_schedule_after_runPairs
        (Goal := fun E => InSswap E ∧ ResAns (majorityAnswer E) E)
        P D L0 ⟨γ1, t1, by
          rcases hFinal with ⟨hInSswap, hResFinal, _hPhiZero⟩
          exact ⟨hInSswap, hResFinal⟩⟩
  · exact
      exists_schedule_after_runPairs
        (Goal := fun E => InSswap E ∧ ResAns (majorityAnswer E) E)
        P D L0 ⟨fun _ => default, 0, hProg⟩

set_option maxHeartbeats 8000000 in
-- Reset-leaf consumer with the strong seed disjunct routed through the log
-- fresh bridge instead of the old positive-resetcount path.
theorem reservoir_reset_leaf_from_strong_seed_and_reentry_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hSeedPrefix :
      ReservoirCaseProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn) :
    ReservoirResetLeaf_tau (τ := τ) Rmax Emax Dmax hn := by
  classical
  intro D hSswap hRes hPhiPos hCase
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨L0, hCaseL⟩ :=
    hSeedPrefix D hSswap hRes hPhiPos hCase
  set C0 : Config (AgentState n) Opinion n := runPairs P D L0 with hC0def
  have hCaseL' :
      CorrectResetSeedStrong Rmax C0 ∨
      (InSswap C0 ∧ ResAns (majorityAnswer C0) C0 ∧
        phiCount C0 < phiCount D) := by
    simpa [C0, hP] using hCaseL
  rcases hCaseL' with hSeed0 | hProg
  · obtain ⟨γ1, t1, hFinal⟩ :=
      correct_reset_seed_strong_to_InSswap_ResAns_phi_zero_log
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hSeed0
    refine
      exists_schedule_after_runPairs
        (Goal := fun E =>
          (InSswap E ∧ ResAns (majorityAnswer E) E) ∧
          phiCount E < phiCount D)
        P D L0 ?_
    refine ⟨γ1, t1, ?_⟩
    rcases hFinal with ⟨hInSswap, hResFinal, hPhiZero⟩
    refine ⟨⟨hInSswap, hResFinal⟩, ?_⟩
    rw [hPhiZero]
    exact hPhiPos
  · exact
      exists_schedule_after_runPairs
        (Goal := fun E =>
          (InSswap E ∧ ResAns (majorityAnswer E) E) ∧
          phiCount E < phiCount D)
        P D L0 ⟨fun _ => default, 0, by
          rcases hProg with ⟨hI, hR, hPhi⟩
          exact ⟨⟨hI, hR⟩, hPhi⟩⟩

set_option maxHeartbeats 8000000 in
-- Wrapper composition is elaboration-heavy because both re-entry branches
-- retain the full scheduler/execution goal shape.
theorem hMedCorrectExit_from_log_reentry_and_strong_seed_prefixes
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax) (hRmax_pos : 0 < Rmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hEntrySeed :
      MedCorrectLiveProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn)
    (hLeafSeed :
      ReservoirCaseProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn) :
    ∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n,
      InSswap D →
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (D μ).1.timer) →
      0 < wrongAnswerCount D →
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
        (D μ).1.answer = majorityAnswer D) →
      wrongAnswerCount D ≤ k →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t) := by
  exact
    hMedCorrectExit_from_reservoir_entry_and_reset_leaf_tau
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4
      (med_correct_live_InSswap_to_reservoir_entry_from_strong_seed_and_reentry_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hEntrySeed)
      (reservoir_reset_leaf_from_strong_seed_and_reentry_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax1 hRmax_pos hRlog hLeafSeed)

set_option maxHeartbeats 16000000 in
theorem burmanConvergence_concrete_log_with_strong_seed_prefixes
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hEntrySeed :
      MedCorrectLiveProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn)
    (hLeafSeed :
      ReservoirCaseProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn) :
    BurmanConvergence τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) where
  ranking := fun C₀ =>
    ranking_field_proof_log
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hn4 hDmax1 hRlog C₀
  epidemic := fun C₀ _h_correct => by
    classical
    obtain ⟨γ₁, t₁, hInSrank, hdisj⟩ :=
      ranking_field_proof_log
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn4 hDmax1 hRlog C₀
    set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
    have hclose :
        ∀ E : Config (AgentState n) Opinion n,
          (∃ (γ : DetScheduler n) (t : ℕ),
            E = execution P C₀ γ t ∧ IsConsensusConfig E) →
          ∃ (γ : DetScheduler n) (t : ℕ),
            InSswap (execution P C₀ γ t) ∧
            (∀ w : Fin n,
              (execution P C₀ γ t w).1.answer = majorityAnswer C₀) ∧
            ((∀ μ : Fin n,
              (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
              1 ≤ (execution P C₀ γ t μ).1.timer) ∨
             IsConsensusConfig (execution P C₀ γ t)) := by
      rintro E ⟨γ, t, hEeq, hconsE⟩
      have hStim : InStim (execution P C₀ γ t) := by
        rw [← hEeq]; exact (InStim_iff_IsConsensusConfig _).mpr hconsE
      have hconsE' : IsConsensusConfig (execution P C₀ γ t) := by
        rw [← hEeq]; exact hconsE
      refine ⟨γ, t, hStim.toInSswap, ?_, Or.inr hconsE'⟩
      intro w
      have hmajγ : majorityAnswer (execution P C₀ γ t) = majorityAnswer C₀ :=
        majorityAnswer_execution_eq C₀ γ t
      have hw : (execution P C₀ γ t w).1.answer
          = majorityAnswer (execution P C₀ γ t) :=
        hconsE'.allAnswerCorrect w
      rw [hw, hmajγ]
    rcases hdisj with htimer | hcons
    · set E₁ : Config (AgentState n) Opinion n := execution P C₀ γ₁ t₁
        with hE₁def
      have hMedCorrectExit :
          ∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n,
            InSswap D →
            (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
              1 ≤ (D μ).1.timer) →
            0 < wrongAnswerCount D →
            (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
              (D μ).1.answer = majorityAnswer D) →
            wrongAnswerCount D ≤ k →
            ∃ (γ : DetScheduler n) (t : ℕ),
              IsConsensusConfig (execution (protocolPEM n τ Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t) := by
        exact
          hMedCorrectExit_from_log_reentry_and_strong_seed_prefixes
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax1 (by omega : 0 < Rmax) hRlog hEntrySeed hLeafSeed
      have hbridge :
          ∃ (γ : DetScheduler n) (t : ℕ),
            IsConsensusConfig (execution P E₁ γ t) :=
        epidemic_timer_branch_to_consensus_tau
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 (C₁ := E₁)
          (by simpa [E₁, hP] using hInSrank)
          (by
            intro μ hμ
            have h2 := htimer μ (by simpa [E₁, hP] using hμ)
            omega)
          (by simpa [hP] using hMedCorrectExit)
      obtain ⟨γ₂, t₂, hcons₂⟩ := hbridge
      refine hclose (execution P E₁ γ₂ t₂) ⟨concatScheduler γ₁ t₁ γ₂,
        t₁ + t₂, ?_, hcons₂⟩
      rw [hE₁def, execution_concat]
    · exact hclose (execution P C₀ γ₁ t₁) ⟨γ₁, t₁, rfl, hcons⟩

theorem P_EM_solves_SSEM_log_with_strong_seed_prefixes
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hEntrySeed :
      MedCorrectLiveProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn)
    (hLeafSeed :
      ReservoirCaseProducesStrongSeedOrProgress (τ := τ) Rmax Emax Dmax hn) :
    SolvesSSEM (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n :=
  P_EM_solves_SSEM_from_BurmanConvergence_only
    rankDeltaOSSR_satisfies_fix
    hn4
    (burmanConvergence_concrete_log_with_strong_seed_prefixes
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax1 hRlog hEntrySeed hLeafSeed)

theorem burmanConvergence_concrete_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax) :
    BurmanConvergence τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) :=
  burmanConvergence_concrete_log_with_strong_seed_prefixes
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hDmax1 hRlog
    (medCorrectLiveProducesStrongSeedOrProgress_holds
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))
    (reservoirCaseProducesStrongSeedOrProgress_holds
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))

theorem P_EM_solves_SSEM_log
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax) :
    SolvesSSEM (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n :=
  P_EM_solves_SSEM_log_with_strong_seed_prefixes
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hDmax1 hRlog
    (medCorrectLiveProducesStrongSeedOrProgress_holds
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))
    (reservoirCaseProducesStrongSeedOrProgress_holds
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (by omega : 0 < Rmax))

end SSEM

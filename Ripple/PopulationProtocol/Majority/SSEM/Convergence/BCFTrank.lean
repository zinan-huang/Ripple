import Ripple.PopulationProtocol.Majority.SSEM.Convergence.LogRegimeConvergence
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal

/-! BCFTrank: tau-generalized clones of the post-reset reset/ranking/swap/drive
    composition layer from BurmanProof and BurmanConvergenceFinal.  Each `_tau`
    decl is a verbatim clone with the protocol's trank slot generalized from the
    hardcoded Rmax to the free section variable tau; rankDelta params and the phase4
    Rmax decision threshold unchanged.  trank only feeds the wake-timer reset
    7*(trank+4); it does not change role/resetcount/leader/rank/answer outcomes.
    Three protocol-agnostic private BCF helpers are re-declared verbatim. -/

namespace SSEM

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 8000000

variable {n τ : ℕ}

theorem trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_no_swap_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

theorem trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot_tau
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_even_lower_timer_zero_no_swap_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hμv hpar hμ_lower hv_not_lower hv_not_upper h_timer
      h_no_swap h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

theorem no_reset_even_lower_max_timer_one_step_state_tau
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_even_lower_max_timer_one_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  refine ⟨?_, ?_, ?_⟩
  · dsimp [C']
    unfold Config.step
    simp [P, hμv]
    change
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1 =
        { (C μ).1 with timer := 0 }
    rw [htr]
  · dsimp [C']
    unfold Config.step
    simp [P, hμv, hμv.symm]
    change
      ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2,
        (C v).2) =
      C v
    rw [htr]
  · intro w hwμ hwv
    dsimp [C', P]
    simp [Config.step, hμv, hwμ, hwv]

theorem no_reset_even_lower_max_timer_one_step_InSswap_tau
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  obtain ⟨hμ_state, hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  have hμ_state' : C' μ = ({ (C μ).1 with timer := 0 }, (C μ).2) := by
    simpa [C', P] using hμ_state
  have hv_state' : C' v = C v := by
    simpa [C', P] using hv_state
  have hothers' : ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
    intro w hwμ hwv
    simpa [C', P] using hothers w hwμ hwv
  have hrole : ∀ w : Fin n, (C' w).1.role = .Settled := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state']
      exact hSwap.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [hv_state']
        exact hSwap.allSettled v
      · rw [hothers' w hwμ hwv]
        exact hSwap.allSettled w
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state']
    · by_cases hwv : w = v
      · subst w
        rw [hv_state']
      · rw [hothers' w hwμ hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state']
    · by_cases hwv : w = v
      · subst w
        rw [hv_state']
      · rw [hothers' w hwμ hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  change
    InSswap C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine { allSettled := ?_, ranks_inj := ?_, input_rank := ?_ }
    · intro w
      exact hrole w
    · intro w₁ w₂ heq
      apply hSwap.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hSwap.input_rank w
  · rw [hμ_state']
  · rw [hμ_state']
  · rw [hμ_state']
    exact hμ_lower

theorem trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot_tau
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

theorem trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_no_swap_max_timer_one_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

theorem no_reset_no_swap_max_timer_one_step_InSrank_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSrank C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
      (C' μ).1.rank.val + 1 = ceilHalf n := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_no_swap_max_timer_one_trace
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_same
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hothers : ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
    intro w hwμ hwv
    dsimp [C', P]
    simp [Config.step, hμv, hwμ, hwv]
  have hμ_state : (C' μ).1 = { (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 } := by
    dsimp [C']
    rw [hfst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1 =
      { (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 }
    rw [htr]
  have hv_state : (C' v).1 = (C v).1 := by
    dsimp [C']
    rw [hsnd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2 =
      (C v).1
    rw [htr]
  have hrole : ∀ w : Fin n, (C' w).1.role = .Settled := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
        exact hC.allSettled v
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
        exact hC.allSettled w
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hrole, ?_⟩
    intro w₁ w₂ heq
    have heqC' : (C' w₁).1.rank = (C' w₂).1.rank := by
      simpa [C'] using heq
    exact hC.ranks_inj (by simpa [hrank w₁, hrank w₂] using heqC')
  · rw [hμ_state]
  · rw [hμ_state]
  · rw [hμ_state]
    exact hμ_med

theorem trigger_reset_from_all_settled_non_InSrank_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C₀ : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C₀ v).1.role = .Settled)
    (hNotInSrank : ¬ InSrank C₀) :
    ∃ u v : Fin n, u ≠ v ∧
      let C' := C₀.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      (C' u).1.role = .Resetting ∧ (C' v).1.role = .Resetting ∧
      (C' u).1.resetcount = Rmax ∧ (C' v).1.resetcount = Rmax := by
  have hNotInj : ¬ Function.Injective (fun v : Fin n => (C₀ v).1.rank) := by
    intro hInj
    exact hNotInSrank ⟨hSettled, hInj⟩
  obtain ⟨u, v, huv, h_same⟩ := exists_collision_of_not_inj hSettled hNotInj
  refine ⟨u, v, huv, ?_⟩
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_tr := transitionPEM_collision_both_resetting (trank := τ) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) (C := C₀) (u := u) (v := v)
    (hSettled u) (hSettled v) h_same
  have h_fst := Config.step_fst_state P C₀ huv
  have h_snd := Config.step_snd_state P C₀ huv huv.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.role = .Resetting
    exact h_tr.1
  · rw [congrArg AgentState.role h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.role = .Resetting
    exact h_tr.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.resetcount = Rmax
    exact h_tr.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    change (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.resetcount = Rmax
    exact h_tr.2.2.2

theorem trigger_reset_from_all_settled_non_InSrank_with_leader_tau
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

/-- Local progress trace for Algorithm 1 when the first interacting agent is
Unsettled and no Resetting agents are present before the interaction.

This packages the expensive `transitionPEM`/`rankDeltaOSSR` case analysis so
`unsettled_one_step_progress_tau (τ := τ)` does not repeatedly unfold the whole protocol
inside a `simp` call. -/
theorem transitionPEM_unsettled_one_step_progress_tau
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

theorem transitionPEM_unsettled_one_step_resetcount_tau
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

theorem transitionPEM_unsettled_one_step_reset_leader_tau
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

theorem unsettled_one_step_progress_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C' := runPairs P C [(w, v)]
  have hC' : C' = C.step P w v := by
    simp [C', runPairs]
  have hstep :=
    transitionPEM_unsettled_one_step_progress_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  dsimp at hstep
  change (∃ x : Fin n, (C' x).1.role = .Resetting) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C)
  have hfst : (C' w).1 =
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_fst_state P C hwv.symm
  have hsnd : (C' v).1 =
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_snd_state P C hwv.symm hwv
  rcases hstep with hreset | hprogress
  · rcases hreset with hreset | hreset
    · exact Or.inl ⟨w, by rw [hfst]; exact hreset⟩
    · exact Or.inl ⟨v, by rw [hsnd]; exact hreset⟩
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

theorem unsettled_one_step_progress_reset_snapshot_tau
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
    transitionPEM_unsettled_one_step_progress_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hrc :=
    transitionPEM_unsettled_one_step_resetcount_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hleader :=
    transitionPEM_unsettled_one_step_reset_leader_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem unsettled_branch_eventually_reset_or_allSettled_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
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
          (∃ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting) ∨
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Settled) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hmass hNoReset₀
      by_cases hUn : ∃ w : Fin n, (C₀ w).1.role = .Unsettled
      · rcases hUn with ⟨w, hw_unsettled⟩
        rcases hne_of_fin w with ⟨v, hvw⟩
        have hstep :=
          unsettled_one_step_progress_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
          simpa [C₁, runPairs_cons] using htail
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

theorem unsettled_branch_eventually_reset_snapshot_or_allSettled_tau
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
          unsettled_one_step_progress_reset_snapshot_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

/-- Phase 1: From ANY config, reach InSrank OR produce ≥ 1 Resetting agent.
(ChatGPT insight: returning InSrank directly handles the case where
Unsettled agents get recruited to Settled without triggering reset.) -/
theorem phase1_trigger_reset_or_InSrank_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨ (∃ w : Fin n, (C' w).1.role = .Resetting) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨ (∃ w : Fin n, (C' w).1.role = .Resetting)
  by_cases hReset : ∃ w : Fin n, (C w).1.role = .Resetting
  · refine ⟨[], ?_⟩
    simp only [runPairs_nil]
    exact Or.inr hReset
  · have hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting := by
      intro w hw
      exact hReset ⟨w, hw⟩
    have hReach :
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
          (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
      by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
      · simpa [P] using
          unsettled_branch_eventually_reset_or_allSettled_tau (τ := τ)
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
          trigger_reset_from_all_settled_non_InSrank_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C₀ := C₀) hAllSettled₀ hSrank
        refine ⟨L₀ ++ [(u, v)], ?_⟩
        refine Or.inr ⟨u, ?_⟩
        have hcol_u : (runPairs P C₀ [(u, v)] u).1.role = .Resetting := by
          simpa [P, runPairs] using hcol.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        exact hcol_u

theorem phase1_no_reset_trigger_snapshot_or_InSrank_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
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
        unsettled_branch_eventually_reset_snapshot_or_allSettled_tau (τ := τ)
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
        trigger_reset_from_all_settled_non_InSrank_with_leader_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

/-- Single-step spread: Resetting(rc>0) meets non-Resetting → second becomes Resetting. -/
theorem propagate_reset_one_step_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C₀.step P r v v).1.role = .Resetting := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change (C₀.step P r v v).1.role = .Resetting
  have h_rd := rankDeltaOSSR_propagate_reset (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hr_res hr_rc hv_not hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
    intro hsettled
    rw [h_rd] at hsettled
    exact Role.noConfusion hsettled.2
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C₀ r).2) (x₁ := (C₀ v).2)
    h_not_both
  have h_snd := Config.step_snd_state P C₀ hrv hrv.symm
  rw [congrArg AgentState.role h_snd]
  exact h_pass.2.2.2.2.2.2.1 ▸ h_rd

/-- After spread step, the spreader stays Resetting with rc decremented. -/
theorem propagate_reset_spreader_state_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C₀.step P r v r).1.role = .Resetting ∧
    (C₀.step P r v r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₀.step P r v r).1.leader = (C₀ r).1.leader := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change (C₀.step P r v r).1.role = .Resetting ∧
    (C₀.step P r v r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₀.step P r v r).1.leader = (C₀ r).1.leader
  have h_rd := rankDeltaOSSR_propagate_reset_spreader (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hr_res hr_rc hv_not hDmax
  have h_rd_leader := rankDeltaOSSR_propagate_reset_spreader_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
    intro hsettled
    rw [h_rd.1] at hsettled
    exact Role.noConfusion hsettled.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C₀ r).2) (x₁ := (C₀ v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C₀ hrv
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd_leader

theorem propagate_reset_step_nonResettingCount_lt_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C₁ := C₀.step P r v
    (C₁ r).1.role = .Resetting ∧
    (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₁ v).1.role = .Resetting ∧
    nonResettingCount C₁ < nonResettingCount C₀ := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C₁ := C₀.step P r v with hC₁
  have hv_reset : (C₁ v).1.role = .Resetting := by
    rw [hC₁]
    exact propagate_reset_one_step_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C₀ hrv hr_res hr_rc hv_not
  have hr_trace :=
    propagate_reset_spreader_state_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C₀ hrv hr_res hr_rc hv_not
  have hr_reset : (C₁ r).1.role = .Resetting := by
    rw [hC₁]
    exact hr_trace.1
  have hr_rc_eq : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
    rw [hC₁]
    exact hr_trace.2.1
  set S := Finset.univ.filter (fun w : Fin n => (C₀ w).1.role ≠ .Resetting) with hS
  set S' := Finset.univ.filter (fun w : Fin n => (C₁ w).1.role ≠ .Resetting) with hS'
  have hv_mem : v ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, hv_not⟩
  have hsub : S' ⊆ S.erase v := by
    intro x hx
    have hx_not : (C₁ x).1.role ≠ .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_v : x ≠ v := by
      intro hxv
      subst x
      exact hx_not hv_reset
    have hx_ne_r : x ≠ r := by
      intro hxr
      subst x
      exact hx_not hr_reset
    have hx_C : (C₀ x).1.role ≠ .Resetting := by
      have hx_state : C₁ x = C₀ x := by
        rw [hC₁]
        unfold Config.step
        simp [hrv, hx_ne_r, hx_ne_v]
      intro hx_reset
      exact hx_not (by rw [hx_state]; exact hx_reset)
    rw [Finset.mem_erase]
    exact ⟨hx_ne_v, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ x, hx_C⟩⟩
  have hcard_le : S'.card ≤ (S.erase v).card := Finset.card_le_card hsub
  have hcard_erase : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv_mem
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv_mem⟩
  have hcount_lt : S'.card < S.card := by omega
  refine ⟨hr_reset, hr_rc_eq, hv_reset, ?_⟩
  change S'.card < S.card
  exact hcount_lt

/-- Phase 2: From config with ≥ 1 Resetting (with sufficient resetcount), spread to all agents. -/
theorem phase2_propagate_reset_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting ∧ n ≤ (C r).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      ∀ w : Fin n, (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L w).1.role = .Resetting := by
  classical
  rcases hReset with ⟨r, hr_res, hr_rc_ge⟩
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        nonResettingCount C₀ = k →
        (C₀ r).1.role = .Resetting →
        nonResettingCount C₀ < (C₀ r).1.resetcount →
        ∃ L : List (Fin n × Fin n),
          ∀ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hcount hr_res₀ hcount_lt_rc
      by_cases hk0 : k = 0
      · refine ⟨[], ?_⟩
        intro w
        simp only [runPairs_nil]
        by_contra hw_not
        have hw_mem :
            w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ w, hw_not⟩
        have hpos :
            0 < (Finset.univ.filter
              (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
          Finset.card_pos.mpr ⟨w, hw_mem⟩
        unfold nonResettingCount at hcount
        omega
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hcount_pos : 0 < nonResettingCount C₀ := by
          rw [hcount]
          exact hkpos
        obtain ⟨v, hv_mem⟩ : ∃ v : Fin n,
            v ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          exact Finset.card_pos.mp hcount_pos
        have hv_not : (C₀ v).1.role ≠ .Resetting :=
          (Finset.mem_filter.mp hv_mem).2
        have hrv : r ≠ v := by
          intro hrv_eq
          subst v
          exact hv_not hr_res₀
        have hr_rc_pos : 0 < (C₀ r).1.resetcount := by omega
        have hstep :=
          propagate_reset_step_nonResettingCount_lt_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        set C₁ := C₀.step P r v with hC₁
        have hr_res₁ : (C₁ r).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.1
        have hr_rc₁ : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
          rw [hC₁]
          exact hstep.2.1
        have hcount_lt : nonResettingCount C₁ < nonResettingCount C₀ := by
          rw [hC₁]
          exact hstep.2.2.2
        have hlt_k : nonResettingCount C₁ < k := by
          rw [← hcount]
          exact hcount_lt
        have hcount_lt_rc₁ : nonResettingCount C₁ < (C₁ r).1.resetcount := by
          rw [hr_rc₁]
          omega
        obtain ⟨Ltail, htail⟩ :=
          ih (nonResettingCount C₁) hlt_k C₁ rfl hr_res₁ hcount_lt_rc₁
        refine ⟨(r, v) :: Ltail, ?_⟩
        simpa [C₁, runPairs_cons] using htail
  have hcount_lt_initial : nonResettingCount C < (C r).1.resetcount := by
    set S := Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting) with hS
    have hsub : S ⊆ (Finset.univ.erase r) := by
      intro x hx
      have hx_not : (C x).1.role ≠ .Resetting := by
        rw [hS] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_res
      rw [Finset.mem_erase]
      exact ⟨hx_ne_r, Finset.mem_univ x⟩
    have hcard_le : S.card ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have hcard_erase : (Finset.univ.erase r).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r)]
      simp
    unfold nonResettingCount
    rw [← hS]
    omega
  exact hrec (nonResettingCount C) C rfl hr_res hcount_lt_initial

theorem phase2_propagate_reset_with_leader_pos_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting ∧
      n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L)
    (hResetPos : ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
      (∃ ℓ : Fin n, (C' ℓ).1.leader = .L) := by
  classical
  rcases hReset with ⟨r, hr_res, hr_rc_ge, hr_leader⟩
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        nonResettingCount C₀ = k →
        (C₀ r).1.role = .Resetting →
        (C₀ r).1.leader = .L →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting → 0 < (C₀ w).1.resetcount) →
        nonResettingCount C₀ < (C₀ r).1.resetcount →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
          (C' r).1.leader = .L := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hcount hr_res₀ hr_leader₀ hPos₀ hcount_lt_rc
      by_cases hk0 : k = 0
      · refine ⟨[], ?_, ?_, ?_⟩
        · intro w
          simp only [runPairs_nil]
          by_contra hw_not
          have hw_mem :
              w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ w, hw_not⟩
          have hpos :
              0 < (Finset.univ.filter
                (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
            Finset.card_pos.mpr ⟨w, hw_mem⟩
          unfold nonResettingCount at hcount
          omega
        · intro w
          simp only [runPairs_nil]
          have hw_res : (C₀ w).1.role = .Resetting := by
            by_contra hw_not
            have hw_mem :
                w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ w, hw_not⟩
            have hpos :
                0 < (Finset.univ.filter
                  (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
              Finset.card_pos.mpr ⟨w, hw_mem⟩
            unfold nonResettingCount at hcount
            omega
          exact hPos₀ w hw_res
        · simp only [runPairs_nil]
          exact hr_leader₀
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hcount_pos : 0 < nonResettingCount C₀ := by
          rw [hcount]
          exact hkpos
        obtain ⟨v, hv_mem⟩ : ∃ v : Fin n,
            v ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          exact Finset.card_pos.mp hcount_pos
        have hv_not : (C₀ v).1.role ≠ .Resetting :=
          (Finset.mem_filter.mp hv_mem).2
        have hrv : r ≠ v := by
          intro hrv_eq
          subst v
          exact hv_not hr_res₀
        have hr_rc_pos : 0 < (C₀ r).1.resetcount := hPos₀ r hr_res₀
        have hstep :=
          propagate_reset_step_nonResettingCount_lt_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        have htrace :=
          propagate_reset_spreader_state_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        set C₁ := C₀.step P r v with hC₁
        have hr_res₁ : (C₁ r).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.1
        have hv_res₁ : (C₁ v).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.2.2.1
        have hr_leader₁ : (C₁ r).1.leader = .L := by
          rw [hC₁]
          rw [htrace.2.2]
          exact hr_leader₀
        have hr_rc₁ : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
          rw [hC₁]
          exact hstep.2.1
        have hcount_lt : nonResettingCount C₁ < nonResettingCount C₀ := by
          rw [hC₁]
          exact hstep.2.2.2
        have hlt_k : nonResettingCount C₁ < k := by
          rw [← hcount]
          exact hcount_lt
        have hcount_lt_rc₁ : nonResettingCount C₁ < (C₁ r).1.resetcount := by
          rw [hr_rc₁]
          omega
        have hr_rc_pos₁ : 0 < (C₁ r).1.resetcount := by
          have hnonneg : 0 ≤ nonResettingCount C₁ := Nat.zero_le _
          exact Nat.lt_of_le_of_lt hnonneg hcount_lt_rc₁
        have hPos₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting → 0 < (C₁ w).1.resetcount := by
          intro w hw_res
          by_cases hwr : w = r
          · subst w
            exact hr_rc_pos₁
          · by_cases hwv : w = v
            · subst w
              have hv_rc_eq : (C₁ v).1.resetcount = (C₁ r).1.resetcount := by
                rw [hC₁]
                have hchild_rc :
                    (C₀.step P r v v).1.resetcount = (C₀ r).1.resetcount - 1 := by
                  set rankDelta := rankDeltaOSSR Rmax Emax Dmax hn
                  have h_rd_child :
                      (rankDelta ((C₀ r).1, (C₀ v).1)).2.resetcount =
                        (C₀ r).1.resetcount - 1 := by
                    unfold rankDelta rankDeltaOSSR propagateReset processAgent
                    by_cases hrc1 : (C₀ r).1.resetcount = 1
                    · simp [hr_res₀, hv_not, hrc1, resetOSSR,
                        show (Dmax : ℕ) ≠ 0 from by omega,
                        show Dmax - 1 ≠ 0 from by omega]
                      split_ifs <;> rfl
                    · have hne : (C₀ r).1.resetcount - 1 ≠ 0 := by omega
                      simp [hr_res₀, hr_rc_pos, hv_not, hne, resetOSSR,
                        show (Dmax : ℕ) ≠ 0 from by omega]
                      split_ifs <;> rfl
                  have h_not_both :
                      ¬((rankDelta ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
                        (rankDelta ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
                    intro hboth
                    have hchild_reset :
                        (rankDelta ((C₀ r).1, (C₀ v).1)).2.role = .Resetting := by
                      simpa [rankDelta] using
                        rankDeltaOSSR_propagate_reset
                          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                          hr_res₀ hr_rc_pos hv_not hDmax
                    rw [hchild_reset] at hboth
                    exact Role.noConfusion hboth.2
                  have h_pass := transitionPEM_structural_passthrough
                    (n := n) (trank := τ) (Rmax := Rmax)
                    (rankDelta := rankDelta) (s₀ := (C₀ r).1) (s₁ := (C₀ v).1)
                    (x₀ := (C₀ r).2) (x₁ := (C₀ v).2) h_not_both
                  have h_snd := Config.step_snd_state P C₀ hrv hrv.symm
                  rw [congrArg AgentState.resetcount h_snd]
                  exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd_child
                rw [hchild_rc]
                exact hr_rc₁.symm
              rw [hv_rc_eq]
              exact hr_rc_pos₁
            · have hw_old : C₁ w = C₀ w := by
                rw [hC₁]
                simp [Config.step, hrv, hwr, hwv]
              have hw_old_res : (C₀ w).1.role = .Resetting := by
                rw [← hw_old]
                exact hw_res
              rw [hw_old]
              exact hPos₀ w hw_old_res
        obtain ⟨Ltail, htail_roles, htail_pos, htail_leader⟩ :=
          ih (nonResettingCount C₁) hlt_k C₁ rfl hr_res₁ hr_leader₁ hPos₁ hcount_lt_rc₁
        refine ⟨(r, v) :: Ltail, ?_⟩
        rw [runPairs_cons]
        change
          let C' := runPairs P C₁ Ltail
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
          (C' r).1.leader = .L
        exact ⟨htail_roles, htail_pos, htail_leader⟩
  have hcount_lt_initial : nonResettingCount C < (C r).1.resetcount := by
    set S := Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting) with hS
    have hsub : S ⊆ (Finset.univ.erase r) := by
      intro x hx
      have hx_not : (C x).1.role ≠ .Resetting := by
        rw [hS] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_res
      rw [Finset.mem_erase]
      exact ⟨hx_ne_r, Finset.mem_univ x⟩
    have hcard_le : S.card ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have hcard_erase : (Finset.univ.erase r).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r)]
      simp
    unfold nonResettingCount
    rw [← hS]
    omega
  obtain ⟨L, hroles, hpos, hleader⟩ :=
    hrec (nonResettingCount C) C rfl hr_res hr_leader hResetPos hcount_lt_initial
  exact ⟨L, hroles, hpos, ⟨r, hleader⟩⟩

theorem phase12_no_reset_to_all_resetting_pos_with_leader_or_InSrank_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        ((∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
          ∃ ℓ : Fin n, (C' ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase1_no_reset_trigger_snapshot_or_InSrank_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hReset
  · refine ⟨L₁, ?_⟩
    exact Or.inl hSrank
  · obtain ⟨r, hr_role, hr_rc, hr_leader, hSnapshot⟩ := hReset
    have hDmax_gt_one : 1 < Dmax := by omega
    have hReset_phase2 : ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        n ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
      refine ⟨r, ?_, ?_, ?_⟩
      · simpa [C₁, P] using hr_role
      · have hrc₁ : (C₁ r).1.resetcount = Rmax := by
          simpa [C₁, P] using hr_rc
        rw [hrc₁]
        exact hRmax
      · simpa [C₁, P] using hr_leader
    have hResetPos₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting → 0 < (C₁ w).1.resetcount := by
      intro w hw
      have hfields := hSnapshot w (by simpa [C₁, P] using hw)
      have hrc : (C₁ w).1.resetcount = Rmax := by
        simpa [C₁, P] using hfields.1
      rw [hrc]
      have hn_pos : 0 < n := Nat.lt_of_lt_of_le (by omega : 0 < 4) hn4
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    obtain ⟨L₂, hroles, hpos, hleader⟩ :=
      phase2_propagate_reset_with_leader_pos_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_gt_one C₁ hReset_phase2 hResetPos₁
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    change InSrank (runPairs P C₁ L₂) ∨
      ((∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting) ∧
        (∀ w : Fin n, 0 < (runPairs P C₁ L₂ w).1.resetcount) ∧
        ∃ ℓ : Fin n, (runPairs P C₁ L₂ ℓ).1.leader = .L)
    exact Or.inr ⟨hroles, hpos, hleader⟩

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_fst_delay_final_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hnew : Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.delaytimer = Dmax := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd_role := rankDeltaOSSR_both_rc_pos_role (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hDmax
  have h_rd_delay := rankDeltaOSSR_both_rc_pos_fst_delay_final
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hnew hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd_role.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  change (C.step P u v u).1.delaytimer = Dmax
  rw [congrArg AgentState.delaytimer h_fst]
  exact h_pass.2.2.2.2.2.1 ▸ h_rd_delay

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_LF_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_LF_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_F hDmax
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
theorem step_both_rc_pos_FF_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_FF_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_F hv_F hDmax
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
theorem step_both_rc_pos_LL_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_LL_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_L hDmax
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
theorem step_L_pos_F_zero_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
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
  have h_rd := rankDeltaOSSR_L_pos_F_zero_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_F hv_dt hDmax
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
theorem step_L_pos_L_zero_tau
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
theorem step_F_pos_F_zero_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_F_zero_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_F hv_F hv_dt hDmax
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
theorem step_L_pos_any_zero_gt_one_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_any_zero_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L
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
theorem step_F_pos_F_zero_gt_one_tau
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
theorem step_L_pos_one_F_zero_low_tau
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
theorem step_F_pos_one_F_zero_low_tau
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
theorem step_F_pos_one_settled_L_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_settled : (C v).1.role = .Settled)
    (hu_rc : (C u).1.resetcount = 1)
    (hu_F : (C u).1.leader = .F) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.leader = .L ∧
    (C' v).1.delaytimer = Dmax - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_one_settled_L_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_settled hu_rc hu_F hv_L hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_one_L_zero_low_tau
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
theorem step_L_zero_F_pos_tau
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
theorem step_L_zero_F_pos_gt_one_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 1 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
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
theorem step_L_zero_F_pos_one_low_tau
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
theorem step_L_zero_L_pos_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
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
  have h_rd := rankDeltaOSSR_L_zero_L_pos_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_L hu_dt hDmax
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

theorem transitionPEM_prePhase4_dormant_leader_roles_tau
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


lemma prePhase4_recruit_ba_answer_preserved_tau
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


/-- Config.step lift of `rankDeltaOSSR_leader_dedup_step`: pair two L agents
(both R, both rc=0, both dt>1), second's leader becomes F, both dt decrease. -/
theorem step_leader_dedup_tau
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

theorem step_leader_dedup_trace_tau
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
    step_leader_dedup_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (ℓ := ℓ) (w := w) hℓw
      hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
    hstep.2.2.2.2.1, hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2.1,
    hstep.2.2.2.2.2.2.2, ?_⟩
  intro x hxℓ hxw
  simp [Config.step, hℓw, hxℓ, hxw, P]

theorem step_leader_dedup_resetLeaderCount_lt_tau
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
    step_leader_dedup_trace_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_LF_tau
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
    have h_step := step_both_rc_pos_LF_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
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
theorem drain_pair_rc_FF_tau
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
    have h_step := step_both_rc_pos_FF_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
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
theorem drain_pair_rc_LF_with_u_delay_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
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
      (runPairs P C L u).1.delaytimer = Dmax ∧
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
        (runPairs P C' L u).1.delaytimer = Dmax ∧
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
    have h_step := step_both_rc_pos_LF_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F'
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
      have hnew : Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) = 0 := by
        have hdone' := hdone
        rw [hu_rc₁_eq, hv_rc₁_eq] at hdone'
        simpa using hdone'
      have hu_delay₁ : (C'.step P u v u).1.delaytimer = Dmax :=
        step_both_rc_pos_fst_delay_final_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] u).1.leader = .L
        simp [runPairs]; exact hu_L₁
      · show (runPairs P C' [(u, v)] u).1.delaytimer = Dmax
        simp [runPairs]; rw [hu_delay₁]
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
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hu_dt_t,
          hv_role_t, hv_rc_t, hv_F_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hu_L₁ hv_F₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.leader = .L
        simp [runPairs]; exact hu_L_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.delaytimer = Dmax
        simp [runPairs]; exact hu_dt_t
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
theorem drain_pair_rc_LL_to_LF_zero_with_u_delay_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer = Dmax ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_both_rc_pos_LL_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hu_L hv_L
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount =
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount =
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero :
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0
  · have hu_delay₁ : (C₁ u).1.delaytimer = Dmax := by
      simpa [C₁, P] using
        step_both_rc_pos_fst_delay_final_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hzero
    refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] u).1.delaytimer = Dmax
      simp [runPairs, C₁, P]
      exact hu_delay₁
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
  · have hposM : 0 < Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hposM
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hposM
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hu_dt_t,
        hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF_with_u_delay_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      show (runPairs P C₁ Ltail u).1.delaytimer = Dmax
      exact hu_dt_t
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
theorem drain_L_pos_F_zero_to_zero_tau
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
  have hstep := step_L_pos_F_zero_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
      drain_pair_rc_LF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
theorem drain_L_pos_L_zero_to_zero_tau
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
  have hstep := step_L_pos_L_zero_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
      drain_pair_rc_LF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem drain_L_pos_any_zero_to_zero_tau
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
      exact drain_L_pos_L_zero_to_zero_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hv_dt
  | F =>
      exact drain_L_pos_F_zero_to_zero_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hv_dt

set_option maxHeartbeats 8000000 in
theorem drain_F_pos_F_zero_to_zero_FF_tau
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
  have hstep := step_F_pos_F_zero_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
      drain_pair_rc_FF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
theorem drain_L_zero_pos_to_zero_of_step_with_anchor_delay_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hv_rc : 0 < (C v).1.resetcount)
    (hu_dt : 1 < (C u).1.delaytimer)
    (hstep :
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧
      (C' v).1.role = .Resetting ∧
      (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
      (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
      (C' u).1.leader = .L ∧
      (C' v).1.leader = .F ∧
      (C' u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer)) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax) ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C v).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C v).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2.1
  have hu_dt₁ : (C₁ u).1.delaytimer =
      (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer) := by
    simpa [C₁, P] using hstep.2.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C v).1.resetcount - 1 = 0
  · have hv_one : (C v).1.resetcount = 1 := by omega
    refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] u).1.delaytimer =
          (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax)
      simp [runPairs, C₁, P]
      rw [hu_dt₁, if_pos hv_one]
      rw [if_pos hv_one]
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
  · have hpos : 0 < (C v).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hu_dt_t,
        hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF_with_u_delay_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · have hv_not_one : (C v).1.resetcount ≠ 1 := by
        intro hv_one
        exact hzero (by omega)
      rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax)
      rw [hu_dt_t, if_neg hv_not_one]
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

theorem drain_L_zero_any_pos_to_zero_with_anchor_delay_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hu_dt : 1 < (C u).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax) ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      have hstep_full := step_L_zero_L_pos_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
        (by omega : 1 < (C u).1.delaytimer)
      exact drain_L_zero_pos_to_zero_of_step_with_anchor_delay_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hv_rc hu_dt hstep_full
  | F =>
      have hstep_full := step_L_zero_F_pos_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
        (by omega : 1 < (C u).1.delaytimer)
      exact drain_L_zero_pos_to_zero_of_step_with_anchor_delay_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hv_rc hu_dt hstep_full

theorem drain_pair_rc_L_any_to_LF_zero_with_u_delay_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer = Dmax ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      exact drain_pair_rc_LL_to_LF_zero_with_u_delay_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
  | F =>
      obtain ⟨L, hu_role, hu_rc0, hu_L', hu_dt, hv_role, hv_rc0, hv_F', hothers⟩ :=
        drain_pair_rc_LF_with_u_delay_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
      exact ⟨L, hu_role, hu_rc0, hu_L', hu_dt, hv_role, hv_rc0, hv_F', hothers⟩

set_option maxHeartbeats 16000000 in
theorem drain_positive_except_anchor_to_zero_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hBudget : (positiveRcExcept C ℓ).card < (C ℓ).1.delaytimer)
    (hZeroF : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0 → (C w).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (C' ℓ).1.resetcount = 0 ∧
      (C' ℓ).1.leader = .L ∧
      (∀ w : Fin n, w ≠ ℓ → (C' w).1.resetcount = 0) ∧
      (∀ w : Fin n, w ≠ ℓ → (C' w).1.leader = .F) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcExcept C₀ ℓ).card ≤ k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (C₀ ℓ).1.leader = .L →
        (C₀ ℓ).1.resetcount = 0 →
        (positiveRcExcept C₀ ℓ).card < (C₀ ℓ).1.delaytimer →
        (∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 → (C₀ w).1.leader = .F) →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (C' ℓ).1.resetcount = 0 ∧
          (C' ℓ).1.leader = .L ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.resetcount = 0) ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.leader = .F) by
    exact drain (positiveRcExcept C ℓ).card C le_rfl hAllReset hℓ_L hℓ_rc0 hBudget hZeroF
  intro k
  induction k with
  | zero =>
      intro C₀ hcard_le hAll hL hrc0 _hBudget hZero
      have hcard0 : (positiveRcExcept C₀ ℓ).card = 0 := by omega
      have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
        (positiveRcExcept_eq_zero_iff.mp hcard0)
      refine ⟨[], ?_⟩
      simp only [runPairs_nil]
      exact ⟨hAll, hrc0, hL, hAllRc0_except,
        fun w hw_ne => hZero w hw_ne (hAllRc0_except w hw_ne)⟩
  | succ k ih =>
      intro C₀ hcard_le hAll hL hrc0 hBudget₀ hZero
      by_cases hcard0 : (positiveRcExcept C₀ ℓ).card = 0
      · have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
          (positiveRcExcept_eq_zero_iff.mp hcard0)
        refine ⟨[], ?_⟩
        simp only [runPairs_nil]
        exact ⟨hAll, hrc0, hL, hAllRc0_except,
          fun w hw_ne => hZero w hw_ne (hAllRc0_except w hw_ne)⟩
      · have hcard_pos : 0 < (positiveRcExcept C₀ ℓ).card :=
          Nat.pos_of_ne_zero hcard0
        obtain ⟨v, hv_ne, hv_pos⟩ :=
          positiveRcExcept_exists_of_card_pos (C := C₀) (ℓ := ℓ) hcard_pos
        have hℓv : ℓ ≠ v := hv_ne.symm
        have hℓ_delay : 1 < (C₀ ℓ).1.delaytimer := by omega
        obtain ⟨Lstep, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_dt₁,
            hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
          drain_L_zero_any_pos_to_zero_with_anchor_delay_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hℓv (hAll ℓ) (hAll v) hrc0 hv_pos hL hℓ_delay
        let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ Lstep
        have hAll₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
          intro w
          by_cases hwℓ : w = ℓ
          · subst w
            exact hℓ_role₁
          · by_cases hwv : w = v
            · subst w
              exact hv_role₁
            · dsimp [C₁]
              rw [hothers₁ w hwℓ hwv]
              exact hAll w
        have hZero₁ : ∀ w : Fin n, w ≠ ℓ → (C₁ w).1.resetcount = 0 → (C₁ w).1.leader = .F := by
          intro w hw_ne hw_rc0
          by_cases hwv : w = v
          · subst w
            exact hv_F₁
          · have hw_old : C₁ w = C₀ w := hothers₁ w hw_ne hwv
            have hw_old_rc0 : (C₀ w).1.resetcount = 0 := by
              rw [← hw_old]
              exact hw_rc0
            rw [hw_old]
            exact hZero w hw_ne hw_old_rc0
        have hsub : positiveRcExcept C₁ ℓ ⊆ (positiveRcExcept C₀ ℓ).erase v := by
          intro w hw_mem
          rw [positiveRcExcept, Finset.mem_filter] at hw_mem
          have hw_ne : w ≠ ℓ := hw_mem.2.1
          have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2.2
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro hwv
            subst w
            rw [hv_rc₁] at hw_pos
            omega
          · rw [positiveRcExcept, Finset.mem_filter]
            by_cases hwv : w = v
            · subst w
              rw [hv_rc₁] at hw_pos
              omega
            · have hw_old : C₁ w = C₀ w := hothers₁ w hw_ne hwv
              have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                rwa [hw_old] at hw_pos
              exact ⟨Finset.mem_univ w, hw_ne, hw_old_pos⟩
        have hv_mem_old : v ∈ positiveRcExcept C₀ ℓ := by
          rw [positiveRcExcept, Finset.mem_filter]
          exact ⟨Finset.mem_univ v, hv_ne, hv_pos⟩
        have hcard_erase :
            ((positiveRcExcept C₀ ℓ).erase v).card =
              (positiveRcExcept C₀ ℓ).card - 1 :=
          Finset.card_erase_of_mem hv_mem_old
        have hcard₁_le : (positiveRcExcept C₁ ℓ).card ≤ k := by
          have hle := Finset.card_le_card hsub
          rw [hcard_erase] at hle
          omega
        have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
          by_cases hv_one : (C₀ v).1.resetcount = 1
          · have hdt : (C₁ ℓ).1.delaytimer = (C₀ ℓ).1.delaytimer - 1 := by
              rw [hℓ_dt₁, if_pos hv_one]
            rw [hdt]
            have hle := Finset.card_le_card hsub
            rw [hcard_erase] at hle
            omega
          · have hdt : (C₁ ℓ).1.delaytimer = Dmax := by
              rw [hℓ_dt₁, if_neg hv_one]
            rw [hdt]
            exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax_n
        obtain ⟨Ltail, htail⟩ :=
          ih C₁ hcard₁_le hAll₁ hℓ_L₁ hℓ_rc₁ hBudget₁ hZero₁
        refine ⟨Lstep ++ Ltail, ?_⟩
        rw [runPairs_append]
        change
          let C' := runPairs P C₁ Ltail
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (C' ℓ).1.resetcount = 0 ∧
          (C' ℓ).1.leader = .L ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.resetcount = 0) ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.leader = .F)
        exact htail

set_option maxHeartbeats 16000000 in
theorem drain_positive_except_anchor_to_all_zero_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hBudget : (positiveRcExcept C ℓ).card < (C ℓ).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
      (C' ℓ).1.leader = .L := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcExcept C₀ ℓ).card ≤ k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (C₀ ℓ).1.leader = .L →
        (C₀ ℓ).1.resetcount = 0 →
        (positiveRcExcept C₀ ℓ).card < (C₀ ℓ).1.delaytimer →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
          (C' ℓ).1.leader = .L by
    exact drain (positiveRcExcept C ℓ).card C le_rfl hAllReset hℓ_L hℓ_rc0 hBudget
  intro k
  induction k with
  | zero =>
      intro C₀ hcard_le hAll hL hrc0 _hBudget
      have hcard0 : (positiveRcExcept C₀ ℓ).card = 0 := by omega
      have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
        (positiveRcExcept_eq_zero_iff.mp hcard0)
      refine ⟨[], ?_⟩
      simp only [runPairs_nil]
      refine ⟨hAll, ?_, hL⟩
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        exact hrc0
      · exact hAllRc0_except w hwℓ
  | succ k ih =>
      intro C₀ hcard_le hAll hL hrc0 hBudget₀
      by_cases hcard0 : (positiveRcExcept C₀ ℓ).card = 0
      · have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
          (positiveRcExcept_eq_zero_iff.mp hcard0)
        refine ⟨[], ?_⟩
        simp only [runPairs_nil]
        refine ⟨hAll, ?_, hL⟩
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          exact hrc0
        · exact hAllRc0_except w hwℓ
      · have hcard_pos : 0 < (positiveRcExcept C₀ ℓ).card :=
          Nat.pos_of_ne_zero hcard0
        obtain ⟨v, hv_ne, hv_pos⟩ :=
          positiveRcExcept_exists_of_card_pos (C := C₀) (ℓ := ℓ) hcard_pos
        have hℓv : ℓ ≠ v := hv_ne.symm
        have hℓ_delay : 1 < (C₀ ℓ).1.delaytimer := by omega
        obtain ⟨Lstep, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_dt₁,
            hv_role₁, hv_rc₁, _hv_F₁, hothers₁⟩ :=
          drain_L_zero_any_pos_to_zero_with_anchor_delay_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hℓv (hAll ℓ) (hAll v) hrc0 hv_pos hL hℓ_delay
        let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ Lstep
        have hAll₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
          intro w
          by_cases hwℓ : w = ℓ
          · subst w
            exact hℓ_role₁
          · by_cases hwv : w = v
            · subst w
              exact hv_role₁
            · dsimp [C₁]
              rw [hothers₁ w hwℓ hwv]
              exact hAll w
        have hsub : positiveRcExcept C₁ ℓ ⊆ (positiveRcExcept C₀ ℓ).erase v := by
          intro w hw_mem
          rw [positiveRcExcept, Finset.mem_filter] at hw_mem
          have hw_ne : w ≠ ℓ := hw_mem.2.1
          have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2.2
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro hwv
            subst w
            rw [hv_rc₁] at hw_pos
            omega
          · rw [positiveRcExcept, Finset.mem_filter]
            by_cases hwv : w = v
            · subst w
              rw [hv_rc₁] at hw_pos
              omega
            · have hw_old : C₁ w = C₀ w := hothers₁ w hw_ne hwv
              have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                rwa [hw_old] at hw_pos
              exact ⟨Finset.mem_univ w, hw_ne, hw_old_pos⟩
        have hv_mem_old : v ∈ positiveRcExcept C₀ ℓ := by
          rw [positiveRcExcept, Finset.mem_filter]
          exact ⟨Finset.mem_univ v, hv_ne, hv_pos⟩
        have hcard_erase :
            ((positiveRcExcept C₀ ℓ).erase v).card =
              (positiveRcExcept C₀ ℓ).card - 1 :=
          Finset.card_erase_of_mem hv_mem_old
        have hcard₁_le : (positiveRcExcept C₁ ℓ).card ≤ k := by
          have hle := Finset.card_le_card hsub
          rw [hcard_erase] at hle
          omega
        have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
          by_cases hv_one : (C₀ v).1.resetcount = 1
          · have hdt : (C₁ ℓ).1.delaytimer = (C₀ ℓ).1.delaytimer - 1 := by
              rw [hℓ_dt₁, if_pos hv_one]
            rw [hdt]
            have hle := Finset.card_le_card hsub
            rw [hcard_erase] at hle
            omega
          · have hdt : (C₁ ℓ).1.delaytimer = Dmax := by
              rw [hℓ_dt₁, if_neg hv_one]
            rw [hdt]
            exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax_n
        obtain ⟨Ltail, htail⟩ :=
          ih C₁ hcard₁_le hAll₁ hℓ_L₁ hℓ_rc₁ hBudget₁
        refine ⟨Lstep ++ Ltail, ?_⟩
        rw [runPairs_append]
        change
          let C' := runPairs P C₁ Ltail
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
          (C' ℓ).1.leader = .L
        exact htail

set_option maxHeartbeats 64000000 in
theorem all_resetting_pos_with_leader_to_dormant_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, 0 < (C w).1.resetcount)
    (hHasL : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      IsDormantConfig
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨ℓ, hℓ_L⟩ := hHasL
  have hne_of_fin (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  obtain ⟨v, hv_ne_ℓ⟩ := hne_of_fin ℓ
  have hℓv : ℓ ≠ v := hv_ne_ℓ.symm
  obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_delay₁,
      hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
    drain_pair_rc_L_any_to_LF_zero_with_u_delay_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hℓv (hAllReset ℓ) (hAllReset v)
      (hAllPos ℓ) (hAllPos v) hℓ_L
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
    intro w
    by_cases hwℓ : w = ℓ
    · subst w
      exact hℓ_role₁
    · by_cases hwv : w = v
      · subst w
        exact hv_role₁
      · dsimp [C₁]
        rw [hothers₁ w hwℓ hwv]
        exact hAllReset w
  have hZeroF₁ :
      ∀ w : Fin n, w ≠ ℓ → (C₁ w).1.resetcount = 0 → (C₁ w).1.leader = .F := by
    intro w hw_ne hw_rc0
    by_cases hwv : w = v
    · subst w
      exact hv_F₁
    · have hw_old : C₁ w = C w := hothers₁ w hw_ne hwv
      have hw_old_rc0 : (C w).1.resetcount = 0 := by
        rw [← hw_old]
        exact hw_rc0
      have hw_pos := hAllPos w
      omega
  have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
    rw [hℓ_delay₁]
    exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax_n
  obtain ⟨L₂, hAllReset₂, hℓ_rc₂, hℓ_L₂, hAllRc0_except₂, hAllF_except₂⟩ :=
    drain_positive_except_anchor_to_zero_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one hDmax_n C₁ hAllReset₁ hℓ_L₁ hℓ_rc₁ hBudget₁ hZeroF₁
  refine ⟨L₁ ++ L₂, ?_⟩
  rw [runPairs_append]
  change IsDormantConfig (runPairs P C₁ L₂)
  refine ⟨hAllReset₂, ?_, ?_, ?_⟩
  · intro w
    by_cases hwℓ : w = ℓ
    · subst w
      exact hℓ_rc₂
    · exact hAllRc0_except₂ w hwℓ
  · refine ⟨ℓ, hℓ_L₂, ?_⟩
    intro w hwL
    by_cases hwℓ : w = ℓ
    · exact hwℓ
    · have hwF := hAllF_except₂ w hwℓ
      rw [hwF] at hwL
      cases hwL
  · intro w
    cases (runPairs P C₁ L₂ w).1.leader <;> simp

/-- TransitionPEM wrapper: both dormant with dt > 1 → both stay Resetting, dt decreased. -/
theorem transitionPEM_dormant_dt_decrease_tau
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
  have h_rd := rankDeltaOSSR_dormant_dt_decrease (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_F hℓ_dt hw_dt
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
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_leader_low_dt_wakes_tau
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
  have h_rd :=
    rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
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
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
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

theorem transitionPEM_dormant_leader_low_dt_follower_leader_tau
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
  have h_rd :=
    rankDeltaOSSR_dormant_leader_low_dt_follower_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_role :=
    rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
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
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  change (Config.step P C ℓ w w).1.leader = .F
  rw [congrArg AgentState.leader h_snd]
  exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_follower_low_dt_unsettles_tau
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
  have h_rd :=
    rankDeltaOSSR_dormant_follower_low_dt_unsettles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_dt hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
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

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_follower_with_unsettled_partner_wakes_tau
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

theorem transitionPEM_dormant_follower_with_nonresetting_partner_wakes_tau
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

theorem dormant_follower_unsettled_step_followerDormantMeasure_lt_tau
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
      (transitionPEM_dormant_follower_with_unsettled_partner_wakes_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem dormant_follower_nonresetting_step_followerDormantMeasure_lt_tau
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
      (transitionPEM_dormant_follower_with_nonresetting_partner_wakes_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
theorem transitionPEM_dormant_leader_with_unsettled_follower_wakes_tau
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
    have hw_role : (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Unsettled := by
      rw [h_rd.2.2.2.2]
      exact hw_unsettled
    rw [hw_role] at hboth
    exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
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

set_option maxHeartbeats 64000000 in
theorem transitionPEM_both_dormant_followers_low_dt_unsettle_tau
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

theorem both_dormant_followers_low_dt_step_followerDormantMeasure_lt_tau
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
      (transitionPEM_both_dormant_followers_low_dt_unsettle_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

set_option maxHeartbeats 64000000 in
theorem transitionPEM_both_dormant_followers_dt_decrease_tau
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

theorem both_dormant_followers_dt_step_followerDormantMeasure_lt_tau
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
      (transitionPEM_both_dormant_followers_dt_decrease_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
theorem transitionPEM_dormant_followers_low_high_tau
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

theorem dormant_followers_low_high_step_followerDormantMeasure_lt_tau
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
      (transitionPEM_dormant_followers_low_high_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem follower_clean_to_no_reset_tau
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
                  (transitionPEM_both_dormant_followers_low_dt_unsettle_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_low hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (both_dormant_followers_low_dt_step_followerDormantMeasure_lt_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
                  (transitionPEM_dormant_followers_low_high_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (dormant_followers_low_high_step_followerDormantMeasure_lt_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
                  (transitionPEM_dormant_followers_low_high_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := v) (v := u) hvu
                    hv_res hv_fields.1 hv_low hv_fields.2
                    hu_res hu_fields.1 hu_high hu_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (dormant_followers_low_high_step_followerDormantMeasure_lt_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
                  (transitionPEM_both_dormant_followers_dt_decrease_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_high hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (both_dormant_followers_dt_step_followerDormantMeasure_lt_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
              (transitionPEM_dormant_follower_with_unsettled_partner_wakes_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw
                hu_res hu_fields.1 hu_fields.2 hw_un)
          have hmeasure :
              followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
            simpa [P, C₁] using
              (dormant_follower_unsettled_step_followerDormantMeasure_lt_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem follower_dormant_or_nonresetting_to_no_reset_tau
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
            follower_clean_to_no_reset_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
              (transitionPEM_dormant_follower_with_nonresetting_partner_wakes_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw hu_res hu_fields.1 hu_fields.2
                hw_not_reset)
          have hmeasure :
              followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
            simpa [P, C₁] using
              (dormant_follower_nonresetting_step_followerDormantMeasure_lt_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

  /-- RankDeltaOSSR: Settled root meets dormant follower → root unchanged, follower Unsettled. -/
  theorem rankDeltaOSSR_settled_meets_dormant_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_settled : s.role = .Settled)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1 = s ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_settled, ht_res, ht_rc, ht_F]

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_leader_low_dt_L_partner_wakes_tau
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

theorem transitionPEM_settled_meets_dormant_trace_tau
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
  have h_rd := rankDeltaOSSR_settled_meets_dormant (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_settled hw_res hw_rc hw_F
  have h_rd_leader := rankDeltaOSSR_settled_meets_dormant_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_settled hw_res hw_rc hw_F
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩; rw [h_rd.2] at h2; exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
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

theorem transitionPEM_settled_meets_dormant_L_trace_tau
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

theorem settled_root_dormant_step_resettingCount_lt_tau
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
          transitionPEM_settled_meets_dormant_trace_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
          transitionPEM_settled_meets_dormant_L_trace_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
theorem settled_root_zero_resetting_to_no_reset_tau
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
          (settled_root_dormant_step_resettingCount_lt_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
              transitionPEM_settled_meets_dormant_trace_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
              transitionPEM_settled_meets_dormant_L_trace_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem phase3a_to_awakening_tau
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
          (transitionPEM_dormant_leader_low_dt_wakes_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAllRc0 ℓ) hℓ_low hℓ_L
            (hAllR w) (hAllRc0 w) hw_F)
      have hw_leader₁ : (C₁ w).1.leader = .F := by
        simpa [C₁, P] using
          (transitionPEM_dormant_leader_low_dt_follower_leader_tau (τ := τ)
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
            (transitionPEM_dormant_follower_low_dt_unsettles_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAllRc0 ℓ) hℓ_high hℓ_L
              (hAllR w) (hAllRc0 w) hw_low hw_F)
        have hstep₂ := by
          simpa [P, C₁] using
            (transitionPEM_dormant_leader_with_unsettled_follower_wakes_tau (τ := τ)
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
            (transitionPEM_dormant_dt_decrease_tau (τ := τ)
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

/-- Phase 3b+3c: from IsAwakeningConfig, sweep to FreshRankingStart.
(ChatGPT: unique leader enables clean one-pass sweep.) -/
theorem phase3bc_from_awakening_tau
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
          (transitionPEM_settled_meets_dormant_trace_tau (τ := τ)
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


/-- tau-clone of `prePhase4_recruit_ba_child_timer_of_median`: trank slot split
from the rankDelta parameters; the recruited child timer is the tau wake value. -/
lemma prePhase4_recruit_ba_child_timer_of_median_tau
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

/-- tau-clone of `prePhase4_recruit_ba_parent_timer`. -/
lemma prePhase4_recruit_ba_parent_timer_tau
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

lemma transitionPEM_recruit_ba_rank_children_tau
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

set_option maxHeartbeats 8000000 in
lemma transitionPEM_recruit_ba_settled_rank_children_tau
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
    transitionPEM_recruit_ba_rank_children_tau (τ := τ)
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
      prePhase4_recruit_ba_child_timer_of_median_tau
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
      prePhase4_recruit_ba_parent_timer_tau
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

lemma transitionPEM_recruit_ba_child_timer_ge_three_tau
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
    prePhase4_recruit_ba_child_timer_of_median_tau
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid (by simpa [p, hp₁_rank] using hmed)
  have ht :
      transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  unfold phase4_propagate
  simp [hq₁_med, hq₂_not_max]
  split_ifs <;> rw [hdt.1, hp_timer] <;> omega

lemma transitionPEM_recruit_ba_parent_timer_bounds_tau
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
    prePhase4_recruit_ba_parent_timer_tau
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

theorem heapPrefix_recruit_step_tau [Inhabited (Fin n × Fin n)]
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
    transitionPEM_recruit_ba_settled_rank_children_tau (τ := τ)
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
        transitionPEM_recruit_ba_child_timer_ge_three_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
      exact Nat.le_trans (show 2 ≤ 3 by omega) (by simpa using hge3)
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds_tau (τ := τ)
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
        transitionPEM_recruit_ba_child_timer_ge_three_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds_tau (τ := τ)
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

/-- Phase 4: binary tree recruitment → InSrank (ChatGPT induction on n-k). -/
theorem phase4_binary_tree_tau
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
              heapPrefix_recruit_step_tau (τ := τ)
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

/-- Phase 3+4 composition: all-Resetting → InSrank. -/
theorem phase34_rerank_tau
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
    phase3a_to_awakening_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hSeed⟩ :=
    phase3bc_from_awakening_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C₁ (by simpa [C₁, P] using hAwake)
  let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
  obtain ⟨L₃, hRanked⟩ :=
    phase4_binary_tree_tau (τ := τ)
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
  simpa [P] using hRanked

theorem dormant_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨L, hL⟩ :=
    phase34_rerank_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  exact ⟨L, hL⟩

theorem all_resetting_pos_with_leader_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, 0 < (C w).1.resetcount)
    (hHasL : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  obtain ⟨L₁, hDormant⟩ :=
    all_resetting_pos_with_leader_to_dormant_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax_n C hAllReset hAllPos hHasL
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hRanked⟩ :=
    dormant_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax_pos C₁ (by simpa [C₁, P] using hDormant)
  refine ⟨L₁ ++ L₂, ?_⟩
  rw [runPairs_append]
  exact hRanked

theorem phase12_no_reset_to_RankingEndpoint_or_InSrank_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨ RankingEndpoint C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase12_no_reset_to_all_resetting_pos_with_leader_or_InSrank_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hReset
  · refine ⟨L₁, ?_⟩
    exact Or.inl hSrank
  · obtain ⟨hAllReset, hAllPos, hHasL⟩ := hReset
    have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    obtain ⟨L₂, hEndpoint⟩ :=
      all_resetting_pos_with_leader_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hDmax C₁
        (by simpa [C₁, P] using hAllReset)
        (by simpa [C₁, P] using hAllPos)
        (by simpa [C₁, P] using hHasL)
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    change InSrank (runPairs P C₁ L₂) ∨ RankingEndpoint (runPairs P C₁ L₂)
    exact Or.inr hEndpoint

theorem ranking_goal_of_runPairs_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {L : List (Fin n × Fin n)}
    (hEndpoint :
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    exists_schedule_of_runPairs
      (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      hEndpoint

theorem reset_snapshot_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L)
    (hResetPos :
      ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  obtain ⟨L₁, hAll₁, hPos₁, hLeader₁⟩ :=
    phase2_propagate_reset_with_leader_pos_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hReset hResetPos
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hEndpoint⟩ :=
    all_resetting_pos_with_leader_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax C₁
      (by simpa [C₁, P] using hAll₁)
      (by simpa [C₁, P] using hPos₁)
      (by simpa [C₁, P] using hLeader₁)
  refine ⟨L₁ ++ L₂, ?_⟩
  rw [runPairs_append]
  change RankingEndpoint (runPairs P C₁ L₂)
  exact hEndpoint

theorem ranking_goal_of_reset_snapshot_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L)
    (hResetPos :
      ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    reset_snapshot_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) hReset hResetPos
  exact
    ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem step_reset_snapshot_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
  rcases hStep with ⟨hu_role, hu_rc, hu_L, _hv_role, _hv_rc, _hv_L, hSnapshot⟩
  have hReset :
      ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        n ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
    refine ⟨u, hu_role, ?_, hu_L⟩
    rw [hu_rc]
    exact hRmax
  have hResetPos :
      ∀ w : Fin n, (C₁ w).1.role = .Resetting → 0 < (C₁ w).1.resetcount := by
    intro w hw
    have hfields := hSnapshot w hw
    have hrc : (C₁ w).1.resetcount = Rmax := hfields.1
    rw [hrc]
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  obtain ⟨L, hEndpoint⟩ :=
    reset_snapshot_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax C₁ hReset hResetPos
  refine ⟨L, ?_⟩
  rw [runPairs_cons]
  change RankingEndpoint (runPairs P C₁ L)
  exact hEndpoint

theorem InSrank_misorder_step_reset_snapshot_of_not_both_settled_tau
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
    · have hy_state : C' y = C y := by
        dsimp [C', P]
        unfold Config.step
        simp [huv, hyu, hyv]
      have hy_reset_C : (C y).1.role = .Resetting := by
        simpa [C', P, Config.step, huv, hyu, hyv] using hy
      rw [hC.allSettled y] at hy_reset_C
      cases hy_reset_C

theorem InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
      InSrank_misorder_step_reset_snapshot_of_not_both_settled_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC hMis hrole
    obtain ⟨L, hEndpoint⟩ :=
      step_reset_snapshot_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax (C := C) (u := u) (v := v) hstep
    exact Or.inl ⟨L, hEndpoint⟩

theorem InSrank_reaches_RankingEndpoint_or_InSswap_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
          InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax hRmax hC hMis
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

theorem ranking_of_no_reset_with_bad_start_handler_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
    phase12_no_reset_to_RankingEndpoint_or_InSrank_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hEndpoint
  · by_cases hDone : RankingEndpoint C₁
    · exact
        ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁) (by simpa [C₁, P] using hDone)
    · obtain ⟨L₂, hEndpoint₂⟩ := hBad C₁ ⟨by simpa [C₁, P] using hSrank, hDone⟩
      have hEndpoint_total :
          RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
        rw [runPairs_append]
        change RankingEndpoint (runPairs P C₁ L₂)
        exact hEndpoint₂
      exact
        ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂) hEndpoint_total
  · exact
      ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁) (by simpa [C₁, P] using hEndpoint)

theorem InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
    trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hμw hpar hμ_lower hw_not_lower hw_not_upper h_timer
      h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := w) hstep
  exact ⟨(μ, w) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
    no_reset_even_lower_max_timer_one_step_state_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap_pack :=
    no_reset_even_lower_max_timer_one_step_InSswap_tau (τ := τ)
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
    InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hC₁_swap hpar hμw hμ_lower₁ hw_not_upper₁
      hμ_timer₁ hμ_correct₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_bad_even_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
                InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax hRmax hSwap hpar hμw hμ_lower hw_upper htimer0
                  hμ_correct hw_wrong
          · obtain ⟨ρ, hμρ, hρ_max⟩ :=
              hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
            by_cases hρ_wrong : (C ρ).1.answer ≠ majorityAnswer C
            · exact
                InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax hRmax hSwap hpar hμρ hμ_lower hρ_max htimer1
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
                  InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint_tau (τ := τ)
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax hRmax hSwap hpar hμρ hμw hwρ hμ_lower hρ_max
                    hw_upper htimer1 hμ_correct hρ_correct hw_wrong
  simpa [P, motive] using hmain (wrongAnswerCount C) C hbad hSwap rfl

theorem BadRankingStart_even_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1
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
        InSswap_bad_even_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem ranking_of_no_reset_even_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    ranking_of_no_reset_with_bad_start_handler_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
      (fun Cbad hbad =>
        BadRankingStart_even_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar)

theorem InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμw hμ_med hw_no_med h_timer
      h_no_swap hpar h_post_diff

theorem InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint_tau
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

theorem InSswap_bad_timer_zero_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
      InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint_tau (τ := τ)
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
      InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad hSwap hμ_med hw_no_med h_timer hpar hw_wrong

theorem InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
    no_reset_no_swap_max_timer_one_step_InSrank_tau (τ := τ)
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
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hC₁ hμw hμ_med₁ hw_no_med₁ hμ_timer₁
      h_no_swap_w₁ hpar h_post_diff_w₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint_tau
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

theorem InSswap_bad_timer_one_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
      InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad.1 hμv hμ_med hv_max h_timer
        h_no_swap_max hpar h_post_diff
  · have hv_correct : (C v).1.answer = majorityAnswer C := by
      exact not_not.mp hv_wrong
    by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
    · exact
        InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint_tau (τ := τ)
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
        InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad.1 hμv hwm.symm hwv hμ_med hv_max hw_no_med h_timer
          h_no_swap_max h_no_swap_w hpar h_post_same_max h_post_diff_w

theorem InSswap_bad_odd_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
  rcases htimer with htimer0 | htimer1
  · exact
      InSswap_bad_timer_zero_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad hSwap hμ_med htimer0 hpar
  · exact
      InSswap_bad_timer_one_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad hSwap hμ_med htimer1 hpar

theorem BadRankingStart_odd_to_RankingEndpoint_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1
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
        InSswap_bad_odd_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem ranking_of_no_reset_odd_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : ¬ n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    ranking_of_no_reset_with_bad_start_handler_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
      (fun Cbad hbad =>
        BadRankingStart_odd_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar)

theorem follower_dormant_or_nonresetting_to_ranking_goal_or_bad_start_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    (∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t))) ∨
    ∃ L : List (Fin n × Fin n),
      BadRankingStart
        (runPairs (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    follower_dormant_or_nonresetting_to_no_reset_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hClean
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨L₂, h₂⟩ :=
    phase12_no_reset_to_RankingEndpoint_or_InSrank_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hNoResetC₁
  rcases h₂ with hSrank | hEndpoint
  · by_cases hDone : RankingEndpoint (runPairs P C₁ L₂)
    · exact Or.inl
        (ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂)
          (by
            rw [runPairs_append]
            change RankingEndpoint (runPairs P C₁ L₂)
            exact hDone))
    · exact Or.inr ⟨L₁ ++ L₂, by
        rw [runPairs_append]
        exact ⟨hSrank, hDone⟩⟩
  · exact Or.inl
      (ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂)
        (by
          rw [runPairs_append]
          change RankingEndpoint (runPairs P C₁ L₂)
          exact hEndpoint))

theorem follower_dormant_or_nonresetting_to_ranking_goal_odd_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : ¬ n % 2 = 0)
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
  obtain h | hbadReach :=
    follower_dormant_or_nonresetting_to_ranking_goal_or_bad_start_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean
  · exact h
  · obtain ⟨L₁, hbad₁⟩ := hbadReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hbadC₁ : BadRankingStart C₁ := by
      simpa [C₁, P] using hbad₁
    obtain ⟨L₂, hEndpoint₂⟩ :=
      BadRankingStart_odd_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbadC₁ hpar
    have hEndpoint_total : RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem follower_dormant_or_nonresetting_to_ranking_goal_even_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : n % 2 = 0)
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
  obtain h | hbadReach :=
    follower_dormant_or_nonresetting_to_ranking_goal_or_bad_start_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean
  · exact h
  · obtain ⟨L₁, hbad₁⟩ := hbadReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hbadC₁ : BadRankingStart C₁ := by
      simpa [C₁, P] using hbad₁
    obtain ⟨L₂, hEndpoint₂⟩ :=
      BadRankingStart_even_to_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbadC₁ hpar
    have hEndpoint_total : RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem ranking_of_no_reset_by_parity_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
      ranking_of_no_reset_even_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hNoReset
  · exact
      ranking_of_no_reset_odd_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hNoReset

theorem follower_dormant_or_nonresetting_to_ranking_goal_by_parity_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hpar : n % 2 = 0
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_even_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hClean
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_odd_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hClean

theorem ranking_from_all_resetting_pos_with_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, 0 < (C w).1.resetcount)
    (hHasL : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    all_resetting_pos_with_leader_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax_n C hAllReset hAllPos hHasL
  exact
    ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_from_all_resetting_zero_no_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
    follower_dormant_or_nonresetting_to_ranking_goal_by_parity_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean

theorem ranking_from_all_resetting_zero_unique_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  have hDmax_pos : 0 < Dmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hDmax
  obtain ⟨L, hEndpoint⟩ :=
    dormant_to_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C hDormant
  exact
    ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_from_settled_root_zero_resetting_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    settled_root_zero_resetting_to_no_reset_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hℓ_settled hℓ_rank0 hℓ_children hℓ_L hResetZero
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨γ₁, t₁, hC₁⟩ :=
    exists_schedule_of_runPairs P C L₁
      (Goal := fun C' => C' = C₁)
      (by rfl)
  obtain ⟨γ₂, t₂, hgoal₂⟩ :=
    ranking_of_no_reset_by_parity_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hNoResetC₁
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  rw [execution_concat]
  rw [hC₁]
  simpa [P] using hgoal₂

theorem ranking_goal_of_step_ranking_goal_tau
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
theorem ranking_from_all_resetting_zero_with_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
        ranking_from_all_resetting_zero_unique_leader_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax C₀ hAllR hAll0 hUnique
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
            step_leader_dedup_trace_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
              (step_leader_dedup_resetLeaderCount_lt_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (ℓ := ℓ) (w := w) hℓw
                (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
                hℓ_high hw_high)
          have hgoal₁ :=
            IH (resetLeaderCount C₁) (by omega) C₁ rfl hAllR₁ hAll0₁ hHasL₁
          exact
            ranking_goal_of_step_ranking_goal_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := ℓ) (v := w)
              (by simpa [P, C₁] using hgoal₁)
        · have hw_low : (C₀ w).1.delaytimer ≤ 1 := by omega
          let C₁ : Config (AgentState n) Opinion n := C₀.step P w ℓ
          have hstep :=
            transitionPEM_dormant_leader_low_dt_L_partner_wakes_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
            ranking_from_settled_root_zero_resetting_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hEmax hDmax hRmax C₁
              (ℓ := w) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
          exact
            ranking_goal_of_step_ranking_goal_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := w) (v := ℓ)
              (by simpa [P, C₁] using hgoal₁)
      · have hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1 := by omega
        let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        have hstep :=
          transitionPEM_dormant_leader_low_dt_L_partner_wakes_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
          ranking_from_settled_root_zero_resetting_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₁
            (ℓ := ℓ) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
        exact
          ranking_goal_of_step_ranking_goal_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (u := ℓ) (v := w)
            (by simpa [P, C₁] using hgoal₁)

theorem ranking_from_all_resetting_zero_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
      ranking_from_all_resetting_zero_with_leader_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hAllZero hHasLeader
  · exact
      ranking_from_all_resetting_zero_no_leader_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hAllZero
        (by
          intro w hwL
          exact hHasLeader ⟨w, hwL⟩)

theorem ranking_goal_of_runPairs_ranking_goal_tau
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

theorem ranking_from_all_resetting_zero_leader_budget_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hBudget : (positiveRcExcept C ℓ).card < (C ℓ).1.delaytimer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨L₁, hAllReset₁, hAllZero₁, _hℓ_L₁⟩ :=
    drain_positive_except_anchor_to_all_zero_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one hDmax C hAllReset hℓ_L hℓ_rc0 hBudget
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hgoal₁ :=
    ranking_from_all_resetting_zero_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁
      (by simpa [C₁, P] using hAllReset₁)
      (by simpa [C₁, P] using hAllZero₁)
  exact
    ranking_goal_of_runPairs_ranking_goal_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_pos_leader_with_second_pos_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hv_pos : 0 < (C v).1.resetcount) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_dt₁,
      hv_role₁, _hv_rc₁, _hv_F₁, hothers₁⟩ :=
    drain_pair_rc_L_any_to_LF_zero_with_u_delay_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hℓv (hAllReset ℓ) (hAllReset v) hℓ_pos hv_pos hℓ_L
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
  have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
    have hdt : (C₁ ℓ).1.delaytimer = Dmax := by
      simpa [C₁, P] using hℓ_dt₁
    rw [hdt]
    exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax
  have hgoal₁ :=
    ranking_from_all_resetting_zero_leader_budget_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hAllReset₁
      (by simpa [C₁, P] using hℓ_L₁)
      (by simpa [C₁, P] using hℓ_rc₁)
      hBudget₁
  exact
    ranking_goal_of_runPairs_ranking_goal_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_single_pos_leader_high_zero_partner_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hv_zero : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hv_role₁, hv_rc₁, _hv_F₁, hothers₁⟩ :=
    drain_L_pos_any_zero_to_zero_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_pos hv_zero hℓ_L hv_dt
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
    ranking_from_all_resetting_zero_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hAllReset₁ hAllZero₁
  exact
    ranking_goal_of_runPairs_ranking_goal_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 64000000 in
theorem ranking_from_all_resetting_single_pos_leader_low_zero_partner_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hv_zero : (C v).1.resetcount = 0)
    (hv_low : (C v).1.delaytimer ≤ 1)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  by_cases hgt : 1 < (C ℓ).1.resetcount
  · have hstep :=
      step_L_pos_any_zero_gt_one_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hℓv (hAllReset ℓ) (hAllReset v) hgt hv_zero hℓ_L
    let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
    have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hstep.1
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hstep.2.1
        · dsimp [C₁]
          simp [Config.step, P, hℓv, hwℓ, hwv]
          exact hAllReset w
    have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
      have hrc : (C₁ ℓ).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      rw [hrc]
      omega
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      have hrc : (C₁ v).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      rw [hrc]
      omega
    have hgoal₁ :=
      ranking_from_all_resetting_pos_leader_with_second_pos_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C₁ hℓv hAllReset₁
        (by simpa [C₁, P] using hstep.2.2.2.2.1)
        hℓ_pos₁ hv_pos₁
    exact
      ranking_goal_of_step_ranking_goal_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := ℓ) (v := v)
        (by simpa [C₁, P] using hgoal₁)
  · have hℓ_one : (C ℓ).1.resetcount = 1 := by omega
    cases hv_leader : (C v).1.leader with
    | L =>
        have hstep :=
          step_L_pos_one_L_zero_low_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
          ranking_from_settled_root_zero_resetting_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₁ (ℓ := v)
            (by simpa [C₁, P] using hstep.2.2.2.2.1)
            (by simpa [C₁, P] using hstep.2.2.2.2.2.1)
            (by simpa [C₁, P] using hstep.2.2.2.2.2.2.1)
            (by simpa [C₁, P] using hstep.2.2.2.2.2.2.2)
            hResetZero₁
        exact
          ranking_goal_of_step_ranking_goal_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C) (u := ℓ) (v := v)
            (by simpa [C₁, P] using hgoal₁)
    | F =>
        have hstep₁ :=
          step_L_pos_one_F_zero_low_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
            hℓ_L hv_leader hv_low
        let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
        have hstep₂ :=
          transitionPEM_dormant_leader_with_unsettled_follower_wakes_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
          ranking_from_settled_root_zero_resetting_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₂ (ℓ := ℓ)
            (by simpa [C₂, P] using hstep₂.1)
            (by
              have hrank : (C₂ ℓ).1.rank = ⟨0, hn⟩ := by
                simpa [C₂, P] using hstep₂.2.1
              rw [hrank])
            (by simpa [C₂, P] using hstep₂.2.2.1)
            (by simpa [C₂, P] using hstep₂.2.2.2.1)
            hResetZero₂
        have hgoal₁ :=
          ranking_goal_of_step_ranking_goal_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₁) (u := ℓ) (v := v)
            (by simpa [C₂, P] using hgoal₂)
        exact
          ranking_goal_of_step_ranking_goal_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C) (u := ℓ) (v := v)
            (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_single_pos_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
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
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v hℓv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · exact
      ranking_from_all_resetting_single_pos_leader_high_zero_partner_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hℓv hAllReset hℓ_L hℓ_pos
        hv_zero hv_high hOnlyPos
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    exact
      ranking_from_all_resetting_single_pos_leader_low_zero_partner_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hℓv hAllReset hℓ_L hℓ_pos
        hv_zero hv_low hOnlyPos

theorem ranking_from_all_resetting_with_positive_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  by_cases hSecond : ∃ v : Fin n, v ≠ ℓ ∧ 0 < (C v).1.resetcount
  · obtain ⟨v, hv_ne, hv_pos⟩ := hSecond
    exact
      ranking_from_all_resetting_pos_leader_with_second_pos_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hv_ne.symm hAllReset hℓ_L hℓ_pos hv_pos
  · push_neg at hSecond
    have hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0 := by
      intro w hw
      have hle : (C w).1.resetcount ≤ 0 := hSecond w hw
      omega
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨v, hv_ne⟩ := Fintype.exists_ne_of_one_lt_card hcard ℓ
    exact
      ranking_from_all_resetting_single_pos_leader_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hv_ne.symm hAllReset hℓ_L hℓ_pos hOnlyPos

theorem ranking_from_all_resetting_single_pos_follower_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {u v : Fin n}
    (huv : u ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllF : ∀ w : Fin n, (C w).1.leader = .F)
    (hu_pos : 0 < (C u).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ u → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v huv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · obtain ⟨L₁, hu_role₁, hu_rc₁, hu_F₁, hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
      drain_F_pos_F_zero_to_zero_FF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_pos C huv (hAllReset u) (hAllReset v) hu_pos hv_zero
        (hAllF u) (hAllF v) hv_high
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
      follower_dormant_or_nonresetting_to_ranking_goal_by_parity_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C₁ hClean₁
    exact
      ranking_goal_of_runPairs_ranking_goal_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁)
        (by simpa [C₁, P] using hgoal₁)
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    by_cases hu_gt : 1 < (C u).1.resetcount
    · have hstep :=
        step_F_pos_F_zero_gt_one_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C huv (hAllReset u) (hAllReset v) hu_gt hv_zero (hAllF u) (hAllF v)
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
      have hothers_step : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
        intro w hwu hwv
        simp [C₁, Config.step, P, huv, hwu, hwv]
      have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
        rw [hu_rc₁]
        omega
      have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
        rw [hv_rc₁]
        omega
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_F_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
        drain_pair_rc_FF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_F₁ hv_F₁
      let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ Ltail
      have hClean₂ : FollowerDormantOrNonResetting C₂ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₂, P] using hu_role_t,
            by simpa [C₂, P] using hu_rc_t,
            by simpa [C₂, P] using hu_F_t⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inl ⟨by simpa [C₂, P] using hv_role_t,
              by simpa [C₂, P] using hv_rc_t,
              by simpa [C₂, P] using hv_F_t⟩
          · dsimp [C₂]
            rw [hothers_t w hwu hwv, hothers_step w hwu hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₂ :=
        follower_dormant_or_nonresetting_to_ranking_goal_by_parity_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C₂ hClean₂
      have hgoal₁ :=
        ranking_goal_of_runPairs_ranking_goal_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C₁) (L := Ltail)
          (by simpa [C₂, P] using hgoal₂)
      exact
        ranking_goal_of_step_ranking_goal_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)
    · have hu_one : (C u).1.resetcount = 1 := by omega
      have hstep :=
        step_F_pos_one_F_zero_low_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C huv (hAllReset u) (hAllReset v) hu_one hv_zero
          (hAllF u) (hAllF v) hv_low
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
        follower_dormant_or_nonresetting_to_ranking_goal_by_parity_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C₁ hClean₁
      exact
        ranking_goal_of_step_ranking_goal_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 32000000 in
theorem ranking_from_all_resetting_no_leader_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcAgents C₀).card = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (∀ w : Fin n, (C₀ w).1.leader = .F) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    have hAllF : ∀ w : Fin n, (C w).1.leader = .F := by
      intro w
      cases hleader : (C w).1.leader with
      | L => exact False.elim ((hNoLeader w) hleader)
      | F => rfl
    simpa [P] using go (positiveRcAgents C).card C rfl hAllReset hAllF
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
      intro C₀ hcard hAllReset₀ hAllF₀
      by_cases hcard0 : k = 0
      · have hAllZero₀ : ∀ w : Fin n, (C₀ w).1.resetcount = 0 := by
          apply positiveRcAgents_eq_zero_iff.mp
          rw [hcard, hcard0]
        exact
          ranking_from_all_resetting_zero_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₀ hAllReset₀ hAllZero₀
      · have hcard_pos : 0 < (positiveRcAgents C₀).card := by
          rw [hcard]
          omega
        obtain ⟨u, hu_pos⟩ :=
          positiveRcAgents_exists_of_card_pos (C := C₀) hcard_pos
        by_cases hSecond : ∃ v : Fin n, v ≠ u ∧ 0 < (C₀ v).1.resetcount
        · obtain ⟨v, hv_ne, hv_pos⟩ := hSecond
          have huv : u ≠ v := hv_ne.symm
          obtain ⟨L₁, hu_role₁, hu_rc₁, hu_F₁, hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
            drain_pair_rc_FF_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos C₀ huv (hAllReset₀ u) (hAllReset₀ v)
              hu_pos hv_pos (hAllF₀ u) (hAllF₀ v)
          let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ L₁
          have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
            intro w
            by_cases hwu : w = u
            · subst w
              exact hu_role₁
            · by_cases hwv : w = v
              · subst w
                exact hv_role₁
              · dsimp [C₁]
                rw [hothers₁ w hwu hwv]
                exact hAllReset₀ w
          have hAllF₁ : ∀ w : Fin n, (C₁ w).1.leader = .F := by
            intro w
            by_cases hwu : w = u
            · subst w
              exact hu_F₁
            · by_cases hwv : w = v
              · subst w
                exact hv_F₁
              · dsimp [C₁]
                rw [hothers₁ w hwu hwv]
                exact hAllF₀ w
          have hsub : positiveRcAgents C₁ ⊆ (positiveRcAgents C₀).erase u := by
            intro w hw_mem
            rw [positiveRcAgents, Finset.mem_filter] at hw_mem
            have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hwu
              subst w
              rw [hu_rc₁] at hw_pos
              omega
            · rw [positiveRcAgents, Finset.mem_filter]
              by_cases hwv : w = v
              · subst w
                rw [hv_rc₁] at hw_pos
                omega
              · have hwu : w ≠ u := by
                  intro hwu
                  subst w
                  rw [hu_rc₁] at hw_pos
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
            IH (positiveRcAgents C₁).card hcard₁_lt C₁ rfl hAllReset₁ hAllF₁
          exact
            ranking_goal_of_runPairs_ranking_goal_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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
          exact
            ranking_from_all_resetting_single_pos_follower_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hEmax hDmax hRmax C₀ hv_ne_u.symm hAllReset₀ hAllF₀
              hu_pos hOnlyPos

set_option maxHeartbeats 64000000 in
theorem ranking_from_all_resetting_zero_leader_unit_followers_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hPosUnitF :
      ∀ w : Fin n, w ≠ ℓ → 0 < (C w).1.resetcount →
        (C w).1.leader = .F ∧ (C w).1.resetcount = 1) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hDmax_gt_one : 1 < Dmax := by omega
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcExcept C₀ ℓ).card = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (C₀ ℓ).1.leader = .L →
        (C₀ ℓ).1.resetcount = 0 →
        (∀ w : Fin n, w ≠ ℓ → 0 < (C₀ w).1.resetcount →
          (C₀ w).1.leader = .F ∧ (C₀ w).1.resetcount = 1) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using
      go (positiveRcExcept C ℓ).card C rfl hAllReset hℓ_L hℓ_rc0 hPosUnitF
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
      intro C₀ hcard hAllReset₀ hℓ_L₀ hℓ_rc0₀ hPosUnitF₀
      by_cases hcard0 : k = 0
      · have hAllZero₀ : ∀ w : Fin n, (C₀ w).1.resetcount = 0 := by
          intro w
          by_cases hwℓ : w = ℓ
          · subst w
            exact hℓ_rc0₀
          · exact (positiveRcExcept_eq_zero_iff.mp (by rw [hcard, hcard0])) w hwℓ
        exact
          ranking_from_all_resetting_zero_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₀ hAllReset₀ hAllZero₀
      · by_cases hBudget : (positiveRcExcept C₀ ℓ).card < (C₀ ℓ).1.delaytimer
        · exact
            ranking_from_all_resetting_zero_leader_budget_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hEmax hDmax hRmax C₀ hAllReset₀ hℓ_L₀ hℓ_rc0₀ hBudget
        · have hcard_pos : 0 < (positiveRcExcept C₀ ℓ).card := by
            rw [hcard]
            omega
          obtain ⟨v, hv_ne_ℓ, hv_pos⟩ :=
            positiveRcExcept_exists_of_card_pos (C := C₀) (ℓ := ℓ) hcard_pos
          have hℓv : ℓ ≠ v := hv_ne_ℓ.symm
          have hv_fields := hPosUnitF₀ v hv_ne_ℓ hv_pos
          have hv_F : (C₀ v).1.leader = .F := hv_fields.1
          have hv_one : (C₀ v).1.resetcount = 1 := hv_fields.2
          by_cases hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1
          · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ v
            have hstep₁ :=
              step_L_zero_F_pos_one_low_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hDmax_pos C₀ hℓv (hAllReset₀ ℓ) (hAllReset₀ v)
                hℓ_rc0₀ hv_one hℓ_L₀ hv_F hℓ_low
            by_cases hMore : ∃ p : Fin n, p ≠ ℓ ∧ 0 < (C₁ p).1.resetcount
            · obtain ⟨p, hp_ne_ℓ, hp_pos₁⟩ := hMore
              have hp_ne_v : p ≠ v := by
                intro hpv
                subst p
                have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                  simpa [C₁, P] using hstep₁.2.2.2.2.2.1
                rw [hv_rc₁] at hp_pos₁
                omega
              have hp_old : C₁ p = C₀ p := by
                dsimp [C₁, P]
                simp [Config.step, hℓv, hp_ne_ℓ, hp_ne_v]
              have hp_pos₀ : 0 < (C₀ p).1.resetcount := by
                rwa [hp_old] at hp_pos₁
              have hp_fields := hPosUnitF₀ p hp_ne_ℓ hp_pos₀
              let C₂ : Config (AgentState n) Opinion n := C₁.step P p ℓ
              have hpℓ : p ≠ ℓ := hp_ne_ℓ
              have hstep₂ :=
                step_F_pos_one_settled_L_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hDmax_gt_one C₁ hpℓ
                  (by rw [hp_old]; exact hAllReset₀ p)
                  (by simpa [C₁, P] using hstep₁.1)
                  (by rw [hp_old]; exact hp_fields.2)
                  (by rw [hp_old]; exact hp_fields.1)
                  (by simpa [C₁, P] using hstep₁.2.2.2.1)
              have hAllReset₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting := by
                intro w
                by_cases hwp : w = p
                · subst w
                  simpa [C₂, P] using hstep₂.1
                · by_cases hwℓ : w = ℓ
                  · subst w
                    simpa [C₂, P] using hstep₂.2.2.2.1
                  · have hw_step₂ : C₂ w = C₁ w := by
                      dsimp [C₂, P]
                      simp [Config.step, hpℓ, hwp, hwℓ]
                    rw [hw_step₂]
                    by_cases hwv : w = v
                    · subst w
                      simpa [C₁, P] using hstep₁.2.2.2.2.1
                    · have hw_step₁ : C₁ w = C₀ w := by
                        dsimp [C₁, P]
                        simp [Config.step, hℓv, hwℓ, hwv]
                      rw [hw_step₁]
                      exact hAllReset₀ w
              have hℓ_L₂ : (C₂ ℓ).1.leader = .L := by
                simpa [C₂, P] using hstep₂.2.2.2.2.2.1
              have hℓ_rc₂ : (C₂ ℓ).1.resetcount = 0 := by
                simpa [C₂, P] using hstep₂.2.2.2.2.1
              have hℓ_dt₂ : (C₂ ℓ).1.delaytimer = Dmax - 1 := by
                simpa [C₂, P] using hstep₂.2.2.2.2.2.2
              have hBudget₂ : (positiveRcExcept C₂ ℓ).card < (C₂ ℓ).1.delaytimer := by
                have hsub : positiveRcExcept C₂ ℓ ⊆ (Finset.univ.erase ℓ).erase p := by
                  intro x hx
                  rw [positiveRcExcept, Finset.mem_filter] at hx
                  rw [Finset.mem_erase]
                  refine ⟨?_, ?_⟩
                  · intro hxp
                    subst x
                    have hp_rc₂ : (C₂ p).1.resetcount = 0 := by
                      simpa [C₂, P] using hstep₂.2.1
                    rw [hp_rc₂] at hx
                    omega
                  · rw [Finset.mem_erase]
                    exact ⟨hx.2.1, Finset.mem_univ x⟩
                have hle := Finset.card_le_card hsub
                have hp_mem : p ∈ Finset.univ.erase ℓ := by
                  rw [Finset.mem_erase]
                  exact ⟨hp_ne_ℓ, Finset.mem_univ p⟩
                have hcard_erase :
                    ((Finset.univ.erase ℓ).erase p).card = n - 2 := by
                  rw [Finset.card_erase_of_mem hp_mem]
                  rw [Finset.card_erase_of_mem (Finset.mem_univ ℓ)]
                  simpa using (Nat.sub_sub n 1 1)
                rw [hcard_erase] at hle
                rw [hℓ_dt₂]
                omega
              have hgoal₂ :=
                ranking_from_all_resetting_zero_leader_budget_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hEmax hDmax hRmax C₂ hAllReset₂ hℓ_L₂ hℓ_rc₂ hBudget₂
              have hgoal₁ :=
                ranking_goal_of_step_ranking_goal_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₁) (u := p) (v := ℓ)
                  (by simpa [C₂, P] using hgoal₂)
              exact
                ranking_goal_of_step_ranking_goal_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₀) (u := ℓ) (v := v)
                  (by simpa [C₁, P] using hgoal₁)
            · push_neg at hMore
              have hResetZero₁ :
                  ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
                intro w hw_reset
                by_cases hwℓ : w = ℓ
                · subst w
                  have hsettled : (C₁ ℓ).1.role = .Settled := by
                    simpa [C₁, P] using hstep₁.1
                  rw [hsettled] at hw_reset
                  cases hw_reset
                · have hzero := hMore w hwℓ
                  omega
              have hgoal₁ :=
                ranking_from_settled_root_zero_resetting_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hEmax hDmax hRmax C₁
                  (ℓ := ℓ)
                  (by simpa [C₁, P] using hstep₁.1)
                  (by simpa [C₁, P] using hstep₁.2.1)
                  (by simpa [C₁, P] using hstep₁.2.2.1)
                  (by simpa [C₁, P] using hstep₁.2.2.2.1)
                  hResetZero₁
              exact
                ranking_goal_of_step_ranking_goal_tau (τ := τ)
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₀) (u := ℓ) (v := v)
                  (by simpa [C₁, P] using hgoal₁)
          · have hℓ_high : 1 < (C₀ ℓ).1.delaytimer := by omega
            have hstep₁ :=
              step_L_zero_F_pos_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hDmax_pos C₀ hℓv (hAllReset₀ ℓ) (hAllReset₀ v)
                hℓ_rc0₀ hv_pos hℓ_L₀ hv_F hℓ_high
            let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ v
            have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
              intro w
              by_cases hwℓ : w = ℓ
              · subst w
                simpa [C₁, P] using hstep₁.1
              · by_cases hwv : w = v
                · subst w
                  simpa [C₁, P] using hstep₁.2.1
                · dsimp [C₁, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                  exact hAllReset₀ w
            have hℓ_L₁ : (C₁ ℓ).1.leader = .L := by
              simpa [C₁, P] using hstep₁.2.2.2.2.1
            have hℓ_rc₁ : (C₁ ℓ).1.resetcount = 0 := by
              have hrc : (C₁ ℓ).1.resetcount = (C₀ v).1.resetcount - 1 := by
                simpa [C₁, P] using hstep₁.2.2.1
              rw [hrc, hv_one]
            have hPosUnitF₁ :
                ∀ w : Fin n, w ≠ ℓ → 0 < (C₁ w).1.resetcount →
                  (C₁ w).1.leader = .F ∧ (C₁ w).1.resetcount = 1 := by
              intro w hw_ne hw_pos
              by_cases hwv : w = v
              · subst w
                have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                  have hrc : (C₁ v).1.resetcount = (C₀ v).1.resetcount - 1 := by
                    simpa [C₁, P] using hstep₁.2.2.2.1
                  rw [hrc, hv_one]
                rw [hv_rc₁] at hw_pos
                omega
              · have hw_old : C₁ w = C₀ w := by
                  dsimp [C₁, P]
                  simp [Config.step, hℓv, hw_ne, hwv]
                have hw_pos_old : 0 < (C₀ w).1.resetcount := by
                  rwa [hw_old] at hw_pos
                have hw_fields := hPosUnitF₀ w hw_ne hw_pos_old
                rw [hw_old]
                exact hw_fields
            have hsub : positiveRcExcept C₁ ℓ ⊆ (positiveRcExcept C₀ ℓ).erase v := by
              intro w hw_mem
              rw [positiveRcExcept, Finset.mem_filter] at hw_mem
              rw [Finset.mem_erase]
              refine ⟨?_, ?_⟩
              · intro hwv
                subst w
                have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                  have hrc : (C₁ v).1.resetcount = (C₀ v).1.resetcount - 1 := by
                    simpa [C₁, P] using hstep₁.2.2.2.1
                  rw [hrc, hv_one]
                rw [hv_rc₁] at hw_mem
                omega
              · rw [positiveRcExcept, Finset.mem_filter]
                by_cases hwv : w = v
                · subst w
                  have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                    have hrc : (C₁ v).1.resetcount = (C₀ v).1.resetcount - 1 := by
                      simpa [C₁, P] using hstep₁.2.2.2.1
                    rw [hrc, hv_one]
                  rw [hv_rc₁] at hw_mem
                  omega
                · have hw_old : C₁ w = C₀ w := by
                    dsimp [C₁, P]
                    simp [Config.step, hℓv, hw_mem.2.1, hwv]
                  have hw_pos_old : 0 < (C₀ w).1.resetcount := by
                    have hpos := hw_mem.2.2
                    rwa [hw_old] at hpos
                  exact ⟨Finset.mem_univ w, hw_mem.2.1, hw_pos_old⟩
            have hv_mem_old : v ∈ positiveRcExcept C₀ ℓ := by
              rw [positiveRcExcept, Finset.mem_filter]
              exact ⟨Finset.mem_univ v, hv_ne_ℓ, hv_pos⟩
            have hcard₁_lt : (positiveRcExcept C₁ ℓ).card < k := by
              have hle := Finset.card_le_card hsub
              have herase :
                  ((positiveRcExcept C₀ ℓ).erase v).card =
                    (positiveRcExcept C₀ ℓ).card - 1 :=
                Finset.card_erase_of_mem hv_mem_old
              rw [herase, hcard] at hle
              omega
            have hgoal₁ :=
              IH (positiveRcExcept C₁ ℓ).card hcard₁_lt C₁ rfl
                hAllReset₁ hℓ_L₁ hℓ_rc₁ hPosUnitF₁
            exact
              ranking_goal_of_step_ranking_goal_tau (τ := τ)
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := ℓ) (v := v)
                (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_zero_leader_mixed_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hNoPosLeader : ∀ w : Fin n, (C w).1.leader = .L → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  by_cases hGt : ∃ v : Fin n, v ≠ ℓ ∧ 1 < (C v).1.resetcount
  · obtain ⟨v, hv_ne_ℓ, hv_gt⟩ := hGt
    have hℓv : ℓ ≠ v := hv_ne_ℓ.symm
    have hv_F : (C v).1.leader = .F := by
      cases hv_leader : (C v).1.leader with
      | L =>
          have hv_zero := hNoPosLeader v hv_leader
          omega
      | F => rfl
    have hstep :=
      step_L_zero_F_pos_gt_one_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hℓv (hAllReset ℓ) (hAllReset v) hℓ_rc0 hv_gt hℓ_L hv_F
    let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
    have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hstep.1
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hstep.2.1
        · dsimp [C₁, P]
          simp [Config.step, hℓv, hwℓ, hwv]
          exact hAllReset w
    have hℓ_L₁ : (C₁ ℓ).1.leader = .L := by
      simpa [C₁, P] using hstep.2.2.2.2.1
    have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
      have hrc : (C₁ ℓ).1.resetcount = (C v).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      rw [hrc]
      omega
    have hgoal₁ :=
      ranking_from_all_resetting_with_positive_leader_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C₁ hAllReset₁ hℓ_L₁ hℓ_pos₁
    exact
      ranking_goal_of_step_ranking_goal_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := ℓ) (v := v)
        (by simpa [C₁, P] using hgoal₁)
  · have hPosUnitF :
        ∀ w : Fin n, w ≠ ℓ → 0 < (C w).1.resetcount →
          (C w).1.leader = .F ∧ (C w).1.resetcount = 1 := by
      intro w hw_ne hw_pos
      constructor
      · cases hw_leader : (C w).1.leader with
        | L =>
            have hw_zero := hNoPosLeader w hw_leader
            omega
        | F => rfl
      · have hw_not_gt : ¬ 1 < (C w).1.resetcount := by
          intro hw_gt
          exact hGt ⟨w, hw_ne, hw_gt⟩
        omega
    exact
      ranking_from_all_resetting_zero_leader_unit_followers_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hℓ_L hℓ_rc0 hPosUnitF

theorem ranking_from_all_resetting_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  by_cases hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L
  · obtain ⟨ℓ, hℓ_L⟩ := hHasLeader
    by_cases hPosLeader : ∃ r : Fin n, (C r).1.leader = .L ∧ 0 < (C r).1.resetcount
    · obtain ⟨r, hr_L, hr_pos⟩ := hPosLeader
      exact
        ranking_from_all_resetting_with_positive_leader_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C hAllReset hr_L hr_pos
    · have hNoPosLeader :
          ∀ w : Fin n, (C w).1.leader = .L → (C w).1.resetcount = 0 := by
        intro w hw_L
        have hw_not_pos : ¬ 0 < (C w).1.resetcount := by
          intro hw_pos
          exact hPosLeader ⟨w, hw_L, hw_pos⟩
        omega
      exact
        ranking_from_all_resetting_zero_leader_mixed_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C hAllReset hℓ_L
          (hNoPosLeader ℓ hℓ_L) hNoPosLeader
  · have hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L := by
      intro w hw_L
      exact hHasLeader ⟨w, hw_L⟩
    exact
      ranking_from_all_resetting_no_leader_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hNoLeader

theorem ranking_from_known_reset_entry_or_all_resetting_zero_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
      (C : Config (AgentState n) Opinion n)
      (hEntry :
        (∀ w : Fin n, (C w).1.role ≠ .Resetting) ∨
        FollowerDormantOrNonResetting C ∨
        ((∃ r : Fin n, (C r).1.role = .Resetting ∧
            n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) ∧
          ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C w).1.resetcount) ∧
          ∃ r : Fin n, (C r).1.leader = .L) ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
          ∀ w : Fin n, (C w).1.resetcount = 0) ∨
        (∀ w : Fin n, (C w).1.role = .Resetting)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  rcases hEntry with hNoReset | hEntry
  · exact
      ranking_of_no_reset_by_parity_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hNoReset
  rcases hEntry with hClean | hEntry
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_by_parity_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hClean
  rcases hEntry with hSnapshot | hAllReset
  · exact
      ranking_goal_of_reset_snapshot_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax (C := C) hSnapshot.1 hSnapshot.2
  rcases hAllReset with hAllPos | hAllReset
  · rcases hAllPos with ⟨hAllReset, hAllPos, hHasLeader⟩
    have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    exact
      ranking_from_all_resetting_pos_with_leader_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hDmax C hAllReset hAllPos hHasLeader
  · rcases hAllReset with hAllZero | hAllReset
    · rcases hAllZero with ⟨hAllReset, hAllZero⟩
      exact
        ranking_from_all_resetting_zero_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C hAllReset hAllZero
    · exact
        ranking_from_all_resetting_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C hAllReset

theorem ranking_from_InSrank_by_parity_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
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
      ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := [])
        (by simpa using hDone)
  · have hbad : BadRankingStart C := ⟨hSrank, hDone⟩
    by_cases hpar : n % 2 = 0
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_even_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_odd_to_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint


set_option maxHeartbeats 8000000 in
/-- F-leader wake step strictly drops `resetFuel`. Packages
`nonResettingCount + contribution` into a single per-agent summand so the
classic `Finset.sum_lt_sum` pattern (pointwise ≤ + a strict witness) applies
directly. -/
theorem dormant_follower_step_resetFuel_lt_tau
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
      (transitionPEM_dormant_follower_with_nonresetting_partner_wakes_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

/-- Config.step-level partner rc trace. -/
theorem propagate_reset_step_partner_rc_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P r v v).1.role = .Resetting ∧
    (C.step P r v v).1.resetcount = (C r).1.resetcount - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_propagate_reset_recruit_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩
    rw [h_rd.1] at h2
    exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C r).2) (x₁ := (C v).2) h_not_both
  have h_snd := Config.step_snd_state P C hrv hrv.symm
  refine ⟨?_, ?_⟩
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2

/-- Config.step-level sender rc trace: at position `r` after `Config.step P r v`,
the sender stays `.Resetting` with `resetcount` decremented by 1. -/
theorem propagate_reset_step_sender_rc_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P r v r).1.role = .Resetting ∧
    (C.step P r v r).1.resetcount = (C r).1.resetcount - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_propagate_reset_spreader_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C r).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C hrv
  refine ⟨?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2

set_option maxHeartbeats 8000000 in
/-- Propagate-reset step strictly drops `resetFuel`. Sender `r` (Resetting,
rc=k>0) and partner `v` (non-Resetting) both end Resetting at rc=k-1. The
exponential weight gives total drop of exactly 1:
`2^(k+1) + 1` becomes `2^k + 2^k`, and `2^(k+1) = 2·2^k`. -/
theorem propagate_reset_step_resetFuel_lt_tau
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
      (propagate_reset_step_partner_rc_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
        C hrv hr_res hr_rc hv_not)
  have hsender : (C₁ r).1.role = .Resetting ∧
                 (C₁ r).1.resetcount = (C r).1.resetcount - 1 := by
    simpa [P, C₁] using
      (propagate_reset_step_sender_rc_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
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

set_option maxHeartbeats 8000000 in
/-- One-step trace for `transitionPEM` starting from `(s = Resetting rc=0
leader=L, t non-Resetting)`: either both endpoints are non-Resetting (clean
wake) or both are `(Resetting, rc=Rmax, leader=L)` (Phase 4 bounce). -/
theorem transitionPEM_dormant_leader_nonresetting_bounce_or_nonresetting_tau
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
  have h_pre := transitionPEM_prePhase4_dormant_leader_roles_tau
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (s := s) (t := t) (x := x) (y := y)
    hs_res hs_rc hs_L ht_not_res
  by_cases ht_settled : t.role = .Settled
  · -- Both prePhase4 outputs are Settled → apply Phase 4 helper.
    have hpre0 : (transitionPEM_prePhase4 n τ
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
  · -- t is .Unsettled; use transitionPEM_structural_passthrough.
    have ht_unsettled : t.role = .Unsettled := by
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

set_option maxHeartbeats 8000000 in
/-- L-leader wake-or-bounce step: either `resetFuel` strictly drops, or a
strong seed `(R, rc=Rmax, leader=L)` appears. -/
theorem dormant_leader_nonresetting_step_resetFuel_lt_or_seed_tau
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
    transitionPEM_dormant_leader_nonresetting_bounce_or_nonresetting_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
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

/-- Auxiliary: from a configuration with a "fresh seed" — a Resetting
agent whose `resetcount` already exceeds `nonResettingCount` — drive the
protocol to an all-Resetting state by repeatedly propagating the seed
into non-Resetting partners. Each step decrements `nonResettingCount` by
exactly 1 (via `propagate_reset_step_nonResettingCount_lt_tau (τ := τ)` in
`BurmanProof.lean`) and decrements the seed's `resetcount` by 1, so the
invariant "rc ≥ remaining non-R count" is maintained. -/
theorem all_resetting_from_seed_aux_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) :
    ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      nonResettingCount C ≤ k →
      (∃ r : Fin n,
        (C r).1.role = .Resetting ∧
        nonResettingCount C ≤ (C r).1.resetcount) →
      ∃ L : List (Fin n × Fin n),
        ∀ w : Fin n,
          ((runPairs (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.role = .Resetting := by
  classical
  intro k
  induction k with
  | zero =>
    intro C hN _hSeed
    have hN0 : nonResettingCount C = 0 := Nat.le_zero.mp hN
    refine ⟨[], ?_⟩
    intro w
    by_contra hwne
    have hpos : 0 < nonResettingCount C := by
      unfold nonResettingCount
      apply Finset.card_pos.mpr
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwne⟩⟩
    omega
  | succ k ih =>
    intro C hN hSeed
    by_cases hN0 : nonResettingCount C = 0
    · refine ⟨[], ?_⟩
      intro w; by_contra hwne
      have hpos : 0 < nonResettingCount C := by
        unfold nonResettingCount; apply Finset.card_pos.mpr
        exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwne⟩⟩
      omega
    · have hN_pos : 0 < nonResettingCount C := Nat.pos_of_ne_zero hN0
      have hv_exists : ∃ v, (C v).1.role ≠ .Resetting := by
        have : (Finset.univ.filter
            (fun x : Fin n => (C x).1.role ≠ .Resetting)).Nonempty := by
          rw [← Finset.card_pos]
          unfold nonResettingCount at hN_pos
          exact hN_pos
        obtain ⟨v, hv⟩ := this
        exact ⟨v, (Finset.mem_filter.mp hv).2⟩
      obtain ⟨v, hv_not⟩ := hv_exists
      obtain ⟨r, hr_res, hr_rc_big⟩ := hSeed
      have hr_rc_pos : 0 < (C r).1.resetcount := by omega
      have hrv : r ≠ v := fun heq => by subst heq; exact hv_not hr_res
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
      let C₁ := C.step P r v
      have h_step :=
        propagate_reset_step_nonResettingCount_lt_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
          C hrv hr_res hr_rc_pos hv_not
      have hC1_r_role : (C₁ r).1.role = .Resetting := h_step.1
      have hC1_r_rc : (C₁ r).1.resetcount = (C r).1.resetcount - 1 := h_step.2.1
      have hN_drop : nonResettingCount C₁ < nonResettingCount C := h_step.2.2.2
      have hN1 : nonResettingCount C₁ ≤ k := by omega
      have hr_rc_C1 : nonResettingCount C₁ ≤ (C₁ r).1.resetcount := by
        rw [hC1_r_rc]; omega
      have hSeed1 :
          ∃ r' : Fin n, (C₁ r').1.role = .Resetting ∧
              nonResettingCount C₁ ≤ (C₁ r').1.resetcount :=
        ⟨r, hC1_r_role, hr_rc_C1⟩
      obtain ⟨L, hL⟩ := ih C₁ hN1 hSeed1
      refine ⟨(r, v) :: L, ?_⟩
      intro w
      simp only [runPairs_cons]
      exact hL w

/-- **One propagate-reset step carries the majority answer to BOTH endpoints.**
If sender `r` is `.Resetting` with `resetcount > 0` holding `majorityAnswer C`
and partner `v` is non-`.Resetting`, then after `Config.step P r v`, both `r`
and `v` hold `majorityAnswer` of the new configuration (which is unchanged). -/
theorem propagate_reset_step_answer_trace_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n) {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting)
    (hr_ans : (C r).1.answer = majorityAnswer C) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ((C.step P r v) r).1.answer = majorityAnswer (C.step P r v) ∧
    ((C.step P r v) v).1.answer = majorityAnswer (C.step P r v) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  -- rankDelta puts both into Resetting and preserves answers.
  have h_rd_snd := rankDeltaOSSR_propagate_reset_recruit_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_rd_fst := rankDeltaOSSR_propagate_reset_spreader_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  -- answer preservation through rankDeltaOSSR (propagateReset + leader dedup)
  have h_ans : (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.answer
        = (C r).1.answer ∧
      (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.answer
        = (C v).1.answer := by
    unfold rankDeltaOSSR
    simp only [hr_res, true_or, ite_true]
    have hpr := propagateReset_answer_preserved (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (C r).1 (C v).1
    refine ⟨?_, ?_⟩
    · exact hpr.1
    · split_ifs <;> exact hpr.2
  -- prePhase4 answer trace.
  have h_pre := transitionPEM_prePhase4_propagate_answer
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C r).1) (s₁ := (C v).1) (x₀ := (C r).2) (x₁ := (C v).2)
    (ans := majorityAnswer C)
    hr_res hv_not h_rd_fst.1 h_rd_snd.1
    (hr_ans ▸ h_ans.1) h_ans.2 (majorityAnswer_ne_phi C)
  -- transitionPEM = prePhase4 then phase4; phase4 skipped (not both Settled).
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.role = .Settled) := by
    rintro ⟨h1, _⟩
    rw [h_rd_fst.1] at h1; exact Role.noConfusion h1
  have h_pre_not_settled :
      ¬ ((transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C r).1 (C v).1 (C r).2 (C v).2).1.role = .Settled ∧
          (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C r).1 (C v).1 (C r).2 (C v).2).2.role = .Settled) := by
    have hpre_struct := transitionPEM_prePhase4_structural
      (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C r).1) (s₁ := (C v).1) (x₀ := (C r).2) (x₁ := (C v).2)
    rintro ⟨h1, _⟩
    rw [hpre_struct.1, h_rd_fst.1] at h1
    exact Role.noConfusion h1
  -- The δ output answers.
  have h_delta_ans :
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C r).1, (C r).2), ((C v).1, (C v).2))).1.answer = majorityAnswer C ∧
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C r).1, (C r).2), ((C v).1, (C v).2))).2.answer = majorityAnswer C := by
    rw [transitionPEM_eq]
    rw [transitionPEM_phase4_of_not_both_settled h_pre_not_settled]
    exact h_pre
  -- majorityAnswer invariant under the step.
  have h_maj : majorityAnswer (C.step P r v) = majorityAnswer C := by
    rw [hP]; exact majorityAnswer_step_eq C r v
  have h_fst := Config.step_fst_state P C hrv
  have h_snd := Config.step_snd_state P C hrv hrv.symm
  refine ⟨?_, ?_⟩
  · rw [h_maj]
    rw [congrArg AgentState.answer h_fst]
    show (P.δ (C r, C v)).1.answer = majorityAnswer C
    simp only [hP, protocolPEM]
    exact h_delta_ans.1
  · rw [h_maj]
    rw [congrArg AgentState.answer h_snd]
    show (P.δ (C r, C v)).2.answer = majorityAnswer C
    simp only [hP, protocolPEM]
    exact h_delta_ans.2

/-- **Trigger a correct reset from an `InSswap` configuration.**

From an `InSswap` configuration (which extends `InSrank`) whose median
agent `μ` has a dead timer (`timer = 0`) and a non-median, non-max agent
`v` whose `.answer` disagrees with the median's post-decision answer, a
single propagation step (`runPairs [(μ, v)]`) drives the protocol into a
configuration `C'` such that:

* there EXISTS a Resetting agent (namely `μ`) whose `.answer`
  equals `majorityAnswer C'`, with `resetcount` set to `Rmax ≥ n ≥
  nonResettingCount C'`, so `all_resetting_from_seed_answer_aux_tau (τ := τ)` applies;
* every Resetting agent of `C'` has `.answer = majorityAnswer C'` — the
  only Resetting agents are `μ, v` (all others stay `.Settled`), and both
  carry `opinionToAnswer (median input) = majorityAnswer` (odd `n`) or the
  median's already-correct decided answer (even `n`).

This is exactly the "fresh reset just fired, every Resetting agent already
holds the correct answer" entry the answer-tracking normalizer
`all_resetting_from_seed_answer_aux_tau (τ := τ)` consumes.

**Hypothesis note.** The bare `InSrank + (timer ≥ 2 @ median)` form is
*literally unprovable*: if every answer is already correct the
configuration is a consensus and the protocol cannot produce ANY Resetting
agent from it, so the required `∃ r, role = .Resetting ∧ …` is false. The
spirit is preserved by giving the directly-fireable reset witness (median
with dead timer + a disagreeing partner), which is precisely the state
reached after timer descent + locating a wrong agent; the even-`n` branch
additionally takes the median's already-decided correct answer
(`(C μ).1.answer = majorityAnswer C`), true at the call site because the
decision phase precedes the wrong-agent reset. -/
theorem trigger_correct_reset_from_InSrank_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hne : nAOf C ≠ nBOf C)
    (hμ_ans : (C μ).1.answer = majorityAnswer C)
    (h_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      (∃ r : Fin n,
        (C' r).1.role = .Resetting ∧
        nonResettingCount C' < (C' r).1.resetcount ∧
        (C' r).1.leader = .L ∧
        (C' r).1.answer = majorityAnswer C') ∧
      (∀ w : Fin n, (C' w).1.role = .Resetting →
        0 < (C' w).1.resetcount ∧
        (C' w).1.answer = majorityAnswer C') := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have hC_rank : InSrank C := hC.toInSrank
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank :=
    fun hEq => hμv (hC_rank.ranks_inj hEq)
  -- `majorityAnswer` is invariant under one step at `(μ, v)`.
  have h_maj : majorityAnswer (C.step P μ v) = majorityAnswer C := by
    rw [hP]; exact majorityAnswer_step_eq C μ v
  -- The unused list is the singleton `[(μ, v)]`.
  refine ⟨[(μ, v)], ?_⟩
  -- Snapshot of roles / resetcount / leader after the reset step.
  set C' : Config (AgentState n) Opinion n := C.step P μ v with hC'def
  have hC'_runPairs :
      runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, hC'def]
  -- No-swap holds for a Settled pair: derive from the median's input side.
  -- The median's input matches the majority (its post-decision answer is
  -- `majorityAnswer C`).
  have hμ_correct : opinionToAnswer (C μ).2 = majorityAnswer C := by
    by_cases hp : n % 2 = 0
    · have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
        have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
        rw [← hceil]; exact hμ_med
      exact opinionToAnswer_lower_median_eq_majorityAnswer_even hC hμ_lower hp hne
    · exact opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hp
  by_cases hpar : n % 2 = 0
  · -- ===== Even n =====
    have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hμ_med
    have hv_not_lower : (C v).1.rank.val + 1 ≠ n / 2 := by
      rw [← hceil]; exact hv_no_med
    -- No swap: μ's input is on the majority side; characterise it.
    have h_no_swap :
        ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧
          (C v).2 = Opinion.A) := by
      rintro ⟨_, _, _⟩
      -- If a swap-fires structure existed at a Settled pair InSswap, the
      -- inputs would be misordered, contradicting `input_rank` sortedness.
      rename_i hlt _hμB hvA
      have hμlt : (C μ).1.rank.val < (C v).1.rank.val := hlt
      have hvA' : (C v).1.rank.val < nAOf C := (hC.input_rank v).mp hvA
      have hμA : (C μ).2 = Opinion.A :=
        (hC.input_rank μ).mpr (by omega)
      rw [hμA] at _hμB
      exact Opinion.noConfusion _hμB
    have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
      rw [hμ_ans]; intro hEq; exact h_wrong hEq.symm
    -- Roles / resetcount / leader snapshot (even reset trace).
    have hsnap :=
      trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC_rank hμv hpar hμ_lower hv_not_lower hv_no_upper h_timer
        h_no_swap h_post_diff
    -- Explicit answer trace (even).
    have htr :=
      propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC_rank hμv hpar hμ_lower hv_not_lower hv_no_upper h_timer
        h_no_swap h_post_diff
    have hfst := Config.step_fst_state P C hμv
    have hsnd := Config.step_snd_state P C hμv hμv.symm
    -- μ's answer (unchanged by the even trace) is the majority answer.
    have hμ_ans' : (C' μ).1.answer = majorityAnswer C := by
      have : (C' μ).1.answer = (C μ).1.answer := by
        dsimp [C']
        rw [congrArg AgentState.answer hfst]
        change (transitionPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer = _
        rw [htr]
      rw [this, hμ_ans]
    -- v's answer is copied from μ, hence the majority answer.
    have hv_ans' : (C' v).1.answer = majorityAnswer C := by
      have : (C' v).1.answer = (C μ).1.answer := by
        dsimp [C']
        rw [congrArg AgentState.answer hsnd]
        change (transitionPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer = _
        rw [htr]
      rw [this, hμ_ans]
    obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, hAll⟩ :=
      hsnap
    -- Untouched agents stay Settled.
    have hothers : ∀ x : Fin n, x ≠ μ → x ≠ v → C' x = C x := by
      intro x hxμ hxv
      dsimp [C']
      simp [Config.step, hμv, hxμ, hxv]
    -- `majorityAnswer C' = majorityAnswer C`.
    have h_maj' : majorityAnswer C' = majorityAnswer C := h_maj
    have hN_bound : nonResettingCount C' < Rmax := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hμ_role' : (C' μ).1.role = .Resetting := by
        simpa [C', P] using hμ_role
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          exact hx_not hμ_role'
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      have hn_pos : 0 < n := by omega
      have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
      unfold nonResettingCount
      rw [← hS]
      omega
    have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [hC'_runPairs] using hμ_role
    · rw [hC'_runPairs]
      have := hμ_rc
      simp only at this
      rw [this]
      exact hN_bound
    · simpa [hC'_runPairs] using hμ_leader
    · rw [hC'_runPairs]; rw [hμ_ans', h_maj']
    · intro w hw
      rw [hC'_runPairs] at hw ⊢
      by_cases hwμ : w = μ
      · subst hwμ
        refine ⟨?_, ?_⟩
        · rw [hμ_rc]
          exact hRmax_pos
        · rw [hμ_ans', h_maj']
      · by_cases hwv : w = v
        · subst hwv
          refine ⟨?_, ?_⟩
          · rw [hv_rc]
            exact hRmax_pos
          · rw [hv_ans', h_maj']
        · -- w untouched ⇒ still Settled ⇒ vacuous.
          have hwx : C' w = C w := hothers w hwμ hwv
          rw [hwx] at hw
          exact absurd hw (by rw [hC_rank.allSettled w]; decide)
  · -- ===== Odd n =====
    have h_no_swap :
        ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧
          (C v).2 = Opinion.A) := by
      rintro ⟨hlt, hμB, hvA⟩
      have hμlt : (C μ).1.rank.val < (C v).1.rank.val := hlt
      have hvA' : (C v).1.rank.val < nAOf C := (hC.input_rank v).mp hvA
      have hμA : (C μ).2 = Opinion.A :=
        (hC.input_rank μ).mpr (by omega)
      rw [hμA] at hμB
      exact Opinion.noConfusion hμB
    have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
      rw [hμ_correct]; intro hEq; exact h_wrong hEq.symm
    -- Roles / resetcount / leader snapshot (odd reset trace).
    have hsnap :=
      trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC_rank hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
    -- Explicit answer trace (odd).
    have htr :=
      propagation_reset_fires_no_swap_trace
        (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC_rank hμv hμ_med hv_no_med h_timer h_no_swap hpar
        h_post_diff
    have hfst := Config.step_fst_state P C hμv
    have hsnd := Config.step_snd_state P C hμv hμv.symm
    have hμ_ans' : (C' μ).1.answer = majorityAnswer C := by
      have : (C' μ).1.answer = opinionToAnswer (C μ).2 := by
        dsimp [C']
        rw [congrArg AgentState.answer hfst]
        change (transitionPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.answer = _
        rw [htr]
      rw [this, hμ_correct]
    have hv_ans' : (C' v).1.answer = majorityAnswer C := by
      have : (C' v).1.answer = opinionToAnswer (C μ).2 := by
        dsimp [C']
        rw [congrArg AgentState.answer hsnd]
        change (transitionPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.answer = _
        rw [htr]
      rw [this, hμ_correct]
    obtain ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, hAll⟩ :=
      hsnap
    have hothers : ∀ x : Fin n, x ≠ μ → x ≠ v → C' x = C x := by
      intro x hxμ hxv
      dsimp [C']
      simp [Config.step, hμv, hxμ, hxv]
    have h_maj' : majorityAnswer C' = majorityAnswer C := h_maj
    have hN_bound : nonResettingCount C' < Rmax := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hμ_role' : (C' μ).1.role = .Resetting := by
        simpa [C', P] using hμ_role
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          exact hx_not hμ_role'
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      have hn_pos : 0 < n := by omega
      have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
      unfold nonResettingCount
      rw [← hS]
      omega
    have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    refine ⟨⟨μ, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [hC'_runPairs] using hμ_role
    · rw [hC'_runPairs]
      have := hμ_rc
      simp only at this
      rw [this]
      exact hN_bound
    · simpa [hC'_runPairs] using hμ_leader
    · rw [hC'_runPairs]; rw [hμ_ans', h_maj']
    · intro w hw
      rw [hC'_runPairs] at hw ⊢
      by_cases hwμ : w = μ
      · subst hwμ
        refine ⟨?_, ?_⟩
        · rw [hμ_rc]
          exact hRmax_pos
        · rw [hμ_ans', h_maj']
      · by_cases hwv : w = v
        · subst hwv
          refine ⟨?_, ?_⟩
          · rw [hv_rc]
            exact hRmax_pos
          · rw [hv_ans', h_maj']
        · have hwx : C' w = C w := hothers w hwμ hwv
          rw [hwx] at hw
          exact absurd hw (by rw [hC_rank.allSettled w]; decide)

/-- **Answer-tracking twin of `all_resetting_from_seed_aux_tau`.** Same
propagate-reset induction on `nonResettingCount`, but carrying the invariant
that EVERY Resetting agent holds `majorityAnswer C` (the seed in particular).
At the end (all Resetting) EVERY agent holds `majorityAnswer C`: each
propagate step keeps the seed Resetting holding the answer and copies the
answer into the freshly-recruited partner (via prePhase4's phi-wipe followed
by phi-spread, `propagate_reset_step_answer_trace_tau (τ := τ)`); untouched agents are
unchanged so the invariant is maintained, and at `nonResettingCount = 0`
every agent is Resetting and therefore holds the answer.

The answer invariant is stated for *all* Resetting agents (not the seed
alone): a seed-only invariant is provably insufficient because freshly
recruited agents must also be tracked, and any Resetting agent never chosen
as a propagation partner keeps its entry answer.  This is the form actually
produced at the call site (the normalizer fires immediately after a fresh
reset, so every Resetting agent already carries the correct answer). -/
theorem all_resetting_from_seed_answer_aux_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) :
    ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      nonResettingCount C ≤ k →
      (∃ r : Fin n,
        (C r).1.role = .Resetting ∧
        nonResettingCount C ≤ (C r).1.resetcount ∧
        (C r).1.answer = majorityAnswer C) →
      (∀ w : Fin n, (C w).1.role = .Resetting →
        (C w).1.answer = majorityAnswer C) →
      ∃ L : List (Fin n × Fin n),
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.role = .Resetting) ∧
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer
            = majorityAnswer C) := by
  classical
  suffices h_aux : ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      nonResettingCount C ≤ k →
      (∃ r : Fin n,
        (C r).1.role = .Resetting ∧
        nonResettingCount C ≤ (C r).1.resetcount) →
      (∀ w : Fin n, (C w).1.role = .Resetting →
        (C w).1.answer = majorityAnswer C) →
      ∃ L : List (Fin n × Fin n),
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.role = .Resetting) ∧
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer
            = majorityAnswer C) by
    intro k C hN hSeed hAllAns
    obtain ⟨r, hr_res, hr_rc, _hr_ans⟩ := hSeed
    exact h_aux k C hN ⟨r, hr_res, hr_rc⟩ hAllAns
  -- Proof of the strengthened lemma `h_aux`.
  intro k
  induction k with
  | zero =>
    intro C hN _hSeed hAllAns
    have hN0 : nonResettingCount C = 0 := Nat.le_zero.mp hN
    have hAllRes : ∀ w : Fin n, (C w).1.role = .Resetting := by
      intro w
      by_contra hwne
      have hpos : 0 < nonResettingCount C := by
        unfold nonResettingCount
        apply Finset.card_pos.mpr
        exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwne⟩⟩
      omega
    refine ⟨[], ?_, ?_⟩
    · intro w; simpa using hAllRes w
    · intro w; simpa using hAllAns w (hAllRes w)
  | succ k ih =>
    intro C hN hSeed hAllAns
    by_cases hN0 : nonResettingCount C = 0
    · have hAllRes : ∀ w : Fin n, (C w).1.role = .Resetting := by
        intro w
        by_contra hwne
        have hpos : 0 < nonResettingCount C := by
          unfold nonResettingCount
          apply Finset.card_pos.mpr
          exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwne⟩⟩
        omega
      refine ⟨[], ?_, ?_⟩
      · intro w; simpa using hAllRes w
      · intro w; simpa using hAllAns w (hAllRes w)
    · have hN_pos : 0 < nonResettingCount C := Nat.pos_of_ne_zero hN0
      have hv_exists : ∃ v, (C v).1.role ≠ .Resetting := by
        have : (Finset.univ.filter
            (fun x : Fin n => (C x).1.role ≠ .Resetting)).Nonempty := by
          rw [← Finset.card_pos]
          unfold nonResettingCount at hN_pos
          exact hN_pos
        obtain ⟨v, hv⟩ := this
        exact ⟨v, (Finset.mem_filter.mp hv).2⟩
      obtain ⟨v, hv_not⟩ := hv_exists
      obtain ⟨r, hr_res, hr_rc_big⟩ := hSeed
      have hr_rc_pos : 0 < (C r).1.resetcount := by omega
      have hrv : r ≠ v := fun heq => by subst heq; exact hv_not hr_res
      have hr_ans : (C r).1.answer = majorityAnswer C := hAllAns r hr_res
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        with hP
      let C₁ := C.step P r v
      have h_step :=
        propagate_reset_step_nonResettingCount_lt_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
          C hrv hr_res hr_rc_pos hv_not
      have hC1_r_role : (C₁ r).1.role = .Resetting := h_step.1
      have hC1_r_rc : (C₁ r).1.resetcount = (C r).1.resetcount - 1 :=
        h_step.2.1
      have hN_drop : nonResettingCount C₁ < nonResettingCount C :=
        h_step.2.2.2
      have hN1 : nonResettingCount C₁ ≤ k := by omega
      have hr_rc_C1 : nonResettingCount C₁ ≤ (C₁ r).1.resetcount := by
        rw [hC1_r_rc]; omega
      have hSeed1 :
          ∃ r' : Fin n, (C₁ r').1.role = .Resetting ∧
              nonResettingCount C₁ ≤ (C₁ r').1.resetcount :=
        ⟨r, hC1_r_role, hr_rc_C1⟩
      -- Maintain the strengthened answer invariant for C₁.
      have h_maj : majorityAnswer C₁ = majorityAnswer C := by
        show majorityAnswer (C.step P r v) = majorityAnswer C
        rw [hP]; exact majorityAnswer_step_eq C r v
      have h_ans_trace :=
        propagate_reset_step_answer_trace_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
          C hrv hr_res hr_rc_pos hv_not hr_ans
      have hC1_r_ans : (C₁ r).1.answer = majorityAnswer C₁ := by
        simpa [C₁, P] using h_ans_trace.1
      have hC1_v_ans : (C₁ v).1.answer = majorityAnswer C₁ := by
        simpa [C₁, P] using h_ans_trace.2
      -- Untouched agents keep their state.
      have hothers : ∀ x : Fin n, x ≠ r → x ≠ v → C₁ x = C x := by
        intro x hxr hxv
        dsimp [C₁, P]
        simp [Config.step, hrv, hxr, hxv]
      have hAllAns1 : ∀ w : Fin n, (C₁ w).1.role = .Resetting →
          (C₁ w).1.answer = majorityAnswer C₁ := by
        intro w hwres
        by_cases hwr : w = r
        · subst hwr; exact hC1_r_ans
        · by_cases hwv : w = v
          · subst hwv; exact hC1_v_ans
          · have hwx : C₁ w = C w := hothers w hwr hwv
            rw [hwx] at hwres ⊢
            rw [h_maj]
            exact hAllAns w hwres
      obtain ⟨L, hLrole, hLans⟩ := ih C₁ hN1 hSeed1 hAllAns1
      refine ⟨(r, v) :: L, ?_, ?_⟩
      · intro w
        simp only [runPairs_cons]
        exact hLrole w
      · intro w
        simp only [runPairs_cons]
        rw [hLans w, h_maj]

/-- **Partial → KnownRankingEntry.** From any configuration with both
Resetting and non-Resetting agents, drive the protocol to a configuration
satisfying one of the six `KnownRankingEntry` disjuncts.

Proof strategy: strong recursion on `resetFuel`. Dispatch on the chosen
Resetting agent's `leader/resetcount`. Fuel-decrease lemmas
(`dormant_follower_step_resetFuel_lt_tau (τ := τ)`, `propagate_reset_step_resetFuel_lt_tau (τ := τ)`,
`dormant_leader_nonresetting_step_resetFuel_lt_or_seed_tau (τ := τ)`) close the bulk of
cases; the seed case escapes the fuel induction by calling
`all_resetting_from_seed_aux_tau (τ := τ)` to drive to all-R (disjunct 6). -/
theorem partial_resetting_to_known_entry_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSomeReset : ∃ r : Fin n, (C r).1.role = .Resetting)
    (hNotAllReset : ¬ ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ L : List (Fin n × Fin n),
      KnownRankingEntry
        (runPairs
          (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn))
          C L) := by
  classical
  have hDmax_pos : 1 < Dmax := by omega
  -- Strong recursion on `resetFuel`.
  suffices h_aux : ∀ k : ℕ, ∀ C' : Config (AgentState n) Opinion n,
      resetFuel C' ≤ k →
      (∃ r : Fin n, (C' r).1.role = .Resetting) →
      (¬ ∀ w : Fin n, (C' w).1.role = .Resetting) →
      ∃ L : List (Fin n × Fin n),
        KnownRankingEntry
          (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C' L) by
    exact h_aux (resetFuel C) C le_rfl hSomeReset hNotAllReset
  intro k
  induction k with
  | zero =>
    intro C' hF hSome _hNot
    -- resetFuel = 0 contradicts the existence of a Resetting agent.
    obtain ⟨r, hr⟩ := hSome
    have hcontrib_pos : 0 < resetFuelContribution (C' r).1 := by
      unfold resetFuelContribution
      rw [if_pos hr]
      exact Nat.pow_pos (by decide : (0:ℕ) < 2)
    have hsum_pos :
        0 < ∑ w : Fin n, resetFuelContribution (C' w).1 := by
      refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ?_
      exact ⟨r, Finset.mem_univ r, hcontrib_pos⟩
    have hf_pos : 0 < resetFuel C' := by
      unfold resetFuel; omega
    omega
  | succ k ih =>
    intro C' hF hSome hNot
    obtain ⟨r, hr_res⟩ := hSome
    push_neg at hNot
    obtain ⟨v, hv_not⟩ := hNot
    have hrv : r ≠ v := fun heq => by subst heq; exact hv_not hr_res
    -- Helper: after taking a step that drops fuel, dispatch on whether the
    -- result is all-R, all-non-R, or still partial.
    set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP_def
    -- We always interact at pair (r, v); the proof obligation reduces to
    -- showing fuel drops and then recursing (or producing a seed witness).
    let C₁ := C'.step P r v
    have dispatch_after_step :
        resetFuel C₁ < resetFuel C' →
        ∃ L : List (Fin n × Fin n),
          KnownRankingEntry (runPairs P C₁ L) := by
      intro h_dec
      have hF1 : resetFuel C₁ ≤ k := by omega
      by_cases hAllRes : ∀ w, (C₁ w).1.role = .Resetting
      · exact ⟨[], by simpa using KnownRankingEntry.of_all_resetting hAllRes⟩
      · by_cases hNoRes : ∀ w, (C₁ w).1.role ≠ .Resetting
        · exact ⟨[], by simpa using KnownRankingEntry.of_no_reset hNoRes⟩
        · have hSomeC1 : ∃ r' : Fin n, (C₁ r').1.role = .Resetting := by
            push_neg at hNoRes; exact hNoRes
          exact ih C₁ hF1 hSomeC1 hAllRes
    -- Dispatch on r's leader/resetcount to obtain a fuel drop (or a seed).
    by_cases hr_rc : (C' r).1.resetcount = 0
    · -- rc = 0; dispatch on leader.
      cases hr_leader : (C' r).1.leader with
      | F =>
        have h_dec :=
          dormant_follower_step_resetFuel_lt_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hrv hr_res hr_rc hr_leader hv_not
        have h_dec' : resetFuel C₁ < resetFuel C' := by simpa [C₁, P] using h_dec
        obtain ⟨L, hL⟩ := dispatch_after_step h_dec'
        exact ⟨(r, v) :: L, by simpa [runPairs_cons] using hL⟩
      | L =>
        rcases
          dormant_leader_nonresetting_step_resetFuel_lt_or_seed_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hrv hr_res hr_rc hr_leader hv_not
          with h_dec | ⟨r_seed, hseed_res, hseed_rc, _hseed_L⟩
        · have h_dec' : resetFuel C₁ < resetFuel C' := by simpa [C₁, P] using h_dec
          obtain ⟨L, hL⟩ := dispatch_after_step h_dec'
          exact ⟨(r, v) :: L, by simpa [runPairs_cons] using hL⟩
        · -- Bounce case: seed witness in C₁.
          have hC1_seed_res : (C₁ r_seed).1.role = .Resetting := by
            simpa [C₁, P] using hseed_res
          have hC1_seed_rc : (C₁ r_seed).1.resetcount = Rmax := by
            simpa [C₁, P] using hseed_rc
          have hN_bound : nonResettingCount C₁ ≤ Rmax := by
            unfold nonResettingCount
            calc (Finset.univ.filter
                    (fun w : Fin n => (C₁ w).1.role ≠ .Resetting)).card
                ≤ (Finset.univ : Finset (Fin n)).card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
              _ = n := by simp
              _ ≤ Rmax := hRmax
          have hSeed' :
              ∃ r' : Fin n, (C₁ r').1.role = .Resetting ∧
                  nonResettingCount C₁ ≤ (C₁ r').1.resetcount :=
            ⟨r_seed, hC1_seed_res, hC1_seed_rc ▸ hN_bound⟩
          obtain ⟨L, hL⟩ :=
            all_resetting_from_seed_aux_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos (nonResettingCount C₁) C₁ le_rfl hSeed'
          refine ⟨(r, v) :: L, ?_⟩
          simp only [runPairs_cons]
          exact KnownRankingEntry.of_all_resetting hL
    · -- rc > 0; propagate-reset.
      have hr_rc_pos : 0 < (C' r).1.resetcount := Nat.pos_of_ne_zero hr_rc
      have h_dec :=
        propagate_reset_step_resetFuel_lt_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax_pos
          C' hrv hr_res hr_rc_pos hv_not
      have h_dec' : resetFuel C₁ < resetFuel C' := by simpa [C₁, P] using h_dec
      obtain ⟨L, hL⟩ := dispatch_after_step h_dec'
      exact ⟨(r, v) :: L, by simpa [runPairs_cons] using hL⟩

/-- **Reset normalizer.** Given any configuration with at least one
Resetting agent, drive the protocol to one of the six `KnownRankingEntry`
cases. -/
theorem resetting_exists_to_known_entry_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting) :
    ∃ L : List (Fin n × Fin n),
      KnownRankingEntry
        (runPairs
          (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn))
          C L) := by
  classical
  by_cases hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting
  · exact ⟨[], KnownRankingEntry.of_all_resetting (by simpa using hAllReset)⟩
  · exact
      partial_resetting_to_known_entry_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn4 hEmax hDmax hRmax
        C hReset hAllReset

/-- From any configuration, reach either `InSrank` or one of the known
ranking-entry cases. -/
theorem reach_known_entry_from_any_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C₀ : Config (AgentState n) Opinion n) :
    ∃ L : List (Fin n × Fin n),
      InSrank
        (runPairs
          (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C₀ L) ∨
      KnownRankingEntry
        (runPairs
          (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C₀ L) := by
  classical
  obtain ⟨L₁, h₁⟩ :=
    phase1_trigger_reset_or_InSrank_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hn4 hEmax hDmax C₀
  rcases h₁ with hSrank | hReset
  · exact ⟨L₁, Or.inl hSrank⟩
  · obtain ⟨L₂, hEntry⟩ :=
      resetting_exists_to_known_entry_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn4 hEmax hDmax hRmax _ hReset
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    exact Or.inr hEntry

/-- The ranking field of `BurmanConvergence` as a standalone theorem. -/
theorem ranking_field_proof_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C₀ : Config (AgentState n) Opinion n) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank
        (execution
          (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C₀ γ t) ∧
      ((∀ μ : Fin n,
        (execution
          (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤
          (execution
            (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            C₀ γ t μ).1.timer) ∨
       IsConsensusConfig
        (execution
          (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C₀ γ t)) := by
  classical
  obtain ⟨L, h⟩ :=
    reach_known_entry_from_any_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hn4 hEmax hDmax hRmax C₀
  rcases h with hSrank | hEntry
  · exact
      exists_schedule_after_runPairs
        (Goal := fun C =>
          InSrank C ∧
            ((∀ μ : Fin n,
              (C μ).1.rank.val + 1 = ceilHalf n →
              2 ≤ (C μ).1.timer) ∨
             IsConsensusConfig C))
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C₀ L
        (ranking_from_InSrank_by_parity_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) hn4 hDmax hRmax _ hSrank)
  · -- `KnownRankingEntry C` unfolds to the same 6-way disjunction expected by
    -- `ranking_from_known_reset_entry_or_all_resetting_zero_tau`.
    exact
      exists_schedule_after_runPairs
        (Goal := fun C =>
          InSrank C ∧
            ((∀ μ : Fin n,
              (C μ).1.rank.val + 1 = ceilHalf n →
              2 ≤ (C μ).1.timer) ∨
             IsConsensusConfig C))
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C₀ L
        (ranking_from_known_reset_entry_or_all_resetting_zero_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) hn4 hEmax hDmax hRmax _ hEntry)

private theorem majorityCountOfAnswerBCF_step_eq_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m : Answer} (hMajOut : m = .outA ∨ m = .outB)
    (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    majorityCountOfAnswerBCF
        (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) m =
      majorityCountOfAnswerBCF C m := by
  rcases hMajOut with rfl | rfl
  · exact nAOf_step_eq C u v
  · exact nBOf_step_eq C u v

private theorem settledCount_of_heapPrefix_BCF
    {C : Config (AgentState n) Opinion n} {k : ℕ}
    (hHeap : HeapPrefix C k) :
    settledCount C = k := by
  classical
  rcases hHeap with ⟨_hkn, hRankLt, hUnique, _hRoles, _hChildren⟩
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun w : Fin n => (C w).1.role == Role.Settled)
  have hmem_settled : ∀ w : {w : Fin n // w ∈ S}, (C w.1).1.role = .Settled := by
    intro w
    simpa [S, beq_iff_eq] using w.2
  let rankOnSettled : {w : Fin n // w ∈ S} → Fin k :=
    fun w => ⟨(C w.1).1.rank.val, hRankLt w.1 (hmem_settled w)⟩
  have hBij : Function.Bijective rankOnSettled := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hxS : (C x.1).1.role = .Settled := hmem_settled x
      have hyS : (C y.1).1.role = .Settled := hmem_settled y
      have hrank_val : (C x.1).1.rank.val = (C y.1).1.rank.val := by
        simpa [rankOnSettled] using congrArg Fin.val hxy
      obtain ⟨z, _hz, hz_unique⟩ :=
        hUnique (C x.1).1.rank.val (hRankLt x.1 hxS)
      have hxz : x.1 = z := hz_unique x.1 ⟨hxS, rfl⟩
      have hyz : y.1 = z := hz_unique y.1 ⟨hyS, hrank_val.symm⟩
      exact hxz.trans hyz.symm
    · intro r
      obtain ⟨w, hw, _hw_unique⟩ := hUnique r.val r.isLt
      refine ⟨⟨w, ?_⟩, ?_⟩
      · simpa [S, beq_iff_eq] using hw.1
      · apply Fin.ext
        simp [rankOnSettled, hw.2]
  have hCardSubtype :
      Fintype.card {w : Fin n // w ∈ S} = Fintype.card (Fin k) :=
    Fintype.card_congr (Equiv.ofBijective rankOnSettled hBij)
  have hCardS : S.card = k := by
    have hSubtypeCard : Fintype.card {w : Fin n // w ∈ S} = S.card := by
      simpa using (Finset.card_attach S)
    rw [← hSubtypeCard]
    simpa using hCardSubtype
  simpa [settledCount, S] using hCardS

private theorem ceilHalf_le_majorityCountOfAnswerBCF_of_majorityAnswer
    {C : Config (AgentState n) Opinion n} {m : Answer}
    (hm : m = majorityAnswer C)
    (hMajOut : m = .outA ∨ m = .outB) :
    ceilHalf n ≤ majorityCountOfAnswerBCF C m := by
  rcases hMajOut with rfl | rfl
  · unfold majorityAnswer at hm
    by_cases hAB : nAOf C > nBOf C
    · have hsum := nAOf_add_nBOf C
      simp [majorityCountOfAnswerBCF]
      unfold ceilHalf
      omega
    · simp [hAB] at hm
      by_cases hBA : nBOf C > nAOf C <;> simp [hBA] at hm
  · unfold majorityAnswer at hm
    by_cases hAB : nAOf C > nBOf C
    · simp [hAB] at hm
    · simp [hAB] at hm
      by_cases hBA : nBOf C > nAOf C
      · have hsum := nAOf_add_nBOf C
        simp [hBA, majorityCountOfAnswerBCF]
        unfold ceilHalf
        omega
      · simp [hBA] at hm

/-- **One `Config.step` preserves the reservoir invariant** when the
scheduled pair is not both-`Settled` at the `rankDelta` output (so Phase 4
is the identity and the only answer writes are the phi-wipe and the
phi-spread, both of which keep every answer in `{m, .phi}`). -/
theorem step_preserves_ResAns_of_not_both_settled_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n} {a b : Fin n}
    (hRes : ResAns m C)
    (h_not_both_settled :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).1.role = .Settled ∧
         (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).2.role = .Settled)) :
    ResAns m
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) a b) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  by_cases hab : a = b
  · subst hab
    intro w
    have : (C.step P a a) = C := by
      funext z; simp [Config.step]
    rw [this]; exact hRes w
  -- rankDelta preserves answers, so both rankDelta outputs are in {m, phi}.
  have h_rd_ans :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) (C a).1 (C b).1
  have hrd0 : (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).1.answer = m ∨
      (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).1.answer = .phi := by
    rw [h_rd_ans.1]; exact hRes a
  have hrd1 : (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).2.answer = m ∨
      (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).2.answer = .phi := by
    rw [h_rd_ans.2]; exact hRes b
  -- prePhase4 keeps both endpoint answers in {m, phi}.
  have h_pre :=
    transitionPEM_prePhase4_resAns
      (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C a).1) (s₁ := (C b).1) (x₀ := (C a).2) (x₁ := (C b).2)
      hrd0 hrd1
  -- Phase 4 is identity since prePhase4 output is not both-Settled.
  have h_pre_not_settled :
      ¬ ((transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C a).1 (C b).1 (C a).2 (C b).2).1.role = .Settled ∧
          (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C a).1 (C b).1 (C a).2 (C b).2).2.role = .Settled) := by
    have hstruct := transitionPEM_prePhase4_structural
      (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C a).1) (s₁ := (C b).1) (x₀ := (C a).2) (x₁ := (C b).2)
    rw [hstruct.1, hstruct.2.2.2.2.2.2.1]
    exact h_not_both_settled
  have h_delta :
      ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C a).1, (C a).2), ((C b).1, (C b).2))).1.answer = m ∨
       (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C a).1, (C a).2), ((C b).1, (C b).2))).1.answer = .phi) ∧
      ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C a).1, (C a).2), ((C b).1, (C b).2))).2.answer = m ∨
       (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C a).1, (C a).2), ((C b).1, (C b).2))).2.answer = .phi) := by
    rw [transitionPEM_eq, transitionPEM_phase4_of_not_both_settled h_pre_not_settled]
    exact h_pre
  intro w
  by_cases hwa : w = a
  · subst hwa
    rw [Config.step_fst_state P C hab]
    show (P.δ (C w, C b)).1.answer = m ∨ (P.δ (C w, C b)).1.answer = .phi
    simp only [hP, protocolPEM]; exact h_delta.1
  · by_cases hwb : w = b
    · subst hwb
      rw [Config.step_snd_state P C hab (fun h => hab h.symm)]
      show (P.δ (C a, C w)).2.answer = m ∨ (P.δ (C a, C w)).2.answer = .phi
      simp only [hP, protocolPEM]; exact h_delta.2
    · have : (C.step P a b) w = C w := by
        simp [Config.step, hab, hwa, hwb]
      rw [this]; exact hRes w

/-- `majorityAnswer` is invariant under `runPairs` (every `Config.step`
preserves it via `majorityAnswer_step_eq`). -/
theorem majorityAnswer_runPairs_eq_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) (L : List (Fin n × Fin n)) :
    majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  induction L generalizing C with
  | nil => simp
  | cons ij L ih =>
    rw [runPairs_cons, ih]
    exact majorityAnswer_step_eq C ij.1 ij.2

/-- **All-`Resetting` + all-correct, normalized.**  From all-`Resetting`
with every answer `= majorityAnswer C`, there is a `runPairs` prefix after
which every agent is `Resetting` *and* every answer equals
`majorityAnswer` of the new configuration. -/
theorem all_resetting_correct_normalize_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.role = .Resetting) ∧
      (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer
          = majorityAnswer C) := by
  classical
  -- `nonResettingCount C = 0` because every agent is `Resetting`.
  have hN0 : nonResettingCount C = 0 := by
    unfold nonResettingCount
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro w _
    simp only [not_not]
    exact hAllR w
  -- Pick any agent as the (vacuous) seed.
  have hn_pos : 0 < n := hn
  obtain ⟨r⟩ : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hseed :
      ∃ r : Fin n,
        (C r).1.role = .Resetting ∧
        nonResettingCount C ≤ (C r).1.resetcount ∧
        (C r).1.answer = majorityAnswer C :=
    ⟨r, hAllR r, by rw [hN0]; exact Nat.zero_le _, hAllCorrect r⟩
  have hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C := fun w _ => hAllCorrect w
  exact
    all_resetting_from_seed_answer_aux_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hDmax
      (nonResettingCount C) C le_rfl hseed hAllAns

/-- **All-`Resetting` + all-correct, normalized to all-`m`, with the
reservoir already stabilized.**  Strengthens `all_resetting_correct_normalize_tau (τ := τ)`
with the explicit `ResAns m` and no-`.phi` facts at the normalized config
(both immediate from "every answer equals `majorityAnswer`").  Unconditional. -/
theorem all_resetting_correct_normalize_resAns_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.role = .Resetting) ∧
      (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer
          = majorityAnswer C) ∧
      ResAns (majorityAnswer C)
        (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer ≠ .phi) := by
  obtain ⟨L, hL_role, hL_ans⟩ :=
    all_resetting_correct_normalize_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hAllR hAllCorrect
  refine ⟨L, hL_role, hL_ans, ?_, ?_⟩
  · intro w; exact Or.inl (hL_ans w)
  · intro w
    rw [hL_ans w]
    exact majorityAnswer_ne_phi C

/-- **Cycle macro-step driver, instantiated at the reservoir potential.**

This is `reach_zero_potential_macro` specialised to the concrete protocol,
the reservoir-paired invariant
`Pinv C := InSswap C ∧ ResAns (majorityAnswer C) C`, and the cycle
potential `phiCount`.  Given a macro-step that, from any such
non-`phiCount`-zero configuration, reaches another one with strictly
smaller `phiCount`, a finite deterministic schedule reaches a
`phiCount = 0` configuration — which is then a consensus by
`isConsensusConfig_of_InSswap_phiCount_zero`.  Unconditional,
sorry/axiom-free; this is the strong-recursion-on-potential skeleton the
cycle-termination proof plugs into (mirroring how
`partial_resetting_to_known_entry_tau (τ := τ)` plugs into `resetFuel`). -/
theorem cycle_potential_reaches_consensus_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hMacro :
      ∀ C : Config (AgentState n) Opinion n,
        (InSswap C ∧ ResAns (majorityAnswer C) C) → 0 < phiCount C →
        ∃ (γ : DetScheduler n) (k : ℕ),
          (InSswap (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) ∧
            ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k))
              (execution (protocolPEM n τ Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k)) ∧
          phiCount (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) < phiCount C) :
    ∀ C : Config (AgentState n) Opinion n,
      InSswap C → ResAns (majorityAnswer C) C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig
          (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) := by
  intro C hSswap hRes
  obtain ⟨γ, t, ⟨hSswap_t, hRes_t⟩, h0_t⟩ :=
    reach_zero_potential_macro
      (P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (Pinv := fun C => InSswap C ∧ ResAns (majorityAnswer C) C)
      (φ := phiCount) hMacro C ⟨hSswap, hRes⟩
  exact ⟨γ, t, isConsensusConfig_of_InSswap_phiCount_zero
    hSswap_t hRes_t h0_t⟩

/-- **The non-circular median-wrong decision macro-step.**

From an `InSswap` configuration with a live median timer
(`1 ≤ timer @ median`) and *some* median agent whose answer is wrong, a
single decision step at a chosen non-`.Resetting`-introducing pair strictly
decreases `wrongAnswerCount` while preserving both `InSswap` and the
median-timer bound.  This is **exactly** the non-circular witness pattern
of `P_EM_solves_SSEM_from_BurmanConvergence_only`'s `hDrive` recursion
(`evenCase_witness_when_median_wrong{,_tie}` /
`oddCase_witness_when_median_wrong_with_timer` +
`decision_step_at_median_*_decreases` + `step_preserves_timer_no_max`),
packaged as a reusable single-step macro.  It uses **no** epidemic /
Burman / answer-stability / circular hypothesis.  The median-*correct*
case is intentionally excluded (it is handled separately, under the
reservoir invariant, by the trigger-reset renormalizer). -/
theorem median_wrong_decision_step_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hC_timer : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                 (C μ).1.answer ≠ majorityAnswer C) :
    ∃ p : Fin n × Fin n,
      InSswap (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ∧
      (∀ μ : Fin n,
        (C.step (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2 μ).1.rank.val + 1
            = ceilHalf n →
        1 ≤ (C.step (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2 μ).1.timer) ∧
      wrongAnswerCount (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) < wrongAnswerCount C := by
  classical
  obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
  by_cases hpar : n % 2 = 0
  · by_cases hTie : nAOf C = nBOf C
    · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
        evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie
          ⟨μ, hμ_med, hμ_wrong⟩
      have h_dec := decision_step_at_median_pair_even_tie_decreases
        (n := n) (trank := τ) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn))
        hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
      have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
      have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
      exact ⟨(u, v),
        h_dec.1,
        step_preserves_timer_no_max
          (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
            (Dmax := Dmax) (hn := hn))
          hC.toInSrank huv hu_no_max hv_no_max hC_timer,
        h_dec.2⟩
    · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
        evenCase_witness_when_median_wrong hC hpar hn4 hTie
          ⟨μ, hμ_med, hμ_wrong⟩
      have h_dec := decision_step_at_median_pair_even_decreases
        (trank := τ) (Rmax := Rmax)
        (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn))
        hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
      have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
      have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
      exact ⟨(u, v),
        h_dec.1,
        step_preserves_timer_no_max
          (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
            (Dmax := Dmax) (hn := hn))
          hC.toInSrank huv hu_no_max hv_no_max hC_timer,
        h_dec.2⟩
  · obtain ⟨μ', v, hμv, hμ'_med, hv_no_med, hv_no_max, h_rank_gt,
      h_timer, hμ'_wrong⟩ :=
      oddCase_witness_when_median_wrong_with_timer hC hpar
        (by omega : 3 ≤ n) ⟨μ, hμ_med, hμ_wrong⟩ hC_timer
    have h_step := decision_step_at_median_no_swap_odd_decreases
      (trank := τ) (Rmax := Rmax)
      (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn))
      hC hμv hpar hμ'_med hv_no_med hv_no_max h_rank_gt h_timer hμ'_wrong
    have hμ'_no_max : (C μ').1.rank.val + 1 ≠ n := by
      unfold ceilHalf at hμ'_med; omega
    exact ⟨(μ', v),
      h_step.1,
      step_preserves_timer_no_max
        (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn))
        hC.toInSrank hμv hμ'_no_max hv_no_max hC_timer,
      h_step.2⟩

/-- **Median-wrong decision drive to consensus.**

From an `InSswap` configuration with a live median timer, *iterating*
`median_wrong_decision_step_tau (τ := τ)` strictly decreases `wrongAnswerCount` whenever
the median is wrong; combined with the early exit on
`wrongAnswerCount = 0` (`isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero`)
and the epidemic-free median-*correct* exit *under the reservoir
invariant* (median correct + reservoir ⇒ a `.phi` non-median is a genuine
mismatch with the m₀ median, which the trigger-reset renormalizer
absorbs), this is the strong-recursion engine.  Here we package the
purely-non-circular sub-engine: **as long as the median stays wrong**, a
finite schedule drives `wrongAnswerCount` to `0`, i.e. to consensus.
Unconditional, non-circular. -/
theorem median_wrong_only_drive_to_consensus_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) :
    ∀ (b : ℕ) (C : Config (AgentState n) Opinion n),
      InSswap C →
      (∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer) →
      wrongAnswerCount C ≤ b →
      ((∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n,
          InSswap D →
          (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (D μ).1.timer) →
          0 < wrongAnswerCount D →
          (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
            (D μ).1.answer = majorityAnswer D) →
          wrongAnswerCount D ≤ k →
          ∃ (γ : DetScheduler n) (t : ℕ),
            IsConsensusConfig (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t))) →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  intro b
  induction b with
  | zero =>
    intro C hC _htimer hle _hMedCorrectExit
    have hzero : wrongAnswerCount C = 0 := Nat.le_zero.mp hle
    exact ⟨fun _ => default, 0,
      isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC hzero⟩
  | succ b ih =>
    intro C hC htimer hle hMedCorrectExit
    by_cases hpos : 0 < wrongAnswerCount C
    · by_cases h_med_correct :
          ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                       (C μ).1.answer = majorityAnswer C
      · -- Median correct: hand off to the supplied (reservoir-based,
        -- non-circular) median-correct exit.
        exact hMedCorrectExit (wrongAnswerCount C) C hC htimer hpos
          h_med_correct le_rfl
      · -- Median wrong: one non-circular decision step, then recurse.
        push_neg at h_med_correct
        obtain ⟨p, hC', htimer', hdec⟩ :=
          median_wrong_decision_step_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hC htimer h_med_correct
        have hle' : wrongAnswerCount (C.step P p.1 p.2) ≤ b := by
          simp only [hP] at hdec ⊢; omega
        obtain ⟨γ', t', hcons⟩ :=
          ih (C.step P p.1 p.2)
            (by simpa [hP] using hC')
            (by simpa [hP] using htimer')
            hle' hMedCorrectExit
        refine ⟨concatScheduler (fun _ => p) 1 γ', 1 + t', ?_⟩
        have hone : execution P C (fun _ => p) 1 = C.step P p.1 p.2 := rfl
        rw [execution_concat, hone]; exact hcons
    · push_neg at hpos
      have hzero : wrongAnswerCount C = 0 := Nat.le_zero.mp hpos
      exact ⟨fun _ => default, 0,
        isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC hzero⟩

/-- **Pair-level reservoir safety.**  After the concrete `transitionPEM`
step at the pair `(C u, C v)`, both endpoint answers remain in the
reservoir set `{m₀, .phi}`.  This is the per-pair decision-safety witness
threaded through the explicit schedule. -/
def PairResAnsSafe_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (m₀ : Answer)
    (C : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  let out :=
    transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (((C u).1, (C u).2), ((C v).1, (C v).2))
  AnswerInResAns m₀ out.1.answer ∧
  AnswerInResAns m₀ out.2.answer

/-- Pair-level no-`.phi` safety.  This is deliberately separate from
`PairResAnsSafe_tau (τ := τ)`: `ResAns` allows `.phi`, while the re-entry endpoint needs
to preserve its absence. -/
def PairNoPhiSafe_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (u v : Fin n) : Prop :=
  let out :=
    transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (((C u).1, (C u).2), ((C v).1, (C v).2))
  out.1.answer ≠ .phi ∧ out.2.answer ≠ .phi

private lemma phase4_nonmedian_answer_eq_BCF
    {Rmax : ℕ} {a₀ a₁ : AgentState n} {x₀ x₁ : Opinion}
    (hodd : ¬ n % 2 = 0)
    (ha₀ : a₀.role = .Settled) (ha₁ : a₁.role = .Settled)
    (hr₀ : a₀.rank.val + 1 ≠ ceilHalf n)
    (hr₁ : a₁.rank.val + 1 ≠ ceilHalf n) :
    let out := transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁
    (out.1.answer = a₀.answer ∨ out.1.answer = a₁.answer) ∧
    (out.2.answer = a₀.answer ∨ out.2.answer = a₁.answer) := by
  unfold transitionPEM_phase4
  dsimp only []
  rw [if_pos ⟨ha₀, ha₁⟩]
  have hdec : ∀ b₀ b₁ : AgentState n,
      b₀.rank.val + 1 ≠ ceilHalf n → b₁.rank.val + 1 ≠ ceilHalf n →
      phase4_decide n b₀ b₁ x₀ x₁ = (b₀, b₁) := by
    intro b₀ b₁ hb₀ hb₁
    unfold phase4_decide
    rw [if_neg hodd, if_neg hb₀, if_neg hb₁]
  have hprop : ∀ b₀ b₁ : AgentState n,
      b₀.rank.val + 1 ≠ ceilHalf n → b₁.rank.val + 1 ≠ ceilHalf n →
      (phase4_propagate n Rmax b₀ b₁).1.answer = b₀.answer ∧
      (phase4_propagate n Rmax b₀ b₁).2.answer = b₁.answer := by
    intro b₀ b₁ hb₀ hb₁
    unfold phase4_propagate
    rw [if_neg hb₀, if_neg hb₁]
    exact ⟨rfl, rfl⟩
  unfold phase4_swap
  by_cases hsw : a₀.rank < a₁.rank ∧ x₀ = Opinion.B ∧ x₁ = Opinion.A
  · rw [if_pos hsw, hdec a₁ a₀ hr₁ hr₀]
    obtain ⟨h1, h2⟩ := hprop a₁ a₀ hr₁ hr₀
    exact ⟨Or.inr h1, Or.inl h2⟩
  · rw [if_neg hsw, hdec a₀ a₁ hr₀ hr₁]
    obtain ⟨h1, h2⟩ := hprop a₀ a₁ hr₀ hr₁
    exact ⟨Or.inl h1, Or.inr h2⟩



private theorem even_recruit_not_median_pair_BCF
    {p_rank children : ℕ}
    (hn4 : 4 ≤ n)
    (hchildren : children < 2)
    (_hvalid : 2 * p_rank + children + 1 < n)
    (heven : n % 2 = 0) :
    ¬ (p_rank + 1 = n / 2 ∧ (2 * p_rank + children + 1) + 1 = n / 2 + 1) ∧
    ¬ ((2 * p_rank + children + 1) + 1 = n / 2 ∧ p_rank + 1 = n / 2 + 1) := by
  have hndvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
  have hn2 : n / 2 * 2 = n := Nat.div_mul_cancel hndvd
  constructor
  · intro h
    rcases h with ⟨hp, ht⟩
    have hn2' : 2 * (n / 2) = n := by omega
    omega
  · intro h
    rcases h with ⟨ht, hp⟩
    have hn2' : 2 * (n / 2) = n := by omega
    omega



private theorem phase4_decide_identity_even_pair_BCF
    {b₀ b₁ : AgentState n} {x₀ x₁ : Opinion}
    (heven : n % 2 = 0)
    (hnot01 : ¬ (b₀.rank.val + 1 = n / 2 ∧ b₁.rank.val + 1 = n / 2 + 1))
    (hnot10 : ¬ (b₁.rank.val + 1 = n / 2 ∧ b₀.rank.val + 1 = n / 2 + 1)) :
    phase4_decide n b₀ b₁ x₀ x₁ = (b₀, b₁) := by
  unfold phase4_decide
  rw [if_pos heven, if_neg hnot01, if_neg hnot10]


private theorem phase4_propagate_preserves_PairResAns_BCF
    {Rmax : ℕ}
    {b₀ b₁ : AgentState n} {m₀ : Answer}
    (h₀ : AnswerInResAns m₀ b₀.answer)
    (h₁ : AnswerInResAns m₀ b₁.answer) :
    AnswerInResAns m₀ (phase4_propagate n Rmax b₀ b₁).1.answer ∧
    AnswerInResAns m₀ (phase4_propagate n Rmax b₀ b₁).2.answer := by
  unfold phase4_propagate AnswerInResAns at *
  repeat split_ifs <;> simp_all


private theorem phase4_propagate_preserves_noPhi_BCF
    {Rmax : ℕ}
    {b₀ b₁ : AgentState n}
    (h₀ : b₀.answer ≠ .phi)
    (h₁ : b₁.answer ≠ .phi) :
    (phase4_propagate n Rmax b₀ b₁).1.answer ≠ .phi ∧
    (phase4_propagate n Rmax b₀ b₁).2.answer ≠ .phi := by
  unfold phase4_propagate at *
  repeat split_ifs <;> simp_all


private theorem valid_parent_not_at_median_odd_BCF
    (hodd : ¬ n % 2 = 0)
    {rank children : ℕ}
    (hch : children < 2)
    (hvalid : 2 * rank + children + 1 < n) :
    rank + 1 ≠ ceilHalf n := by
  unfold ceilHalf
  omega

set_option maxHeartbeats 4000000 in
theorem odd_nonmedian_recruit_ba_PairResAnsSafe_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    {D : Config (AgentState n) Opinion n}
    {child p : Fin n}
    (hodd : ¬ n % 2 = 0)
    (hRes : ResAns m₀ D)
    (hc : (D child).1.role = .Unsettled)
    (hp : (D p).1.role = .Settled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n)
    (hnonmed :
      2 * (D p).1.rank.val + (D p).1.children + 1 + 1 ≠ ceilHalf n) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D child p := by
  set pre := transitionPEM_prePhase4 n τ
    (rankDeltaOSSR Rmax Emax Dmax hn)
    (D child).1 (D p).1 (D child).2 (D p).2
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn)
      (a := (D child).1) (b := (D p).1)
      hc hp hchildren hvalid
  have hpre_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D child).1) (s₁ := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
  have hpre_ans := prePhase4_recruit_ba_answer_preserved_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := (D child).1) (b := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hc hp hchildren hvalid
  have hpre0_role : pre.1.role = .Settled := by
    simpa [pre, hrd] using hpre_struct.1
  have hpre1_role : pre.2.role = .Settled := by
    simpa [pre, hrd, hp] using hpre_struct.2.2.2.2.2.2.1
  have hpre0_rank : pre.1.rank.val =
      2 * (D p).1.rank.val + (D p).1.children + 1 := by
    have h : pre.1.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).1.rank :=
      hpre_struct.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre1_rank : pre.2.rank.val = (D p).1.rank.val := by
    have h : pre.2.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).2.rank :=
      hpre_struct.2.2.2.2.2.2.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre0_not_med : pre.1.rank.val + 1 ≠ ceilHalf n := by
    rw [hpre0_rank]
    exact hnonmed
  have hpre1_not_med : pre.2.rank.val + 1 ≠ ceilHalf n := by
    rw [hpre1_rank]
    exact valid_parent_not_at_median_odd_BCF hodd hchildren hvalid
  unfold PairResAnsSafe_tau AnswerInResAns
  simp only [transitionPEM_eq]
  change AnswerInResAns m₀
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).1.answer ∧
    AnswerInResAns m₀
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).2.answer
  unfold AnswerInResAns
  obtain ⟨h1, h2⟩ := phase4_nonmedian_answer_eq_BCF
    (n := n) (Rmax := Rmax) (a₀ := pre.1) (a₁ := pre.2)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hodd hpre0_role hpre1_role hpre0_not_med hpre1_not_med
  constructor
  · rcases h1 with h | h <;> rw [h]
    · rw [hpre_ans.1]; exact hRes child
    · rw [hpre_ans.2]; exact hRes p
  · rcases h2 with h | h <;> rw [h]
    · rw [hpre_ans.1]; exact hRes child
    · rw [hpre_ans.2]; exact hRes p

theorem odd_nonmedian_recruit_ba_PairNoPhiSafe_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {child p : Fin n}
    (hodd : ¬ n % 2 = 0)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hc : (D child).1.role = .Unsettled)
    (hp : (D p).1.role = .Settled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n)
    (hnonmed :
      2 * (D p).1.rank.val + (D p).1.children + 1 + 1 ≠ ceilHalf n) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D child p := by
  set pre := transitionPEM_prePhase4 n τ
    (rankDeltaOSSR Rmax Emax Dmax hn)
    (D child).1 (D p).1 (D child).2 (D p).2
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn)
      (a := (D child).1) (b := (D p).1)
      hc hp hchildren hvalid
  have hpre_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D child).1) (s₁ := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
  have hpre_ans := prePhase4_recruit_ba_answer_preserved_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := (D child).1) (b := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hc hp hchildren hvalid
  have hpre0_role : pre.1.role = .Settled := by
    simpa [pre, hrd] using hpre_struct.1
  have hpre1_role : pre.2.role = .Settled := by
    simpa [pre, hrd, hp] using hpre_struct.2.2.2.2.2.2.1
  have hpre0_rank : pre.1.rank.val =
      2 * (D p).1.rank.val + (D p).1.children + 1 := by
    have h : pre.1.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).1.rank :=
      hpre_struct.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre1_rank : pre.2.rank.val = (D p).1.rank.val := by
    have h : pre.2.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).2.rank :=
      hpre_struct.2.2.2.2.2.2.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre0_not_med : pre.1.rank.val + 1 ≠ ceilHalf n := by
    rw [hpre0_rank]
    exact hnonmed
  have hpre1_not_med : pre.2.rank.val + 1 ≠ ceilHalf n := by
    rw [hpre1_rank]
    exact valid_parent_not_at_median_odd_BCF hodd hchildren hvalid
  unfold PairNoPhiSafe_tau
  simp only [transitionPEM_eq]
  change
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).1.answer ≠ .phi ∧
    (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).2.answer ≠ .phi
  obtain ⟨h1, h2⟩ := phase4_nonmedian_answer_eq_BCF
    (n := n) (Rmax := Rmax) (a₀ := pre.1) (a₁ := pre.2)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hodd hpre0_role hpre1_role hpre0_not_med hpre1_not_med
  constructor
  · rcases h1 with h | h <;> rw [h]
    · rw [hpre_ans.1]; exact hNoPhi child
    · rw [hpre_ans.2]; exact hNoPhi p
  · rcases h2 with h | h <;> rw [h]
    · rw [hpre_ans.1]; exact hNoPhi child
    · rw [hpre_ans.2]; exact hNoPhi p

/-- **A `Config.step` whose pair is `PairResAnsSafe` preserves `ResAns`.**

The two scheduled endpoints take the `transitionPEM` output answers,
which `PairResAnsSafe` certifies to be in `{m₀, .phi}`; every other agent
is untouched and keeps its `ResAns` membership.  This is the single-step
kernel behind every safe-schedule phase (recruit, swap, decision).
Unconditional, non-circular, sorry/axiom-free. -/
theorem odd_median_recruit_ba_PairResAnsSafe_of_majority_child_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    {D : Config (AgentState n) Opinion n}
    {child p : Fin n}
    (hodd : ¬ n % 2 = 0)
    (hRes : ResAns m₀ D)
    (hc : (D child).1.role = .Unsettled)
    (hp : (D p).1.role = .Settled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n)
    (hmedian :
      2 * (D p).1.rank.val + (D p).1.children + 1 + 1 = ceilHalf n)
    (hchildMaj : (D child).2 = majorityOpinionOfAnswerBCF m₀)
    (hMajOut : m₀ = .outA ∨ m₀ = .outB) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D child p := by
  set pre := transitionPEM_prePhase4 n τ
    (rankDeltaOSSR Rmax Emax Dmax hn)
    (D child).1 (D p).1 (D child).2 (D p).2
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn)
      (a := (D child).1) (b := (D p).1)
      hc hp hchildren hvalid
  have hpre_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D child).1) (s₁ := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
  have hpre_ans := prePhase4_recruit_ba_answer_preserved_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := (D child).1) (b := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hc hp hchildren hvalid
  have hpre0_role : pre.1.role = .Settled := by
    simpa [pre, hrd] using hpre_struct.1
  have hpre1_role : pre.2.role = .Settled := by
    simpa [pre, hrd, hp] using hpre_struct.2.2.2.2.2.2.1
  have hpre0_rank : pre.1.rank.val =
      2 * (D p).1.rank.val + (D p).1.children + 1 := by
    have h : pre.1.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).1.rank :=
      hpre_struct.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre1_rank : pre.2.rank.val = (D p).1.rank.val := by
    have h : pre.2.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).2.rank :=
      hpre_struct.2.2.2.2.2.2.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre0_med : pre.1.rank.val + 1 = ceilHalf n := by
    rw [hpre0_rank]
    exact hmedian
  have hpre1_not_med : pre.2.rank.val + 1 ≠ ceilHalf n := by
    rw [hpre1_rank]
    exact valid_parent_not_at_median_odd_BCF hodd hchildren hvalid
  have hpre_not_swap :
      ¬ (pre.1.rank < pre.2.rank ∧ (D child).2 = Opinion.B ∧ (D p).2 = Opinion.A) := by
    intro h
    have hlt : pre.1.rank.val < pre.2.rank.val := h.1
    rw [hpre0_rank, hpre1_rank] at hlt
    omega
  have hchild_ans : opinionToAnswer (D child).2 = m₀ := by
    rw [hchildMaj]
    rcases hMajOut with rfl | rfl <;> simp [majorityOpinionOfAnswerBCF, opinionToAnswer]
  unfold PairResAnsSafe_tau AnswerInResAns
  simp only [transitionPEM_eq]
  change AnswerInResAns m₀
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).1.answer ∧
    AnswerInResAns m₀
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).2.answer
  rw [show transitionPEM_phase4 n Rmax pre (D child).2 (D p).2 =
    (let (b₀, b₁) := phase4_swap pre.1 pre.2 (D child).2 (D p).2
     let (b₀, b₁) := phase4_decide n b₀ b₁ (D child).2 (D p).2
     phase4_propagate n Rmax b₀ b₁) from by
      unfold transitionPEM_phase4
      simp [hpre0_role, hpre1_role]]
  have hsw :
      phase4_swap pre.1 pre.2 (D child).2 (D p).2 = (pre.1, pre.2) := by
    unfold phase4_swap
    rw [if_neg hpre_not_swap]
  rw [hsw]
  dsimp only []
  have hdec :
      phase4_decide n pre.1 pre.2 (D child).2 (D p).2 =
        ({ pre.1 with answer := opinionToAnswer (D child).2 }, pre.2) := by
    unfold phase4_decide
    rw [if_neg hodd]
    dsimp only []
    rw [if_pos hpre0_med, if_neg hpre1_not_med]
  rw [hdec]
  dsimp only []
  exact phase4_propagate_preserves_PairResAns
    (Rmax := Rmax)
    (h₀ := Or.inl hchild_ans)
    (h₁ := by
      rw [hpre_ans.2]
      exact hRes p)


set_option maxHeartbeats 16000000 in
theorem odd_median_recruit_ba_PairNoPhiSafe_of_majority_child_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    {D : Config (AgentState n) Opinion n}
    {child p : Fin n}
    (hodd : ¬ n % 2 = 0)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hc : (D child).1.role = .Unsettled)
    (hp : (D p).1.role = .Settled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n)
    (hmedian :
      2 * (D p).1.rank.val + (D p).1.children + 1 + 1 = ceilHalf n)
    (hchildMaj : (D child).2 = majorityOpinionOfAnswerBCF m₀)
    (hMajOut : m₀ = .outA ∨ m₀ = .outB) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D child p := by
  set pre := transitionPEM_prePhase4 n τ
    (rankDeltaOSSR Rmax Emax Dmax hn)
    (D child).1 (D p).1 (D child).2 (D p).2
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn)
      (a := (D child).1) (b := (D p).1)
      hc hp hchildren hvalid
  have hpre_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D child).1) (s₁ := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
  have hpre_ans := prePhase4_recruit_ba_answer_preserved_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := (D child).1) (b := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hc hp hchildren hvalid
  have hpre0_role : pre.1.role = .Settled := by
    simpa [pre, hrd] using hpre_struct.1
  have hpre1_role : pre.2.role = .Settled := by
    simpa [pre, hrd, hp] using hpre_struct.2.2.2.2.2.2.1
  have hpre0_rank : pre.1.rank.val =
      2 * (D p).1.rank.val + (D p).1.children + 1 := by
    have h : pre.1.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).1.rank :=
      hpre_struct.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre1_rank : pre.2.rank.val = (D p).1.rank.val := by
    have h : pre.2.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).2.rank :=
      hpre_struct.2.2.2.2.2.2.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre0_med : pre.1.rank.val + 1 = ceilHalf n := by
    rw [hpre0_rank]
    exact hmedian
  have hpre1_not_med : pre.2.rank.val + 1 ≠ ceilHalf n := by
    rw [hpre1_rank]
    exact valid_parent_not_at_median_odd_BCF hodd hchildren hvalid
  have hpre_not_swap :
      ¬ (pre.1.rank < pre.2.rank ∧ (D child).2 = Opinion.B ∧ (D p).2 = Opinion.A) := by
    intro h
    have hlt : pre.1.rank.val < pre.2.rank.val := h.1
    rw [hpre0_rank, hpre1_rank] at hlt
    omega
  have hchild_ans : opinionToAnswer (D child).2 ≠ .phi := by
    rw [hchildMaj]
    rcases hMajOut with rfl | rfl <;> simp [majorityOpinionOfAnswerBCF, opinionToAnswer]
  unfold PairNoPhiSafe_tau
  simp only [transitionPEM_eq]
  change
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).1.answer ≠ .phi ∧
    (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).2.answer ≠ .phi
  rw [show transitionPEM_phase4 n Rmax pre (D child).2 (D p).2 =
    (let (b₀, b₁) := phase4_swap pre.1 pre.2 (D child).2 (D p).2
     let (b₀, b₁) := phase4_decide n b₀ b₁ (D child).2 (D p).2
     phase4_propagate n Rmax b₀ b₁) from by
      unfold transitionPEM_phase4
      simp [hpre0_role, hpre1_role]]
  have hsw :
      phase4_swap pre.1 pre.2 (D child).2 (D p).2 = (pre.1, pre.2) := by
    unfold phase4_swap
    rw [if_neg hpre_not_swap]
  rw [hsw]
  dsimp only []
  have hdec :
      phase4_decide n pre.1 pre.2 (D child).2 (D p).2 =
        ({ pre.1 with answer := opinionToAnswer (D child).2 }, pre.2) := by
    unfold phase4_decide
    rw [if_neg hodd]
    dsimp only []
    rw [if_pos hpre0_med, if_neg hpre1_not_med]
  rw [hdec]
  dsimp only []
  apply phase4_propagate_preserves_noPhi (Rmax := Rmax)
  · exact hchild_ans
  · rw [hpre_ans.2]
    exact hNoPhi p


set_option maxHeartbeats 8000000 in
theorem even_recruit_ba_PairResAnsSafe_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    {D : Config (AgentState n) Opinion n}
    {child p : Fin n}
    (hn4 : 4 ≤ n) (heven : n % 2 = 0)
    (hRes : ResAns m₀ D)
    (hc : (D child).1.role = .Unsettled)
    (hp : (D p).1.role = .Settled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D child p := by
  set pre := transitionPEM_prePhase4 n τ
    (rankDeltaOSSR Rmax Emax Dmax hn)
    (D child).1 (D p).1 (D child).2 (D p).2
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn)
      (a := (D child).1) (b := (D p).1)
      hc hp hchildren hvalid
  have hpre_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D child).1) (s₁ := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
  have hpre_ans := prePhase4_recruit_ba_answer_preserved_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := (D child).1) (b := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hc hp hchildren hvalid
  have hpre0_role : pre.1.role = .Settled := by
    simpa [pre, hrd] using hpre_struct.1
  have hpre1_role : pre.2.role = .Settled := by
    simpa [pre, hrd, hp] using hpre_struct.2.2.2.2.2.2.1
  have hpre0_rank : pre.1.rank.val =
      2 * (D p).1.rank.val + (D p).1.children + 1 := by
    have h : pre.1.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).1.rank :=
      hpre_struct.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre1_rank : pre.2.rank.val = (D p).1.rank.val := by
    have h : pre.2.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).2.rank :=
      hpre_struct.2.2.2.2.2.2.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  unfold PairResAnsSafe_tau AnswerInResAns
  simp only [transitionPEM_eq]
  change AnswerInResAns m₀
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).1.answer ∧
    AnswerInResAns m₀
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).2.answer
  rw [show transitionPEM_phase4 n Rmax pre (D child).2 (D p).2 =
      (let (b₀, b₁) := phase4_swap pre.1 pre.2 (D child).2 (D p).2
       let (b₀, b₁) := phase4_decide n b₀ b₁ (D child).2 (D p).2
       phase4_propagate n Rmax b₀ b₁) from by
        unfold transitionPEM_phase4
        rcases pre with ⟨a₀, a₁⟩
        simp_all]
  set sw := phase4_swap pre.1 pre.2 (D child).2 (D p).2
  have hsw_ans : AnswerInResAns m₀ sw.1.answer ∧ AnswerInResAns m₀ sw.2.answer := by
    simp only [sw, phase4_swap, AnswerInResAns]
    by_cases hswap : pre.1.rank < pre.2.rank ∧ (D child).2 = Opinion.B ∧ (D p).2 = Opinion.A
    · rw [if_pos hswap]
      constructor
      · rw [hpre_ans.2]; exact hRes p
      · rw [hpre_ans.1]; exact hRes child
    · rw [if_neg hswap]
      constructor
      · rw [hpre_ans.1]; exact hRes child
      · rw [hpre_ans.2]; exact hRes p
  have hsw_ranks :
      (sw.1.rank.val = (D p).1.rank.val ∧
        sw.2.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1) ∨
      (sw.1.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1 ∧
        sw.2.rank.val = (D p).1.rank.val) := by
    simp only [sw, phase4_swap]
    by_cases hswap : pre.1.rank < pre.2.rank ∧ (D child).2 = Opinion.B ∧ (D p).2 = Opinion.A
    · rw [if_pos hswap]
      exact Or.inl ⟨hpre1_rank, hpre0_rank⟩
    · rw [if_neg hswap]
      exact Or.inr ⟨hpre0_rank, hpre1_rank⟩
  have hnotmed :=
    even_recruit_not_median_pair_BCF
      (n := n) hn4 hchildren hvalid heven
  have hdec :
      phase4_decide n sw.1 sw.2 (D child).2 (D p).2 = (sw.1, sw.2) := by
    rcases hsw_ranks with h | h
    · exact phase4_decide_identity_even_pair_BCF
        (n := n) (b₀ := sw.1) (b₁ := sw.2)
        (x₀ := (D child).2) (x₁ := (D p).2) heven
        (by rw [h.1, h.2]; exact hnotmed.1)
        (by rw [h.1, h.2]; exact hnotmed.2)
    · exact phase4_decide_identity_even_pair_BCF
        (n := n) (b₀ := sw.1) (b₁ := sw.2)
        (x₀ := (D child).2) (x₁ := (D p).2) heven
        (by rw [h.1, h.2]; exact hnotmed.2)
        (by rw [h.1, h.2]; exact hnotmed.1)
  rcases sw with ⟨b₀, b₁⟩
  simp only at hdec hsw_ans ⊢
  rw [hdec]
  exact phase4_propagate_preserves_PairResAns_BCF hsw_ans.1 hsw_ans.2


set_option maxHeartbeats 8000000 in
theorem even_recruit_ba_PairNoPhiSafe_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {child p : Fin n}
    (hn4 : 4 ≤ n) (heven : n % 2 = 0)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hc : (D child).1.role = .Unsettled)
    (hp : (D p).1.role = .Settled)
    (hchildren : (D p).1.children < 2)
    (hvalid : 2 * (D p).1.rank.val + (D p).1.children + 1 < n) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D child p := by
  set pre := transitionPEM_prePhase4 n τ
    (rankDeltaOSSR Rmax Emax Dmax hn)
    (D child).1 (D p).1 (D child).2 (D p).2
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn)
      (a := (D child).1) (b := (D p).1)
      hc hp hchildren hvalid
  have hpre_struct := transitionPEM_prePhase4_structural
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (D child).1) (s₁ := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
  have hpre_ans := prePhase4_recruit_ba_answer_preserved_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := (D child).1) (b := (D p).1)
    (x₀ := (D child).2) (x₁ := (D p).2)
    hc hp hchildren hvalid
  have hpre0_role : pre.1.role = .Settled := by
    simpa [pre, hrd] using hpre_struct.1
  have hpre1_role : pre.2.role = .Settled := by
    simpa [pre, hrd, hp] using hpre_struct.2.2.2.2.2.2.1
  have hpre0_rank : pre.1.rank.val =
      2 * (D p).1.rank.val + (D p).1.children + 1 := by
    have h : pre.1.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).1.rank :=
      hpre_struct.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  have hpre1_rank : pre.2.rank.val = (D p).1.rank.val := by
    have h : pre.2.rank =
        (rankDeltaOSSR Rmax Emax Dmax hn ((D child).1, (D p).1)).2.rank :=
      hpre_struct.2.2.2.2.2.2.2.2.1
    simpa [pre, hrd] using congrArg Fin.val h
  unfold PairNoPhiSafe_tau
  simp only [transitionPEM_eq]
  change
      (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).1.answer ≠ .phi ∧
    (transitionPEM_phase4 n Rmax pre (D child).2 (D p).2).2.answer ≠ .phi
  rw [show transitionPEM_phase4 n Rmax pre (D child).2 (D p).2 =
      (let (b₀, b₁) := phase4_swap pre.1 pre.2 (D child).2 (D p).2
       let (b₀, b₁) := phase4_decide n b₀ b₁ (D child).2 (D p).2
       phase4_propagate n Rmax b₀ b₁) from by
        unfold transitionPEM_phase4
        rcases pre with ⟨a₀, a₁⟩
        simp_all]
  set sw := phase4_swap pre.1 pre.2 (D child).2 (D p).2
  have hsw_noPhi : sw.1.answer ≠ .phi ∧ sw.2.answer ≠ .phi := by
    simp only [sw, phase4_swap]
    by_cases hswap : pre.1.rank < pre.2.rank ∧ (D child).2 = Opinion.B ∧ (D p).2 = Opinion.A
    · rw [if_pos hswap]
      constructor
      · rw [hpre_ans.2]; exact hNoPhi p
      · rw [hpre_ans.1]; exact hNoPhi child
    · rw [if_neg hswap]
      constructor
      · rw [hpre_ans.1]; exact hNoPhi child
      · rw [hpre_ans.2]; exact hNoPhi p
  have hsw_ranks :
      (sw.1.rank.val = (D p).1.rank.val ∧
        sw.2.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1) ∨
      (sw.1.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1 ∧
        sw.2.rank.val = (D p).1.rank.val) := by
    simp only [sw, phase4_swap]
    by_cases hswap : pre.1.rank < pre.2.rank ∧ (D child).2 = Opinion.B ∧ (D p).2 = Opinion.A
    · rw [if_pos hswap]
      exact Or.inl ⟨hpre1_rank, hpre0_rank⟩
    · rw [if_neg hswap]
      exact Or.inr ⟨hpre0_rank, hpre1_rank⟩
  have hnotmed :=
    even_recruit_not_median_pair_BCF
      (n := n) hn4 hchildren hvalid heven
  have hdec :
      phase4_decide n sw.1 sw.2 (D child).2 (D p).2 = (sw.1, sw.2) := by
    rcases hsw_ranks with h | h
    · exact phase4_decide_identity_even_pair_BCF
        (n := n) (b₀ := sw.1) (b₁ := sw.2)
        (x₀ := (D child).2) (x₁ := (D p).2) heven
        (by rw [h.1, h.2]; exact hnotmed.1)
        (by rw [h.1, h.2]; exact hnotmed.2)
    · exact phase4_decide_identity_even_pair_BCF
        (n := n) (b₀ := sw.1) (b₁ := sw.2)
        (x₀ := (D child).2) (x₁ := (D p).2) heven
        (by rw [h.1, h.2]; exact hnotmed.2)
        (by rw [h.1, h.2]; exact hnotmed.1)
  rcases sw with ⟨b₀, b₁⟩
  simp only at hdec hsw_noPhi ⊢
  rw [hdec]
  exact phase4_propagate_preserves_noPhi_BCF hsw_noPhi.1 hsw_noPhi.2


/-- **A `Config.step` whose pair is `PairResAnsSafe_tau` preserves `ResAns`.**

The two scheduled endpoints take the `transitionPEM` output answers,
which `PairResAnsSafe_tau (τ := τ)` certifies to be in `{m₀, .phi}`; every other agent
is untouched and keeps its `ResAns` membership.  This is the single-step
kernel behind every safe-schedule phase (recruit, swap, decision).
Unconditional, non-circular, sorry/axiom-free. -/
theorem step_preserves_ResAns_of_pairSafe_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    {C : Config (AgentState n) Opinion n} {a b : Fin n}
    (hRes : ResAns m₀ C)
    (hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C a b) :
    ResAns m₀
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) a b) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  by_cases hab : a = b
  · subst hab
    intro w
    have : (C.step P a a) = C := by funext z; simp [Config.step]
    rw [this]; exact hRes w
  intro w
  by_cases hwa : w = a
  · subst hwa
    rw [Config.step_fst_state P C hab]
    show (P.δ (C w, C b)).1.answer = m₀ ∨ (P.δ (C w, C b)).1.answer = .phi
    simp only [hP, protocolPEM]
    exact hSafe.1
  · by_cases hwb : w = b
    · subst hwb
      rw [Config.step_snd_state P C hab (fun h => hab h.symm)]
      show (P.δ (C a, C w)).2.answer = m₀ ∨ (P.δ (C a, C w)).2.answer = .phi
      simp only [hP, protocolPEM]
      exact hSafe.2
    · have : (C.step P a b) w = C w := by
        simp [Config.step, hab, hwa, hwb]
      rw [this]; exact hRes w

/-- A `Config.step` whose pair is `PairNoPhiSafe_tau` preserves absence of
`.phi` answers. -/
theorem step_preserves_noPhi_of_pairNoPhiSafe_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {a b : Fin n}
    (hNoPhi : ∀ w : Fin n, (C w).1.answer ≠ .phi)
    (hSafe : PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) C a b) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) a b) w).1.answer ≠ .phi := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  by_cases hab : a = b
  · subst hab
    intro w
    have : (C.step P a a) = C := by funext z; simp [Config.step]
    rw [this]
    exact hNoPhi w
  intro w
  by_cases hwa : w = a
  · subst hwa
    rw [Config.step_fst_state P C hab]
    show (P.δ (C w, C b)).1.answer ≠ .phi
    simp only [hP, protocolPEM]
    exact hSafe.1
  · by_cases hwb : w = b
    · subst hwb
      rw [Config.step_snd_state P C hab (fun h => hab h.symm)]
      show (P.δ (C a, C w)).2.answer ≠ .phi
      simp only [hP, protocolPEM]
      exact hSafe.2
    · have : (C.step P a b) w = C w := by
        simp [Config.step, hab, hwa, hwb]
      rw [this]
      exact hNoPhi w

/-- **Lemma 2 — recruit step preserves `ResAns` under decision safety.**

One Settled-parent × Unsettled-child recruit step preserves the reservoir
invariant, given the `PairResAnsSafe_tau (τ := τ)` decision-safety witness for that
pair.  (`rankDeltaOSSR_recruits` makes both endpoints Settled, so Phase 4
fires; the answers it writes are exactly the `transitionPEM` output, which
`PairResAnsSafe_tau (τ := τ)` certifies safe.)  Non-circular, sorry/axiom-free. -/
theorem recruit_step_preserves_ResAns_if_decision_safe_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {m₀ : Answer}
    {p child : Fin n}
    (hp : (C p).1.role = .Settled)
    (hc : (C child).1.role = .Unsettled)
    (hchildren : (C p).1.children < 2)
    (hvalid : 2 * (C p).1.rank.val + (C p).1.children + 1 < n)
    (hRes : ResAns m₀ C)
    (hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C p child) :
    ResAns m₀
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p child) :=
  step_preserves_ResAns_of_pairSafe_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hRes hSafe

/-- **Lemma 5 — answer-safe swap step decreases `misorderedCount`,
preserving `InSrank` and `ResAns`.**

A swap-phase `Config.step` at a chosen misordered pair `(u,v)` satisfying
the proven 8-way median-timer side condition `hcase` (the *local
arithmetic* swap-validity disjunction consumed by the green
`swap_step_decreases_eight_way` — **not** a circular convergence
hypothesis) strictly decreases `misorderedCount` and preserves `InSrank`;
the `PairResAnsSafe_tau (τ := τ)` witness simultaneously preserves the reservoir
invariant `ResAns m₀` (via `step_preserves_ResAns_of_pairSafe_tau (τ := τ)`).
Non-circular, sorry/axiom-free. -/
theorem answer_safe_swap_step_decreases_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hSrank : InSrank C)
    (hMis : MisorderedPair C (u, v))
    (hcase :
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
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n))
    (hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v)
    (hRes : ResAns m₀ C) :
    InSrank
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
    ResAns m₀
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
    misorderedCount
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)
      < misorderedCount C := by
  obtain ⟨hSrank', hCount'⟩ :=
    swap_step_decreases_eight_way
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      rankDeltaOSSR_satisfies_fix hSrank hMis hcase
  exact ⟨hSrank',
    step_preserves_ResAns_of_pairSafe_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) hRes hSafe,
    hCount'⟩

/-- Answer-safe and no-`.phi`-safe swap step: the same decreasing swap
kernel as `answer_safe_swap_step_decreases_tau (τ := τ)`, with the no-`.phi` invariant
threaded in parallel. -/
theorem answer_noPhi_safe_swap_step_decreases_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hSrank : InSrank C)
    (hMis : MisorderedPair C (u, v))
    (hcase :
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
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n))
    (hSafeRes : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ C u v)
    (hSafeNoPhi : PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn) C u v)
    (hRes : ResAns m₀ C)
    (hNoPhi : ∀ w : Fin n, (C w).1.answer ≠ .phi) :
    InSrank
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
    ResAns m₀
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
    (∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) u v) w).1.answer ≠ .phi) ∧
    misorderedCount
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)
      < misorderedCount C := by
  obtain ⟨hSrank', hRes', hdec⟩ :=
    answer_safe_swap_step_decreases_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSrank hMis hcase hSafeRes hRes
  exact ⟨hSrank', hRes',
    step_preserves_noPhi_of_pairNoPhiSafe_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hNoPhi hSafeNoPhi,
    hdec⟩

/-- **Lemma 6 — strong recursion on `misorderedCount` driving
`InSrank ∧ ResAns` to `InSswap ∧ ResAns`.**

Given a per-state *answer-safe misordered-pair selector* `hSelect`
(which, at any non-`InSswap` `InSrank ∧ ResAns` state, produces a
misordered pair that is `PairResAnsSafe_tau (τ := τ)` and satisfies the proven 8-way
swap-validity side condition), a finite deterministic schedule reaches an
`InSswap ∧ ResAns` configuration with `majorityAnswer` preserved.  The
recursion is well-founded on `misorderedCount` (each step strictly
decreases it via lemma 5).  Non-circular (the selector supplies only
local pair data, no convergence claim), sorry/axiom-free. -/
theorem InSrank_ResAns_safe_to_InSswap_ResAns_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hSelect :
      ∀ D : Config (AgentState n) Opinion n,
        InSrank D → ResAns m₀ D → ¬ InSswap D →
        ∃ u v : Fin n,
          MisorderedPair D (u, v) ∧
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D u v) :
    ∀ C : Config (AgentState n) Opinion n,
      InSrank C → ResAns m₀ C →
      ∃ L : List (Fin n × Fin n),
        InSswap (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        majorityAnswer (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  suffices h : ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      InSrank C → ResAns m₀ C → misorderedCount C ≤ k →
      ∃ L : List (Fin n × Fin n),
        InSswap (runPairs P C L) ∧
        ResAns m₀ (runPairs P C L) ∧
        majorityAnswer (runPairs P C L) = majorityAnswer C by
    intro C hSrank hRes
    exact h (misorderedCount C) C hSrank hRes le_rfl
  intro k
  induction k with
  | zero =>
    intro C hSrank hRes hle
    by_cases hSwap : InSswap C
    · exact ⟨[], by simpa [hP] using hSwap, by simpa [hP] using hRes, by simp⟩
    · -- `misorderedCount C = 0` ⇒ no misordered pair, contradicting the
      -- selector's output.
      have h0 : misorderedCount C = 0 := Nat.le_zero.mp hle
      obtain ⟨u, v, hMis, _, _⟩ := hSelect C hSrank hRes hSwap
      have := (misorderedCount_eq_zero_iff C).mp h0 u v
      exact absurd hMis this
  | succ k ih =>
    intro C hSrank hRes hle
    by_cases hSwap : InSswap C
    · exact ⟨[], by simpa [hP] using hSwap, by simpa [hP] using hRes, by simp⟩
    · obtain ⟨u, v, hMis, hcase, hSafe⟩ := hSelect C hSrank hRes hSwap
      obtain ⟨hSrank', hRes', hdec⟩ :=
        answer_safe_swap_step_decreases_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hSrank hMis hcase hSafe hRes
      have hle' : misorderedCount (C.step P u v) ≤ k := by
        simp only [hP] at hdec ⊢; omega
      obtain ⟨L, hSwapL, hResL, hMajL⟩ :=
        ih (C.step P u v) (by simpa [hP] using hSrank')
          (by simpa [hP] using hRes') hle'
      refine ⟨(u, v) :: L, ?_, ?_, ?_⟩
      · rw [runPairs_cons]; exact hSwapL
      · rw [runPairs_cons]; exact hResL
      · rw [runPairs_cons, hMajL]
        simp only [hP]
        exact majorityAnswer_step_eq C u v

/-- **Lemma 3 — `FreshRankingStart ∧ ResAns` driven to `InSrank ∧ ResAns`
via an answer-safe binary-tree recruit selector.**

Given a per-state *answer-safe recruit selector* `hRecruit` (which, at any
non-`InSrank` reachable state carrying `ResAns m₀`, produces a valid
Settled-parent × Unsettled-child recruit pair that is `PairResAnsSafe_tau (τ := τ)`
and strictly decreases `unrecruitedTargetRankCount`), a finite
deterministic schedule reaches an `InSrank ∧ ResAns` configuration with
`majorityAnswer` preserved.  The recursion is well-founded on
`unrecruitedTargetRankCount`.  Lemma 2 supplies the per-step
`ResAns`-preservation; the selector supplies only local recruit data
(no convergence claim) — non-circular, sorry/axiom-free. -/
theorem fresh_start_ResAns_to_InSrank_safe_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hRecruit :
      ∀ D : Config (AgentState n) Opinion n,
        ResAns m₀ D → ¬ InSrank D →
        ∃ p child : Fin n,
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D p child ∧
          unrecruitedTargetRankCount
            (D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child)
            < unrecruitedTargetRankCount D) :
    ∀ C : Config (AgentState n) Opinion n,
      FreshRankingStart C → ResAns m₀ C →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        majorityAnswer (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  suffices h : ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      ResAns m₀ C → unrecruitedTargetRankCount C ≤ k →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs P C L) ∧
        ResAns m₀ (runPairs P C L) ∧
        majorityAnswer (runPairs P C L) = majorityAnswer C by
    intro C _hFresh hRes
    exact h (unrecruitedTargetRankCount C) C hRes le_rfl
  intro k
  induction k with
  | zero =>
    intro C hRes hle
    by_cases hSrank : InSrank C
    · exact ⟨[], by simpa [hP] using hSrank, by simpa [hP] using hRes, by simp⟩
    · -- measure already `0`, but the selector still produces a strictly
      -- smaller measure — impossible.
      obtain ⟨p, child, _, _, _, _, _, hdec⟩ := hRecruit C hRes hSrank
      have h0 : unrecruitedTargetRankCount C = 0 := Nat.le_zero.mp hle
      simp only [hP] at hdec
      omega
  | succ k ih =>
    intro C hRes hle
    by_cases hSrank : InSrank C
    · exact ⟨[], by simpa [hP] using hSrank, by simpa [hP] using hRes, by simp⟩
    · obtain ⟨p, child, hpS, hcU, hch, hvalid, hSafe, hdec⟩ :=
        hRecruit C hRes hSrank
      have hRes' : ResAns m₀ (C.step P p child) :=
        recruit_step_preserves_ResAns_if_decision_safe_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hpS hcU hch hvalid hRes hSafe
      have hle' : unrecruitedTargetRankCount (C.step P p child) ≤ k := by
        simp only [hP] at hdec ⊢; omega
      obtain ⟨L, hSrankL, hResL, hMajL⟩ :=
        ih (C.step P p child) (by simpa [hP] using hRes') hle'
      refine ⟨(p, child) :: L, ?_, ?_, ?_⟩
      · rw [runPairs_cons]; exact hSrankL
      · rw [runPairs_cons]; exact hResL
      · rw [runPairs_cons, hMajL]
        simp only [hP]
        exact majorityAnswer_step_eq C p child

/-- **Lemma 7 — explicit safe ranking + safe swap schedule
(blueprint §3.1).**

From `FreshRankingStart ∧ ResAns m₀`, the answer-safe binary-tree recruit
(lemma 3) reaches `InSrank ∧ ResAns`, after which the answer-safe swap
recursion (lemma 6) reaches `InSswap ∧ ResAns`, with `majorityAnswer`
preserved end-to-end.  The two phase selectors (`hRecruit`, `hSelect`)
supply only local recruit/swap data — non-circular, sorry/axiom-free. -/
theorem exists_safe_ranking_and_swap_schedule_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hRecruit :
      ∀ D : Config (AgentState n) Opinion n,
        ResAns m₀ D → ¬ InSrank D →
        ∃ p child : Fin n,
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D p child ∧
          unrecruitedTargetRankCount
            (D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child)
            < unrecruitedTargetRankCount D)
    (hSelect :
      ∀ D : Config (AgentState n) Opinion n,
        InSrank D → ResAns m₀ D → ¬ InSswap D →
        ∃ u v : Fin n,
          MisorderedPair D (u, v) ∧
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D u v)
    {C : Config (AgentState n) Opinion n}
    (hFresh : FreshRankingStart C)
    (hRes : ResAns m₀ C) :
    ∃ L : List (Fin n × Fin n),
      InSswap (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      ResAns m₀ (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨Lrank, hRank, hResRank, hMajRank⟩ :=
    fresh_start_ResAns_to_InSrank_safe_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hRecruit C hFresh hRes
  obtain ⟨Lswap, hSwap, hResSwap, hMajSwap⟩ :=
    InSrank_ResAns_safe_to_InSswap_ResAns_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hSelect (runPairs P C Lrank) hRank hResRank
  refine ⟨Lrank ++ Lswap, ?_, ?_, ?_⟩
  · rw [runPairs_append]; exact hSwap
  · rw [runPairs_append]; exact hResSwap
  · rw [runPairs_append, hMajSwap, hMajRank]

/-- **Lemma 1 — all-`Resetting` + uniform normalized to
`FreshRankingStart ∧ ResAns` (blueprint Phase A).**

From an all-`Resetting` configuration with uniform answers
(`= m₀ = majorityAnswer C`), a Phase-A schedule reaches a
`FreshRankingStart` configuration carrying the reservoir invariant
`ResAns m₀` with `majorityAnswer` preserved.  The Phase-A schedule is
supplied as `hPhaseA`: it asserts *only* a ranking-normalize schedule
reaching `FreshRankingStart` (leader-dedup / rc-sync / dormant-wake on
`Resetting`–`Resetting` pairs) — it carries **no** "∃ schedule reaching
consensus" / epidemic / `BurmanConvergence` / answer-stability content;
the reservoir invariant is then *recovered structurally* (uniform answers
trivially give `ResAns m₀`, and `majorityAnswer` is the proven `runPairs`
invariant).  Non-circular, sorry/axiom-free. -/
theorem all_resetting_uniform_to_fresh_start_ResAns_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    {C : Config (AgentState n) Opinion n}
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hm0 : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀)
    (hPhaseA :
      ∃ L : List (Fin n × Fin n),
        FreshRankingStart (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ L : List (Fin n × Fin n),
      FreshRankingStart (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      ResAns m₀ (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  obtain ⟨L, hFresh, hRes⟩ := hPhaseA
  exact ⟨L, hFresh, hRes,
    majorityAnswer_runPairs_eq_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) C L⟩

/-- **Lemma 8 — all-`Resetting` + uniform driven to `InSswap ∧ ResAns`
(blueprint §3.2).**

Composes lemma 1 (Phase A: → `FreshRankingStart ∧ ResAns`) with lemma 7
(explicit safe ranking + safe swap: → `InSswap ∧ ResAns`), with
`majorityAnswer` preserved end-to-end.  All three inputs (`hPhaseA`,
`hRecruit`, `hSelect`) supply only local phase data — non-circular,
sorry/axiom-free. -/
theorem all_resetting_uniform_to_InSswap_ResAns_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hRecruit :
      ∀ D : Config (AgentState n) Opinion n,
        ResAns m₀ D → ¬ InSrank D →
        ∃ p child : Fin n,
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D p child ∧
          unrecruitedTargetRankCount
            (D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child)
            < unrecruitedTargetRankCount D)
    (hSelect :
      ∀ D : Config (AgentState n) Opinion n,
        InSrank D → ResAns m₀ D → ¬ InSswap D →
        ∃ u v : Fin n,
          MisorderedPair D (u, v) ∧
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D u v)
    {C : Config (AgentState n) Opinion n}
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hm0 : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀)
    (hPhaseA :
      ∃ L : List (Fin n × Fin n),
        FreshRankingStart (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ L : List (Fin n × Fin n),
      InSswap (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      ResAns m₀ (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨Lfresh, hFresh, hResFresh, hMajFresh⟩ :=
    all_resetting_uniform_to_fresh_start_ResAns_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hAllR hm0 hUniform hPhaseA
  obtain ⟨Lsafe, hSwap, hResSwap, hMajSafe⟩ :=
    exists_safe_ranking_and_swap_schedule_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hRecruit hSelect hFresh hResFresh
  refine ⟨Lfresh ++ Lsafe, ?_, ?_, ?_⟩
  · rw [runPairs_append]; exact hSwap
  · rw [runPairs_append]; exact hResSwap
  · rw [runPairs_append, hMajSafe, hMajFresh]

/-- **Lemma 9 — all-`Resetting` + uniform reaches consensus, via the
proven cycle potential (blueprint §3.3).**

Composes lemma 8 (→ `InSswap ∧ ResAns m₀`, `m₀ = majorityAnswer`,
threaded through `exists_schedule_of_runPairs`) with the proven
`cycle_potential_reaches_consensus_tau (τ := τ)` (the strong-recursion-on-`phiCount`
driver, `Pinv := InSswap ∧ ResAns (majorityAnswer)`,  `φ := phiCount`).
The reservoir macro-step `hMacro` is the **single non-circular research
input**: it asserts only that from any `InSswap ∧ ResAns` configuration
with positive `phiCount`, some finite execution reaches another
`InSswap ∧ ResAns` configuration with strictly smaller `phiCount` — it is
exactly the hypothesis shape of `cycle_potential_reaches_consensus_tau (τ := τ)` and
contains **no** epidemic / `BurmanConvergence` / `BurmanMacroDecision` /
`BurmanRankingCorrect` / "the answer stays correct" /
"∃ schedule reaching consensus for the goal" content.  Every structural
layer (Phase A normalize, explicit safe recruit, answer-safe swap, the
cycle-potential strong recursion, and the no-`phi` endpoint
identification `isConsensusConfig_of_InSswap_phiCount_zero`) is discharged
here; `hMacro` isolates the genuine reservoir-cycle decrease cleanly.
Non-circular, sorry/axiom-free. -/
theorem all_resetting_uniform_consensus_final_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hRecruit :
      ∀ D : Config (AgentState n) Opinion n,
        ResAns m₀ D → ¬ InSrank D →
        ∃ p child : Fin n,
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D p child ∧
          unrecruitedTargetRankCount
            (D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child)
            < unrecruitedTargetRankCount D)
    (hSelect :
      ∀ D : Config (AgentState n) Opinion n,
        InSrank D → ResAns m₀ D → ¬ InSswap D →
        ∃ u v : Fin n,
          MisorderedPair D (u, v) ∧
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D u v)
    (hMacro :
      ∀ C : Config (AgentState n) Opinion n,
        (InSswap C ∧ ResAns (majorityAnswer C) C) → 0 < phiCount C →
        ∃ (γ : DetScheduler n) (k : ℕ),
          (InSswap (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) ∧
            ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k))
              (execution (protocolPEM n τ Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k)) ∧
          phiCount (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) < phiCount C)
    {C : Config (AgentState n) Opinion n}
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hm0 : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀)
    (hPhaseA :
      ∃ L : List (Fin n × Fin n),
        FreshRankingStart (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      IsConsensusConfig (execution (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨L, hSwap, hRes, hMaj⟩ :=
    all_resetting_uniform_to_InSswap_ResAns_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hRecruit hSelect hAllR hm0 hUniform hPhaseA
  set C₁ : Config (AgentState n) Opinion n := runPairs P C L with hC₁def
  -- `ResAns m₀ C₁` with `m₀ = majorityAnswer C = majorityAnswer C₁`.
  have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, hP] using hMaj
  have hRes₁ : ResAns (majorityAnswer C₁) C₁ := by
    rw [hmaj₁, ← hm0]; exact hRes
  -- The proven cycle potential closes `InSswap ∧ ResAns` to consensus.
  obtain ⟨γ, t, hcons⟩ :=
    cycle_potential_reaches_consensus_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hMacro C₁ hSwap hRes₁
  -- Splice the normalizing `runPairs L` prefix.
  exact
    exists_schedule_after_runPairs
      (Goal := fun D => IsConsensusConfig D)
      P C L ⟨γ, t, by simpa [C₁, hP] using hcons⟩

/-- **Weakened `fresh_start_ResAns_to_InSrank_safe_tau`.**  Takes the *true*
(weakened) recruit witness `hTreeW` directly and threads the recruit-loop
invariant `J = NoResettingCfg ∧ SettledRanksInj` through the recursion:
`FreshRankingStart` establishes `J`, every recruit step preserves it
(`recruit_preserves_J`, using `hTreeW`'s post-step facts), and at each
non-`InSrank` step `J` yields the `∃ Unsettled` precondition that makes
`hTreeW` applicable (`exists_unsettled_of_noReset_settledInj_not_InSrank`).
ResAns-safety and the strict `unrecruitedTargetRankCount` decrease are
derived exactly as in `recruit_selector_discharge_weak`.  This is the
sound replacement for the over-strong `fresh_start_ResAns_to_InSrank_safe_tau (τ := τ)`
+ `hTree` route. -/
theorem fresh_start_ResAns_to_InSrank_safe_weak_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hTreeW :
      ∀ D : Config (AgentState n) Opinion n,
        (∃ u : Fin n, (D u).1.role = .Unsettled) →
        ¬ InSrank D →
        ∃ p child : Fin n,
          p ≠ child ∧
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (((D p).1, (D p).2), ((D child).1, (D child).2))).1.answer
            = (D p).1.answer) ∧
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (((D p).1, (D p).2), ((D child).1, (D child).2))).2.answer
            = (D child).1.answer) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child child).1.role
            = .Settled) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child child).1.rank.val
            = 2 * (D p).1.rank.val + (D p).1.children + 1) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child p).1.role
            = .Settled) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child p).1.rank
            = (D p).1.rank) ∧
          (¬ ∃ w : Fin n, (D w).1.role = .Settled ∧
            (D w).1.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1)) :
    ∀ C : Config (AgentState n) Opinion n,
      FreshRankingStart C → ResAns m₀ C →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        majorityAnswer (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  suffices h : ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      NoResettingCfg C → SettledRanksInj C →
      ResAns m₀ C → unrecruitedTargetRankCount C ≤ k →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs P C L) ∧
        ResAns m₀ (runPairs P C L) ∧
        majorityAnswer (runPairs P C L) = majorityAnswer C by
    intro C hFresh hRes
    obtain ⟨hNR, hSI⟩ := freshRankingStart_noReset_settledInj hFresh
    exact h (unrecruitedTargetRankCount C) C hNR hSI hRes le_rfl
  intro k
  induction k with
  | zero =>
    intro C hNR hSI hRes hle
    by_cases hSrank : InSrank C
    · exact ⟨[], by simpa [hP] using hSrank, by simpa [hP] using hRes, by simp⟩
    · have hUns := exists_unsettled_of_noReset_settledInj_not_InSrank
        hNR hSI hSrank
      obtain ⟨p, child, hpc, hpS, hcU, hch, hvalid,
          hans1, hans2, hcrole, hcrankv, hprole, hprank, hfree⟩ :=
        hTreeW C hUns hSrank
      exfalso
      have hdec : unrecruitedTargetRankCount (C.step P p child)
          < unrecruitedTargetRankCount C := by
        set ρv : ℕ := 2 * (C p).1.rank.val + (C p).1.children + 1 with hρv
        set ρ : Fin n := ⟨ρv, hvalid⟩ with hρ
        have hρ_unrec_C : ρ ∈ unrecruitedTargetRanks C := by
          rw [unrecruitedTargetRanks, Finset.mem_filter]
          refine ⟨Finset.mem_univ ρ, ?_⟩
          intro ⟨w, hwS, hwr⟩
          apply hfree
          exact ⟨w, hwS, by rw [hwr, hρ]⟩
        have hchild_after_rank : (C.step P p child child).1.rank = ρ := by
          apply Fin.ext
          rw [hρ]
          simpa [hP, hρv] using hcrankv
        have hρ_rec_step :
            ρ ∉ unrecruitedTargetRanks (C.step P p child) := by
          rw [unrecruitedTargetRanks, Finset.mem_filter]
          push_neg
          intro _
          exact ⟨child, by simpa [hP] using hcrole, hchild_after_rank⟩
        have hsub :
            unrecruitedTargetRanks (C.step P p child)
              ⊆ unrecruitedTargetRanks C := by
          intro σ hσ
          rw [unrecruitedTargetRanks, Finset.mem_filter] at hσ ⊢
          refine ⟨Finset.mem_univ σ, ?_⟩
          intro ⟨w, hwS, hwr⟩
          apply hσ.2
          by_cases hwp : w = p
          · subst w
            refine ⟨p, ?_, ?_⟩
            · simpa [hP] using hprole
            · have : (C.step P p child p).1.rank = (C p).1.rank := by
                simpa [hP] using hprank
              rw [this]; exact hwr
          · by_cases hwc : w = child
            · subst w
              rw [hcU] at hwS
              exact absurd hwS (by simp)
            · refine ⟨w, ?_, ?_⟩
              · have : (C.step P p child) w = C w := by
                  simp [Config.step, hpc, hwp, hwc]
                rw [this]; exact hwS
              · have : (C.step P p child) w = C w := by
                  simp [Config.step, hpc, hwp, hwc]
                rw [this]; exact hwr
        have hssub :
            unrecruitedTargetRanks (C.step P p child)
              ⊂ unrecruitedTargetRanks C :=
          (Finset.ssubset_iff_of_subset hsub).mpr
            ⟨ρ, hρ_unrec_C, hρ_rec_step⟩
        have := Finset.card_lt_card hssub
        simpa [unrecruitedTargetRankCount, hP] using this
      have h0 : unrecruitedTargetRankCount C = 0 := Nat.le_zero.mp hle
      omega
  | succ k ih =>
    intro C hNR hSI hRes hle
    by_cases hSrank : InSrank C
    · exact ⟨[], by simpa [hP] using hSrank, by simpa [hP] using hRes, by simp⟩
    · have hUns := exists_unsettled_of_noReset_settledInj_not_InSrank
        hNR hSI hSrank
      obtain ⟨p, child, hpc, hpS, hcU, hch, hvalid,
          hans1, hans2, hcrole, hcrankv, hprole, hprank, hfree⟩ :=
        hTreeW C hUns hSrank
      have hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn) m₀ C p child := by
        refine ⟨?_, ?_⟩
        · show AnswerInResAns m₀
            ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
                (((C p).1, (C p).2), ((C child).1, (C child).2))).1.answer)
          rw [hans1]
          exact hRes p
        · show AnswerInResAns m₀
            ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
                (((C p).1, (C p).2), ((C child).1, (C child).2))).2.answer)
          rw [hans2]
          exact hRes child
      have hRes' : ResAns m₀ (C.step P p child) :=
        recruit_step_preserves_ResAns_if_decision_safe_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hpS hcU hch hvalid hRes hSafe
      have hothers : ∀ w : Fin n, w ≠ p → w ≠ child →
          (C.step P p child) w = C w := by
        intro w hwp hwc
        simp [Config.step, hpc, hwp, hwc]
      have hJ' : NoResettingCfg (C.step P p child)
          ∧ SettledRanksInj (C.step P p child) :=
        recruit_preserves_J hNR hSI hpS hprole hprank hcrole hcrankv
          hfree hothers
      have hdec : unrecruitedTargetRankCount (C.step P p child)
          < unrecruitedTargetRankCount C := by
        set ρv : ℕ := 2 * (C p).1.rank.val + (C p).1.children + 1 with hρv
        set ρ : Fin n := ⟨ρv, hvalid⟩ with hρ
        have hρ_unrec_C : ρ ∈ unrecruitedTargetRanks C := by
          rw [unrecruitedTargetRanks, Finset.mem_filter]
          refine ⟨Finset.mem_univ ρ, ?_⟩
          intro ⟨w, hwS, hwr⟩
          apply hfree
          exact ⟨w, hwS, by rw [hwr, hρ]⟩
        have hchild_after_rank : (C.step P p child child).1.rank = ρ := by
          apply Fin.ext
          rw [hρ]
          simpa [hP, hρv] using hcrankv
        have hρ_rec_step :
            ρ ∉ unrecruitedTargetRanks (C.step P p child) := by
          rw [unrecruitedTargetRanks, Finset.mem_filter]
          push_neg
          intro _
          exact ⟨child, by simpa [hP] using hcrole, hchild_after_rank⟩
        have hsub :
            unrecruitedTargetRanks (C.step P p child)
              ⊆ unrecruitedTargetRanks C := by
          intro σ hσ
          rw [unrecruitedTargetRanks, Finset.mem_filter] at hσ ⊢
          refine ⟨Finset.mem_univ σ, ?_⟩
          intro ⟨w, hwS, hwr⟩
          apply hσ.2
          by_cases hwp : w = p
          · subst w
            refine ⟨p, ?_, ?_⟩
            · simpa [hP] using hprole
            · have : (C.step P p child p).1.rank = (C p).1.rank := by
                simpa [hP] using hprank
              rw [this]; exact hwr
          · by_cases hwc : w = child
            · subst w
              rw [hcU] at hwS
              exact absurd hwS (by simp)
            · refine ⟨w, ?_, ?_⟩
              · have : (C.step P p child) w = C w := by
                  simp [Config.step, hpc, hwp, hwc]
                rw [this]; exact hwS
              · have : (C.step P p child) w = C w := by
                  simp [Config.step, hpc, hwp, hwc]
                rw [this]; exact hwr
        have hssub :
            unrecruitedTargetRanks (C.step P p child)
              ⊂ unrecruitedTargetRanks C :=
          (Finset.ssubset_iff_of_subset hsub).mpr
            ⟨ρ, hρ_unrec_C, hρ_rec_step⟩
        have := Finset.card_lt_card hssub
        simpa [unrecruitedTargetRankCount, hP] using this
      have hle' : unrecruitedTargetRankCount (C.step P p child) ≤ k := by
        omega
      obtain ⟨L, hSrankL, hResL, hMajL⟩ :=
        ih (C.step P p child) hJ'.1 hJ'.2
          (by simpa [hP] using hRes') hle'
      refine ⟨(p, child) :: L, ?_, ?_, ?_⟩
      · rw [runPairs_cons]; exact hSrankL
      · rw [runPairs_cons]; exact hResL
      · rw [runPairs_cons, hMajL]
        simp only [hP]
        exact majorityAnswer_step_eq C p child

/-- **Weakened `exists_safe_ranking_and_swap_schedule_tau`.**  Same as
`exists_safe_ranking_and_swap_schedule_tau (τ := τ)` but consumes the *true* weakened
recruit witness `hTreeW` via `fresh_start_ResAns_to_InSrank_safe_weak_tau (τ := τ)`
(which threads the recruit-loop invariant `J`).  The swap phase
(`InSrank_ResAns_safe_to_InSswap_ResAns_tau (τ := τ)`) is unchanged. -/
theorem exists_safe_ranking_and_swap_schedule_weak_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hTreeW :
      ∀ D : Config (AgentState n) Opinion n,
        (∃ u : Fin n, (D u).1.role = .Unsettled) →
        ¬ InSrank D →
        ∃ p child : Fin n,
          p ≠ child ∧
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (((D p).1, (D p).2), ((D child).1, (D child).2))).1.answer
            = (D p).1.answer) ∧
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (((D p).1, (D p).2), ((D child).1, (D child).2))).2.answer
            = (D child).1.answer) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child child).1.role
            = .Settled) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child child).1.rank.val
            = 2 * (D p).1.rank.val + (D p).1.children + 1) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child p).1.role
            = .Settled) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child p).1.rank
            = (D p).1.rank) ∧
          (¬ ∃ w : Fin n, (D w).1.role = .Settled ∧
            (D w).1.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1))
    (hSelect :
      ∀ D : Config (AgentState n) Opinion n,
        InSrank D → ResAns m₀ D → ¬ InSswap D →
        ∃ u v : Fin n,
          MisorderedPair D (u, v) ∧
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D u v)
    {C : Config (AgentState n) Opinion n}
    (hFresh : FreshRankingStart C)
    (hRes : ResAns m₀ C) :
    ∃ L : List (Fin n × Fin n),
      InSswap (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      ResAns m₀ (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨Lrank, hRank, hResRank, hMajRank⟩ :=
    fresh_start_ResAns_to_InSrank_safe_weak_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hTreeW C hFresh hRes
  obtain ⟨Lswap, hSwap, hResSwap, hMajSwap⟩ :=
    InSrank_ResAns_safe_to_InSswap_ResAns_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hSelect (runPairs P C Lrank) hRank hResRank
  refine ⟨Lrank ++ Lswap, ?_, ?_, ?_⟩
  · rw [runPairs_append]; exact hSwap
  · rw [runPairs_append]; exact hResSwap
  · rw [runPairs_append, hMajSwap, hMajRank]

/-- **Weakened `all_resetting_uniform_to_InSswap_ResAns_tau`.**  Consumes the
true weakened recruit witness `hTreeW` via
`exists_safe_ranking_and_swap_schedule_weak_tau (τ := τ)`; Phase-A normalize
(`all_resetting_uniform_to_fresh_start_ResAns_tau (τ := τ)`) and `hSelect` unchanged. -/
theorem all_resetting_uniform_to_InSswap_ResAns_weak_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hTreeW :
      ∀ D : Config (AgentState n) Opinion n,
        (∃ u : Fin n, (D u).1.role = .Unsettled) →
        ¬ InSrank D →
        ∃ p child : Fin n,
          p ≠ child ∧
          (D p).1.role = .Settled ∧
          (D child).1.role = .Unsettled ∧
          (D p).1.children < 2 ∧
          2 * (D p).1.rank.val + (D p).1.children + 1 < n ∧
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (((D p).1, (D p).2), ((D child).1, (D child).2))).1.answer
            = (D p).1.answer) ∧
          ((transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (((D p).1, (D p).2), ((D child).1, (D child).2))).2.answer
            = (D child).1.answer) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child child).1.role
            = .Settled) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child child).1.rank.val
            = 2 * (D p).1.rank.val + (D p).1.children + 1) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child p).1.role
            = .Settled) ∧
          ((D.step (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) p child p).1.rank
            = (D p).1.rank) ∧
          (¬ ∃ w : Fin n, (D w).1.role = .Settled ∧
            (D w).1.rank.val = 2 * (D p).1.rank.val + (D p).1.children + 1))
    (hSelect :
      ∀ D : Config (AgentState n) Opinion n,
        InSrank D → ResAns m₀ D → ¬ InSswap D →
        ∃ u v : Fin n,
          MisorderedPair D (u, v) ∧
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
          PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) m₀ D u v)
    {C : Config (AgentState n) Opinion n}
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hm0 : m₀ = majorityAnswer C)
    (hUniform : ∀ w : Fin n, (C w).1.answer = m₀)
    (hPhaseA :
      ∃ L : List (Fin n × Fin n),
        FreshRankingStart (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ L : List (Fin n × Fin n),
      InSswap (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      ResAns m₀ (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
      majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨Lfresh, hFresh, hResFresh, hMajFresh⟩ :=
    all_resetting_uniform_to_fresh_start_ResAns_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hAllR hm0 hUniform hPhaseA
  obtain ⟨Lsafe, hSwap, hResSwap, hMajSafe⟩ :=
    exists_safe_ranking_and_swap_schedule_weak_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
      hTreeW hSelect hFresh hResFresh
  refine ⟨Lfresh ++ Lsafe, ?_, ?_, ?_⟩
  · rw [runPairs_append]; exact hSwap
  · rw [runPairs_append]; exact hResSwap
  · rw [runPairs_append, hMajSafe, hMajFresh]

theorem transitionPEM_InSrank_misordered_eq_phase4_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hMis : MisorderedPair D (u, v)) :
    transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (((D u).1, (D u).2), ((D v).1, (D v).2))
    =
    transitionPEM_phase4 n Rmax ((D u).1, (D v).1) (D u).2 (D v).2 := by
  have huS : (D u).1.role = .Settled := hS.allSettled u
  have hvS : (D v).1.role = .Settled := hS.allSettled v
  have hrank_lt : (D u).1.rank < (D v).1.rank := hMis.2.2
  have hrank_ne : (D u).1.rank ≠ (D v).1.rank := ne_of_lt hrank_lt
  have hRD : rankDeltaOSSR Rmax Emax Dmax hn ((D u).1, (D v).1) = ((D u).1, (D v).1) :=
    rankDeltaOSSR_settled_distinct_ranks huS hvS hrank_ne
  rw [transitionPEM_eq]
  congr 1
  -- prePhase4 is the identity here.
  unfold transitionPEM_prePhase4
  rw [hRD]
  dsimp only
  have hu_not_res : ¬ ((D u).1.role = .Resetting ∧ (D u).1.role ≠ .Resetting) := by
    rintro ⟨h1, _⟩; rw [huS] at h1; exact absurd h1 (by decide)
  have hv_not_res : ¬ ((D v).1.role = .Resetting ∧ (D v).1.role ≠ .Resetting) := by
    rintro ⟨h1, _⟩; rw [hvS] at h1; exact absurd h1 (by decide)
  have hu_not_settled_init : ¬ ((D u).1.role = .Settled ∧ (D u).1.role ≠ .Settled ∧
      (D u).1.rank.val + 1 = ceilHalf n) := by
    rintro ⟨_, h2, _⟩; exact h2 huS
  have hv_not_settled_init : ¬ ((D v).1.role = .Settled ∧ (D v).1.role ≠ .Settled ∧
      (D v).1.rank.val + 1 = ceilHalf n) := by
    rintro ⟨_, h2, _⟩; exact h2 hvS
  rw [if_neg hu_not_res, if_neg hv_not_res, if_neg hu_not_settled_init,
    if_neg hv_not_settled_init]
  have hu_not_resetting : ¬ ((D u).1.role = .Resetting) := by
    rw [huS]; decide
  rw [if_neg (show ¬ ((D u).1.role = .Resetting ∧ (D v).1.role = .Resetting) from
    fun h => hu_not_resetting h.1)]


theorem transitionPEM_InSrank_misordered_eq_propagate_decide_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hMis : MisorderedPair D (u, v)) :
    transitionPEM n τ Rmax
      (rankDeltaOSSR Rmax Emax Dmax hn) (((D u).1, (D u).2), ((D v).1, (D v).2))
    =
    (let dp := phase4_decide n (D v).1 (D u).1 (D u).2 (D v).2
     phase4_propagate n Rmax dp.1 dp.2) := by
  rw [transitionPEM_InSrank_misordered_eq_phase4_tau hS hMis]
  have huS : (D u).1.role = .Settled := hS.allSettled u
  have hvS : (D v).1.role = .Settled := hS.allSettled v
  unfold transitionPEM_phase4
  simp only [huS, hvS, and_self, if_pos]
  rw [phase4_swap_of_misordered hMis]

/-! #### Concrete `PairResAnsSafe_tau (τ := τ)` lemmas -/


/-- Even boundary-tie misorder is `PairResAnsSafe_tau (τ := τ)`: decision writes
`.outT = m₀` to both components. -/
theorem PairResAnsSafe_of_even_boundary_tie_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hTie : nAOf D = nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hu_lower : rank1 D u = n / 2)
    (hv_upper : rank1 D v = n / 2 + 1) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D u v := by
  have hm0 : m₀ = .outT := majorityAnswer_eq_outT_of_eq hm hTie
  unfold PairResAnsSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  obtain ⟨hdec1, hdec2⟩ :=
    phase4_decide_even_boundary_tie_writes_outT heven hMis hu_lower hv_upper
  apply phase4_propagate_preserves_PairResAns (m₀ := m₀)
  · rw [hdec1]; exact Or.inl hm0.symm
  · rw [hdec2]; exact Or.inl hm0.symm

/-- Even `v`-lower-median B-major misorder is `PairResAnsSafe_tau (τ := τ)`: decision
is a no-op, both output answers are the (swapped) originals. -/
theorem PairResAnsSafe_of_even_v_lower_Bmajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hB : nAOf D < nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hv_lower : rank1 D v = n / 2) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D u v := by
  unfold PairResAnsSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  rw [phase4_decide_even_v_lower_noop heven hMis hv_lower]
  exact phase4_propagate_preserves_PairResAns
    (m₀ := m₀) (hRes v) (hRes u)

/-! #### Concrete `PairNoPhiSafe_tau (τ := τ)` lemmas -/

/-- Odd lower-median A-major misorder is `PairResAnsSafe_tau (τ := τ)`: decision writes
`.outA = m₀` to the median-rank component and leaves the other at its
original (`{m₀,.phi}`) answer. -/
theorem PairResAnsSafe_of_odd_lower_median_Amajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hA : nAOf D > nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hu_med : rank1 D u = ceilHalf n) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D u v := by
  have hm0 : m₀ = .outA := majorityAnswer_eq_outA_of_gt hm hA
  unfold PairResAnsSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  obtain ⟨hdec2, hdec1⟩ :=
    phase4_decide_odd_lower_median_misorder_writes_outA hodd hMis hu_med
  apply phase4_propagate_preserves_PairResAns (m₀ := m₀)
  · rw [hdec1]; exact hRes v
  · rw [hdec2]; exact Or.inl hm0.symm

/-- Even non-boundary lower-median A-major misorder is `PairResAnsSafe_tau (τ := τ)`:
decision is a no-op, both output answers are the (swapped) originals. -/
theorem PairResAnsSafe_of_even_lower_nonboundary_Amajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hA : nAOf D > nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hu_lower : rank1 D u = n / 2)
    (hv_not_upper : rank1 D v ≠ n / 2 + 1) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D u v := by
  unfold PairResAnsSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  rw [phase4_decide_even_lower_nonboundary_noop heven hMis hu_lower hv_not_upper]
  exact phase4_propagate_preserves_PairResAns
    (m₀ := m₀) (hRes v) (hRes u)

/-- Nonmedian misorder is `PairResAnsSafe_tau (τ := τ)`: decision is a no-op, both
output answers are the (swapped) originals, each in `{m₀, .phi}` by
`hRes`. -/
theorem PairResAnsSafe_of_nonmedian_misorder_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hMis : MisorderedPair D (u, v))
    (hu_ne_med : rank1 D u ≠ ceilHalf n)
    (hv_ne_med : rank1 D v ≠ ceilHalf n) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D u v := by
  unfold PairResAnsSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  rw [phase4_decide_noop_of_nonmedian_misordered hMis hu_ne_med hv_ne_med]
  exact phase4_propagate_preserves_PairResAns
    (m₀ := m₀) (hRes v) (hRes u)

theorem even_Amajor_all_touch_lower_exists_lower_nonboundary_misorder_tau
    {D : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n)
    (hS : InSrank D)
    (heven : n % 2 = 0)
    (hA : nAOf D > nBOf D)
    (hMisExists : ∃ u v : Fin n, MisorderedPair D (u, v))
    (hAllTouch : ∀ u v : Fin n, MisorderedPair D (u, v) →
      (D u).1.rank.val = ceilHalf n - 1 ∨ (D v).1.rank.val = ceilHalf n - 1) :
    ∃ u v : Fin n,
      MisorderedPair D (u, v) ∧
      (D u).1.rank.val = n / 2 - 1 ∧ (D v).1.rank.val ≠ n / 2 := by
  classical
  have hcm : ceilHalf n - 1 = n / 2 - 1 := by unfold ceilHalf; omega
  obtain ⟨u₀, v₀, hMis₀⟩ := hMisExists
  have hu₀B : (D u₀).2 = Opinion.B := hMis₀.1
  have hv₀A : (D v₀).2 = Opinion.A := hMis₀.2.1
  have hlt₀ : (D u₀).1.rank < (D v₀).1.rank := hMis₀.2.2
  have hlt₀' : (D u₀).1.rank.val < (D v₀).1.rank.val := hlt₀
  have hMisP : MisorderedPair D (u₀, v₀) := ⟨hu₀B, hv₀A, hlt₀⟩
  have hsum := nAOf_add_nBOf D
  rcases hAllTouch u₀ v₀ hMisP with hu_med | hv_med
  · -- u₀ B at lower median (n/2-1).  Find an A strictly above rank n/2.
    rw [hcm] at hu_med
    -- median rank n/2-1 is u₀, which is B (not A): A's with rank ≤ n/2
    -- inject into {rank < n/2-1} ∪ {rank = n/2}, card ≤ n/2 < nA.
    have hAcard :
        (Finset.univ.filter
          (fun w : Fin n => (D w).2 = Opinion.A ∧ (D w).1.rank.val ≤ n / 2)).card
          < nAOf D := by
      have hsub :
          (Finset.univ.filter
            (fun w : Fin n => (D w).2 = Opinion.A ∧ (D w).1.rank.val ≤ n / 2)) ⊆
          (Finset.univ.filter (fun w : Fin n => (D w).1.rank.val < n / 2 - 1)) ∪
          (Finset.univ.filter (fun w : Fin n => (D w).1.rank.val = n / 2)) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨hwA, hwle⟩ := hw
        -- w is A; the median rank (n/2-1) is u₀ which is B, so rank_w ≠ n/2-1.
        have hw_ne_med : (D w).1.rank.val ≠ n / 2 - 1 := by
          intro heq
          have : w = u₀ :=
            hS.ranks_inj (Fin.ext (by rw [heq, hu_med]))
          rw [this] at hwA; rw [hu₀B] at hwA; exact Opinion.noConfusion hwA
        rcases lt_or_eq_of_le hwle with h | h
        · -- rank_w < n/2: either < n/2-1 or = n/2-1 (excluded).
          left; omega
        · right; exact h
      have hcard_le :
          ((Finset.univ.filter (fun w : Fin n => (D w).1.rank.val < n / 2 - 1)) ∪
            (Finset.univ.filter (fun w : Fin n => (D w).1.rank.val = n / 2))).card
            ≤ (n / 2 - 1) + 1 := by
        have h1 := hS.card_rank_lt (k := n / 2 - 1) (by omega)
        have h2 := hS.card_rank_eq_le_one (n / 2)
        have := Finset.card_union_le
          (Finset.univ.filter (fun w : Fin n => (D w).1.rank.val < n / 2 - 1))
          (Finset.univ.filter (fun w : Fin n => (D w).1.rank.val = n / 2))
        omega
      have hle := Finset.card_le_card hsub
      have hchain : (Finset.univ.filter
          (fun w : Fin n => (D w).2 = Opinion.A ∧ (D w).1.rank.val ≤ n / 2)).card
          ≤ (n / 2 - 1) + 1 := le_trans hle hcard_le
      omega
    obtain ⟨y, hyA, hy_gt⟩ := exists_A_rank_gt hAcard
    -- y is A, rank_y > n/2 > n/2-1 = rank_u₀.  Misorder (u₀, y).
    have hru : (D u₀).1.rank.val = n / 2 - 1 := hu_med
    have hlt_uy : (D u₀).1.rank.val < (D y).1.rank.val := by omega
    refine ⟨u₀, y, ⟨hu₀B, hyA, Fin.lt_def.mpr hlt_uy⟩, hu_med, ?_⟩
    omega
  · -- v₀ A at lower median → nA bound contradicts A-major.
    exfalso
    rw [hcm] at hv_med
    have hu_nm : (D u₀).1.rank.val ≠ ceilHalf n - 1 := by rw [hcm]; omega
    have hbound := nA_le_of_nonmedian_B hS hAllTouch hu₀B hu_nm
    omega

/-! #### Final: `exists_answer_safe_misordered_pair_tau`

This is exactly the `hSelect` slot shape of
`all_resetting_uniform_consensus_final`.  Case-split on non-median /
parity / majority, then apply the counting + `PairResAnsSafe_tau (τ := τ)` lemmas. -/

/-- Odd upper-median B-major misorder is `PairResAnsSafe_tau (τ := τ)`: decision writes
`.outB = m₀` to the median-rank component. -/
theorem PairResAnsSafe_of_odd_upper_median_Bmajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    {u v : Fin n}
    (hm : m₀ = majorityAnswer D)
    (hB : nAOf D < nBOf D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hv_med : rank1 D v = ceilHalf n) :
    PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) m₀ D u v := by
  have hm0 : m₀ = .outB := majorityAnswer_eq_outB_of_lt hm hB
  unfold PairResAnsSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  obtain ⟨hdec1, hdec2⟩ :=
    phase4_decide_odd_upper_median_misorder_writes_outB hodd hMis hv_med
  apply phase4_propagate_preserves_PairResAns (m₀ := m₀)
  · rw [hdec1]; exact Or.inl hm0.symm
  · rw [hdec2]; exact hRes u

theorem PairNoPhiSafe_of_odd_upper_median_Bmajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hv_med : rank1 D v = ceilHalf n) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  unfold PairNoPhiSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  obtain ⟨hdec1, hdec2⟩ :=
    phase4_decide_odd_upper_median_misorder_writes_outB hodd hMis hv_med
  apply phase4_propagate_preserves_noPhi (Rmax := Rmax)
  · rw [hdec1]; decide
  · rw [hdec2]; exact hNoPhi u

theorem PairNoPhiSafe_of_nonmedian_misorder_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hMis : MisorderedPair D (u, v))
    (hu_ne_med : rank1 D u ≠ ceilHalf n)
    (hv_ne_med : rank1 D v ≠ ceilHalf n) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  unfold PairNoPhiSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  rw [phase4_decide_noop_of_nonmedian_misordered hMis hu_ne_med hv_ne_med]
  exact phase4_propagate_preserves_noPhi (Rmax := Rmax) (hNoPhi v) (hNoPhi u)

theorem PairNoPhiSafe_of_even_v_lower_Bmajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hv_lower : rank1 D v = n / 2) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  unfold PairNoPhiSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  rw [phase4_decide_even_v_lower_noop heven hMis hv_lower]
  exact phase4_propagate_preserves_noPhi (Rmax := Rmax) (hNoPhi v) (hNoPhi u)

/-! #### Counting infrastructure (pure finite rank/input arithmetic) -/


theorem PairNoPhiSafe_of_even_boundary_tie_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hu_lower : rank1 D u = n / 2)
    (hv_upper : rank1 D v = n / 2 + 1) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  unfold PairNoPhiSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  obtain ⟨hdec1, hdec2⟩ :=
    phase4_decide_even_boundary_tie_writes_outT heven hMis hu_lower hv_upper
  apply phase4_propagate_preserves_noPhi (Rmax := Rmax)
  · rw [hdec1]; decide
  · rw [hdec2]; decide

theorem PairNoPhiSafe_of_even_lower_nonboundary_Amajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (heven : n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hu_lower : rank1 D u = n / 2)
    (hv_not_upper : rank1 D v ≠ n / 2 + 1) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  unfold PairNoPhiSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  rw [phase4_decide_even_lower_nonboundary_noop heven hMis hu_lower hv_not_upper]
  exact phase4_propagate_preserves_noPhi (Rmax := Rmax) (hNoPhi v) (hNoPhi u)

/-- Under `InSrank` and a misordered pair, `transitionPEM` reduces to
`phase4_propagate (phase4_decide (swap))` where the swap is the reversed
state pair. -/
theorem PairNoPhiSafe_of_odd_lower_median_Amajor_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hodd : ¬ n % 2 = 0)
    (hMis : MisorderedPair D (u, v))
    (hu_med : rank1 D u = ceilHalf n) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  unfold PairNoPhiSafe_tau
  rw [transitionPEM_InSrank_misordered_eq_propagate_decide_tau hS hMis]
  obtain ⟨hdec2, hdec1⟩ :=
    phase4_decide_odd_lower_median_misorder_writes_outA hodd hMis hu_med
  apply phase4_propagate_preserves_noPhi (Rmax := Rmax)
  · rw [hdec1]; exact hNoPhi v
  · rw [hdec2]; decide

theorem PairNoPhiSafe_of_answer_safe_misorder_case_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hS : InSrank D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hMis : MisorderedPair D (u, v))
    (hcase :
      (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (D v).1.timer) ∨
      (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
        1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n))) :
    PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) D u v := by
  classical
  rcases hcase with hnon | hrest
  · exact PairNoPhiSafe_of_nonmedian_misorder_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi hMis (by simpa [rank1] using hnon.1)
      (by simpa [rank1] using hnon.2)
  rcases hrest with hoddLower | hrest
  · rcases hoddLower with ⟨hodd, huMed, _hvNotMax, _htu⟩
    exact PairNoPhiSafe_of_odd_lower_median_Amajor_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi hodd hMis (by simpa [rank1] using huMed)
  rcases hrest with hoddLowerMax | hrest
  · rcases hoddLowerMax with ⟨hodd, huMed, _hvMax, _htu⟩
    exact PairNoPhiSafe_of_odd_lower_median_Amajor_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi hodd hMis (by simpa [rank1] using huMed)
  rcases hrest with hevenBoundary | hrest
  · rcases hevenBoundary with ⟨heven, huLower, hvUpper, _⟩
    exact PairNoPhiSafe_of_even_boundary_tie_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS heven hMis (by simpa [rank1] using huLower)
      (by simpa [rank1] using hvUpper)
  rcases hrest with hoddUpper | hrest
  · rcases hoddUpper with ⟨hodd, hvMed, _htv⟩
    exact PairNoPhiSafe_of_odd_upper_median_Bmajor_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi hodd hMis (by simpa [rank1] using hvMed)
  rcases hrest with hevenVLower | hrest
  · rcases hevenVLower with ⟨heven, hvLower, _htv, _⟩
    exact PairNoPhiSafe_of_even_v_lower_Bmajor_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi heven hMis (by simpa [rank1] using hvLower)
  rcases hrest with hevenLower | hevenLowerMax
  · rcases hevenLower with ⟨heven, huLower, hvNotUpper, _hvNotMax, _htu, _⟩
    exact PairNoPhiSafe_of_even_lower_nonboundary_Amajor_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi heven hMis (by simpa [rank1] using huLower)
      (by simpa [rank1] using hvNotUpper)
  · rcases hevenLowerMax with ⟨heven, huLower, hvMax, _htu, _⟩
    have hvNotUpper : (D v).1.rank.val + 1 ≠ n / 2 + 1 := by
      intro hvUpper
      omega
    exact PairNoPhiSafe_of_even_lower_nonboundary_Amajor_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hS hNoPhi heven hMis (by simpa [rank1] using huLower)
      (by simpa [rank1] using hvNotUpper)


set_option maxHeartbeats 1600000 in
theorem exists_answer_safe_misordered_pair_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hTimer : ∀ μ : Fin n, rank1 D μ = ceilHalf n → 2 ≤ (D μ).1.timer)
    (hNotSwap : ¬ InSswap D) :
    ∃ u v : Fin n,
      MisorderedPair D (u, v) ∧
      (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (D v).1.timer) ∨
      (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
        1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
      PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ D u v := by
  classical
  have hn0 : 0 < n := by omega
  -- 1. Standard inversion extraction.
  obtain ⟨u₀, v₀, hMis₀⟩ := exists_misordered_of_not_InSswap hS hNotSwap
  -- 2. First try a non-median misorder.
  by_cases hNonMed :
      ∃ u v : Fin n,
        MisorderedPair D (u, v) ∧
        rank1 D u ≠ ceilHalf n ∧ rank1 D v ≠ ceilHalf n
  · obtain ⟨u, v, hMis, huN, hvN⟩ := hNonMed
    refine ⟨u, v, hMis, Or.inl ⟨huN, hvN⟩,
      PairResAnsSafe_of_nonmedian_misorder_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hRes hMis huN hvN⟩
  · -- 3. Otherwise every misorder touches the (lower) median rank.
    have hAllTouch :
        ∀ u v : Fin n, MisorderedPair D (u, v) →
          (D u).1.rank.val = ceilHalf n - 1 ∨ (D v).1.rank.val = ceilHalf n - 1 := by
      intro u v hMis
      by_contra hbad
      push_neg at hbad
      refine hNonMed ⟨u, v, hMis, ?_, ?_⟩
      · intro hc; exact hbad.1 ((rank1_eq_ceilHalf_iff hn0).mp hc)
      · intro hc; exact hbad.2 ((rank1_eq_ceilHalf_iff hn0).mp hc)
    by_cases heven : n % 2 = 0
    · -- Even
      have hcm : ceilHalf n - 1 = n / 2 - 1 := by unfold ceilHalf; omega
      have hch : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even heven
      by_cases hTie : nAOf D = nBOf D
      · obtain ⟨u, v, hMis, huL, hvU⟩ :=
          even_tie_all_touch_lower_exists_boundary_misorder
            hn4 hS heven hTie ⟨u₀, v₀, hMis₀⟩ hAllTouch
        refine ⟨u, v, hMis, ?_, ?_⟩
        · refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨heven, ?_, ?_, hn4⟩
          · omega
          · omega
        · exact PairResAnsSafe_of_even_boundary_tie_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hTie hS hRes heven hMis (by unfold rank1; omega)
              (by unfold rank1; omega)
      · by_cases hA : nAOf D > nBOf D
        · obtain ⟨u, v, hMis, huL, hvNB⟩ :=
            even_Amajor_all_touch_lower_exists_lower_nonboundary_misorder_tau
              hn4 hS heven hA ⟨u₀, v₀, hMis₀⟩ hAllTouch
          have hu_med1 : rank1 D u = ceilHalf n :=
            (rank1_eq_ceilHalf_iff hn0).mpr (by omega)
          have htu2 : 2 ≤ (D u).1.timer := hTimer u hu_med1
          refine ⟨u, v, hMis, ?_, ?_⟩
          · by_cases hvMax : (D v).1.rank.val + 1 = n
            · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
                ⟨heven, by omega, hvMax, htu2, hn4⟩
            · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
                ⟨heven, by omega, by omega, hvMax, by omega, hn4⟩
          · exact PairResAnsSafe_of_even_lower_nonboundary_Amajor_tau
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hm hA hS hRes heven hMis (by unfold rank1; omega)
                (by unfold rank1; omega)
        · have hB : nAOf D < nBOf D := by omega
          obtain ⟨u, v, hMis, hvL⟩ :=
            even_Bmajor_all_touch_lower_exists_v_lower_misorder
              hn4 hS heven hB ⟨u₀, v₀, hMis₀⟩ hAllTouch
          have hv_med1 : rank1 D v = ceilHalf n :=
            (rank1_eq_ceilHalf_iff hn0).mpr (by omega)
          have htv2 : 2 ≤ (D v).1.timer := hTimer v hv_med1
          refine ⟨u, v, hMis, ?_, ?_⟩
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
              ⟨heven, by omega, by omega, hn4⟩
          · exact PairResAnsSafe_of_even_v_lower_Bmajor_tau
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hm hB hS hRes heven hMis (by unfold rank1; omega)
    · -- Odd
      have hodd : ¬ n % 2 = 0 := heven
      by_cases hA : nAOf D > nBOf D
      · obtain ⟨u, v, hMis, huMed⟩ :=
          odd_Amajor_all_touch_median_exists_lower_median_misorder
            hn0 hS hodd hA ⟨u₀, v₀, hMis₀⟩ hAllTouch
        have hu_med1 : rank1 D u = ceilHalf n :=
          (rank1_eq_ceilHalf_iff hn0).mpr huMed
        have htu2 : 2 ≤ (D u).1.timer := hTimer u hu_med1
        refine ⟨u, v, hMis, ?_, ?_⟩
        · by_cases hvMax : (D v).1.rank.val + 1 = n
          · exact Or.inr <| Or.inr <| Or.inl
              ⟨hodd, by unfold rank1 at hu_med1; omega, hvMax, htu2⟩
          · exact Or.inr <| Or.inl
              ⟨hodd, by unfold rank1 at hu_med1; omega, hvMax, by omega⟩
        · exact PairResAnsSafe_of_odd_lower_median_Amajor_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hA hS hRes hodd hMis hu_med1
      · have hB : nAOf D < nBOf D := by
          have hsum := nAOf_add_nBOf D; omega
        obtain ⟨u, v, hMis, hvMed⟩ :=
          odd_Bmajor_all_touch_median_exists_upper_median_misorder
            hn0 hS hodd hB ⟨u₀, v₀, hMis₀⟩ hAllTouch
        have hv_med1 : rank1 D v = ceilHalf n :=
          (rank1_eq_ceilHalf_iff hn0).mpr hvMed
        have htv2 : 2 ≤ (D v).1.timer := hTimer v hv_med1
        refine ⟨u, v, hMis, ?_, ?_⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨hodd, by unfold rank1 at hv_med1; omega, by omega⟩
        · exact PairResAnsSafe_of_odd_upper_median_Bmajor_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hB hS hRes hodd hMis hv_med1

#print axioms exists_answer_safe_misordered_pair_tau


theorem exists_answer_safe_noPhi_misordered_pair_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer D)
    (hS : InSrank D)
    (hRes : ResAns m₀ D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hTimer : ∀ μ : Fin n, rank1 D μ = ceilHalf n → 2 ≤ (D μ).1.timer)
    (hNotSwap : ¬ InSswap D) :
    ∃ u v : Fin n,
      MisorderedPair D (u, v) ∧
      (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (D v).1.timer) ∨
      (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
        1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
      PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ D u v ∧
      PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) D u v := by
  classical
  obtain ⟨u, v, hMis, hcase, hSafeRes⟩ :=
    exists_answer_safe_misordered_pair_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hm hS hRes hTimer hNotSwap
  have hSafeNoPhi :
      PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) D u v := by
    rcases hcase with hnon | hrest
    · exact PairNoPhiSafe_of_nonmedian_misorder_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi hMis (by simpa [rank1] using hnon.1)
        (by simpa [rank1] using hnon.2)
    rcases hrest with hoddLower | hrest
    · rcases hoddLower with ⟨hodd, huMed, _hvNotMax, _htu⟩
      exact PairNoPhiSafe_of_odd_lower_median_Amajor_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi hodd hMis (by simpa [rank1] using huMed)
    rcases hrest with hoddLowerMax | hrest
    · rcases hoddLowerMax with ⟨hodd, huMed, _hvMax, _htu⟩
      exact PairNoPhiSafe_of_odd_lower_median_Amajor_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi hodd hMis (by simpa [rank1] using huMed)
    rcases hrest with hevenBoundary | hrest
    · rcases hevenBoundary with ⟨heven, huLower, hvUpper, _⟩
      exact PairNoPhiSafe_of_even_boundary_tie_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS heven hMis (by simpa [rank1] using huLower)
        (by simpa [rank1] using hvUpper)
    rcases hrest with hoddUpper | hrest
    · rcases hoddUpper with ⟨hodd, hvMed, _htv⟩
      exact PairNoPhiSafe_of_odd_upper_median_Bmajor_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi hodd hMis (by simpa [rank1] using hvMed)
    rcases hrest with hevenVLower | hrest
    · rcases hevenVLower with ⟨heven, hvLower, _htv, _⟩
      exact PairNoPhiSafe_of_even_v_lower_Bmajor_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi heven hMis (by simpa [rank1] using hvLower)
    rcases hrest with hevenLower | hevenLowerMax
    · rcases hevenLower with ⟨heven, huLower, hvNotUpper, _hvNotMax, _htu, _⟩
      exact PairNoPhiSafe_of_even_lower_nonboundary_Amajor_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi heven hMis (by simpa [rank1] using huLower)
        (by simpa [rank1] using hvNotUpper)
    · rcases hevenLowerMax with ⟨heven, huLower, hvMax, _htu, _⟩
      have hvNotUpper : (D v).1.rank.val + 1 ≠ n / 2 + 1 := by
        intro hvUpper
        have hnHalfLt : n / 2 + 1 < n := by omega
        omega
      exact PairNoPhiSafe_of_even_lower_nonboundary_Amajor_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hNoPhi heven hMis (by simpa [rank1] using huLower)
        (by simpa [rank1] using hvNotUpper)
  exact ⟨u, v, hMis, hcase, hSafeRes, hSafeNoPhi⟩


set_option maxHeartbeats 1600000 in
theorem exists_answer_safe_noPhi_misordered_pair_of_swapInv_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n} {m₀ : Answer}
    (hm : m₀ = majorityAnswer D)
    (hInv : SwapInv D)
    (hRes : ResAns m₀ D)
    (hNoPhi : ∀ w : Fin n, (D w).1.answer ≠ .phi)
    (hNotSwap : ¬ InSswap D) :
    ∃ u v : Fin n,
      MisorderedPair D (u, v) ∧
      (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (D v).1.timer) ∨
      (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
        1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
        (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) ∧
      PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) m₀ D u v ∧
      PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) D u v := by
  classical
  obtain ⟨hS, hTimerState⟩ := hInv
  rcases hTimerState with hTimer2 | hRight
  · exact exists_answer_safe_noPhi_misordered_pair_tau
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hm hS hRes hNoPhi (by intro μ hμ; exact hTimer2 μ hμ) hNotSwap
  obtain ⟨hTimer1, hMaxB⟩ := hRight
  have hn0 : 0 < n := by omega
  obtain ⟨u₀, v₀, hMis₀⟩ := exists_misordered_of_not_InSswap hS hNotSwap
  by_cases hNonMed :
      ∃ u v : Fin n,
        MisorderedPair D (u, v) ∧
        rank1 D u ≠ ceilHalf n ∧ rank1 D v ≠ ceilHalf n
  · obtain ⟨u, v, hMis, huN, hvN⟩ := hNonMed
    have hcase :
        (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
        (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
          (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
        (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
          (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
        (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
          (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
        (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
          1 ≤ (D v).1.timer) ∨
        (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
          1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
        (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
          (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
          1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
        (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
          (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) := Or.inl ⟨huN, hvN⟩
    refine ⟨u, v, hMis, hcase, ?_, ?_⟩
    · exact PairResAnsSafe_of_nonmedian_misorder_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hS hRes hMis huN hvN
    · exact PairNoPhiSafe_of_answer_safe_misorder_case_tau
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hS hNoPhi hMis hcase
  have hAllTouch :
      ∀ u v : Fin n, MisorderedPair D (u, v) →
        (D u).1.rank.val = ceilHalf n - 1 ∨ (D v).1.rank.val = ceilHalf n - 1 := by
    intro u v hMis
    by_contra hbad
    push_neg at hbad
    refine hNonMed ⟨u, v, hMis, ?_, ?_⟩
    · intro hc; exact hbad.1 ((rank1_eq_ceilHalf_iff hn0).mp hc)
    · intro hc; exact hbad.2 ((rank1_eq_ceilHalf_iff hn0).mp hc)
  by_cases heven : n % 2 = 0
  · by_cases hTie : nAOf D = nBOf D
    · obtain ⟨u, v, hMis, huL, hvU⟩ :=
        even_tie_all_touch_lower_exists_boundary_misorder
          hn4 hS heven hTie ⟨u₀, v₀, hMis₀⟩ hAllTouch
      have hcase :
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) := by
        exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨heven, by omega, by omega, hn4⟩
      refine ⟨u, v, hMis, hcase, ?_, ?_⟩
      · exact PairResAnsSafe_of_even_boundary_tie_tau
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hm hTie hS hRes heven hMis (by unfold rank1; omega)
          (by unfold rank1; omega)
      · exact PairNoPhiSafe_of_answer_safe_misorder_case_tau
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hS hNoPhi hMis hcase
    · by_cases hA : nAOf D > nBOf D
      · obtain ⟨u, v, hMis, huL, hvNB⟩ :=
          even_Amajor_all_touch_lower_exists_lower_nonboundary_misorder_tau
            hn4 hS heven hA ⟨u₀, v₀, hMis₀⟩ hAllTouch
        have hu_med1 : rank1 D u = ceilHalf n :=
          (rank1_eq_ceilHalf_iff hn0).mpr (by
            have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even heven
            omega)
        have htu1 : 1 ≤ (D u).1.timer := hTimer1 u hu_med1
        have hvMaxFalse : (D v).1.rank.val + 1 ≠ n := by
          intro hvMax
          rcases no_misorder_at_max_with_B hS hn0 hMaxB u v hMis with huNotMed | hvNotMax
          · exact huNotMed hu_med1
          · exact hvNotMax hvMax
        have hcase :
            (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
            (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
              (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
            (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
              (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
            (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
              (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
            (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
              1 ≤ (D v).1.timer) ∨
            (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
              1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
            (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
              (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
              1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
            (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
              (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) := by
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨heven, by omega, by omega, hvMaxFalse, htu1, hn4⟩
        refine ⟨u, v, hMis, hcase, ?_, ?_⟩
        · exact PairResAnsSafe_of_even_lower_nonboundary_Amajor_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hA hS hRes heven hMis (by unfold rank1; omega)
            (by unfold rank1; omega)
        · exact PairNoPhiSafe_of_answer_safe_misorder_case_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hS hNoPhi hMis hcase
      · have hB : nAOf D < nBOf D := by omega
        obtain ⟨u, v, hMis, hvL⟩ :=
          even_Bmajor_all_touch_lower_exists_v_lower_misorder
            hn4 hS heven hB ⟨u₀, v₀, hMis₀⟩ hAllTouch
        have hv_med1 : rank1 D v = ceilHalf n :=
          (rank1_eq_ceilHalf_iff hn0).mpr (by
            have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even heven
            omega)
        have htv1 : 1 ≤ (D v).1.timer := hTimer1 v hv_med1
        have hcase :
            (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
            (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
              (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
            (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
              (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
            (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
              (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
            (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
              1 ≤ (D v).1.timer) ∨
            (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
              1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
            (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
              (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
              1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
            (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
              (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) := by
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨heven, by omega, htv1, hn4⟩
        refine ⟨u, v, hMis, hcase, ?_, ?_⟩
        · exact PairResAnsSafe_of_even_v_lower_Bmajor_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hm hB hS hRes heven hMis (by unfold rank1; omega)
        · exact PairNoPhiSafe_of_answer_safe_misorder_case_tau
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hS hNoPhi hMis hcase
  · have hodd : ¬ n % 2 = 0 := heven
    by_cases hA : nAOf D > nBOf D
    · obtain ⟨u, v, hMis, huMed⟩ :=
        odd_Amajor_all_touch_median_exists_lower_median_misorder
          hn0 hS hodd hA ⟨u₀, v₀, hMis₀⟩ hAllTouch
      have hu_med1 : rank1 D u = ceilHalf n :=
        (rank1_eq_ceilHalf_iff hn0).mpr huMed
      have htu1 : 1 ≤ (D u).1.timer := hTimer1 u hu_med1
      have hvMaxFalse : (D v).1.rank.val + 1 ≠ n := by
        intro hvMax
        rcases no_misorder_at_max_with_B hS hn0 hMaxB u v hMis with huNotMed | hvNotMax
        · exact huNotMed hu_med1
        · exact hvNotMax hvMax
      have hcase :
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) := by
        exact Or.inr <| Or.inl ⟨hodd, by unfold rank1 at hu_med1; omega,
          hvMaxFalse, htu1⟩
      refine ⟨u, v, hMis, hcase, ?_, ?_⟩
      · exact PairResAnsSafe_of_odd_lower_median_Amajor_tau
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hm hA hS hRes hodd hMis hu_med1
      · exact PairNoPhiSafe_of_answer_safe_misorder_case_tau
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hS hNoPhi hMis hcase
    · have hB : nAOf D < nBOf D := by
        have hsum := nAOf_add_nBOf D; omega
      obtain ⟨u, v, hMis, hvMed⟩ :=
        odd_Bmajor_all_touch_median_exists_upper_median_misorder
          hn0 hS hodd hB ⟨u₀, v₀, hMis₀⟩ hAllTouch
      have hv_med1 : rank1 D v = ceilHalf n :=
        (rank1_eq_ceilHalf_iff hn0).mpr hvMed
      have htv1 : 1 ≤ (D v).1.timer := hTimer1 v hv_med1
      have hcase :
          (((D u).1.rank.val + 1 ≠ ceilHalf n ∧ (D v).1.rank.val + 1 ≠ ceilHalf n) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 ≠ n ∧ 1 ≤ (D u).1.timer) ∨
          (¬ n % 2 = 0 ∧ (D u).1.rank.val + 1 = ceilHalf n ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
          (¬ n % 2 = 0 ∧ (D v).1.rank.val + 1 = ceilHalf n ∧
            1 ≤ (D v).1.timer) ∨
          (n % 2 = 0 ∧ (D v).1.rank.val + 1 = n / 2 ∧
            1 ≤ (D v).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (D v).1.rank.val + 1 ≠ n ∧
            1 ≤ (D u).1.timer ∧ 4 ≤ n) ∨
          (n % 2 = 0 ∧ (D u).1.rank.val + 1 = n / 2 ∧
            (D v).1.rank.val + 1 = n ∧ 2 ≤ (D u).1.timer ∧ 4 ≤ n)) := by
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨hodd, by unfold rank1 at hv_med1; omega, htv1⟩
      refine ⟨u, v, hMis, hcase, ?_, ?_⟩
      · exact PairResAnsSafe_of_odd_upper_median_Bmajor_tau
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hm hB hS hRes hodd hMis hv_med1
      · exact PairNoPhiSafe_of_answer_safe_misorder_case_tau
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hS hNoPhi hMis hcase



set_option maxHeartbeats 8000000 in
theorem InSrank_to_InSswap_ResAns_noPhi_with_swapInv_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n) :
    ∀ C : Config (AgentState n) Opinion n,
      SwapInv C →
      ResAns m₀ C →
      (∀ w : Fin n, (C w).1.answer ≠ .phi) →
      m₀ = majorityAnswer C →
      ∃ L : List (Fin n × Fin n),
        let E := runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L
        InSswap E ∧
        ResAns m₀ E ∧
        (∀ w : Fin n, (E w).1.answer ≠ .phi) ∧
        majorityAnswer E = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  suffices h : ∀ k : ℕ, ∀ C : Config (AgentState n) Opinion n,
      SwapInv C →
      ResAns m₀ C →
      (∀ w : Fin n, (C w).1.answer ≠ .phi) →
      m₀ = majorityAnswer C →
      misorderedCount C ≤ k →
      ∃ L : List (Fin n × Fin n),
        InSswap (runPairs P C L) ∧
        ResAns m₀ (runPairs P C L) ∧
        (∀ w : Fin n, ((runPairs P C L) w).1.answer ≠ .phi) ∧
        majorityAnswer (runPairs P C L) = majorityAnswer C by
    intro C hInv hRes hNoPhi hm
    exact h (misorderedCount C) C hInv hRes hNoPhi hm le_rfl
  intro k
  induction k with
  | zero =>
    intro C hInv hRes hNoPhi _hm hle
    by_cases hSwap : InSswap C
    · exact ⟨[], by simpa [hP] using hSwap, by simpa [hP] using hRes,
        by simpa [hP] using hNoPhi, by simp⟩
    · have h0 : misorderedCount C = 0 := Nat.le_zero.mp hle
      obtain ⟨u, v, hMis, _, _, _⟩ :=
        exists_answer_safe_noPhi_misordered_pair_of_swapInv_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 _hm hInv hRes hNoPhi hSwap
      have := (misorderedCount_eq_zero_iff C).mp h0 u v
      exact absurd hMis this
  | succ k ih =>
    intro C hInv hRes hNoPhi hm hle
    by_cases hSwap : InSswap C
    · exact ⟨[], by simpa [hP] using hSwap, by simpa [hP] using hRes,
        by simpa [hP] using hNoPhi, by simp⟩
    · obtain ⟨u, v, hMis, hcase, hSafeRes, hSafeNoPhi⟩ :=
        exists_answer_safe_noPhi_misordered_pair_of_swapInv_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hm hInv hRes hNoPhi hSwap
      obtain ⟨hSrank', hRes', hNoPhi', hdec⟩ :=
        answer_noPhi_safe_swap_step_decreases_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hInv.1 hMis hcase hSafeRes hSafeNoPhi hRes hNoPhi
      have hInv' : SwapInv (C.step P u v) := by
        refine ⟨by simpa [hP] using hSrank', ?_⟩
        rcases hInv.2 with hTimer2 | hRight
        · by_cases hvMax : (C v).1.rank.val + 1 = n
          · exact Or.inr
              (by
                simpa [hP] using
                  (step_at_v_max_gives_right_disjunct
                    (trank := τ) (Rmax := Rmax)
                    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                    rankDeltaOSSR_satisfies_fix hInv.1 hMis hvMax hn4 hTimer2))
          · have huNotMax : (C u).1.rank.val + 1 ≠ n :=
              fun huMax => absurd hMis (not_misordered_fst_at_max_rank huMax)
            exact Or.inl
              (by
                simpa [hP] using
                  (step_at_misorder_preserves_timer_geK
                    (trank := τ) (Rmax := Rmax)
                    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                    rankDeltaOSSR_satisfies_fix hInv.1 hMis huNotMax hvMax
                    hTimer2))
        · obtain ⟨hTimer1, hMaxB⟩ := hRight
          obtain ⟨q, hqMax, hqB⟩ := hMaxB
          have huNotMax : (C u).1.rank.val + 1 ≠ n :=
            fun huMax => absurd hMis (not_misordered_fst_at_max_rank huMax)
          have hvNotMax : (C v).1.rank.val + 1 ≠ n := by
            intro hvMax
            have : (C v).2 = Opinion.B := by
              have hvq : v = q := by
                have hvRank : (C v).1.rank.val = n - 1 := by omega
                have hqRank : (C q).1.rank.val = n - 1 := by omega
                apply hInv.1.ranks_inj
                apply Fin.ext
                exact hvRank.trans hqRank.symm
              rw [hvq]; exact hqB
            exact absurd hMis (not_misordered_snd_at_max_with_B this)
          exact Or.inr
            ⟨by
              simpa [hP] using
                (step_at_misorder_preserves_timer_geK
                  (trank := τ) (Rmax := Rmax)
                  (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                  rankDeltaOSSR_satisfies_fix hInv.1 hMis huNotMax hvNotMax
                  hTimer1),
             ⟨q, by
              simpa [hP] using
                (step_at_misorder_preserves_max_B
                  (trank := τ) (Rmax := Rmax)
                  (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
                  hInv.1 hMis hqMax hqB)⟩⟩
      have hm' : m₀ = majorityAnswer (C.step P u v) := by
        rw [majorityAnswer_step_eq C u v]
        exact hm
      have hle' : misorderedCount (C.step P u v) ≤ k := by
        simp only [hP] at hdec ⊢
        omega
      obtain ⟨L, hSwapL, hResL, hNoPhiL, hMajL⟩ :=
        ih (C.step P u v) hInv' (by simpa [hP] using hRes')
          (by simpa [hP] using hNoPhi') hm' hle'
      refine ⟨(u, v) :: L, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_cons]; exact hSwapL
      · rw [runPairs_cons]; exact hResL
      · rw [runPairs_cons]; exact hNoPhiL
      · rw [runPairs_cons, hMajL]
        simp only [hP]
        exact majorityAnswer_step_eq C u v

theorem InSrank_to_InSswap_ResAns_with_inv_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C)
    (hRes : ResAns m₀ C)
    (hNoPhi : ∀ w : Fin n, (C w).1.answer ≠ .phi)
    (hm : m₀ = majorityAnswer C)
    (hTimer : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
      2 ≤ (C μ).1.timer) :
    ∃ L : List (Fin n × Fin n),
      let E := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap E ∧
      ResAns m₀ E ∧
      (∀ w : Fin n, (E w).1.answer ≠ .phi) ∧
      majorityAnswer E = majorityAnswer C :=
  InSrank_to_InSswap_ResAns_noPhi_with_swapInv_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) (m₀ := m₀)
    hn4 C ⟨hSrank, Or.inl hTimer⟩ hRes hNoPhi hm

/-- **CASE 2 — median-wrong decision step preserves `InSswap`, the
median-timer bound, `ResAns (majorityAnswer)`, and strictly decreases
`wrongAnswerCount`.**  The 3-branch mirror of `median_wrong_decision_step_tau (τ := τ)`
additionally certifying the reservoir invariant.  Unconditional,
non-circular. -/
theorem median_wrong_step_resAns_decrease_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (hNoTie : nAOf C ≠ nBOf C)
    (hC_timer : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                 (C μ).1.answer ≠ majorityAnswer C) :
    ∃ p : Fin n × Fin n,
      InSswap (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ∧
      ResAns (majorityAnswer (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2))
        (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ∧
      (∀ μ : Fin n,
        (C.step (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2 μ).1.rank.val + 1
            = ceilHalf n →
        1 ≤ (C.step (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2 μ).1.timer) ∧
      wrongAnswerCount (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) < wrongAnswerCount C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have hRfix := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn)
  obtain ⟨μ0, hμ0_med, hμ0_wrong⟩ := h_med_wrong
  -- `majorityAnswer` is step-invariant; reuse for the `ResAns` rewrite.
  have hmaj_step : ∀ u v : Fin n,
      majorityAnswer (C.step P u v) = majorityAnswer C := by
    intro u v; rw [hP]; exact majorityAnswer_step_eq C u v
  by_cases hpar : n % 2 = 0
  · by_cases hTie : nAOf C = nBOf C
    · -- Even, tie branch: both endpoints get `.outT = majorityAnswer C`.
      obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
        evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie
          ⟨μ0, hμ0_med, hμ0_wrong⟩
      have hsu := hC.allSettled u
      have hsv := hC.allSettled v
      have h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
        intro ⟨hxuB, _⟩
        have hsum := nAOf_add_nBOf C
        have : (C u).2 = Opinion.A := (hC.input_rank u).mpr (by omega)
        rw [this] at hxuB; cases hxuB
      obtain ⟨h_u, h_v, h_others, _h_inputs⟩ :=
        step_at_median_pair_even_disagreed_inputs
          (trank := τ) (Rmax := Rmax)
          hRfix huv hsu hsv hpar hu_med hv_upper h_disagree h_no_swap hn4
      have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hTie
      have h_dec := decision_step_at_median_pair_even_tie_decreases
        (trank := τ) (Rmax := Rmax) hRfix
        hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
      have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
      have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
      refine ⟨(u, v), h_dec.1, ?_,
        step_preserves_timer_no_max (trank := τ) (Rmax := Rmax)
          hRfix hC.toInSrank huv hu_no_max hv_no_max hC_timer,
        h_dec.2⟩
      -- ResAns: rewrite `majorityAnswer (step) = majorityAnswer C`.
      rw [hmaj_step]
      intro w
      by_cases hwu : w = u
      · left
        have hwa : (C.step P u v w).1.answer = .outT := by
          rw [hwu]
          have : (C.step P u v u).1 = {(C u).1 with answer := .outT} := h_u
          rw [this]
        rw [hwa, h_outT]
      · by_cases hwv : w = v
        · left
          have hwa : (C.step P u v w).1.answer = .outT := by
            rw [hwv]
            have : (C.step P u v v).1 = {(C v).1 with answer := .outT} := h_v
            rw [this]
          rw [hwa, h_outT]
        · have hww : (C.step P u v) w = C w := h_others w hwu hwv
          rw [show (C.step P u v w).1.answer = (C w).1.answer from
                by rw [hww]]
          exact hRes w
    · -- Even, strict-majority branch: both endpoints get
      -- `opinionToAnswer (C u).2 = majorityAnswer C`.
      obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
        evenCase_witness_when_median_wrong hC hpar hn4 hTie
          ⟨μ0, hμ0_med, hμ0_wrong⟩
      have hsu := hC.allSettled u
      have hsv := hC.allSettled v
      have hC'_eq := step_at_median_pair_even_agreed_inputs
        (trank := τ) (Rmax := Rmax)
        hRfix huv hsu hsv hpar hu_med hv_upper h_agree hn4
      have h_correct : opinionToAnswer (C u).2 = majorityAnswer C :=
        opinionToAnswer_lower_median_eq_majorityAnswer_even hC hu_med hpar hTie
      have h_dec := decision_step_at_median_pair_even_decreases
        (trank := τ) (Rmax := Rmax) hRfix
        hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
      have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
      have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
      refine ⟨(u, v), h_dec.1, ?_,
        step_preserves_timer_no_max (trank := τ) (Rmax := Rmax)
          hRfix hC.toInSrank huv hu_no_max hv_no_max hC_timer,
        h_dec.2⟩
      rw [hmaj_step]
      intro w
      have hval := congrFun hC'_eq w
      by_cases hwu : w = u
      · left
        have : (C.step P u v w).1.answer = opinionToAnswer (C u).2 := by
          rw [hval]; rw [if_pos hwu]
        rw [this]; exact h_correct
      · by_cases hwv : w = v
        · left
          have : (C.step P u v w).1.answer = opinionToAnswer (C u).2 := by
            rw [hval]; rw [if_neg hwu, if_pos hwv]
          rw [this]; exact h_correct
        · have hww : (C.step P u v w).1.answer = (C w).1.answer := by
            rw [hval]; rw [if_neg hwu, if_neg hwv]
          rw [hww]; exact hRes w
  · -- Odd branch: median μ' gets `opinionToAnswer (C μ').2 = majorityAnswer C`,
    -- partner `v` is left exactly unchanged.
    obtain ⟨μ', v, hμv, hμ'_med, hv_no_med, hv_no_max, h_rank_gt,
        h_timer, hμ'_wrong⟩ :=
      oddCase_witness_when_median_wrong_with_timer hC hpar
        (by omega : 3 ≤ n) ⟨μ0, hμ0_med, hμ0_wrong⟩ hC_timer
    have hsμ' := hC.allSettled μ'
    have hsv := hC.allSettled v
    have hC'_eq := step_at_median_no_swap_odd_v_not_max
      (trank := τ) (Rmax := Rmax)
      hRfix hμv hsμ' hsv hpar hμ'_med hv_no_med hv_no_max h_rank_gt h_timer
    have h_correct : opinionToAnswer (C μ').2 = majorityAnswer C :=
      opinionToAnswer_median_eq_majorityAnswer_odd hC hμ'_med hpar
    have h_step := decision_step_at_median_no_swap_odd_decreases
      (trank := τ) (Rmax := Rmax) hRfix
      hC hμv hpar hμ'_med hv_no_med hv_no_max h_rank_gt h_timer hμ'_wrong
    have hμ'_no_max : (C μ').1.rank.val + 1 ≠ n := by
      unfold ceilHalf at hμ'_med; omega
    refine ⟨(μ', v), h_step.1, ?_,
      step_preserves_timer_no_max (trank := τ) (Rmax := Rmax)
        hRfix hC.toInSrank hμv hμ'_no_max hv_no_max hC_timer,
      h_step.2⟩
    rw [hmaj_step]
    intro w
    have hval := congrFun hC'_eq w
    by_cases hwμ : w = μ'
    · left
      have : (C.step P μ' v w).1.answer = opinionToAnswer (C μ').2 := by
        rw [hval]; rw [if_pos hwμ]
      rw [this]; exact h_correct
    · by_cases hwv : w = v
      · have hww : (C.step P μ' v w).1.answer = (C v).1.answer := by
          rw [hval]; rw [if_neg hwμ, if_pos hwv]
        rw [hww]
        rcases hRes v with hm | hp
        · exact Or.inl hm
        · exact Or.inr hp
      · have hww : (C.step P μ' v w).1.answer = (C w).1.answer := by
          rw [hval]; rw [if_neg hwμ, if_neg hwv]
        rw [hww]; exact hRes w

/-- **`cycle_macro_discharge_tau` — the Phase-E reservoir-cycle macro-step,
matching the `hMacro` slot of `all_resetting_uniform_consensus_final_tau (τ := τ)`
exactly, with NO circular hypothesis.**

Carries only documented **non-circular structural** hypotheses:

* `hn4 : 4 ≤ n` — numeric.
* `hNoTie : ∀ D, InSswap D → nAOf D ≠ nBOf D` — the exact-majority
  structural assumption (used identically throughout this codebase); no
  consensus / epidemic / answer-stability content.
* `hResetLeaf` — the **timer-free** reservoir/reset renormalizer: from
  an `InSswap ∧ ResAns (majorityAnswer)` config with positive `phiCount`
  that is *either* median-*correct* *or* has *some median agent with
  `timer = 0`*, a finite execution reaches an
  `InSswap ∧ ResAns (majorityAnswer)` config with strictly smaller
  `phiCount`.  Both disjuncts are the `timer = 0`-compatible reset
  paths (the reset condition is `timer = 0 ∧ answer-mismatch`); the leaf
  carries **no** universal timer-live hypothesis.  This is the
  trigger-reset structural leaf the blueprint isolates (discharged green
  by `trigger_correct_reset_from_InSrank_tau (τ := τ)` /
  `all_resetting_from_seed_answer_aux_tau (τ := τ)` /
  `all_resetting_uniform_to_InSswap_ResAns_tau (τ := τ)`); it asserts **no** consensus
  / epidemic / `BurmanConvergence` / answer-stability / "∃ schedule
  reaching consensus for the goal" content — it is strictly weaker than,
  and non-circular with respect to, `hMacro` and the consensus engine.

Non-circular, sorry/axiom-free. -/
theorem cycle_macro_discharge_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hNoTie : ∀ D : Config (AgentState n) Opinion n,
      InSswap D → nAOf D ≠ nBOf D)
    (hResetLeaf :
      ∀ D : Config (AgentState n) Opinion n,
        InSswap D → ResAns (majorityAnswer D) D → 0 < phiCount D →
        -- timer-FREE reservoir/reset leaf: it fires on either the
        -- median-*correct* sub-case OR the median-wrong-*timer-0*
        -- sub-case (the two `timer = 0`-compatible reset paths).  It
        -- carries NO universal timer-live hypothesis (the removed false
        -- `hTimerLive`); the median-wrong-timer≥1 sub-case is the only
        -- one needing a *local* timer fact and is discharged here from
        -- the local `by_cases` directly, never assumed everywhere.
        ((∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
            (D μ).1.answer = majorityAnswer D) ∨
         (∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
            (D μ).1.timer = 0)) →
        ∃ (γ : DetScheduler n) (k : ℕ),
          (InSswap (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k) ∧
            ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k))
              (execution (protocolPEM n τ Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k)) ∧
          phiCount (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k) < phiCount D) :
    ∀ C : Config (AgentState n) Opinion n,
      (InSswap C ∧ ResAns (majorityAnswer C) C) → 0 < phiCount C →
      ∃ (γ : DetScheduler n) (k : ℕ),
        (InSswap (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) ∧
          ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k))
            (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k)) ∧
        phiCount (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) < phiCount C := by
  classical
  intro C ⟨hSswap, hRes⟩ hpos
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  -- Under `ResAns`, `phiCount = wrongAnswerCount`.
  have hphi_eq : phiCount C = wrongAnswerCount C :=
    phiCount_eq_wrongAnswerCount_of_resAns hRes
  have hwpos : 0 < wrongAnswerCount C := by rw [← hphi_eq]; exact hpos
  have hNoTieC : nAOf C ≠ nBOf C := hNoTie C hSswap
  by_cases hMedWrong :
      ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
        (C μ).1.answer ≠ majorityAnswer C
  · -- CASE 2: median wrong.  Case-split on the median timer *locally*
    -- (NO false universal `hTimerLive`).
    by_cases hTimerC :
        ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
          1 ≤ (C μ).1.timer
    · -- 2a: all median agents have timer ≥ 1 (local fact, derived from
      -- this `by_cases` branch — not an assumed universal).  One green
      -- median-wrong decision step strictly drops `phiCount`.
      obtain ⟨p, hSswap', hRes', _htimer', hdec⟩ :=
        median_wrong_step_resAns_decrease_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hRes hNoTieC hTimerC hMedWrong
      refine ⟨fun _ => p, 1, ⟨?_, ?_⟩, ?_⟩
      · show InSswap (execution P C (fun _ => p) 1)
        rw [show execution P C (fun _ => p) 1 = C.step P p.1 p.2 from rfl]
        simpa [hP] using hSswap'
      · show ResAns
          (majorityAnswer (execution P C (fun _ => p) 1))
          (execution P C (fun _ => p) 1)
        rw [show execution P C (fun _ => p) 1 = C.step P p.1 p.2 from rfl]
        simpa [hP] using hRes'
      · show phiCount (execution P C (fun _ => p) 1) < phiCount C
        rw [show execution P C (fun _ => p) 1 = C.step P p.1 p.2 from rfl]
        have hRes'' : ResAns (majorityAnswer (C.step P p.1 p.2))
            (C.step P p.1 p.2) := by simpa [hP] using hRes'
        rw [phiCount_eq_wrongAnswerCount_of_resAns hRes'', hphi_eq]
        simpa [hP] using hdec
    · -- 2b: some median agent has timer = 0.  This is exactly a
      -- `timer = 0`-compatible reset path — fold into the timer-free
      -- reservoir/reset leaf via its second disjunct.
      push_neg at hTimerC
      obtain ⟨μ0, hμ0_med, hμ0_t⟩ := hTimerC
      have hμ0_t0 : (C μ0).1.timer = 0 := by omega
      exact hResetLeaf C hSswap hRes hpos
        (Or.inr ⟨μ0, hμ0_med, hμ0_t0⟩)
  · -- CASE 3: every median correct, `phiCount > 0` — the median-correct
    -- `timer = 0`-compatible reset path (first disjunct of the leaf).
    push_neg at hMedWrong
    exact hResetLeaf C hSswap hRes hpos (Or.inl hMedWrong)

/-- **Epidemic timer-branch bridge — fully proven down to the single
non-circular median-correct reservoir leaf.**

Given `InSrank C₁` with a live (`≥2`) median timer (the timer disjunct of
`ranking_field_proof_tau (τ := τ)`), this drives — through the *proven, non-circular*
swap reachability `swap_reaches_Sswap_from_timer_bound_with_timer` and the
*proven, non-circular* median-wrong strong recursion
`median_wrong_only_drive_to_consensus_tau (τ := τ)` — to an `IsConsensusConfig`.

The single residual `hMedCorrectExit` is the **reservoir median-correct
renormalizer leaf**: it speaks *only* of a configuration `D` that is
already `InSswap`, has a live median timer, a positive wrong-answer count,
and an *already-correct median*.  It carries **no** epidemic /
`BurmanConvergence` / `BurmanMacroDecision` / `BurmanRankingCorrect` /
answer-stability / "∃ schedule reaching consensus for the goal" content
(it never refers to `C₁`, the epidemic goal, or this theorem); it is the
precise, minimal, non-circular shape isolated by `EPIDEMIC_STRATEGY.md`
(discharged by `trigger_correct_reset_from_InSrank_tau (τ := τ)` /
`all_resetting_from_seed_answer_aux_tau (τ := τ)` /
`all_resetting_uniform_to_InSswap_ResAns_tau (τ := τ)` once the answer-and-timer
overlay re-derivation of the recruit/swap kernel — the documented open
core — is completed).  The entire ranking entry, swap reachability, and
median-wrong recursion around it are closed here non-circularly. -/
theorem epidemic_timer_branch_to_consensus_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C₁ : Config (AgentState n) Opinion n}
    (hInSrank : InSrank C₁)
    (htimer :
      ∀ μ : Fin n,
        (C₁ μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (C₁ μ).1.timer)
    (hMedCorrectExit :
      ∀ k : ℕ, ∀ D : Config (AgentState n) Opinion n,
        InSswap D →
        (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (D μ).1.timer) →
        0 < wrongAnswerCount D →
        (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
          (D μ).1.answer = majorityAnswer D) →
        wrongAnswerCount D ≤ k →
        ∃ (γ : DetScheduler n) (t : ℕ),
          IsConsensusConfig (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      IsConsensusConfig (execution (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C₁ γ t) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  -- Proven swap reachability: `InSrank` + `2 ≤ timer@median` reaches
  -- `InSswap` with `1 ≤ timer@median`.
  obtain ⟨γ₁, t₁, hSswap, htimer₁⟩ :=
    swap_reaches_Sswap_from_timer_bound_with_timer
      (trank := τ) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      rankDeltaOSSR_satisfies_fix hn4
      (C₀ := C₁) hInSrank htimer
  set E₁ : Config (AgentState n) Opinion n := execution P C₁ γ₁ t₁ with hE₁def
  -- Proven non-circular median-wrong strong recursion; the median-correct
  -- arm is the supplied non-circular reservoir leaf.
  obtain ⟨γ₂, t₂, hcons₂⟩ :=
    median_wrong_only_drive_to_consensus_tau (τ := τ)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 (wrongAnswerCount E₁) E₁
      (by simpa [E₁, hP] using hSswap)
      (by
        intro μ hμ
        have := htimer₁ μ
        simpa [E₁, hP] using this hμ)
      le_rfl hMedCorrectExit
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  have hsplit :
      execution P C₁ (concatScheduler γ₁ t₁ γ₂) (t₁ + t₂)
        = execution P E₁ γ₂ t₂ := by
    rw [execution_concat]
  rw [hsplit]
  simpa [E₁, hP] using hcons₂

/-- **InSswap median-timer drain step (even-n, max-rank partner, same
answer).**  Stable-named wrapper around the proven
`no_reset_even_lower_max_timer_one_step_InSswap_tau (τ := τ)` (BurmanProof:692) using
the `runPairs` interface so it composes directly with the
`hMedCorrectExit` schedule.  Given `InSswap C` (even `n`, `n ≥ 4`), a
lower-median `μ` with timer = 1, a distinct max-rank `v` whose input
opinion forbids the B/A swap, and whose `.answer` matches μ's (so no
reset fires), running `runPairs P C [(μ, v)]` leaves `μ` at the same
lower-median rank with timer = 0 and answer unchanged, preserving
`InSswap`.  Pure wrapping — `sorry`/`axiom`-free. -/
theorem insswap_drain_median_timer_one_step_tau
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
    let C' := runPairs P C [(μ, v)]
    InSswap C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have h := no_reset_even_lower_max_timer_one_step_InSswap_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hSwap hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  change
    InSswap (runPairs P C [(μ, v)]) ∧
      (runPairs P C [(μ, v)] μ).1.timer = 0 ∧
      (runPairs P C [(μ, v)] μ).1.answer = (C μ).1.answer ∧
      (runPairs P C [(μ, v)] μ).1.rank.val + 1 = n / 2
  have hrew : runPairs P C [(μ, v)] = C.step P μ v := by
    simp only [runPairs_cons, runPairs_nil]
  rw [hrew]
  exact h

set_option maxHeartbeats 16000000 in
/-- Tie-aware version of `median_wrong_step_resAns_decrease_tau`.

The old theorem takes a local `hNoTie : nAOf C ≠ nBOf C`, but its proof
already contains the even-tie branch.  This wrapper uses the old theorem
on the no-tie branch and gives the missing even-tie branch directly. -/
theorem median_wrong_step_resAns_decrease_tieaware_tau
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (hC_timer : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                 (C μ).1.answer ≠ majorityAnswer C) :
    ∃ p : Fin n × Fin n,
      InSswap (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ∧
      ResAns (majorityAnswer (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2))
        (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ∧
      (∀ μ : Fin n,
        (C.step (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2 μ).1.rank.val + 1
            = ceilHalf n →
        1 ≤ (C.step (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2 μ).1.timer) ∧
      wrongAnswerCount (C.step (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) < wrongAnswerCount C := by
  classical
  by_cases hNoTie : nAOf C ≠ nBOf C
  · exact
      median_wrong_step_resAns_decrease_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hC hRes hNoTie hC_timer h_med_wrong
  · push_neg at hNoTie
    set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
    have hRfix := rankDeltaOSSR_satisfies_fix
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    obtain ⟨μ0, hμ0_med, hμ0_wrong⟩ := h_med_wrong
    have hpar : n % 2 = 0 := by
      have hsum := nAOf_add_nBOf C
      omega
    obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong_tie hC hpar hn4 hNoTie
        ⟨μ0, hμ0_med, hμ0_wrong⟩
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
      intro h
      rcases h with ⟨huB, hvA⟩
      have hsum := nAOf_add_nBOf C
      have huA : (C u).2 = Opinion.A := (hC.input_rank u).mpr (by omega)
      rw [huA] at huB
      exact Opinion.noConfusion huB
    obtain ⟨h_u, h_v, h_others, _h_inputs⟩ :=
      step_at_median_pair_even_disagreed_inputs
        (trank := τ) (Rmax := Rmax)
        hRfix huv hsu hsv hpar hu_med hv_upper h_disagree h_no_swap hn4
    have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hNoTie
    have h_dec := decision_step_at_median_pair_even_tie_decreases
      (trank := τ) (Rmax := Rmax) hRfix
      hC huv hpar hu_med hv_upper h_disagree hNoTie hn4 h_wrong
    have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
    have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
    have hmaj_step : majorityAnswer (C.step P u v) = majorityAnswer C := by
      rw [hP]
      exact majorityAnswer_step_eq C u v
    refine ⟨(u, v), h_dec.1, ?_, ?_, h_dec.2⟩
    · rw [hmaj_step]
      intro w
      by_cases hwu : w = u
      · left
        have hwa : (C.step P u v w).1.answer = .outT := by
          subst hwu
          rw [h_u]
        rw [hwa, h_outT]
      · by_cases hwv : w = v
        · left
          have hwa : (C.step P u v w).1.answer = .outT := by
            subst hwv
            rw [h_v]
          rw [hwa, h_outT]
        · have hww : (C.step P u v w).1.answer = (C w).1.answer := by
            have hstate : (C.step P u v) w = C w := h_others w hwu hwv
            rw [hstate]
          rw [hww]
          exact hRes w
    · exact
        step_preserves_timer_no_max
          (trank := τ) (Rmax := Rmax)
          hRfix hC.toInSrank huv hu_no_max hv_no_max hC_timer

set_option maxHeartbeats 16000000 in
/-- Tie-aware `cycle_macro_discharge_tau`: no universal `hNoTie` premise.

This is the same macro-step as `cycle_macro_discharge_tau (τ := τ)`, but CASE 2 calls
`median_wrong_step_resAns_decrease_tieaware_tau (τ := τ)`, so even ties are handled by
the local tie branch. -/
theorem cycle_macro_discharge_tieaware_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hResetLeaf :
      ∀ D : Config (AgentState n) Opinion n,
        InSswap D → ResAns (majorityAnswer D) D → 0 < phiCount D →
        ((∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
            (D μ).1.answer = majorityAnswer D) ∨
         (∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
            (D μ).1.timer = 0)) →
        ∃ (γ : DetScheduler n) (k : ℕ),
          (InSswap (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k) ∧
            ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k))
              (execution (protocolPEM n τ Rmax
                (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k)) ∧
          phiCount (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k) < phiCount D) :
    ∀ C : Config (AgentState n) Opinion n,
      (InSswap C ∧ ResAns (majorityAnswer C) C) → 0 < phiCount C →
      ∃ (γ : DetScheduler n) (k : ℕ),
        (InSswap (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) ∧
          ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k))
            (execution (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k)) ∧
        phiCount (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C γ k) < phiCount C := by
  classical
  intro C ⟨hSswap, hRes⟩ hpos
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have hphi_eq : phiCount C = wrongAnswerCount C :=
    phiCount_eq_wrongAnswerCount_of_resAns hRes
  have hwpos : 0 < wrongAnswerCount C := by
    rw [← hphi_eq]
    exact hpos
  by_cases hMedWrong :
      ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
        (C μ).1.answer ≠ majorityAnswer C
  · by_cases hTimerC :
        ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
          1 ≤ (C μ).1.timer
    · obtain ⟨p, hSswap', hRes', _htimer', hdec⟩ :=
        median_wrong_step_resAns_decrease_tieaware_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSswap hRes hTimerC hMedWrong
      refine ⟨fun _ => p, 1, ⟨?_, ?_⟩, ?_⟩
      · show InSswap (execution P C (fun _ => p) 1)
        rw [show execution P C (fun _ => p) 1 = C.step P p.1 p.2 from rfl]
        simpa [hP] using hSswap'
      · show ResAns
          (majorityAnswer (execution P C (fun _ => p) 1))
          (execution P C (fun _ => p) 1)
        rw [show execution P C (fun _ => p) 1 = C.step P p.1 p.2 from rfl]
        simpa [hP] using hRes'
      · show phiCount (execution P C (fun _ => p) 1) < phiCount C
        rw [show execution P C (fun _ => p) 1 = C.step P p.1 p.2 from rfl]
        have hRes'' : ResAns (majorityAnswer (C.step P p.1 p.2))
            (C.step P p.1 p.2) := by
          simpa [hP] using hRes'
        rw [phiCount_eq_wrongAnswerCount_of_resAns hRes'', hphi_eq]
        simpa [hP] using hdec
    · push_neg at hTimerC
      obtain ⟨μ0, hμ0_med, hμ0_t⟩ := hTimerC
      have hμ0_t0 : (C μ0).1.timer = 0 := by omega
      exact hResetLeaf C hSswap hRes hpos
        (Or.inr ⟨μ0, hμ0_med, hμ0_t0⟩)
  · push_neg at hMedWrong
    exact hResetLeaf C hSswap hRes hpos (Or.inl hMedWrong)

/-- The exact median-correct reservoir-entry auxiliary needed to close the
local `hMedCorrectExit`.  This is not derivable from the current green
lemmas alone; it is the missing timer-drain/reset-entry construction. -/
def MedCorrectLiveInSswapToReservoirEntry_tau
    [Inhabited (Fin n × Fin n)]
    (Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (D μ).1.timer) →
    0 < wrongAnswerCount D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D) →
    ∃ (γ : DetScheduler n) (t : ℕ),
      let E := execution
        (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D γ t
      InSswap E ∧ ResAns (majorityAnswer E) E

/-- The exact reset leaf needed by the tie-aware cycle macro-step. -/
def ReservoirResetLeaf_tau
    [Inhabited (Fin n × Fin n)]
    (Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D → ResAns (majorityAnswer D) D → 0 < phiCount D →
    ((∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
        (D μ).1.answer = majorityAnswer D) ∨
     (∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
        (D μ).1.timer = 0)) →
    ∃ (γ : DetScheduler n) (k : ℕ),
      (InSswap (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k) ∧
        ResAns (majorityAnswer (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k))
          (execution (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k)) ∧
      phiCount (execution (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) D γ k) < phiCount D

set_option maxHeartbeats 8000000 in
/-- This is the non-circular composition that closes the local
`hMedCorrectExit` once the two genuine missing auxiliaries are supplied. -/
theorem hMedCorrectExit_from_reservoir_entry_and_reset_leaf_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hEntry : MedCorrectLiveInSswapToReservoirEntry_tau (τ := τ) Rmax Emax Dmax hn)
    (hLeaf : ReservoirResetLeaf_tau (τ := τ) Rmax Emax Dmax hn) :
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
  classical
  intro k D hD hTimer hpos hMedCorrect _hle
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  obtain ⟨γ₀, t₀, hE_s, hE_res⟩ :=
    hEntry D hD hTimer hpos hMedCorrect
  set E : Config (AgentState n) Opinion n := execution P D γ₀ t₀ with hEdef
  have hE_s' : InSswap E := by
    simpa [E, hP] using hE_s
  have hE_res' : ResAns (majorityAnswer E) E := by
    simpa [E, hP] using hE_res
  by_cases hphi0 : phiCount E = 0
  · refine ⟨γ₀, t₀, ?_⟩
    simpa [E, hP] using
      (isConsensusConfig_of_InSswap_phiCount_zero hE_s' hE_res' hphi0)
  · have hphi_pos : 0 < phiCount E := Nat.pos_of_ne_zero hphi0
    have hMacro :=
      cycle_macro_discharge_tieaware_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hLeaf
    obtain ⟨γ₁, t₁, hCons⟩ :=
      cycle_potential_reaches_consensus_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hMacro E hE_s' hE_res'
    refine ⟨concatScheduler γ₀ t₀ γ₁, t₀ + t₁, ?_⟩
    have hsplit :
        execution P D (concatScheduler γ₀ t₀ γ₁) (t₀ + t₁)
          = execution P E γ₁ t₁ := by
      rw [execution_concat]
    rw [hsplit]
    simpa [E, hP] using hCons

set_option maxHeartbeats 24000000 in
theorem heapPrefix_recruit_step_with_child_BCF_tau [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {k : ℕ}
    (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C)
    (u : Fin n) (hu_unsettled : (C u).1.role = .Unsettled) :
    ∃ parent : Fin n,
      (C parent).1.role = .Settled ∧
      (C parent).1.children < 2 ∧
      2 * (C parent).1.rank.val + (C parent).1.children + 1 < n ∧
      2 * (C parent).1.rank.val + (C parent).1.children + 1 = k ∧
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C [(u, parent)]
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
    transitionPEM_recruit_ba_settled_rank_children_tau (τ := τ)
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
        transitionPEM_recruit_ba_child_timer_ge_three_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
      exact Nat.le_trans (show 2 ≤ 3 by omega) (by simpa using hge3)
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds_tau (τ := τ)
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
        transitionPEM_recruit_ba_child_timer_ge_three_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds_tau (τ := τ)
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
  refine ⟨v, hv_settled, hv_children_lt, h_valid, ?_, ?_⟩
  · rw [hv_rank, hv_children_old]
    exact heap_parent_rank hk_pos
  · exact ⟨hHeap', hTimerGood', hTimerStrong'⟩

set_option maxHeartbeats 32000000 in
private theorem heapPrefix_ranking_with_ResAns_odd_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (hodd : ¬ n % 2 = 0) (hMajOut : m₀ = .outA ∨ m₀ = .outB) (hn4 : 4 ≤ n) :
    ∀ m k : ℕ, k + m = n → 1 ≤ k →
      ∀ D : Config (AgentState n) Opinion n,
        HeapPrefix D k → SettledMedianTimerStrong D → ResAns m₀ D →
        (∀ w : Fin n, (D w).1.answer ≠ .phi) →
        ceilHalf n ≤ majorityCountOfAnswerBCF D m₀ →
        ∃ L : List (Fin n × Fin n),
          InSrank (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) ∧
          ResAns m₀ (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) ∧
          (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) w).1.answer ≠ .phi) ∧
          majorityAnswer (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) = majorityAnswer D ∧
          (∀ μ : Fin n,
            ((runPairs (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D L) μ).1.rank.val + 1
                = ceilHalf n →
            2 ≤ ((runPairs (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D L) μ).1.timer) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  intro m
  induction m with
  | zero =>
    intro k hkn _ D hHeap hTimer hRes hNoPhi _hMajCount
    have : k = n := by omega
    subst this
    exact ⟨[], by simpa using HeapPrefix.to_InSrank hHeap, by simpa using hRes,
      by simpa using hNoPhi, by simp, by
        intro μ hμ
        have hs : (D μ).1.role = .Settled := (HeapPrefix.to_InSrank hHeap).allSettled μ
        exact (SettledMedianTimerStrong.toGood hTimer) μ hs hμ⟩
  | succ m ih =>
    intro k hkn hk1 D hHeap hTimer hRes hNoPhi hMajCount
    have hk_lt : k < n := by omega
    have hpr_lt : heapParent k < k := heapParent_lt_self hk1
    obtain ⟨v, ⟨hv_settled, hv_rank⟩, _hv_unique⟩ :=
      hHeap.2.2.1 (heapParent k) hpr_lt
    have hv_children : (D v).1.children = heapChildIndex k := by
      rw [hHeap.2.2.2.2 v hv_settled, hv_rank]
      exact heapChildrenBefore_parent hk1
    have hExistsUnsettled : ∃ u : Fin n, (D u).1.role = .Unsettled := by
      by_contra hnone
      push_neg at hnone
      exact heapPrefix_no_unsettled_contradiction hk_lt hHeap
        (fun w => by
          rcases hHeap.2.2.2.1 w with hs | hu
          · exact hs
          · exact absurd hu (hnone w))
    by_cases hnonmed : k + 1 ≠ ceilHalf n
    · obtain ⟨u', hu'U⟩ := hExistsUnsettled
      obtain ⟨v', hv'S, hv'children, hv'valid, hv'target, hStepRest⟩ :=
        heapPrefix_recruit_step_with_child_BCF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hk1 hk_lt D hHeap hTimer u' hu'U
      dsimp only [] at hStepRest
      obtain ⟨hHeapStep, hTimerGood, hTimerStrong⟩ := hStepRest
      set C' := runPairs P D [(u', v')]
      have hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) m₀ D u' v' := by
        exact odd_nonmedian_recruit_ba_PairResAnsSafe_BCF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (m₀ := m₀) (D := D) (child := u') (p := v')
          hodd hRes hu'U hv'S hv'children hv'valid
          (by
            rw [hv'target]
            exact hnonmed)
      have hRes' : ResAns m₀ C' := by
        simpa [C', runPairs] using step_preserves_ResAns_of_pairSafe_tau (τ := τ) hRes hSafe
      have hSafeNoPhi : PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn) D u' v' := by
        exact odd_nonmedian_recruit_ba_PairNoPhiSafe_BCF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (D := D) (child := u') (p := v')
          hodd hNoPhi hu'U hv'S hv'children hv'valid
          (by
            rw [hv'target]
            exact hnonmed)
      have hNoPhi' : ∀ w : Fin n, (C' w).1.answer ≠ .phi := by
        simpa [C', runPairs] using
          step_preserves_noPhi_of_pairNoPhiSafe_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := D) (a := u') (b := v') hNoPhi hSafeNoPhi
      have hMaj' : majorityAnswer C' = majorityAnswer D := by
        simpa [C', runPairs] using majorityAnswer_step_eq D u' v'
      have hMajCount' : ceilHalf n ≤ majorityCountOfAnswerBCF C' m₀ := by
        have hcnt : majorityCountOfAnswerBCF C' m₀ = majorityCountOfAnswerBCF D m₀ := by
          simpa [C', P, runPairs] using
            majorityCountOfAnswerBCF_step_eq_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hMajOut D u' v'
        rw [hcnt]
        exact hMajCount
      by_cases hk1n : k + 1 < n
      · have hTimerS' := hTimerStrong hk1n
        obtain ⟨L, hSrank, hResL, hNoPhiL, hMajL, hTimerL⟩ :=
          ih (k + 1) (by omega) (by omega) C' hHeapStep hTimerS' hRes' hNoPhi'
            hMajCount'
        exact ⟨(u', v') :: L, by simpa [C', runPairs] using hSrank,
               by simpa [C', runPairs] using hResL,
               by simpa [C', runPairs] using hNoPhiL,
               by
                rw [show runPairs P D ((u', v') :: L) = runPairs P C' L from by
                  simp [C', runPairs]]
                rw [hMajL, hMaj'],
               by simpa [C', runPairs] using hTimerL⟩
      · have hk1_eq : k + 1 = n := by omega
        rw [hk1_eq] at hHeapStep
        exact ⟨[(u', v')], by simpa [C', runPairs] using HeapPrefix.to_InSrank hHeapStep,
               by simpa [C', runPairs] using hRes',
               by simpa [C', runPairs] using hNoPhi',
               by simpa [C', runPairs] using hMaj',
               by
                intro μ hμ
                have hs : (C' μ).1.role = .Settled :=
                  (HeapPrefix.to_InSrank hHeapStep).allSettled μ
                simpa [C', runPairs] using hTimerGood μ hs hμ⟩
    · push_neg at hnonmed
      have hSettledLtMaj : settledCount D < majorityCountOfAnswerBCF D m₀ := by
        rw [settledCount_of_heapPrefix_BCF hHeap]
        omega
      have hNonSettledUnsettled :
          ∀ w : Fin n, (D w).1.role ≠ .Settled → (D w).1.role = .Unsettled := by
        intro w hw
        rcases hHeap.2.2.2.1 w with hs | hu
        · exact False.elim (hw hs)
        · exact hu
      obtain ⟨u', hu'U, hu'Maj⟩ :=
        exists_unsettled_majority_child_of_settled_lt_majority_BCF
          (C := D) (m := m₀)
          hMajOut hSettledLtMaj hNonSettledUnsettled
      obtain ⟨v', hv'S, hv'children, hv'valid, hv'target, hStepRest⟩ :=
        heapPrefix_recruit_step_with_child_BCF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hk1 hk_lt D hHeap hTimer u' hu'U
      dsimp only [] at hStepRest
      obtain ⟨hHeapStep, hTimerGood, hTimerStrong⟩ := hStepRest
      set C' := runPairs P D [(u', v')]
      have hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) m₀ D u' v' := by
        exact odd_median_recruit_ba_PairResAnsSafe_of_majority_child_BCF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (m₀ := m₀) (D := D) (child := u') (p := v')
          hodd hRes hu'U hv'S hv'children hv'valid
          (by
            rw [hv'target]
            exact hnonmed)
          hu'Maj hMajOut
      have hRes' : ResAns m₀ C' := by
        simpa [C', runPairs] using step_preserves_ResAns_of_pairSafe_tau (τ := τ) hRes hSafe
      have hSafeNoPhi : PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) (hn := hn) D u' v' := by
        exact odd_median_recruit_ba_PairNoPhiSafe_of_majority_child_BCF_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (D := D) (child := u') (p := v')
          hodd hNoPhi hu'U hv'S hv'children hv'valid
          (by
            rw [hv'target]
            exact hnonmed)
          hu'Maj hMajOut
      have hNoPhi' : ∀ w : Fin n, (C' w).1.answer ≠ .phi := by
        simpa [C', runPairs] using
          step_preserves_noPhi_of_pairNoPhiSafe_tau (τ := τ)
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := D) (a := u') (b := v') hNoPhi hSafeNoPhi
      have hMaj' : majorityAnswer C' = majorityAnswer D := by
        simpa [C', runPairs] using majorityAnswer_step_eq D u' v'
      have hMajCount' : ceilHalf n ≤ majorityCountOfAnswerBCF C' m₀ := by
        have hcnt : majorityCountOfAnswerBCF C' m₀ = majorityCountOfAnswerBCF D m₀ := by
          simpa [C', P, runPairs] using
            majorityCountOfAnswerBCF_step_eq_tau (τ := τ)
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hMajOut D u' v'
        rw [hcnt]
        exact hMajCount
      by_cases hk1n : k + 1 < n
      · have hTimerS' := hTimerStrong hk1n
        obtain ⟨L, hSrank, hResL, hNoPhiL, hMajL, hTimerL⟩ :=
          ih (k + 1) (by omega) (by omega) C' hHeapStep hTimerS' hRes' hNoPhi'
            hMajCount'
        exact ⟨(u', v') :: L, by simpa [C', runPairs] using hSrank,
               by simpa [C', runPairs] using hResL,
               by simpa [C', runPairs] using hNoPhiL,
               by
                rw [show runPairs P D ((u', v') :: L) = runPairs P C' L from by
                  simp [C', runPairs]]
                rw [hMajL, hMaj'],
               by simpa [C', runPairs] using hTimerL⟩
      · have hk1_eq : k + 1 = n := by omega
        rw [hk1_eq] at hHeapStep
        exact ⟨[(u', v')], by simpa [C', runPairs] using HeapPrefix.to_InSrank hHeapStep,
               by simpa [C', runPairs] using hRes',
               by simpa [C', runPairs] using hNoPhi',
               by simpa [C', runPairs] using hMaj',
               by
                intro μ hμ
                have hs : (C' μ).1.role = .Settled :=
                  (HeapPrefix.to_InSrank hHeapStep).allSettled μ
                simpa [C', runPairs] using hTimerGood μ hs hμ⟩

theorem fresh_start_to_InSrank_ResAns_odd_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    (hodd : ¬ n % 2 = 0)
    (hMajOut : m₀ = .outA ∨ m₀ = .outB)
    (hn4 : 4 ≤ n) :
    ∀ C : Config (AgentState n) Opinion n,
      FreshRankingStart C → ResAns m₀ C →
      (∀ w : Fin n, (C w).1.answer ≠ .phi) →
      ceilHalf n ≤ majorityCountOfAnswerBCF C m₀ →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer ≠ .phi) ∧
        majorityAnswer (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C ∧
        (∀ μ : Fin n,
          ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) μ).1.rank.val + 1
              = ceilHalf n →
          2 ≤ ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) μ).1.timer) := by
  intro C hFresh hRes hNoPhi hMajCount
  have hHeap1 := FreshRankingStart.to_heapPrefix_one hFresh
  have hTimer1 : SettledMedianTimerStrong C := by
    intro μ hs hmed
    obtain ⟨root, hroot_s, hroot_r, _, hrest⟩ := hFresh
    by_cases hμr : μ = root
    · subst hμr
      rw [hroot_r] at hmed
      unfold ceilHalf at hmed
      omega
    · rw [hrest μ hμr] at hs
      exact Role.noConfusion hs
  exact heapPrefix_ranking_with_ResAns_odd_BCF_tau (τ := τ)
    hodd hMajOut hn4 (n - 1) 1 (by omega) le_rfl C hHeap1 hTimer1 hRes hNoPhi
      hMajCount

private theorem majorityAnswer_outA_or_outB_of_odd_BCF
    {C : Config (AgentState n) Opinion n}
    (hodd : ¬ n % 2 = 0) :
    majorityAnswer C = .outA ∨ majorityAnswer C = .outB := by
  unfold majorityAnswer
  by_cases hAB : nAOf C > nBOf C
  · simp [hAB]
  · simp [hAB]
    by_cases hBA : nBOf C > nAOf C
    · simp [hBA]
    · have hEq : nAOf C = nBOf C := by omega
      have hsum := nAOf_add_nBOf C
      exfalso
      rw [hEq] at hsum
      omega

theorem fresh_start_to_InSrank_ResAns_odd_majority_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    (hodd : ¬ n % 2 = 0) (hn4 : 4 ≤ n) :
    ∀ C : Config (AgentState n) Opinion n,
      m₀ = majorityAnswer C →
      FreshRankingStart C → ResAns m₀ C →
      (∀ w : Fin n, (C w).1.answer ≠ .phi) →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer ≠ .phi) ∧
        majorityAnswer (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C ∧
        (∀ μ : Fin n,
          ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) μ).1.rank.val + 1
              = ceilHalf n →
          2 ≤ ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) μ).1.timer) := by
  intro C hm hFresh hRes hNoPhi
  have hMajOut : m₀ = .outA ∨ m₀ = .outB := by
    rcases majorityAnswer_outA_or_outB_of_odd_BCF (C := C) hodd with hA | hB
    · exact Or.inl (hm.trans hA)
    · exact Or.inr (hm.trans hB)
  have hMajCount : ceilHalf n ≤ majorityCountOfAnswerBCF C m₀ :=
    ceilHalf_le_majorityCountOfAnswerBCF_of_majorityAnswer hm hMajOut
  exact fresh_start_to_InSrank_ResAns_odd_BCF_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hodd hMajOut hn4 C hFresh hRes hNoPhi hMajCount

set_option maxHeartbeats 24000000 in
private theorem heapPrefix_ranking_with_ResAns_even_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m₀ : Answer}
    (heven : n % 2 = 0) (hn4 : 4 ≤ n) :
    ∀ m k : ℕ, k + m = n → 1 ≤ k →
      ∀ D : Config (AgentState n) Opinion n,
        HeapPrefix D k → SettledMedianTimerStrong D → ResAns m₀ D →
        (∀ w : Fin n, (D w).1.answer ≠ .phi) →
        ∃ L : List (Fin n × Fin n),
          InSrank (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) ∧
          ResAns m₀ (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) ∧
          (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) w).1.answer ≠ .phi) ∧
          majorityAnswer (runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) D L) = majorityAnswer D ∧
          (∀ μ : Fin n,
            ((runPairs (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D L) μ).1.rank.val + 1
                = ceilHalf n →
            2 ≤ ((runPairs (protocolPEM n τ Rmax
              (rankDeltaOSSR Rmax Emax Dmax hn)) D L) μ).1.timer) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  intro m
  induction m with
  | zero =>
    intro k hkn _ D hHeap hTimer hRes hNoPhi
    have : k = n := by omega
    subst this
    exact ⟨[], by simpa using HeapPrefix.to_InSrank hHeap, by simpa using hRes,
      by simpa using hNoPhi, by simp, by
        intro μ hμ
        have hs : (D μ).1.role = .Settled := (HeapPrefix.to_InSrank hHeap).allSettled μ
        exact (SettledMedianTimerStrong.toGood hTimer) μ hs hμ⟩
  | succ m ih =>
    intro k hkn hk1 D hHeap hTimer hRes hNoPhi
    have hk_lt : k < n := by omega
    have hExistsUnsettled : ∃ u : Fin n, (D u).1.role = .Unsettled := by
      by_contra hnone
      push_neg at hnone
      exact heapPrefix_no_unsettled_contradiction hk_lt hHeap
        (fun w => by
          rcases hHeap.2.2.2.1 w with hs | hu
          · exact hs
          · exact absurd hu (hnone w))
    obtain ⟨u', hu'U⟩ := hExistsUnsettled
    obtain ⟨v', hv'S, hv'children, hv'valid, _hv'target, hStepRest⟩ :=
      heapPrefix_recruit_step_with_child_BCF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hk1 hk_lt D hHeap hTimer u' hu'U
    dsimp only [] at hStepRest
    obtain ⟨hHeapStep, hTimerGood, hTimerStrong⟩ := hStepRest
    set C' := runPairs P D [(u', v')]
    have hSafe : PairResAnsSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn) m₀ D u' v' := by
      exact even_recruit_ba_PairResAnsSafe_BCF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (m₀ := m₀) (D := D) (child := u') (p := v')
        hn4 heven hRes hu'U hv'S hv'children hv'valid
    have hRes' : ResAns m₀ C' := by
      simpa [C', runPairs] using step_preserves_ResAns_of_pairSafe_tau (τ := τ) hRes hSafe
    have hSafeNoPhi : PairNoPhiSafe_tau (τ := τ) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn) D u' v' := by
      exact even_recruit_ba_PairNoPhiSafe_BCF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (D := D) (child := u') (p := v')
        hn4 heven hNoPhi hu'U hv'S hv'children hv'valid
    have hNoPhi' : ∀ w : Fin n, (C' w).1.answer ≠ .phi := by
      simpa [C', runPairs] using
        step_preserves_noPhi_of_pairNoPhiSafe_tau (τ := τ)
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := D) (a := u') (b := v') hNoPhi hSafeNoPhi
    have hMaj' : majorityAnswer C' = majorityAnswer D := by
      simpa [C', runPairs] using majorityAnswer_step_eq D u' v'
    by_cases hk1n : k + 1 < n
    · have hTimerS' := hTimerStrong hk1n
      obtain ⟨L, hSrank, hResL, hNoPhiL, hMajL, hTimerL⟩ :=
        ih (k + 1) (by omega) (by omega) C' hHeapStep hTimerS' hRes' hNoPhi'
      exact ⟨(u', v') :: L, by simpa [C', runPairs] using hSrank,
             by simpa [C', runPairs] using hResL,
             by simpa [C', runPairs] using hNoPhiL,
             by
              rw [show runPairs P D ((u', v') :: L) = runPairs P C' L from by
                simp [C', runPairs]]
              rw [hMajL, hMaj'],
             by simpa [C', runPairs] using hTimerL⟩
    · have hk1_eq : k + 1 = n := by omega
      rw [hk1_eq] at hHeapStep
      exact ⟨[(u', v')], by simpa [C', runPairs] using HeapPrefix.to_InSrank hHeapStep,
             by simpa [C', runPairs] using hRes',
             by simpa [C', runPairs] using hNoPhi',
             by simpa [C', runPairs] using hMaj',
             by
              intro μ hμ
              have hs : (C' μ).1.role = .Settled :=
                (HeapPrefix.to_InSrank hHeapStep).allSettled μ
              simpa [C', runPairs] using hTimerGood μ hs hμ⟩

theorem fresh_start_to_InSrank_ResAns_even_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {m₀ : Answer}
    (heven : n % 2 = 0) (hn4 : 4 ≤ n) :
    ∀ C : Config (AgentState n) Opinion n,
      FreshRankingStart C → ResAns m₀ C →
      (∀ w : Fin n, (C w).1.answer ≠ .phi) →
      ∃ L : List (Fin n × Fin n),
        InSrank (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        ResAns m₀ (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) ∧
        (∀ w : Fin n, ((runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) w).1.answer ≠ .phi) ∧
        majorityAnswer (runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C ∧
        (∀ μ : Fin n,
          ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) μ).1.rank.val + 1
              = ceilHalf n →
          2 ≤ ((runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C L) μ).1.timer) := by
  intro C hFresh hRes hNoPhi
  have hHeap1 := FreshRankingStart.to_heapPrefix_one hFresh
  have hTimer1 : SettledMedianTimerStrong C := by
    intro μ hs hmed
    obtain ⟨root, hroot_s, hroot_r, _, hrest⟩ := hFresh
    by_cases hμr : μ = root
    · subst hμr
      rw [hroot_r] at hmed
      unfold ceilHalf at hmed
      omega
    · rw [hrest μ hμr] at hs
      exact Role.noConfusion hs
  exact heapPrefix_ranking_with_ResAns_even_BCF_tau (τ := τ)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (m₀ := m₀) heven hn4 (n - 1) 1 (by omega) le_rfl C hHeap1 hTimer1 hRes hNoPhi

theorem fresh_start_to_InSrank_ResAns_by_parity_BCF_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) :
    ∀ (C : Config (AgentState n) Opinion n) (m₀ : Answer),
      m₀ = majorityAnswer C →
      FreshRankingStart C → ResAns m₀ C →
      (∀ w : Fin n, (C w).1.answer ≠ .phi) →
      ∃ L : List (Fin n × Fin n),
        let C₂ := runPairs (protocolPEM n τ Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)) C L
        InSrank C₂ ∧
        ResAns m₀ C₂ ∧
        (∀ w : Fin n, (C₂ w).1.answer ≠ .phi) ∧
        (∀ μ : Fin n, (C₂ μ).1.rank.val + 1 = ceilHalf n →
          2 ≤ (C₂ μ).1.timer) ∧
        majorityAnswer C₂ = majorityAnswer C := by
  intro C m₀ hm hFresh hRes hNoPhi
  by_cases heven : n % 2 = 0
  · obtain ⟨L, hSrank, hResL, hNoPhiL, hMajL, hTimerL⟩ :=
      fresh_start_to_InSrank_ResAns_even_BCF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        heven hn4 C hFresh hRes hNoPhi
    exact ⟨L, hSrank, hResL, hNoPhiL, hTimerL, hMajL⟩
  · obtain ⟨L, hSrank, hResL, hNoPhiL, hMajL, hTimerL⟩ :=
      fresh_start_to_InSrank_ResAns_odd_majority_BCF_tau (τ := τ)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        heven hn4 C hm hFresh hRes hNoPhi
    exact ⟨L, hSrank, hResL, hNoPhiL, hTimerL, hMajL⟩

theorem even_upper_only_wrong_decision_InSswap_ResAns_tau
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C)
    (hOnlyUpperWrong :
      ∀ w : Fin n, (C w).1.answer ≠ majorityAnswer C →
        (C w).1.rank.val + 1 = n / 2 + 1) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSswap C' ∧ ResAns (majorityAnswer C') C' := by
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
  have h_other_correct :
      ∀ w : Fin n, w ≠ v → (C w).1.answer = majorityAnswer C := by
    intro w hwv
    by_contra hwrong
    have hw_upper := hOnlyUpperWrong w hwrong
    apply hwv
    apply hC.ranks_inj
    apply Fin.eq_of_val_eq
    have hw_val : (C w).1.rank.val = n / 2 := by omega
    have hv_val : (C v).1.rank.val = n / 2 := by omega
    exact hw_val.trans hv_val.symm
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
        · left
          have hww : C' w = C w := by
            dsimp [C']
            exact h_others w hwμ hwv
          rw [hww]
          exact h_other_correct w hwv
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
        · left
          dsimp [C']
          rw [hval, if_neg hwμ, if_neg hwv]
          exact h_other_correct w hwv
  refine ⟨[(μ, v)], ?_⟩
  have hRun : runPairs P C [(μ, v)] = C' := by
    simp only [runPairs_cons, runPairs_nil, C']
  rw [hRun]
  exact ⟨hSswap', hRes'⟩

end SSEM

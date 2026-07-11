import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanProof

namespace SSEM

variable {n : ℕ}

private theorem rankDeltaOSSR_converts_resetting_rc0
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc0 : s.resetcount = 0)
    (hFire : t.role ≠ .Resetting ∨ (t.resetcount ≤ 1 ∧ s.delaytimer ≤ 1)) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role ≠ .Resetting := by
  by_cases ht_res : t.role = .Resetting
  · have hsmall : t.resetcount ≤ 1 ∧ s.delaytimer ≤ 1 := by
      rcases hFire with ht_not | hsmall
      · exact False.elim (ht_not ht_res)
      · exact hsmall
    have ht_rc_sub : t.resetcount - 1 = 0 := by omega
    have hs_dt_sub : s.delaytimer - 1 = 0 := by omega
    cases hs_leader : s.leader <;>
      unfold rankDeltaOSSR propagateReset processAgent resetOSSR <;>
      simp [hs_res, hs_rc0, ht_res, ht_rc_sub, hs_dt_sub, hs_leader]
  · cases hs_leader : s.leader <;>
      unfold rankDeltaOSSR propagateReset processAgent resetOSSR <;>
      simp [hs_res, hs_rc0, ht_res, hs_leader]

/-- Structural per-step conversion for an initiator that is `Resetting` with
`resetcount = 0`, in the branch where the P_EM Phase 4 guard is skipped.

The firing condition is the actual `propagateReset`/`processAgent` condition
after resetcount synchronization: either the partner is not `Resetting`, or
the partner's synchronized contribution is already zero and the local
delaytimer fires. -/
theorem step_converts_resetting_rc0
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j)
    (hRes : (C i).1.role = .Resetting)
    (hRc0 : (C i).1.resetcount = 0)
    (hFire :
      (C j).1.role ≠ .Resetting ∨
        ((C j).1.resetcount ≤ 1 ∧ (C i).1.delaytimer ≤ 1))
    (hNoBothSettled :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Settled)) :
    (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j i).1.role ≠
      .Resetting := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrd :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role ≠ .Resetting :=
    rankDeltaOSSR_converts_resetting_rc0
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) hRes hRc0 hFire
  have hpass := transitionPEM_structural_passthrough
    (n := n) (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1)
    (x₀ := (C i).2) (x₁ := (C j).2) hNoBothSettled
  intro hbad
  have hstep := Config.step_fst_state P C hij
  have hdelta :
      (P.δ (C i, C j)).1.role =
        (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role := by
    simpa [P, protocolPEM] using hpass.1
  rw [congrArg AgentState.role hstep, hdelta] at hbad
  exact hrd hbad

/-- Follower specialization: a firing `Resetting`/`resetcount = 0` follower
leaves `Resetting` in one step.  Since the first rankDelta output is
`Unsettled`, Phase 4 is automatically skipped. -/
theorem step_converts_resetting_rc0_follower
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j)
    (hRes : (C i).1.role = .Resetting)
    (hRc0 : (C i).1.resetcount = 0)
    (hFollower : (C i).1.leader = .F)
    (hFire :
      (C j).1.role ≠ .Resetting ∨
        ((C j).1.resetcount ≤ 1 ∧ (C i).1.delaytimer ≤ 1)) :
    (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j i).1.role =
      .Unsettled := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrd_unsettled :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Unsettled := by
    by_cases hj_res : (C j).1.role = .Resetting
    · have hsmall : (C j).1.resetcount ≤ 1 ∧ (C i).1.delaytimer ≤ 1 := by
        rcases hFire with hj_not | hsmall
        · exact False.elim (hj_not hj_res)
        · exact hsmall
      have hj_rc_sub : (C j).1.resetcount - 1 = 0 := by omega
      have hi_dt_sub : (C i).1.delaytimer - 1 = 0 := by omega
      unfold rankDeltaOSSR propagateReset processAgent resetOSSR
      simp [hRes, hRc0, hj_res, hj_rc_sub, hi_dt_sub, hFollower]
    · unfold rankDeltaOSSR propagateReset processAgent resetOSSR
      simp [hRes, hRc0, hj_res, hFollower]
  have hNoBothSettled :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Settled) := by
    intro h
    rw [hrd_unsettled] at h
    exact Role.noConfusion h.1
  have hpass := transitionPEM_structural_passthrough
    (n := n) (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1)
    (x₀ := (C i).2) (x₁ := (C j).2) hNoBothSettled
  have hstep := Config.step_fst_state P C hij
  have hdelta :
      (P.δ (C i, C j)).1.role = .Unsettled := by
    rw [show (P.δ (C i, C j)).1.role =
        (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role by
      simpa [P, protocolPEM] using hpass.1]
    exact hrd_unsettled
  rw [congrArg AgentState.role hstep, hdelta]

end SSEM

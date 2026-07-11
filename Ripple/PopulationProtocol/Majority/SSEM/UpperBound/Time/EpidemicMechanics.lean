import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.EpidemicBound
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

/-!
Protocol-level mechanics for the reset-answer epidemic.

The local epidemic step is the `transitionPEM_prePhase4` phi-spread branch:
when both scheduled endpoints remain `.Resetting`, a `.phi` endpoint copies
the other endpoint's non-`.phi` answer.  The full all-Resetting region alone
does not force that branch, because `propagateReset` may wake dormant
`resetcount = 0` agents through `processAgent`.
-/

def EpidemicRegion {n : ℕ} (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  (∀ w : Fin n, (C w).1.role = .Resetting) ∧
    EpidemicAnswerInv m C ∧ m ≠ .phi ∧
    ∃ w : Fin n, (C w).1.answer = m

theorem epidemicRegion_answerInv {n : ℕ} {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (h : EpidemicRegion m C) :
    EpidemicAnswerInv m C :=
  h.2.1

private theorem answer_eq_m_of_inv_nonphi {n : ℕ} {m : Answer}
    {C : Config (AgentState n) Opinion n} {w : Fin n}
    (hInv : EpidemicAnswerInv m C)
    (hNonphi : (C w).1.answer ≠ .phi) :
    (C w).1.answer = m := by
  rcases hInv w with hm | hphi
  · exact hm
  · exact False.elim (hNonphi hphi)

private theorem transitionPEM_prePhase4_phi_imp_old_phi
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Resetting) (hs₁ : s₁.role = .Resetting)
    (hr₀ : (rankDelta (s₀, s₁)).1.answer = s₀.answer)
    (hr₁ : (rankDelta (s₀, s₁)).2.answer = s₁.answer) :
    ((transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.answer = .phi →
      s₀.answer = .phi) ∧
    ((transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.answer = .phi →
      s₁.answer = .phi) := by
  classical
  simp only [transitionPEM_prePhase4]
  simp [hs₀, hs₁]
  repeat' split_ifs <;> simp_all

private theorem transitionPEM_prePhase4_resAns_of_old_resetting
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} {m : Answer}
    (hr₀ : (rankDelta (s₀, s₁)).1.answer = s₀.answer)
    (hr₁ : (rankDelta (s₀, s₁)).2.answer = s₁.answer)
    (h₀ : s₀.answer = m ∨ s₀.answer = .phi)
    (h₁ : s₁.answer = m ∨ s₁.answer = .phi) :
    ((transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.answer = m ∨
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.answer = .phi) ∧
    ((transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.answer = m ∨
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.answer = .phi) := by
  have hpre :=
    transitionPEM_prePhase4_resAns
      (trank := trank) (rankDelta := rankDelta)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
      (m := m)
      (by simpa [hr₀] using h₀)
      (by simpa [hr₁] using h₁)
  exact hpre

private theorem transitionPEM_prePhase4_phi_m_answers
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} {m : Answer}
    (hs₀ : s₀.role = .Resetting) (hs₁ : s₁.role = .Resetting)
    (hr₀_role : (rankDelta (s₀, s₁)).1.role = .Resetting)
    (hr₁_role : (rankDelta (s₀, s₁)).2.role = .Resetting)
    (hr₀_ans : (rankDelta (s₀, s₁)).1.answer = .phi)
    (hr₁_ans : (rankDelta (s₀, s₁)).2.answer = m)
    (hm : m ≠ .phi) :
    (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.answer = m ∧
    (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.answer = m := by
  classical
  set rd := rankDelta (s₀, s₁) with hrd
  have hr₀_role' : rd.1.role = .Resetting := by
    simpa [hrd] using hr₀_role
  have hr₁_role' : rd.2.role = .Resetting := by
    simpa [hrd] using hr₁_role
  have hr₀_ans' : rd.1.answer = .phi := by
    simpa [hrd] using hr₀_ans
  have hr₁_ans' : rd.2.answer = m := by
    simpa [hrd] using hr₁_ans
  simp only [transitionPEM_prePhase4, ← hrd]
  simp [hs₀, hs₁, hr₀_role', hr₁_role', hr₀_ans', hr₁_ans', hm]

private theorem transitionPEM_prePhase4_m_phi_answers
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} {m : Answer}
    (hs₀ : s₀.role = .Resetting) (hs₁ : s₁.role = .Resetting)
    (hr₀_role : (rankDelta (s₀, s₁)).1.role = .Resetting)
    (hr₁_role : (rankDelta (s₀, s₁)).2.role = .Resetting)
    (hr₀_ans : (rankDelta (s₀, s₁)).1.answer = m)
    (hr₁_ans : (rankDelta (s₀, s₁)).2.answer = .phi)
    (hm : m ≠ .phi) :
    (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.answer = m ∧
    (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.answer = m := by
  classical
  set rd := rankDelta (s₀, s₁) with hrd
  have hr₀_role' : rd.1.role = .Resetting := by
    simpa [hrd] using hr₀_role
  have hr₁_role' : rd.2.role = .Resetting := by
    simpa [hrd] using hr₁_role
  have hr₀_ans' : rd.1.answer = m := by
    simpa [hrd] using hr₀_ans
  have hr₁_ans' : rd.2.answer = .phi := by
    simpa [hrd] using hr₁_ans
  simp only [transitionPEM_prePhase4, ← hrd]
  simp [hs₀, hs₁, hr₀_role', hr₁_role', hr₀_ans', hr₁_ans', hm]

private theorem epidemic_delta_resAns
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hPhase4 :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1.role = .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).2.role = .Settled))
    (h₀ : s₀.answer = m ∨ s₀.answer = .phi)
    (h₁ : s₁.answer = m ∨ s₁.answer = .phi) :
    (((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).1.answer = m ∨
      ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).1.answer = .phi) ∧
    (((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).2.answer = m ∨
      ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).2.answer = .phi) := by
  have hrd :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) s₀ s₁
  have hpre :=
    transitionPEM_prePhase4_resAns_of_old_resetting
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
      (m := m) hrd.1 hrd.2 h₀ h₁
  simpa [protocolPEM, transitionPEM_eq,
    transitionPEM_phase4_of_not_both_settled hPhase4] using hpre

private theorem epidemic_delta_phi_imp_old_phi
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Resetting) (hs₁ : s₁.role = .Resetting)
    (hPhase4 :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1.role = .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).2.role = .Settled)) :
    (((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).1.answer = .phi → s₀.answer = .phi) ∧
    (((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).2.answer = .phi → s₁.answer = .phi) := by
  have hrd :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) s₀ s₁
  have hpre :=
    transitionPEM_prePhase4_phi_imp_old_phi
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
      hs₀ hs₁ hrd.1 hrd.2
  simpa [protocolPEM, transitionPEM_eq,
    transitionPEM_phase4_of_not_both_settled hPhase4] using hpre

private theorem epidemic_delta_phi_m_answers
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Resetting) (hs₁ : s₁.role = .Resetting)
    (hr₀_role :
      (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).1.role = .Resetting)
    (hr₁_role :
      (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).2.role = .Resetting)
    (h₀ : s₀.answer = .phi) (h₁ : s₁.answer = m)
    (hm : m ≠ .phi) :
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).1.answer = m ∧
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).2.answer = m := by
  have hrd :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) s₀ s₁
  have hpre :=
    transitionPEM_prePhase4_phi_m_answers
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
      (m := m) hs₀ hs₁ hr₀_role hr₁_role
      (by simpa [hrd.1] using h₀)
      (by simpa [hrd.2] using h₁) hm
  have hpre_not_both :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1.role = .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).2.role = .Settled) := by
    have hstruct := transitionPEM_prePhase4_structural
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
    intro h
    have hp₀ : (transitionPEM_prePhase4 n Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1.role = .Resetting := by
      rw [hstruct.1, hr₀_role]
    rw [hp₀] at h
    exact Role.noConfusion h.1
  simpa [protocolPEM, transitionPEM_eq,
    transitionPEM_phase4_of_not_both_settled hpre_not_both] using hpre

private theorem epidemic_delta_m_phi_answers
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : s₀.role = .Resetting) (hs₁ : s₁.role = .Resetting)
    (hr₀_role :
      (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).1.role = .Resetting)
    (hr₁_role :
      (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).2.role = .Resetting)
    (h₀ : s₀.answer = m) (h₁ : s₁.answer = .phi)
    (hm : m ≠ .phi) :
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).1.answer = m ∧
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        ((s₀, x₀), (s₁, x₁))).2.answer = m := by
  have hrd :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) s₀ s₁
  have hpre :=
    transitionPEM_prePhase4_m_phi_answers
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
      (m := m) hs₀ hs₁ hr₀_role hr₁_role
      (by simpa [hrd.1] using h₀)
      (by simpa [hrd.2] using h₁) hm
  have hpre_not_both :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1.role = .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).2.role = .Settled) := by
    have hstruct := transitionPEM_prePhase4_structural
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
    intro h
    have hp₀ : (transitionPEM_prePhase4 n Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1.role = .Resetting := by
      rw [hstruct.1, hr₀_role]
    rw [hp₀] at h
    exact Role.noConfusion h.1
  simpa [protocolPEM, transitionPEM_eq,
    transitionPEM_phase4_of_not_both_settled hpre_not_both] using hpre

private theorem epidemic_step_resAns
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n} {i j : Fin n}
    (hReg : EpidemicRegion m C)
    (hPhase4 :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).1.role =
              .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).2.role =
              .Settled)) :
    EpidemicAnswerInv m
      (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  by_cases hij : i = j
  · subst hij
    simpa [Config.step, P] using hReg.2.1
  have hdelta := epidemic_delta_resAns (hn := hn) (m := m)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
    hPhase4 (hReg.2.1 i) (hReg.2.1 j)
  intro w
  by_cases hwi : w = i
  · subst hwi
    rw [Config.step_fst_state P C hij]
    simpa [P] using hdelta.1
  · by_cases hwj : w = j
    · subst hwj
      rw [Config.step_snd_state P C hij (fun h => hij h.symm)]
      simpa [P] using hdelta.2
    · have : C.step P i j w = C w := by
        simp [Config.step, hij, hwi, hwj, P]
      rw [this]
      exact hReg.2.1 w

private theorem epidemic_step_phi_imp_old_phi
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n} {i j w : Fin n}
    (hReg : EpidemicRegion m C)
    (hPhase4 :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).1.role =
              .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).2.role =
              .Settled))
    (hphi :
      ((C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) w).1.answer =
        .phi) :
    (C w).1.answer = .phi := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  by_cases hij : i = j
  · subst hij
    simpa [Config.step, P] using hphi
  have hdelta := epidemic_delta_phi_imp_old_phi (hn := hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
    (hReg.1 i) (hReg.1 j) hPhase4
  by_cases hwi : w = i
  ·
    have hphi' :
        ((P.δ (C i, C j)).1).answer = .phi := by
      have hphi_i : ((C.step P i j) i).1.answer = .phi := by
        simpa [hwi] using hphi
      rwa [Config.step_fst_state P C hij] at hphi_i
    simpa [hwi] using hdelta.1 hphi'
  · by_cases hwj : w = j
    ·
      have hphi' :
          ((P.δ (C i, C j)).2).answer = .phi := by
        have hphi_j : ((C.step P i j) j).1.answer = .phi := by
          simpa [hwj] using hphi
        rwa [Config.step_snd_state P C hij (fun h => hij h.symm)] at hphi_j
      simpa [hwj] using hdelta.2 hphi'
    · have hsame : C.step P i j w = C w := by
        simp [Config.step, hij, hwi, hwj, P]
      simpa [hsame, P] using hphi

theorem epidemicRegion_phiCount_nonincrease
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) (i j : Fin n)
    (hPhase4 :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).1.role =
              .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).2.role =
              .Settled)) :
    phiCount
        (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) ≤
      phiCount C := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hsub : phiAgents (C.step P i j) ⊆ phiAgents C := by
    intro w hw
    have hphi :
        ((C.step P i j) w).1.answer = .phi :=
      (Finset.mem_filter.mp hw).2
    have hOld :=
      epidemic_step_phi_imp_old_phi (hn := hn) (m := m)
        (C := C) (i := i) (j := j) (w := w) hReg hPhase4
        (by simpa [P] using hphi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hOld⟩
  calc
    phiCount (C.step P i j) = (phiAgents (C.step P i j)).card := by
      rw [phiAgents_card]
    _ ≤ (phiAgents C).card := Finset.card_le_card hsub
    _ = phiCount C := by rw [phiAgents_card]

theorem epidemicRegion_step_closed
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) (i j : Fin n)
    (hPhase4 :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).1.role =
              .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn) (C i).1 (C j).1 (C i).2 (C j).2).2.role =
              .Settled))
    (hAllReset :
      ∀ w : Fin n,
        ((C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j)
          w).1.role = .Resetting) :
    EpidemicRegion m
      (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  refine ⟨hAllReset, ?_, hReg.2.2.1, ?_⟩
  · exact epidemic_step_resAns (hn := hn) (m := m)
      (C := C) (i := i) (j := j) hReg hPhase4
  · rcases hReg.2.2.2 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hInv' := epidemic_step_resAns (hn := hn) (m := m)
      (C := C) (i := i) (j := j) hReg hPhase4
    rcases hInv' w with hm' | hphi'
    · exact hm'
    · have hOldPhi :=
        epidemic_step_phi_imp_old_phi (hn := hn) (m := m)
          (C := C) (i := i) (j := j) (w := w) hReg hPhase4
          (by simpa [P] using hphi')
      exact False.elim (hReg.2.2.1 (hw.symm.trans hOldPhi))

private theorem epidemic_pair_step_answers
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n} {i j : Fin n}
    (hReg : EpidemicRegion m C)
    (hr₀_role :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Resetting)
    (hr₁_role :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Resetting)
    (hi_phi : (C i).1.answer = .phi)
    (hj_m : (C j).1.answer = m) :
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        (C i, C j)).1.answer = m ∧
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        (C i, C j)).2.answer = m :=
  epidemic_delta_phi_m_answers (hn := hn) (m := m)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
    (hReg.1 i) (hReg.1 j) hr₀_role hr₁_role hi_phi hj_m hReg.2.2.1

private theorem epidemic_pair_step_answers_symm
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n} {i j : Fin n}
    (hReg : EpidemicRegion m C)
    (hr₀_role :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Resetting)
    (hr₁_role :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Resetting)
    (hi_m : (C i).1.answer = m)
    (hj_phi : (C j).1.answer = .phi) :
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        (C i, C j)).1.answer = m ∧
    ((protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
        (C i, C j)).2.answer = m :=
  epidemic_delta_m_phi_answers (hn := hn) (m := m)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
    (hReg.1 i) (hReg.1 j) hr₀_role hr₁_role hi_m hj_phi hReg.2.2.1

theorem epidemicRegion_phiPair_descent
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) (p : Fin n × Fin n)
    (hp : p ∈ phiNonPhiPairs C)
    (hr₀_role :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C p.1).1, (C p.2).1)).1.role =
        .Resetting)
    (hr₁_role :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C p.1).1, (C p.2).1)).2.role =
        .Resetting) :
    phiCount
        (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          p.1 p.2) <
      phiCount C := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hp_off := (phiNonPhiPairs_subset_offDiagonal C) hp
  have hp_ne : p.1 ≠ p.2 := by
    simpa [Probability.mem_offDiagonalPairs] using hp_off
  have hpre_not_both :
      ¬ ((transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)
            (C p.1).1 (C p.2).1 (C p.1).2 (C p.2).2).1.role = .Settled ∧
          (transitionPEM_prePhase4 n Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)
            (C p.1).1 (C p.2).1 (C p.1).2 (C p.2).2).2.role = .Settled) := by
    have hstruct := transitionPEM_prePhase4_structural
      (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C p.1).1) (s₁ := (C p.2).1)
      (x₀ := (C p.1).2) (x₁ := (C p.2).2)
    intro h
    have hp₀ : (transitionPEM_prePhase4 n Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn)
          (C p.1).1 (C p.2).1 (C p.1).2 (C p.2).2).1.role = .Resetting := by
      rw [hstruct.1, hr₀_role]
    rw [hp₀] at h
    exact Role.noConfusion h.1
  have hsub : phiAgents (C.step P p.1 p.2) ⊆ phiAgents C := by
    intro w hw
    have hphi :
        ((C.step P p.1 p.2) w).1.answer = .phi :=
      (Finset.mem_filter.mp hw).2
    have hOld :=
      epidemic_step_phi_imp_old_phi (hn := hn) (m := m)
        (C := C) (i := p.1) (j := p.2) (w := w) hReg hpre_not_both
        (by simpa [P] using hphi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hOld⟩
  have hwitness :
      ∃ w, w ∈ phiAgents C ∧ w ∉ phiAgents (C.step P p.1 p.2) := by
    rw [phiNonPhiPairs, Finset.mem_union] at hp
    rcases hp with hp | hp
    · have hpair :
          p.1 ∈ phiAgents C ∧ p.2 ∈ nonPhiAgents C := by
        simpa using hp
      have hi_phi : (C p.1).1.answer = .phi :=
        (Finset.mem_filter.mp hpair.1).2
      have hj_m : (C p.2).1.answer = m :=
        answer_eq_m_of_inv_nonphi hReg.2.1 (Finset.mem_filter.mp hpair.2).2
      have hdelta :=
        epidemic_pair_step_answers (hn := hn) (m := m)
          (C := C) hReg hr₀_role hr₁_role hi_phi hj_m
      refine ⟨p.1, hpair.1, ?_⟩
      intro hmem'
      have hphi' : ((C.step P p.1 p.2) p.1).1.answer = .phi :=
        (Finset.mem_filter.mp hmem').2
      have hpost : ((C.step P p.1 p.2) p.1).1.answer = m := by
        rw [Config.step_fst_state P C hp_ne]
        simpa [P] using hdelta.1
      exact hReg.2.2.1 (hpost.symm.trans hphi')
    · have hpair :
          p.1 ∈ nonPhiAgents C ∧ p.2 ∈ phiAgents C := by
        simpa using hp
      have hi_m : (C p.1).1.answer = m :=
        answer_eq_m_of_inv_nonphi hReg.2.1 (Finset.mem_filter.mp hpair.1).2
      have hj_phi : (C p.2).1.answer = .phi :=
        (Finset.mem_filter.mp hpair.2).2
      have hdelta :=
        epidemic_pair_step_answers_symm (hn := hn) (m := m)
          (C := C) hReg hr₀_role hr₁_role hi_m hj_phi
      refine ⟨p.2, hpair.2, ?_⟩
      intro hmem'
      have hphi' : ((C.step P p.1 p.2) p.2).1.answer = .phi :=
        (Finset.mem_filter.mp hmem').2
      have hpost : ((C.step P p.1 p.2) p.2).1.answer = m := by
        rw [Config.step_snd_state P C hp_ne (fun h => hp_ne h.symm)]
        simpa [P] using hdelta.2
      exact hReg.2.2.1 (hpost.symm.trans hphi')
  have hssub : phiAgents (C.step P p.1 p.2) ⊂ phiAgents C := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact hwitness
  calc
    phiCount (C.step P p.1 p.2) = (phiAgents (C.step P p.1 p.2)).card := by
      rw [phiAgents_card]
    _ < (phiAgents C).card := Finset.card_lt_card hssub
    _ = phiCount C := by rw [phiAgents_card]

end SSEM

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Leaders never disappear (P2 Lemma 2.3, P3 Lemma 1(h))

A leader bit changes only by deduplication, which turns the responder from `L` to `F` while the
initiator stays `L`, or by a trigger, which writes `L`. Hence if one of the two agents of an
interaction is a leader before it, one of them is a leader after it (`transitionPEM_hasL`), and
"some agent is a leader" is invariant under every step of P_EM (`exists_leader_step`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.Propagation

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-- One of the two states of a pair is a leader. -/
def HasL (p : AgentState n × AgentState n) : Prop := p.1.leader = .L ∨ p.2.leader = .L

theorem resetOSSR_leader_eq (Emax : ℕ) (hn : 0 < n) (s : AgentState n) :
    (resetOSSR Emax hn s).leader = s.leader := by
  unfold resetOSSR
  cases h : s.leader <;> simp

theorem processAgent_leader (Emax Dmax : ℕ) (hn : 0 < n) (s : AgentState n) (o : ℕ) (b : Bool) :
    (processAgent Emax Dmax hn s o b).leader = s.leader := by
  unfold processAgent
  dsimp only
  split_ifs <;> simp [resetOSSR_leader_eq]

theorem prRecruit_leader (Dmax : ℕ) (a b : AgentState n) :
    (prRecruit Dmax a b).1.leader = a.leader ∧ (prRecruit Dmax a b).2.leader = b.leader := by
  unfold prRecruit
  split_ifs <;> simp

theorem prSync_leader (a b : AgentState n) :
    (prSync a b).1.leader = a.leader ∧ (prSync a b).2.leader = b.leader := by
  unfold prSync
  split_ifs <;> simp

theorem propagateReset_leader (Emax Dmax : ℕ) (hn : 0 < n) (a b : AgentState n) :
    (propagateReset Emax Dmax hn a b).1.leader = a.leader ∧
      (propagateReset Emax Dmax hn a b).2.leader = b.leader := by
  rw [propagateReset_eq]
  simp [processAgent_leader, prSync_leader, prRecruit_leader]

theorem prDedup_hasL (p : AgentState n × AgentState n) (h : HasL p) : HasL (prDedup p) := by
  unfold prDedup HasL at *
  split_ifs with hc
  · exact Or.inl hc.1
  · exact h

theorem rankDeltaOSSR_hasL {Rmax Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (h : a.leader = .L ∨ b.leader = .L) : HasL (rankDeltaOSSR Rmax Emax Dmax hn (a, b)) := by
  by_cases hr : a.role = .Resetting ∨ b.role = .Resetting
  · rw [rankDeltaOSSR_eq_of_resetting hr]
    apply prDedup_hasL
    unfold HasL
    rw [(propagateReset_leader _ _ _ _ _).1, (propagateReset_leader _ _ _ _ _).2]
    exact h
  · simp only [rankDeltaOSSR, if_neg hr]
    split_ifs <;> simp_all [HasL]

theorem preAgent_leader (trank : ℕ) (s r : AgentState n) :
    (preAgent n trank s r).leader = r.leader := by
  unfold preAgent
  dsimp only
  split_ifs <;> simp

theorem preEpi_leader (a₀ a₁ : AgentState n) :
    (preEpi a₀ a₁).1.leader = a₀.leader ∧ (preEpi a₀ a₁).2.leader = a₁.leader := by
  unfold preEpi
  split_ifs <;> simp

theorem phase4_swap_hasL (a b : AgentState n) (x₀ x₁ : Opinion) (h : HasL (a, b)) :
    HasL (phase4_swap a b x₀ x₁) := by
  unfold phase4_swap
  split_ifs
  · exact h.symm
  · exact h

theorem phase4_decide_leader (b₀ b₁ : AgentState n) (x₀ x₁ : Opinion) :
    (phase4_decide n b₀ b₁ x₀ x₁).1.leader = b₀.leader ∧
      (phase4_decide n b₀ b₁ x₀ x₁).2.leader = b₁.leader := by
  unfold phase4_decide
  dsimp only
  split_ifs <;> simp

theorem phase4_propagate_hasL (Rmax : ℕ) (b₀ b₁ : AgentState n) (h : HasL (b₀, b₁)) :
    HasL (phase4_propagate n Rmax b₀ b₁) := by
  unfold HasL at h
  unfold phase4_propagate
  dsimp only
  split_ifs <;> simp_all [HasL]

theorem phase4_hasL (Rmax : ℕ) (p : AgentState n × AgentState n) (x₀ x₁ : Opinion)
    (h : HasL p) : HasL (transitionPEM_phase4 n Rmax p x₀ x₁) := by
  obtain ⟨a, b⟩ := p
  unfold transitionPEM_phase4
  dsimp only
  split_ifs
  · have h1 := phase4_swap_hasL a b x₀ x₁ h
    rcases hsw : phase4_swap a b x₀ x₁ with ⟨c₀, c₁⟩
    rw [hsw] at h1
    dsimp only
    have h2 : HasL (phase4_decide n c₀ c₁ x₀ x₁) := by
      unfold HasL at h1 ⊢
      rw [(phase4_decide_leader _ _ _ _).1, (phase4_decide_leader _ _ _ _).2]
      exact h1
    rcases hd : phase4_decide n c₀ c₁ x₀ x₁ with ⟨d₀, d₁⟩
    rw [hd] at h2
    dsimp only
    exact phase4_propagate_hasL Rmax d₀ d₁ h2
  · exact h

theorem transitionPEM_hasL {trank Rmax Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n)
    (x₀ x₁ : Opinion) (h : a.leader = .L ∨ b.leader = .L) :
    HasL (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁))) := by
  rw [transitionPEM_eq]
  apply phase4_hasL
  rw [prePhase4_eq]
  have hr := rankDeltaOSSR_hasL (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) a b h
  unfold HasL at hr ⊢
  rw [(preEpi_leader _ _).1, (preEpi_leader _ _).2, preAgent_leader, preAgent_leader]
  exact hr

/-- **Some agent is a leader** is invariant under every step of P_EM. -/
theorem exists_leader_step {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) (h : ∃ v, (C v).1.leader = .L) (i j : Fin n) :
    ∃ v, ((C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) v).1.leader
      = .L := by
  obtain ⟨w, hw⟩ := h
  by_cases hij : i = j
  · exact ⟨w, by simp [Config.step, hij, hw]⟩
  by_cases hwi : w = i
  · subst hwi
    have hL := transitionPEM_hasL (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (C w).1 (C j).1 (C w).2 (C j).2 (Or.inl hw)
    rcases hL with hL | hL
    · exact ⟨w, by simpa [Config.step, hij, protocolPEM] using hL⟩
    · exact ⟨j, by simpa [Config.step, hij, Ne.symm hij, protocolPEM] using hL⟩
  by_cases hwj : w = j
  · subst hwj
    have hL := transitionPEM_hasL (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (C i).1 (C w).1 (C i).2 (C w).2 (Or.inr hw)
    rcases hL with hL | hL
    · exact ⟨i, by simpa [Config.step, hij, protocolPEM] using hL⟩
    · exact ⟨w, by simpa [Config.step, hij, Ne.symm hij, protocolPEM] using hL⟩
  · exact ⟨w, by simp [Config.step, hij, hwi, hwj, hw]⟩

end Ripple.PopulationProtocol.SSEM

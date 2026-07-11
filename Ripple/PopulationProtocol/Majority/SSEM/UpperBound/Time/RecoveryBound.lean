import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.RankingBound
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.RecoveryBridge

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

abbrev PEMProtocolCoupled' (n Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

noncomputable def maxRC (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.sup Finset.univ
    (fun w : Fin n => if (C w).1.role = .Resetting then (C w).1.resetcount else 0)

theorem maxRC_le_of_all_le {C : Config (AgentState n) Opinion n} {M : ℕ}
    (h : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount ≤ M) :
    maxRC C ≤ M := by
  unfold maxRC; apply Finset.sup_le; intro w _
  by_cases hr : (C w).1.role = .Resetting
  · simp [hr, h w hr]
  · simp [hr]

structure StrongRecoveryInv (Rmax Dmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop where
  allResetting : ∀ w : Fin n, (C w).1.role = .Resetting
  allCorrect : ∀ w : Fin n, (C w).1.answer = majorityAnswer C
  rcBounded : ∀ w : Fin n, (C w).1.resetcount ≤ Rmax

def Phase1Goal (Rmax Dmax : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  IsConsensusConfig C ∨ (StrongRecoveryInv Rmax Dmax C ∧ maxRC C = 0) ∨
  (∃ w : Fin n, (C w).1.role ≠ .Resetting)

/-! ### Auxiliary lemmas -/

private theorem resetOSSR_rc_preserved {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).resetcount = s.resetcount := by
  unfold resetOSSR; cases s.leader <;> rfl

private theorem processAgent_rc_preserved {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) :
    (processAgent Emax Dmax hn s oldRc pr).resetcount = s.resetcount := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2]; simp only []
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_rc_preserved]
      · rw [if_neg h3]
    · rw [if_neg h2]; simp only []
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_rc_preserved]
      · rw [if_neg h3]
  · rw [if_neg h1]

private theorem propagateReset_rc_of_both_resetting {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting) :
    (propagateReset Emax Dmax hn s t).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (propagateReset Emax Dmax hn s t).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) := by
  unfold propagateReset
  dsimp only []
  simp only [hs, ht,
    show ¬(t.role ≠ .Resetting) from not_not.mpr ht,
    show ¬(s.role ≠ .Resetting) from not_not.mpr hs,
    show ¬(s.role = .Resetting ∧ 0 < s.resetcount ∧ t.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h ht,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h hs,
    show ¬(Role.Resetting ≠ .Resetting) from not_not.mpr rfl,
    show (Role.Resetting == Role.Resetting) = true from rfl,
    and_true, and_false, ite_false, and_self, ite_true, true_and, not_true]
  set M := Nat.max (s.resetcount - 1) (t.resetcount - 1)
  constructor
  · exact processAgent_rc_preserved _ _ _
  · exact processAgent_rc_preserved _ _ _

private theorem rankDeltaOSSR_rc_of_both_resetting
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have hpr := propagateReset_rc_of_both_resetting (Emax := Emax) (Dmax := Dmax) (hn := hn) hs ht
  constructor
  · exact hpr.1
  · split_ifs <;> exact hpr.2

private theorem rc_max_sub_le_max (a b : ℕ) :
    Nat.max (a - 1) (b - 1) ≤ Nat.max a b := by
  simp only [Nat.max]
  exact max_le_max (Nat.sub_le a 1) (Nat.sub_le b 1)

private theorem step_bystander_eq' {P : Protocol (AgentState n) Opinion Output}
    {C : Config (AgentState n) Opinion n}
    {i j w : Fin n} (hij : i ≠ j) (hwi : w ≠ i) (hwj : w ≠ j) :
    (C.step P i j w) = C w := by
  simp [Config.step, hij, hwi, hwj]

/-! ### Rank-zero of a Settled-from-Resetting agent -/

private theorem processAgent_settled_rank_zero {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} (oldRc : ℕ) (pr : Bool)
    (hres : s.role = .Resetting)
    (h : (processAgent Emax Dmax hn s oldRc pr).role = .Settled) :
    (processAgent Emax Dmax hn s oldRc pr).rank.val = 0 := by
  unfold processAgent at h ⊢
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1] at h ⊢
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2] at h ⊢; simp only [] at h ⊢
      by_cases h3 : ((({s with delaytimer := Dmax} : AgentState n)).delaytimer = 0 ∨ (!pr) = true)
      · rw [if_pos h3] at h ⊢
        cases hl : s.leader with
        | L => simp [resetOSSR, hl]
        | F => simp [resetOSSR, hl] at h
      · rw [if_neg h3] at h ⊢
        have h' : s.role = .Settled := h
        rw [hres] at h'; exact absurd h' (by decide)
    · rw [if_neg h2] at h ⊢; simp only [] at h ⊢
      by_cases h3 : ((({s with delaytimer := s.delaytimer - 1} : AgentState n)).delaytimer = 0 ∨ (!pr) = true)
      · rw [if_pos h3] at h ⊢
        cases hl : s.leader with
        | L => simp [resetOSSR, hl]
        | F => simp [resetOSSR, hl] at h
      · rw [if_neg h3] at h ⊢
        have h' : s.role = .Settled := h
        rw [hres] at h'; exact absurd h' (by decide)
  · rw [if_neg h1] at h ⊢
    rw [hres] at h; exact absurd h (by decide)

private theorem propagateReset_settled_rank_zero {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting) :
    ((propagateReset Emax Dmax hn s t).1.role = .Settled →
       (propagateReset Emax Dmax hn s t).1.rank.val = 0) ∧
    ((propagateReset Emax Dmax hn s t).2.role = .Settled →
       (propagateReset Emax Dmax hn s t).2.rank.val = 0) := by
  unfold propagateReset
  rw [if_neg (show ¬(s.role = .Resetting ∧ 0 < s.resetcount ∧ t.role ≠ .Resetting) from
        fun ⟨_, _, h⟩ => h ht),
      if_neg (show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
        fun ⟨_, _, h⟩ => h hs)]
  simp only [hs, ht, and_self, if_true]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact processAgent_settled_rank_zero _ _ (by simpa using hs) h
  · exact processAgent_settled_rank_zero _ _ (by simpa using ht) h

private theorem rd_settled_rank_zero
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting) :
    ((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled →
       (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank.val = 0) ∧
    ((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled →
       (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.rank.val = 0) := by
  have hpa := propagateReset_settled_rank_zero (Emax := Emax) (Dmax := Dmax) (hn := hn) hs ht
  unfold rankDeltaOSSR
  simp only [hs, true_or, if_true]
  set pa := propagateReset Emax Dmax hn s t with hpadef
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hpa.1 h
  · split_ifs at h ⊢ with hd
    · exact hpa.2 h
    · exact hpa.2 h

private theorem phase4_rank_zero_settled_stays
    {Rmax : ℕ} (hn3 : 3 ≤ n) {a₀ a₁ : AgentState n} {x₀ x₁ : Opinion}
    (h0 : a₀.role = .Settled) (h1 : a₁.role = .Settled)
    (hr0 : a₀.rank.val = 0) (hr1 : a₁.rank.val = 0) :
    (transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).1.role = .Settled ∧
    (transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁).2.role = .Settled := by
  have hceil : ceilHalf n ≠ 1 := by unfold ceilHalf; omega
  unfold transitionPEM_phase4
  simp only [h0, h1, and_self, if_true]
  have hnoswap : phase4_swap a₀ a₁ x₀ x₁ = (a₀, a₁) := by
    unfold phase4_swap
    rw [if_neg]
    rintro ⟨hlt, _, _⟩
    rw [Fin.lt_def, hr0, hr1] at hlt; exact absurd hlt (by omega)
  rw [hnoswap]
  have hdec : (phase4_decide n a₀ a₁ x₀ x₁).1.role = .Settled ∧
      (phase4_decide n a₀ a₁ x₀ x₁).1.rank.val = 0 ∧
      (phase4_decide n a₀ a₁ x₀ x₁).2.role = .Settled ∧
      (phase4_decide n a₀ a₁ x₀ x₁).2.rank.val = 0 := by
    unfold phase4_decide
    split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all
  set c := phase4_decide n a₀ a₁ x₀ x₁ with hc
  unfold phase4_propagate
  rw [if_neg (show ¬(c.1.rank.val + 1 = ceilHalf n) from by rw [hdec.2.1]; simpa using fun h => hceil h.symm),
      if_neg (show ¬(c.2.rank.val + 1 = ceilHalf n) from by rw [hdec.2.2.2]; simpa using fun h => hceil h.symm)]
  exact ⟨hdec.1, hdec.2.2.1⟩

private theorem rd_not_both_settled_of_step_resetting
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hi_res' : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j i).1.role = .Resetting) :
    ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Settled ∧
       (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Settled) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set rd := rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
  intro ⟨hrd_s0, hrd_s1⟩
  have hrank := rd_settled_rank_zero (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (hInv.allResetting i) (hInv.allResetting j)
  have hr0 : rd.1.rank.val = 0 := hrank.1 hrd_s0
  have hr1 : rd.2.rank.val = 0 := hrank.2 hrd_s1
  set pre := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C i).1 (C j).1 (C i).2 (C j).2
  have h_pre_s0 : pre.1.role = .Settled := by rw [h_struct.1]; exact hrd_s0
  have h_pre_s1 : pre.2.role = .Settled := by rw [h_struct.2.2.2.2.2.2.1]; exact hrd_s1
  have h_pre_r0 : pre.1.rank.val = 0 := by
    have h : pre.1.rank = rd.1.rank := h_struct.2.2.1; rw [h]; exact hr0
  have h_pre_r1 : pre.2.rank.val = 0 := by
    have h : pre.2.rank = rd.2.rank := h_struct.2.2.2.2.2.2.2.2.1; rw [h]; exact hr1
  have hphase_settled :
      (transitionPEM_phase4 n Rmax pre (C i).2 (C j).2).1.role = .Settled :=
    (phase4_rank_zero_settled_stays (n := n) (Rmax := Rmax) hn3
      (x₀ := (C i).2) (x₁ := (C j).2) h_pre_s0 h_pre_s1 h_pre_r0 h_pre_r1).1
  have h_step_i : (C.step P i j i).1 = (P.δ (C i, C j)).1 :=
    Config.step_fst_state P C hij
  have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax pre (C i).2 (C j).2 := rfl
  rw [h_step_i, h_delta_eq, hphase_settled] at hi_res'
  exact absurd hi_res' (by decide)

private theorem rd_not_both_settled_of_step_resetting_snd
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hj_res' : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j j).1.role = .Resetting) :
    ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Settled ∧
       (rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Settled) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set rd := rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
  intro ⟨hrd_s0, hrd_s1⟩
  have hrank := rd_settled_rank_zero (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (hInv.allResetting i) (hInv.allResetting j)
  have hr0 : rd.1.rank.val = 0 := hrank.1 hrd_s0
  have hr1 : rd.2.rank.val = 0 := hrank.2 hrd_s1
  set pre := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C i).1 (C j).1 (C i).2 (C j).2
  have h_pre_s0 : pre.1.role = .Settled := by rw [h_struct.1]; exact hrd_s0
  have h_pre_s1 : pre.2.role = .Settled := by rw [h_struct.2.2.2.2.2.2.1]; exact hrd_s1
  have h_pre_r0 : pre.1.rank.val = 0 := by
    have h : pre.1.rank = rd.1.rank := h_struct.2.2.1; rw [h]; exact hr0
  have h_pre_r1 : pre.2.rank.val = 0 := by
    have h : pre.2.rank = rd.2.rank := h_struct.2.2.2.2.2.2.2.2.1; rw [h]; exact hr1
  have hphase_settled :
      (transitionPEM_phase4 n Rmax pre (C i).2 (C j).2).2.role = .Settled :=
    (phase4_rank_zero_settled_stays (n := n) (Rmax := Rmax) hn3
      (x₀ := (C i).2) (x₁ := (C j).2) h_pre_s0 h_pre_s1 h_pre_r0 h_pre_r1).2
  have h_step_j : (C.step P i j j).1 = (P.δ (C i, C j)).2 :=
    Config.step_snd_state P C hij (Ne.symm hij)
  have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax pre (C i).2 (C j).2 := rfl
  rw [h_step_j, h_delta_eq, hphase_settled] at hj_res'
  exact absurd hj_res' (by decide)



/-! ### Delaytimer bound lemmas (infrastructure for sub-case 1) -/

private theorem resetOSSR_dt_eq {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).delaytimer = s.delaytimer := by
  unfold resetOSSR; cases s.leader <;> rfl

private theorem processAgent_dt_le {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) (hdt : s.delaytimer ≤ Dmax) :
    (processAgent Emax Dmax hn s oldRc pr).delaytimer ≤ Dmax := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2]; simp only []
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_dt_eq]
      · rw [if_neg h3]
    · rw [if_neg h2]; simp only []
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_dt_eq]; exact le_trans (Nat.sub_le _ _) hdt
      · rw [if_neg h3]; exact le_trans (Nat.sub_le _ _) hdt
  · rw [if_neg h1]; exact hdt

private theorem propagateReset_dt_bounded {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hds : s.delaytimer ≤ Dmax) (hdt : t.delaytimer ≤ Dmax) :
    (propagateReset Emax Dmax hn s t).1.delaytimer ≤ Dmax ∧
    (propagateReset Emax Dmax hn s t).2.delaytimer ≤ Dmax := by
  unfold propagateReset
  rw [if_neg (show ¬(s.role = .Resetting ∧ 0 < s.resetcount ∧ t.role ≠ .Resetting) from
        fun ⟨_, _, h⟩ => h ht),
      if_neg (show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
        fun ⟨_, _, h⟩ => h hs)]
  simp only [hs, ht, and_self, if_true]
  exact ⟨processAgent_dt_le _ _ _ hds, processAgent_dt_le _ _ _ hdt⟩

private theorem rankDeltaOSSR_dt_bounded {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hds : s.delaytimer ≤ Dmax) (hdt : t.delaytimer ≤ Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer ≤ Dmax := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  exact (propagateReset_dt_bounded hs ht hds hdt).1

private theorem rankDeltaOSSR_dt_bounded_snd {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hds : s.delaytimer ≤ Dmax) (hdt : t.delaytimer ≤ Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer ≤ Dmax := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  split_ifs <;> exact (propagateReset_dt_bounded hs ht hds hdt).2

/-! ### Main theorems -/

set_option maxHeartbeats 1600000 in
theorem strongRecoveryInv_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax Dmax C) (i j : Fin n) :
    StrongRecoveryInv Rmax Dmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ∨
    Phase1Goal Rmax Dmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn with hP
  set C' := C.step P i j with hC'
  by_cases hij : i = j
  · left
    have : C' = C := by simp [C', Config.step, hij]
    rw [this]; exact hInv
  · by_cases h_all_res : ∀ w : Fin n, (C' w).1.role = .Resetting
    · left
      have hi_res := hInv.allResetting i
      have hj_res := hInv.allResetting j
      have h_not_both_settled_rd :=
        rd_not_both_settled_of_step_resetting hn3 hij hInv (h_all_res i)
      have h_struct := transitionPEM_prePhase4_structural
        (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
      have h_not_both_settled_pre :
          ¬ ((transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
                (C i).1 (C j).1 (C i).2 (C j).2).1.role = .Settled ∧
              (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
                (C i).1 (C j).1 (C i).2 (C j).2).2.role = .Settled) := by
        rw [h_struct.1, h_struct.2.2.2.2.2.2.1]; exact h_not_both_settled_rd
      have hm := majorityAnswer_ne_phi C
      have h_no_entry_fst :
          ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).1.role = .Resetting ∧
             (C i).1.role ≠ .Resetting) :=
        fun ⟨_, h⟩ => h hi_res
      have h_no_entry_snd :
          ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C i).1, (C j).1)).2.role = .Resetting ∧
             (C j).1.role ≠ .Resetting) :=
        fun ⟨_, h⟩ => h hj_res
      have h_ans_all : ∀ w : Fin n, (C' w).1.answer = majorityAnswer C :=
        step_preserves_uniform_answer_of_no_reset_entry
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hm hij (hInv.allCorrect) h_no_entry_fst h_no_entry_snd h_not_both_settled_rd
      have h_rd_rc := rankDeltaOSSR_rc_of_both_resetting hi_res hj_res
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax
          (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
            (C i).1 (C j).1 (C i).2 (C j).2) (C i).2 (C j).2 := rfl
      have h_phase4_id := transitionPEM_phase4_of_not_both_settled (n := n) (Rmax := Rmax)
        (a := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C i).1 (C j).1 (C i).2 (C j).2)
        (x₀ := (C i).2) (x₁ := (C j).2) h_not_both_settled_pre
      have hbound : Nat.max ((C i).1.resetcount - 1) ((C j).1.resetcount - 1) ≤ Rmax :=
        le_trans (rc_max_sub_le_max _ _) (max_le (hInv.rcBounded i) (hInv.rcBounded j))
      constructor
      · exact h_all_res
      · rw [show majorityAnswer C' = majorityAnswer C from majorityAnswer_step_eq C i j]
        exact h_ans_all
      · intro w
        by_cases hwi : w = i
        · subst hwi
          have hstep : (C' w).1 = (P.δ (C w, C j)).1 := Config.step_fst_state P C hij
          rw [hstep, h_delta_eq, h_phase4_id, h_struct.2.2.2.2.1, h_rd_rc.1]
          exact hbound
        · by_cases hwj : w = j
          · subst hwj
            have hstep : (C' w).1 = (P.δ (C i, C w)).2 :=
              Config.step_snd_state P C hij (Ne.symm hij)
            rw [hstep, h_delta_eq, h_phase4_id,
              h_struct.2.2.2.2.2.2.2.2.2.2.1, h_rd_rc.2]
            exact hbound
          · rw [show (C' w) = C w from step_bystander_eq' hij hwi hwj]
            exact hInv.rcBounded w

    · right; right; right
      push_neg at h_all_res; exact h_all_res

/-- When the step output at position `i` is Resetting (under StrongRecoveryInv,
`n ≥ 3`), its resetcount is exactly `max(rc_i - 1, rc_j - 1)`. -/
private theorem step_fst_rc_eq {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n} {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hi_res : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j i).1.role = .Resetting) :
    (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j i).1.resetcount =
      Nat.max ((C i).1.resetcount - 1) ((C j).1.resetcount - 1) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
  have h_nbs_rd := rd_not_both_settled_of_step_resetting hn3 hij hInv hi_res
  have h_nbs_pre : ¬ ((transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C i).1 (C j).1 (C i).2 (C j).2).1.role = .Settled ∧
      (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C i).1 (C j).1 (C i).2 (C j).2).2.role = .Settled) := by
    rw [h_struct.1, h_struct.2.2.2.2.2.2.1]; exact h_nbs_rd
  have h_rd_rc := rankDeltaOSSR_rc_of_both_resetting (hInv.allResetting i) (hInv.allResetting j)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
  have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax
      (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C i).1 (C j).1 (C i).2 (C j).2) (C i).2 (C j).2 := rfl
  have h_phase4_id := transitionPEM_phase4_of_not_both_settled (n := n) (Rmax := Rmax)
    (a := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C i).1 (C j).1 (C i).2 (C j).2)
    (x₀ := (C i).2) (x₁ := (C j).2) h_nbs_pre
  rw [Config.step_fst_state P C hij, h_delta_eq, h_phase4_id, h_struct.2.2.2.2.1, h_rd_rc.1]

private theorem step_snd_rc_eq {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n} {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hj_res : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j j).1.role = .Resetting) :
    (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j j).1.resetcount =
      Nat.max ((C i).1.resetcount - 1) ((C j).1.resetcount - 1) := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  have h_struct := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C i).1) (s₁ := (C j).1) (x₀ := (C i).2) (x₁ := (C j).2)
  have h_nbs_rd := rd_not_both_settled_of_step_resetting_snd hn3 hij hInv hj_res
  have h_nbs_pre : ¬ ((transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C i).1 (C j).1 (C i).2 (C j).2).1.role = .Settled ∧
      (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C i).1 (C j).1 (C i).2 (C j).2).2.role = .Settled) := by
    rw [h_struct.1, h_struct.2.2.2.2.2.2.1]; exact h_nbs_rd
  have h_rd_rc := rankDeltaOSSR_rc_of_both_resetting (hInv.allResetting i) (hInv.allResetting j)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
  have h_delta_eq : P.δ (C i, C j) = transitionPEM_phase4 n Rmax
      (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C i).1 (C j).1 (C i).2 (C j).2) (C i).2 (C j).2 := rfl
  have h_phase4_id := transitionPEM_phase4_of_not_both_settled (n := n) (Rmax := Rmax)
    (a := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C i).1 (C j).1 (C i).2 (C j).2)
    (x₀ := (C i).2) (x₁ := (C j).2) h_nbs_pre
  rw [Config.step_snd_state P C hij (Ne.symm hij), h_delta_eq, h_phase4_id,
    h_struct.2.2.2.2.2.2.2.2.2.2.1, h_rd_rc.2]

private theorem rc_le_maxRC {Rmax Dmax : ℕ} {C : Config (AgentState n) Opinion n}
    (hInv : StrongRecoveryInv Rmax Dmax C) (w : Fin n) :
    (C w).1.resetcount ≤ maxRC C := by
  unfold maxRC
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ w))
  simp [hInv.allResetting w]

set_option maxHeartbeats 1600000 in
theorem maxRC_step_le_strong
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax Dmax C) (i j : Fin n) :
    maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ≤ maxRC C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn with hP
  set C' := C.step P i j with hC'
  by_cases hij : i = j
  · rw [show C' = C from by simp [C', Config.step, hij]]
  · apply maxRC_le_of_all_le
    intro w hwres
    by_cases hwi : w = i
    · subst hwi
      rw [step_fst_rc_eq hn3 hij hInv hwres]
      exact le_trans (rc_max_sub_le_max _ _) (max_le (rc_le_maxRC hInv w) (rc_le_maxRC hInv j))
    · by_cases hwj : w = j
      · subst hwj
        rw [step_snd_rc_eq hn3 hij hInv hwres]
        exact le_trans (rc_max_sub_le_max _ _) (max_le (rc_le_maxRC hInv i) (rc_le_maxRC hInv w))
      · rw [show (C' w) = C w from step_bystander_eq' hij hwi hwj] at hwres ⊢
        exact rc_le_maxRC hInv w

/-! ### RC-level potential for Phase 1

The potential `rcLevelPotential` combines maxRC and the count of agents at the
max level into a single natural number that strictly decreases with probability
≥ 1/n per step. This replaces the FALSE maxRC single-step descent.

Key insight: under StrongRecoveryInv (all Resetting), if we pick any agent u at
maxRC as initiator and any v ≠ u as responder, both get
`rc = max(u.rc-1, v.rc-1) ≤ maxRC-1`. So the count of agents at maxRC
decreases by at least 1. When it hits 0, maxRC drops, resetting the counter. -/

/-- Number of agents whose resetcount equals `maxRC C`. -/
noncomputable def rcMaxCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter fun w : Fin n =>
    (C w).1.role = .Resetting ∧ (C w).1.resetcount = maxRC C).card

/-- Combined potential: `(maxRC - 1) * n + rcMaxCount`.
When `maxRC = 0` the potential is 0 (goal reached).
Otherwise it is `(maxRC - 1) * n + #{agents at max level}`. -/
noncomputable def rcLevelPotential (C : Config (AgentState n) Opinion n) : ℕ :=
  if maxRC C = 0 then 0 else (maxRC C - 1) * n + rcMaxCount C

/-- rcLevelPotential is bounded above by `Rmax * n`. -/
theorem rcLevelPotential_le_Rmax_n {Rmax Dmax : ℕ}
    {C : Config (AgentState n) Opinion n}
    (hInv : StrongRecoveryInv Rmax Dmax C) :
    rcLevelPotential C ≤ Rmax * n := by
  unfold rcLevelPotential
  split
  · exact Nat.zero_le _
  · next h =>
    have hmaxRC_le : maxRC C ≤ Rmax := maxRC_le_of_all_le (fun w _ => hInv.rcBounded w)
    have hRmax_pos : 1 ≤ Rmax := by
      have : 0 < maxRC C := Nat.pos_of_ne_zero h
      omega
    have hcount_le : rcMaxCount C ≤ n := by
      unfold rcMaxCount
      exact le_trans (Finset.card_filter_le _ _) (by simp [Finset.card_univ])
    calc (maxRC C - 1) * n + rcMaxCount C
        ≤ (Rmax - 1) * n + n := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hmaxRC_le 1)
          · exact hcount_le
      _ = Rmax * n := by
          rw [show (Rmax - 1) * n + n = (Rmax - 1 + 1) * n from by ring]
          congr 1; omega

/-- Under StrongRecoveryInv with `maxRC > 0` and `n > 0`, some agent attains
the maximum resetcount, so `rcMaxCount ≥ 1`. -/
theorem rcMaxCount_pos_of_maxRC_pos
    {C : Config (AgentState n) Opinion n} (hn : 0 < n)
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hmax_pos : 0 < maxRC C) :
    0 < rcMaxCount C := by
  unfold rcMaxCount
  rw [Finset.card_pos]
  unfold maxRC at hmax_pos
  have ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup (Finset.univ (α := Fin n))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun w : Fin n => if (C w).1.role = .Resetting then (C w).1.resetcount else 0)
  simp only [hAllR w, ite_true] at hw
  exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAllR w, hw.symm⟩⟩

/-- `rcLevelPotential C = 0 → Phase1Goal` under `StrongRecoveryInv`. -/
theorem rcLevelPotential_zero_goal {Rmax Dmax : ℕ} (hn : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hphi : rcLevelPotential C = 0) :
    Phase1Goal Rmax Dmax C := by
  unfold rcLevelPotential at hphi
  split at hphi
  · next h => exact Or.inr (Or.inl ⟨hInv, h⟩)
  · next h =>
    -- maxRC C ≠ 0 but (maxRC C - 1) * n + rcMaxCount C = 0.
    -- This is impossible: maxRC > 0 and all Resetting implies rcMaxCount ≥ 1.
    exfalso
    have hmax_pos : 0 < maxRC C := Nat.pos_of_ne_zero h
    have hcount_pos : 0 < rcMaxCount C :=
      rcMaxCount_pos_of_maxRC_pos hn hInv.allResetting hmax_pos
    omega

/-- Under StrongRecoveryInv, `rcLevelPotential` is nonincreasing on every step. -/
private theorem pair_rc_lt_maxRC
    {Rmax Dmax : ℕ}
    {C : Config (AgentState n) Opinion n} {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hmax_pos : 0 < maxRC C) :
    Nat.max ((C i).1.resetcount - 1) ((C j).1.resetcount - 1) < maxRC C := by
  have : Nat.max ((C i).1.resetcount - 1) ((C j).1.resetcount - 1) ≤ maxRC C - 1 :=
    Nat.max_le.mpr ⟨Nat.sub_le_sub_right (rc_le_maxRC hInv i) 1,
                     Nat.sub_le_sub_right (rc_le_maxRC hInv j) 1⟩
  omega

private theorem step_agent_rc_lt_maxRC
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n} {i j w : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hmax_pos : 0 < maxRC C)
    (hw : w = i ∨ w = j)
    (hwres : (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j w).1.role = .Resetting) :
    (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j w).1.resetcount < maxRC C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  rcases hw with rfl | rfl
  · rw [step_fst_rc_eq hn3 hij hInv hwres]
    exact pair_rc_lt_maxRC hij hInv hmax_pos
  · rw [step_snd_rc_eq hn3 hij hInv hwres]
    exact pair_rc_lt_maxRC hij hInv hmax_pos

private theorem rcMaxCount_step_le_of_maxRC_eq
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n} {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hMaxEq : maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) = maxRC C)
    (hmax_pos : 0 < maxRC C) :
    rcMaxCount (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ≤ rcMaxCount C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set C' := C.step P i j
  unfold rcMaxCount
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  obtain ⟨_, hwres', hwrc'⟩ := hw
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hwi : w = i
  · exfalso
    subst hwi
    have hfst := step_fst_rc_eq hn3 hij hInv hwres'
    rw [hfst, hMaxEq] at hwrc'
    exact absurd hwrc' (Nat.ne_of_lt (pair_rc_lt_maxRC hij hInv hmax_pos))
  · by_cases hwj : w = j
    · exfalso
      subst hwj
      have hsnd := step_snd_rc_eq hn3 hij hInv hwres'
      rw [hsnd, hMaxEq] at hwrc'
      exact absurd hwrc' (Nat.ne_of_lt (pair_rc_lt_maxRC hij hInv hmax_pos))
    · rw [show C' w = C w from step_bystander_eq' hij hwi hwj] at hwres' hwrc'
      rw [hMaxEq] at hwrc'
      exact ⟨hwres', hwrc'⟩

theorem rcLevelPotential_step_nonincrease
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax Dmax C) (hGoal : ¬ Phase1Goal Rmax Dmax C)
    (i j : Fin n) :
    rcLevelPotential (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) ≤
      rcLevelPotential C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set C' := C.step P i j
  by_cases hij : i = j
  · rw [show C' = C from by simp [C', Config.step, hij]]
  · have hmaxRC_le := maxRC_step_le_strong (Emax := Emax) (Dmax := Dmax) (hn := hn) hn3 C hInv i j
    -- Case split on whether maxRC C = 0
    by_cases hmax0 : maxRC C = 0
    · -- maxRC C = 0 implies maxRC C' = 0, both potentials are 0
      have hmax0' : maxRC C' = 0 := Nat.eq_zero_of_le_zero (hmax0 ▸ hmaxRC_le)
      show rcLevelPotential C' ≤ rcLevelPotential C
      unfold rcLevelPotential; rw [if_pos hmax0, if_pos hmax0']
    · have hmax_pos : 0 < maxRC C := Nat.pos_of_ne_zero hmax0
      -- Case split on maxRC C' = maxRC C vs strictly less
      by_cases hMaxEq : maxRC C' = maxRC C
      · -- maxRC unchanged
        have hmax0' : maxRC C' ≠ 0 := hMaxEq ▸ hmax0
        show rcLevelPotential C' ≤ rcLevelPotential C
        unfold rcLevelPotential; rw [if_neg hmax0, if_neg hmax0', hMaxEq]
        exact Nat.add_le_add_left (rcMaxCount_step_le_of_maxRC_eq hn3 hij hInv hMaxEq hmax_pos) _
      · -- maxRC strictly dropped
        have hlt : maxRC C' < maxRC C := lt_of_le_of_ne hmaxRC_le hMaxEq
        by_cases hmax0' : maxRC C' = 0
        · show rcLevelPotential C' ≤ rcLevelPotential C
          unfold rcLevelPotential; rw [if_pos hmax0', if_neg hmax0]
          exact Nat.zero_le _
        · show rcLevelPotential C' ≤ rcLevelPotential C
          unfold rcLevelPotential; rw [if_neg hmax0', if_neg hmax0]
          have hle : maxRC C' ≤ maxRC C - 1 := Nat.le_sub_one_of_lt hlt
          have hcount_le : rcMaxCount C' ≤ n := by
            unfold rcMaxCount
            exact le_trans (Finset.card_filter_le _ _) (by simp [Finset.card_univ])
          have h3 : 0 < rcMaxCount C :=
            rcMaxCount_pos_of_maxRC_pos (by omega) hInv.allResetting hmax_pos
          calc (maxRC C' - 1) * n + rcMaxCount C'
              ≤ (maxRC C - 1 - 1) * n + n :=
                Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hle 1)) hcount_le
            _ ≤ (maxRC C - 1) * n + rcMaxCount C := by
                have : (maxRC C - 1 - 1) * n + n ≤ (maxRC C - 1) * n := by
                  rw [show (maxRC C - 1 - 1) * n + n = (maxRC C - 1 - 1 + 1) * n from by ring]
                  exact Nat.mul_le_mul_right _ (by omega)
                omega

/-- Under StrongRecoveryInv with rcLevelPotential > 0, picking any agent u at
maxRC as first coordinate and any v ≠ u guarantees rcLevelPotential strictly
decreases (or Phase1Goal is reached). The probability of picking such a u is
≥ 1/n (at least one of n agents is at maxRC). -/
private theorem rcMaxCount_step_strict_lt_of_maxRC_eq_involving
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n} {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hMaxEq : maxRC (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) = maxRC C)
    {u : Fin n} (hu_at_max : (C u).1.role = .Resetting ∧ (C u).1.resetcount = maxRC C)
    (hu_involved : u = i ∨ u = j)
    (hmax_pos : 0 < maxRC C) :
    rcMaxCount (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) <
      rcMaxCount C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set C' := C.step P i j
  unfold rcMaxCount
  apply Finset.card_lt_card
  constructor
  · -- subset: same as rcMaxCount_step_le_of_maxRC_eq
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨_, hwres', hwrc'⟩ := hw
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hwi : w = i
    · exfalso; subst hwi
      have hfst := step_fst_rc_eq hn3 hij hInv hwres'
      rw [hfst, hMaxEq] at hwrc'
      exact absurd hwrc' (Nat.ne_of_lt (pair_rc_lt_maxRC hij hInv hmax_pos))
    · by_cases hwj : w = j
      · exfalso; subst hwj
        have hsnd := step_snd_rc_eq hn3 hij hInv hwres'
        rw [hsnd, hMaxEq] at hwrc'
        exact absurd hwrc' (Nat.ne_of_lt (pair_rc_lt_maxRC hij hInv hmax_pos))
      · rw [show C' w = C w from step_bystander_eq' hij hwi hwj] at hwres' hwrc'
        rw [hMaxEq] at hwrc'
        exact ⟨hwres', hwrc'⟩
  · -- not surjective: u ∈ C-filter but u ∉ C'-filter
    intro hsurj
    have h_u_in_C : u ∈ Finset.univ.filter (fun w : Fin n =>
        (C w).1.role = .Resetting ∧ (C w).1.resetcount = maxRC C) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_at_max⟩
    have h_u_in_C' := hsurj h_u_in_C
    rw [Finset.mem_filter] at h_u_in_C'
    obtain ⟨_, hures', hurc'⟩ := h_u_in_C'
    rcases hu_involved with rfl | rfl
    · have hfst := step_fst_rc_eq hn3 hij hInv hures'
      rw [hfst, hMaxEq] at hurc'
      exact absurd hurc' (Nat.ne_of_lt (pair_rc_lt_maxRC hij hInv hmax_pos))
    · have hsnd := step_snd_rc_eq hn3 hij hInv hures'
      rw [hsnd, hMaxEq] at hurc'
      exact absurd hurc' (Nat.ne_of_lt (pair_rc_lt_maxRC hij hInv hmax_pos))

private theorem rcLevelPotential_strict_drop_involving_u
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    {C : Config (AgentState n) Opinion n} {i j : Fin n} (hij : i ≠ j)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hInv' : StrongRecoveryInv Rmax Dmax (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j))
    {u : Fin n} (hu_at_max : (C u).1.role = .Resetting ∧ (C u).1.resetcount = maxRC C)
    (hu_involved : u = i ∨ u = j)
    (hmax_pos : 0 < maxRC C) :
    rcLevelPotential (C.step (PEMProtocolCoupled' n Rmax Emax Dmax hn) i j) <
      rcLevelPotential C := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set C' := C.step P i j
  have hmaxRC_le := maxRC_step_le_strong (Emax := Emax) (Dmax := Dmax) (hn := hn) hn3 C hInv i j
  have hmax_ne : maxRC C ≠ 0 := Nat.pos_iff_ne_zero.mp hmax_pos
  by_cases hMaxEq : maxRC C' = maxRC C
  · -- maxRC unchanged → rcMaxCount strictly drops
    have hmax_ne' : maxRC C' ≠ 0 := hMaxEq ▸ hmax_ne
    show rcLevelPotential C' < rcLevelPotential C
    unfold rcLevelPotential; rw [if_neg hmax_ne, if_neg hmax_ne', hMaxEq]
    apply Nat.add_lt_add_left
    exact rcMaxCount_step_strict_lt_of_maxRC_eq_involving hn3 hij hInv hMaxEq
      hu_at_max hu_involved hmax_pos
  · -- maxRC strictly dropped
    have hlt_max : maxRC C' < maxRC C := lt_of_le_of_ne hmaxRC_le hMaxEq
    by_cases hmax0' : maxRC C' = 0
    · show rcLevelPotential C' < rcLevelPotential C
      unfold rcLevelPotential; rw [if_pos hmax0', if_neg hmax_ne]
      exact Nat.add_pos_right _ (rcMaxCount_pos_of_maxRC_pos (by omega) hInv.allResetting hmax_pos)
    · show rcLevelPotential C' < rcLevelPotential C
      unfold rcLevelPotential; rw [if_neg hmax0', if_neg hmax_ne]
      have hle : maxRC C' ≤ maxRC C - 1 := Nat.le_sub_one_of_lt hlt_max
      have hcount_le : rcMaxCount C' ≤ n := by
        unfold rcMaxCount
        exact le_trans (Finset.card_filter_le _ _) (by simp [Finset.card_univ])
      have h3 : 0 < rcMaxCount C :=
        rcMaxCount_pos_of_maxRC_pos (by omega) hInv.allResetting hmax_pos
      calc (maxRC C' - 1) * n + rcMaxCount C'
          ≤ (maxRC C - 1 - 1) * n + n :=
            Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hle 1)) hcount_le
        _ ≤ (maxRC C - 1) * n := by
            rw [show (maxRC C - 1 - 1) * n + n = (maxRC C - 1 - 1 + 1) * n from by ring]
            exact Nat.mul_le_mul_right _ (by omega)
        _ < (maxRC C - 1) * n + rcMaxCount C := Nat.lt_add_of_pos_right h3

theorem rcLevelPotential_one_step_drop_prob
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hn3 : 3 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (C : Config (AgentState n) Opinion n)
    (hInv : StrongRecoveryInv Rmax Dmax C)
    (hphi : rcLevelPotential C = k) :
    ((n : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled' n Rmax Emax Dmax hn)
        (by omega : 2 ≤ n) C
        (fun D => Phase1Goal Rmax Dmax D ∨
          (StrongRecoveryInv Rmax Dmax D ∧ rcLevelPotential D < k)) 1 := by
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn
  set Goal := fun D : Config (AgentState n) Opinion n => Phase1Goal Rmax Dmax D ∨
    (StrongRecoveryInv Rmax Dmax D ∧ rcLevelPotential D < k)
  have hn2 : 2 ≤ n := by omega
  -- k > 0 implies maxRC C > 0
  have hmax_pos : 0 < maxRC C := by
    by_contra h
    push_neg at h
    have hmz : maxRC C = 0 := Nat.eq_zero_of_le_zero (by omega)
    unfold rcLevelPotential at hphi; rw [if_pos hmz] at hphi; omega
  -- Find u at maxRC
  have ⟨u, hu_res, hu_rc⟩ : ∃ u : Fin n, (C u).1.role = .Resetting ∧
      (C u).1.resetcount = maxRC C := by
    have hcnt := rcMaxCount_pos_of_maxRC_pos (by omega : 0 < n) hInv.allResetting hmax_pos
    unfold rcMaxCount at hcnt; rw [Finset.card_pos] at hcnt
    obtain ⟨w, hw⟩ := hcnt
    rw [Finset.mem_filter] at hw
    exact ⟨w, hw.2⟩
  -- Check if Goal already holds at C
  by_cases hGoalC : Goal C
  · -- Goal already holds at C: trivially ProbHitWithin ≥ 1 ≥ 1/n
    have h1 : (1 : ENNReal) ≤ Probability.ProbHitWithin P hn2 C Goal 1 := by
      have h0 := Probability.probHitBy_zero_of_goal P hn2 C Goal hGoalC
      calc (1 : ENNReal) = Probability.ProbHitWithin P hn2 C Goal 0 := h0.symm
        _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
            Probability.ProbHitWithin_mono_time P hn2 C Goal (Nat.zero_le 1)
    calc ((n : ℕ) : ENNReal)⁻¹ ≤ 1 :=
          ENNReal.inv_le_one.mpr (by exact_mod_cast (show 1 ≤ n by omega))
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 := h1
  · -- Goal does not hold at C: use PairsInvolving
    have hstep : ∀ p ∈ Probability.PairsInvolving n u, Goal (C.step P p.1 p.2) := by
      intro ⟨a, b⟩ hp
      rw [Probability.mem_PairsInvolving] at hp
      obtain ⟨hab, ha_or_b⟩ := hp
      rcases strongRecoveryInv_step hn3 C hInv a b with hInv' | hGoal'
      · right
        refine ⟨hInv', ?_⟩
        rw [← hphi]
        have hu_involved : u = a ∨ u = b := by
          rcases ha_or_b with rfl | rfl <;> [left; right] <;> rfl
        exact rcLevelPotential_strict_drop_involving_u hn3 hab hInv hInv'
          ⟨hu_res, hu_rc⟩ hu_involved hmax_pos
      · left; exact hGoal'
    have h2n := Probability.ProbHitWithin_one_lower_bound_of_agent_participation
          P hn2 C Goal hGoalC u hstep
    calc ((n : ℕ) : ENNReal)⁻¹
        ≤ 1 * ((n : ℕ) : ENNReal)⁻¹ := by rw [one_mul]
      _ ≤ (2 : ENNReal) * ((n : ℕ) : ENNReal)⁻¹ := by
          exact mul_le_mul_right' one_le_two _
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 := h2n



/-- Phase 1 only: from all-Resetting with correct answers and bounded rc,
the expected hitting time to Phase1Goal is at most Rmax*n*n.
This is the fully proved Phase 1 (rcLevelPotential descent).
Phase 2 (from Phase1Goal to consensus) is proved in PhaseProofs.lean
where all machinery is available. -/
theorem allR_to_phase1Goal_bound
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hDmax : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w : Fin n, (D w).1.answer = majorityAnswer D)
    (hBounded : ∀ w : Fin n, (D w).1.resetcount ≤ Rmax)
:
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D (Phase1Goal Rmax Dmax) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hInv0 : StrongRecoveryInv Rmax Dmax D := ⟨hAllR, hAllCorrect, hBounded⟩
  have hBound := Probability.expectedHittingTime_le_of_variable_descent_until_goal
    P hn2 D (Phase1Goal Rmax Dmax) (StrongRecoveryInv Rmax Dmax) rcLevelPotential
    (fun _ => ((n : ℕ) : ENNReal)⁻¹)
    hInv0
    (fun C hInv hphi => rcLevelPotential_zero_goal hn0 C hInv hphi)
    (fun C hInv hGoal i j => strongRecoveryInv_step hn3 C hInv i j)
    (fun C hInv hGoal i j => rcLevelPotential_step_nonincrease hn3 C hInv hGoal i j)
    (fun k hk C hInv hphi =>
      rcLevelPotential_one_step_drop_prob hn3 k hk C hInv hphi)
  calc Probability.expectedHittingTime P hn2 D (Phase1Goal Rmax Dmax)
      ≤ ∑ _k ∈ Finset.range (rcLevelPotential D),
          (((n : ℕ) : ENNReal)⁻¹)⁻¹ := hBound
    _ = ∑ _k ∈ Finset.range (rcLevelPotential D),
          ((n : ℕ) : ENNReal) := by
        congr 1; ext; simp [inv_inv]
    _ = ↑(rcLevelPotential D) * ((n : ℕ) : ENNReal) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ↑(Rmax * n) * ((n : ℕ) : ENNReal) := by
        apply mul_le_mul_right'
        norm_cast
        exact rcLevelPotential_le_Rmax_n hInv0
    _ = ((Rmax * n * n : ℕ) : ENNReal) := by push_cast; ring

/-! ### Finite-state-space helpers -/

theorem bounded_configs_finite_rb (n M : ℕ) [NeZero n] :
    Set.Finite {C : Config (AgentState n) Opinion n | IsBoundedConfig M C} := by
  let T := Role × (Fin n) × Leader × (Fin (M+1)) × Answer ×
        (Fin (M+1)) × (Fin (M+1)) × (Fin (M+1)) × (Fin (M+1)) × Opinion
  let encode : T → (AgentState n × Opinion) :=
    fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1.val, x.2.2.2.2.1,
      x.2.2.2.2.2.1.val, x.2.2.2.2.2.2.1.val,
      x.2.2.2.2.2.2.2.1.val, x.2.2.2.2.2.2.2.2.1.val⟩, x.2.2.2.2.2.2.2.2.2)
  apply Set.Finite.subset (Set.finite_range (fun (f : Fin n → T) w => encode (f w)))
  intro C hC
  refine Set.mem_range.mpr ⟨fun w =>
    have hB := hC w
    ((C w).1.role, (C w).1.rank, (C w).1.leader,
     ⟨(C w).1.resetcount, Nat.lt_succ_of_le hB.2.1⟩,
     (C w).1.answer,
     ⟨(C w).1.timer, Nat.lt_succ_of_le hB.1⟩,
     ⟨(C w).1.children, Nat.lt_succ_of_le hB.2.2.2.2⟩,
     ⟨(C w).1.errorcount, Nat.lt_succ_of_le hB.2.2.1⟩,
     ⟨(C w).1.delaytimer, Nat.lt_succ_of_le hB.2.2.2.1⟩,
     (C w).2), funext fun w => Prod.ext (by cases (C w).1; rfl) rfl⟩

private theorem finset_uniform_bound_rb {α : Type*} [DecidableEq α]
    (S : Finset α) {P : α → ℕ → Prop}
    (hMono : ∀ a ∈ S, ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → P a k₁ → P a k₂)
    (hAll : ∀ a ∈ S, ∃ k, P a k) :
    ∃ K, ∀ a ∈ S, P a K := by
  classical
  let wit : α → ℕ := fun a => if h : a ∈ S then (hAll a h).choose else 0
  use S.sup wit
  intro a ha
  have hk := (hAll a ha).choose_spec
  have hwit_a : wit a = (hAll a ha).choose := dif_pos ha
  rw [← hwit_a] at hk
  exact hMono a ha (wit a) (S.sup wit) (Finset.le_sup ha) hk

private theorem inv_le_one_nn1_rb (hn2 : 2 ≤ n) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤ 1 := by
  apply ENNReal.inv_le_one.mpr
  have h1 : 1 ≤ n := by omega
  have h2 : 1 ≤ n - 1 := by omega
  exact_mod_cast Nat.mul_le_mul h1 h2

/-! ### Main ergodicity theorem -/

set_option maxHeartbeats 800000 in
/-- From any bounded config, E[T to IsConsensusConfig] is finite.
Proved via the finite-state-space ergodicity argument: bounded configs
form a finite set, deterministic reachability converts to probabilistic
bounds, and the window lemma gives finiteness. -/
theorem bounded_config_to_consensus
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmaxN : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D IsConsensusConfig < ⊤ := by
  classical
  set M := 7 * (Rmax + 4) + Emax + Dmax
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hBC := burmanConvergence_concrete (Emax := Emax) (Dmax := Dmax) (hn := hn0)
    hn4 hEmax hDmaxN hRmax
  have hReach := P_EM_consensus_reachable_from_BurmanConvergence_only
    rankDeltaOSSR_satisfies_fix hn4 hBC
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, IsBoundedConfig M C →
      ∀ i j : Fin n, IsBoundedConfig M (C.step P i j) :=
    PEMProtocolCoupled_preserves_bounded hn0
  have hn_ne : NeZero n := ⟨by omega⟩
  have hinv1 := inv_le_one_nn1_rb hn2
  have hFin := bounded_configs_finite_rb n M
  have hDistReach : ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig M C → ¬ IsConsensusConfig C →
      ∃ t, ∃ (γ : DetScheduler n),
        (∀ k, k < t → (γ k).1 ≠ (γ k).2) ∧
        IsConsensusConfig (execution P C γ t) := by
    intro C _ _
    obtain ⟨γ, t, hGoal⟩ := hReach C
    obtain ⟨γ', t', _, hdist, hGoal'⟩ := execution_filter_distinct P C γ t hGoal
    exact ⟨t', γ', hdist, hGoal'⟩
  have hProbHit : ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig M C → ¬ IsConsensusConfig C →
      ∃ t, 0 < t ∧
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig t := by
    intro C hC hNotCons
    obtain ⟨t, γ, hdist, hGoal⟩ := hDistReach C hC hNotCons
    by_cases ht0 : t = 0
    · subst ht0; simp [execution] at hGoal; exact absurd hGoal hNotCons
    · exact ⟨t, Nat.pos_of_ne_zero ht0,
        Probability.ProbHitWithin_ge_inv_pow_of_execution P hn2 C IsConsensusConfig γ t hdist hGoal⟩
  have hFinNC : Set.Finite {C : Config (AgentState n) Opinion n |
      IsBoundedConfig M C ∧ ¬ IsConsensusConfig C} :=
    hFin.subset (fun C ⟨h, _⟩ => h)
  let SNC := hFinNC.toFinset
  have hMonoPHW : ∀ C ∈ SNC, ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ →
      (0 < k₁ ∧ ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ k₁ ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig k₁) →
      (0 < k₂ ∧ ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ k₂ ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig k₂) := by
    intro C _ k₁ k₂ hle ⟨hk1, hphw⟩
    exact ⟨by omega,
      (pow_le_pow_of_le_one zero_le hinv1 hle).trans
        (hphw.trans (Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig hle))⟩
  have hAllPHW : ∀ C ∈ SNC, ∃ k,
      0 < k ∧ ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ k ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig k := by
    intro C hC
    exact hProbHit C (hFinNC.mem_toFinset.mp hC).1 (hFinNC.mem_toFinset.mp hC).2
  obtain ⟨K, hK⟩ := finset_uniform_bound_rb SNC hMonoPHW hAllPHW
  by_cases hGoalD : IsConsensusConfig D
  · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D IsConsensusConfig hGoalD]
    exact ENNReal.zero_lt_top
  · have hDSNC : D ∈ SNC := hFinNC.mem_toFinset.mpr ⟨hBounded, hGoalD⟩
    obtain ⟨hKpos, _⟩ := hK D hDSNC
    have hKne : NeZero K := ⟨by omega⟩
    set p := ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ K
    have hp_le_one : p ≤ 1 := pow_le_one₀ zero_le hinv1
    have hwin : ∀ C : Config (AgentState n) Opinion n,
        IsBoundedConfig M C → ¬ IsConsensusConfig C →
        p ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
      intro C hC hNotCons
      exact (hK C (hFinNC.mem_toFinset.mpr ⟨hC, hNotCons⟩)).2
    have hBound := Probability.expectedHittingTime_le_window_mul_inv_of_invariant
      P hn2 D IsConsensusConfig (IsBoundedConfig M) K p hp_le_one
      hBounded hInvStep hwin
    calc Probability.expectedHittingTime P hn2 D IsConsensusConfig
        ≤ (K : ENNReal) * p⁻¹ := hBound
      _ < ⊤ := by
          apply ENNReal.mul_lt_top
          · exact (ENNReal.natCast_ne_top K).lt_top
          · exact (ENNReal.inv_ne_top.mpr (ENNReal.pow_ne_zero
              (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)) K)).lt_top

/-- Corollary: from any bounded config, E[T to AllR or Consensus] is finite. -/
theorem bounded_resetting_to_AllR
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmaxN : n ≤ Dmax)
    (D : Config (AgentState n) Opinion n)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) D) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) D
      (fun C => IsConsensusConfig C ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
         (∀ w : Fin n, (C w).1.answer = majorityAnswer C) ∧
         (∀ w : Fin n, (C w).1.resetcount ≤ Rmax))) < ⊤ := by
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn0
  set Goal := fun C : Config (AgentState n) Opinion n =>
    IsConsensusConfig C ∨
    ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
     (∀ w : Fin n, (C w).1.answer = majorityAnswer C) ∧
     (∀ w : Fin n, (C w).1.resetcount ≤ Rmax))
  calc Probability.expectedHittingTime P hn2 D Goal
      ≤ Probability.expectedHittingTime P hn2 D IsConsensusConfig :=
        Probability.expectedHittingTime_mono_goal P hn2 D IsConsensusConfig Goal
          (fun C h => Or.inl h)
    _ < ⊤ := bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmaxN D hBounded

/-- Phase 2: from Phase1Goal to consensus (finite expected time). -/
theorem phase1Goal_to_consensus
    {Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn : 0 < n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hGoal : Phase1Goal Rmax Dmax C)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn) (by omega : 2 ≤ n)
      C IsConsensusConfig < ⊤ := by
  classical
  set P := PEMProtocolCoupled' n Rmax Emax Dmax hn with hP
  have hn2 : 2 ≤ n := by omega
  rcases hGoal with hcons | hrest
  · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 C IsConsensusConfig hcons]
    exact ENNReal.zero_lt_top
  · exact bounded_config_to_consensus hn4 hn hRmax hEmax hDmax C hBounded

-- allR_to_consensus_bound: moved to PolynomialBound.lean.
-- Composes Phase 1 (rcLevelPotential descent, polynomial) +
-- Phase 2 (ergodicity, finite) via expectedHittingTime_add_le.

end SSEM

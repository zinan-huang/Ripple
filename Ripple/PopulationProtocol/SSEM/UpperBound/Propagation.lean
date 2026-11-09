/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Propagation of a reset: the effective resetcount (Burman et al. Lemma 3.2, deterministic part)

Paper proof: `docs/audit/FIX2-BURMAN.md`, node B32. The *effective resetcount* `effRc s` is `s.resetcount` for a Resetting agent and `0`
otherwise. After any interaction of `rankDeltaOSSR` or of P_EM (`transitionPEM`), the pair of
effective resetcounts is either `(m, m)` with `m = max (effRc a - 1) (effRc b - 1)` or
`(Rmax, Rmax)` (`rankDeltaOSSR_effRc`, `transitionPEM_effRc`). This is the one-step fact behind
the comparison of the reset with the pure max-minus-one propagation process.
-/

import Ripple.PopulationProtocol.SSEM.Convergence.FiniteStatePEM

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-- Effective resetcount: the resetcount of a Resetting agent, `0` otherwise. -/
def effRc (s : AgentState n) : ℕ := if s.role = .Resetting then s.resetcount else 0

/-- The two admissible outcomes for a pair of effective resetcounts. -/
def RcOutcome (m R x y : ℕ) : Prop := (x = m ∧ y = m) ∨ (x = R ∧ y = R)

theorem effRc_of_not_resetting {s : AgentState n} (h : s.role ≠ .Resetting) : effRc s = 0 := by
  simp [effRc, h]

theorem effRc_of_resetting {s : AgentState n} (h : s.role = .Resetting) :
    effRc s = s.resetcount := by
  simp [effRc, h]

theorem effRc_resetOSSR {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    effRc (resetOSSR Emax hn s) = 0 := by
  unfold resetOSSR
  cases s.leader <;> simp [effRc]

theorem effRc_processAgent {Emax Dmax : ℕ} {hn : 0 < n} (s : AgentState n) (o : ℕ) (pr : Bool) :
    effRc (processAgent Emax Dmax hn s o pr) = effRc s := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    have hs : effRc s = 0 := by simp [effRc, h1.1, h1.2]
    rw [hs]
    dsimp only
    split_ifs <;> first | exact effRc_resetOSSR _ | simp_all [effRc]
  · rw [if_neg h1]

theorem prRecruit_effRc (Dmax : ℕ) (a b : AgentState n) :
    effRc (prRecruit Dmax a b).1 = effRc a ∧ effRc (prRecruit Dmax a b).2 = effRc b := by
  unfold prRecruit
  split_ifs with h1 h2
  · exact ⟨rfl, by simp [effRc, h1.2.2]⟩
  · exact ⟨by simp [effRc, h2.2.2], rfl⟩
  · exact ⟨rfl, rfl⟩

theorem prRecruit_both_or_zero (Dmax : ℕ) (a b : AgentState n) :
    ((prRecruit Dmax a b).1.role = .Resetting ∧ (prRecruit Dmax a b).2.role = .Resetting) ∨
      (effRc (prRecruit Dmax a b).1 = 0 ∧ effRc (prRecruit Dmax a b).2 = 0) := by
  unfold prRecruit
  split_ifs with h1 h2
  · exact Or.inl ⟨h1.1, rfl⟩
  · exact Or.inl ⟨rfl, h2.1⟩
  · by_cases ha : a.role = .Resetting <;> by_cases hb : b.role = .Resetting
    · exact Or.inl ⟨ha, hb⟩
    · have hc : a.resetcount = 0 := by
        by_contra hc
        exact h1 ⟨ha, Nat.pos_of_ne_zero hc, hb⟩
      exact Or.inr ⟨by rw [effRc_of_resetting ha, hc], effRc_of_not_resetting hb⟩
    · have hc : b.resetcount = 0 := by
        by_contra hc
        exact h2 ⟨hb, Nat.pos_of_ne_zero hc, ha⟩
      exact Or.inr ⟨effRc_of_not_resetting ha, by rw [effRc_of_resetting hb, hc]⟩
    · exact Or.inr ⟨effRc_of_not_resetting ha, effRc_of_not_resetting hb⟩

theorem prSync_effRc (p q : AgentState n)
    (h : (p.role = .Resetting ∧ q.role = .Resetting) ∨ (effRc p = 0 ∧ effRc q = 0)) :
    effRc (prSync p q).1 = max (effRc p - 1) (effRc q - 1) ∧
      effRc (prSync p q).2 = max (effRc p - 1) (effRc q - 1) := by
  unfold prSync
  split_ifs with hb
  · simp [effRc, hb.1, hb.2]
  · rcases h with h | ⟨h0, h1⟩
    · exact absurd h hb
    · simp [h0, h1]

/-- Recruitment and synchronisation produce the pair `(m, m)`. -/
theorem effRc_prSync_prRecruit (Dmax : ℕ) (a b : AgentState n) :
    effRc (prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).1 =
        max (effRc a - 1) (effRc b - 1) ∧
      effRc (prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).2 =
        max (effRc a - 1) (effRc b - 1) := by
  obtain ⟨A1, A2⟩ := prRecruit_effRc Dmax a b
  rw [← A1, ← A2]
  exact prSync_effRc _ _ (prRecruit_both_or_zero Dmax a b)

theorem effRc_prDedup (p : AgentState n × AgentState n) :
    effRc (prDedup p).1 = effRc p.1 ∧ effRc (prDedup p).2 = effRc p.2 := by
  unfold prDedup
  refine ⟨rfl, ?_⟩
  split_ifs <;> simp [effRc]

theorem effRc_propagateReset {Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n) :
    effRc (propagateReset Emax Dmax hn a b).1 = max (effRc a - 1) (effRc b - 1) ∧
      effRc (propagateReset Emax Dmax hn a b).2 = max (effRc a - 1) (effRc b - 1) := by
  rw [propagateReset_eq]
  simp only [effRc_processAgent]
  exact effRc_prSync_prRecruit Dmax a b

/-- Collision, ranking and error monitoring (neither agent Resetting). -/
theorem effRc_rankDeltaOSSR_of_not_resetting {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} (ha : a.role ≠ .Resetting) (hb : b.role ≠ .Resetting) :
    RcOutcome 0 Rmax (effRc (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1)
      (effRc (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2) := by
  unfold RcOutcome
  simp only [rankDeltaOSSR]
  rw [if_neg (by tauto)]
  split_ifs <;> simp_all [effRc]

/-- **Lemma 1 for `rankDeltaOSSR`.** -/
theorem rankDeltaOSSR_effRc {Rmax Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n) :
    RcOutcome (max (effRc a - 1) (effRc b - 1)) Rmax
      (effRc (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1)
      (effRc (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2) := by
  by_cases h : a.role = .Resetting ∨ b.role = .Resetting
  · rw [rankDeltaOSSR_eq_of_resetting h]
    obtain ⟨h1, h2⟩ := effRc_prDedup (propagateReset Emax Dmax hn a b)
    obtain ⟨h3, h4⟩ := effRc_propagateReset (Emax := Emax) (Dmax := Dmax) (hn := hn) a b
    exact Or.inl ⟨h1.trans h3, h2.trans h4⟩
  · push Not at h
    have hm : max (effRc a - 1) (effRc b - 1) = 0 := by
      simp [effRc_of_not_resetting h.1, effRc_of_not_resetting h.2]
    rw [hm]
    exact effRc_rankDeltaOSSR_of_not_resetting h.1 h.2

/-! ### P_EM -/

theorem preAgent_role_rc (trank : ℕ) (s r : AgentState n) :
    (preAgent n trank s r).role = r.role ∧ (preAgent n trank s r).resetcount = r.resetcount := by
  unfold preAgent
  dsimp only
  split_ifs <;> simp

theorem effRc_preAgent (trank : ℕ) (s r : AgentState n) :
    effRc (preAgent n trank s r) = effRc r := by
  obtain ⟨h1, h2⟩ := preAgent_role_rc trank s r
  simp [effRc, h1, h2]

theorem preEpi_role_rc (a₀ a₁ : AgentState n) :
    (preEpi a₀ a₁).1.role = a₀.role ∧ (preEpi a₀ a₁).1.resetcount = a₀.resetcount ∧
      (preEpi a₀ a₁).2.role = a₁.role ∧ (preEpi a₀ a₁).2.resetcount = a₁.resetcount := by
  unfold preEpi
  split_ifs <;> simp

theorem effRc_preEpi (a₀ a₁ : AgentState n) :
    effRc (preEpi a₀ a₁).1 = effRc a₀ ∧ effRc (preEpi a₀ a₁).2 = effRc a₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := preEpi_role_rc a₀ a₁
  exact ⟨by simp [effRc, h1, h2], by simp [effRc, h3, h4]⟩

theorem effRc_prePhase4 {trank : ℕ} {rd : AgentState n × AgentState n → AgentState n × AgentState n}
    (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    effRc (transitionPEM_prePhase4 n trank rd s₀ s₁ x₀ x₁).1 = effRc (rd (s₀, s₁)).1 ∧
      effRc (transitionPEM_prePhase4 n trank rd s₀ s₁ x₀ x₁).2 = effRc (rd (s₀, s₁)).2 := by
  rw [prePhase4_eq]
  obtain ⟨h1, h2⟩ := effRc_preEpi (preAgent n trank s₀ (rd (s₀, s₁)).1)
    (preAgent n trank s₁ (rd (s₀, s₁)).2)
  exact ⟨h1.trans (effRc_preAgent _ _ _), h2.trans (effRc_preAgent _ _ _)⟩

theorem phase4_swap_settled {a₀ a₁ : AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a₀.role = .Settled) (h₁ : a₁.role = .Settled) :
    (phase4_swap a₀ a₁ x₀ x₁).1.role = .Settled ∧ (phase4_swap a₀ a₁ x₀ x₁).2.role = .Settled := by
  unfold phase4_swap
  split_ifs <;> simp [h₀, h₁]

theorem phase4_decide_role (b₀ b₁ : AgentState n) (x₀ x₁ : Opinion) :
    (phase4_decide n b₀ b₁ x₀ x₁).1.role = b₀.role ∧
      (phase4_decide n b₀ b₁ x₀ x₁).2.role = b₁.role := by
  unfold phase4_decide
  split_ifs <;> simp

theorem phase4_propagate_effRc {Rmax : ℕ} {b₀ b₁ : AgentState n}
    (h₀ : b₀.role = .Settled) (h₁ : b₁.role = .Settled) :
    RcOutcome 0 Rmax (effRc (phase4_propagate n Rmax b₀ b₁).1)
      (effRc (phase4_propagate n Rmax b₀ b₁).2) := by
  unfold RcOutcome phase4_propagate
  dsimp only
  split_ifs <;> simp_all [effRc]

theorem phase4_effRc {Rmax : ℕ} (a : AgentState n × AgentState n) (x₀ x₁ : Opinion) :
    (transitionPEM_phase4 n Rmax a x₀ x₁ = a) ∨
      ((a.1.role = .Settled ∧ a.2.role = .Settled) ∧
        RcOutcome 0 Rmax (effRc (transitionPEM_phase4 n Rmax a x₀ x₁).1)
          (effRc (transitionPEM_phase4 n Rmax a x₀ x₁).2)) := by
  rcases a with ⟨a₀, a₁⟩
  by_cases h : a₀.role = .Settled ∧ a₁.role = .Settled
  · right
    refine ⟨h, ?_⟩
    simp only [transitionPEM_phase4]
    rw [if_pos h]
    obtain ⟨hs₀, hs₁⟩ := phase4_swap_settled (x₀ := x₀) (x₁ := x₁) h.1 h.2
    obtain ⟨hd₀, hd₁⟩ := phase4_decide_role (n := n) (phase4_swap a₀ a₁ x₀ x₁).1
      (phase4_swap a₀ a₁ x₀ x₁).2 x₀ x₁
    exact phase4_propagate_effRc (hd₀.trans hs₀) (hd₁.trans hs₁)
  · left
    exact transitionPEM_phase4_of_not_both_settled h

/-- **Lemma 1 for P_EM** (any timer constant, ranking subprotocol `rankDeltaOSSR` with the same
`Rmax`). -/
theorem transitionPEM_effRc {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    RcOutcome (max (effRc s₀ - 1) (effRc s₁ - 1)) Rmax
      (effRc (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((s₀, x₀), (s₁, x₁))).1)
      (effRc (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s₀, x₀), (s₁, x₁))).2) := by
  rw [transitionPEM_eq]
  obtain ⟨hp₀, hp₁⟩ := effRc_prePhase4 (trank := trank)
    (rd := rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁
  have hrd := rankDeltaOSSR_effRc (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) s₀ s₁
  have h4 := phase4_effRc (Rmax := Rmax)
    (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁) x₀ x₁
  generalize transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁ = pre
    at hp₀ hp₁ h4 ⊢
  rcases h4 with h | ⟨⟨hS₀, hS₁⟩, hout⟩
  · rw [h, hp₀, hp₁]
    exact hrd
  · have e₀ : effRc pre.1 = 0 := effRc_of_not_resetting (by rw [hS₀]; simp)
    have hz : effRc (rankDeltaOSSR Rmax Emax Dmax hn (s₀, s₁)).1 = 0 := by rw [← hp₀]; exact e₀
    rcases hout with ⟨o₀, o₁⟩ | hR
    · unfold RcOutcome
      rw [o₀, o₁]
      rcases hrd with ⟨r₀, -⟩ | ⟨r₀, -⟩
      · exact Or.inl ⟨by rw [← r₀, hz], by rw [← r₀, hz]⟩
      · exact Or.inr ⟨by rw [← r₀, hz], by rw [← r₀, hz]⟩
    · exact Or.inr hR

end Ripple.PopulationProtocol.SSEM

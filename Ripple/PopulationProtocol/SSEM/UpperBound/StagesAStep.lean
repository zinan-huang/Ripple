/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# One step of P_EM away from a trigger (P2 Lemmas 2.1, 2.4, 2.7; P3 Lemma 1)

Every interaction of P_EM either is a *trigger*, after which both participants are Resetting
with `resetcount = Rmax` and leader bit `L` (`TrigPair`), or it moves the two participants in
a controlled way. This file records the controlled moves used by Stage A (P3 Lemma 9):

* `transitionPEM_lift`: Phases 1–4 after the ranking rule keep role, resetcount, leader,
  delay timer and errorcount, except that Phase 4 on two Settled states may trigger; so a
  property of the ranking outputs that only reads these fields passes to the P_EM outputs;
* `step_rc`: the effective resetcounts follow the max-minus-one rule or the step is a trigger
  (P2 Lemma 2.1, with the leader of P3 Lemma 1(c));
* `step_dorm`: with no propagating participant, a Resetting output was a Resetting input,
  has resetcount `0`, and its delay timer dropped by one to a positive value (P2 Lemma 2.4);
* `step_comp`: between two computing agents, outputs are computing, Settled stays Settled,
  and an Unsettled output was Unsettled with errorcount dropped by one to a positive value
  (P2 Lemma 2.7);
* `step_settled`: from two Settled states the outputs are Settled or the step is a trigger;
  equal ranks give a trigger (collision detection).

A trigger at the pair `(u, v)` lands in `PT_L` (`ptl_of_trig`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.SRankStep

namespace Ripple.PopulationProtocol.SSEM

open Probability

variable {n : ℕ}

/-! ### Triggers and core fields -/

/-- Both states of the pair are Resetting with `resetcount = R` and leader bit `L`. -/
def TrigPair (R : ℕ) (p : AgentState n × AgentState n) : Prop :=
  p.1.role = .Resetting ∧ p.1.resetcount = R ∧ p.1.leader = .L ∧
    p.2.role = .Resetting ∧ p.2.resetcount = R ∧ p.2.leader = .L

/-- Two states agree on role, resetcount, leader, delay timer and errorcount. -/
def SameCore (s t : AgentState n) : Prop :=
  s.role = t.role ∧ s.resetcount = t.resetcount ∧ s.leader = t.leader ∧
    s.delaytimer = t.delaytimer ∧ s.errorcount = t.errorcount

theorem SameCore.trans {s t u : AgentState n} (h₁ : SameCore s t) (h₂ : SameCore t u) :
    SameCore s u :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.trans h₂.2.2.2.2⟩

theorem TrigPair.of_sameCore {R : ℕ} {p q : AgentState n × AgentState n} (h : TrigPair R p)
    (h₁ : SameCore q.1 p.1) (h₂ : SameCore q.2 p.2) : TrigPair R q := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨h₁.1.trans a1, h₁.2.1.trans a2, h₁.2.2.1.trans a3, h₂.1.trans a4, h₂.2.1.trans a5,
    h₂.2.2.1.trans a6⟩

theorem sameCore_preAgent (trank : ℕ) (s r : AgentState n) :
    SameCore (preAgent n trank s r) r := by
  unfold preAgent SameCore
  dsimp only
  split_ifs <;> simp

theorem sameCore_preEpi (a₀ a₁ : AgentState n) :
    SameCore (preEpi a₀ a₁).1 a₀ ∧ SameCore (preEpi a₀ a₁).2 a₁ := by
  unfold preEpi SameCore
  split_ifs <;> simp

/-! ### Phase 4 -/

theorem phase4_propagate_cases {R : ℕ} {b₀ b₁ : AgentState n} (h₀ : b₀.role = .Settled)
    (h₁ : b₁.role = .Settled) :
    TrigPair R (phase4_propagate n R b₀ b₁) ∨
      ((phase4_propagate n R b₀ b₁).1.role = .Settled ∧
        (phase4_propagate n R b₀ b₁).2.role = .Settled) := by
  unfold phase4_propagate TrigPair
  dsimp only
  split_ifs <;> simp_all

theorem phase4_cases {R : ℕ} (a : AgentState n × AgentState n) (x₀ x₁ : Opinion) :
    transitionPEM_phase4 n R a x₀ x₁ = a ∨
      ((a.1.role = .Settled ∧ a.2.role = .Settled) ∧
        (TrigPair R (transitionPEM_phase4 n R a x₀ x₁) ∨
          ((transitionPEM_phase4 n R a x₀ x₁).1.role = .Settled ∧
            (transitionPEM_phase4 n R a x₀ x₁).2.role = .Settled))) := by
  rcases a with ⟨a₀, a₁⟩
  by_cases h : a₀.role = .Settled ∧ a₁.role = .Settled
  · right
    refine ⟨h, ?_⟩
    rw [transitionPEM_phase4_settled h.1 h.2]
    obtain ⟨hs₀, hs₁⟩ := phase4_swap_settled (x₀ := x₀) (x₁ := x₁) h.1 h.2
    obtain ⟨hd₀, hd₁⟩ := phase4_decide_role (n := n) (phase4_swap a₀ a₁ x₀ x₁).1
      (phase4_swap a₀ a₁ x₀ x₁).2 x₀ x₁
    exact phase4_propagate_cases (hd₀.trans hs₀) (hd₁.trans hs₁)
  · left
    exact transitionPEM_phase4_of_not_both_settled h

/-- **Lifting a property of the ranking outputs to the P_EM outputs.** `Q s t` relates an input
state `s` to an output state `t`; it may read only the core fields of `t`, and it must not
distinguish two Settled outputs. -/
theorem transitionPEM_lift {trank R : ℕ}
    {rd : AgentState n × AgentState n → AgentState n × AgentState n}
    (Q : AgentState n → AgentState n → Prop)
    (hQc : ∀ s t t', SameCore t' t → Q s t → Q s t')
    (hQs : ∀ s t t', t.role = .Settled → t'.role = .Settled → Q s t → Q s t')
    (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion)
    (h : TrigPair R (rd (s₀, s₁)) ∨ (Q s₀ (rd (s₀, s₁)).1 ∧ Q s₁ (rd (s₀, s₁)).2)) :
    TrigPair R (transitionPEM n trank R rd ((s₀, x₀), (s₁, x₁))) ∨
      (Q s₀ (transitionPEM n trank R rd ((s₀, x₀), (s₁, x₁))).1 ∧
        Q s₁ (transitionPEM n trank R rd ((s₀, x₀), (s₁, x₁))).2) := by
  rw [transitionPEM_eq, prePhase4_eq]
  obtain ⟨e₀, e₁⟩ := sameCore_preEpi (preAgent n trank s₀ (rd (s₀, s₁)).1)
    (preAgent n trank s₁ (rd (s₀, s₁)).2)
  have c₀ := e₀.trans (sameCore_preAgent trank s₀ (rd (s₀, s₁)).1)
  have c₁ := e₁.trans (sameCore_preAgent trank s₁ (rd (s₀, s₁)).2)
  generalize preEpi (preAgent n trank s₀ (rd (s₀, s₁)).1)
    (preAgent n trank s₁ (rd (s₀, s₁)).2) = pre at c₀ c₁ ⊢
  generalize rd (s₀, s₁) = r at h c₀ c₁
  rcases phase4_cases (R := R) pre x₀ x₁ with hp | ⟨⟨hS₀, hS₁⟩, hout⟩
  · rw [hp]
    rcases h with hT | ⟨q₀, q₁⟩
    · exact Or.inl (hT.of_sameCore c₀ c₁)
    · exact Or.inr ⟨hQc _ _ _ c₀ q₀, hQc _ _ _ c₁ q₁⟩
  · have hr₀ : r.1.role = .Settled := c₀.1.symm.trans hS₀
    have hr₁ : r.2.role = .Settled := c₁.1.symm.trans hS₁
    rcases hout with hT | ⟨o₀, o₁⟩
    · exact Or.inl hT
    · rcases h with hT | ⟨q₀, q₁⟩
      · exact absurd (hT.1.symm.trans hr₀) (by decide)
      · exact Or.inr ⟨hQs _ _ _ hr₀ o₀ q₀, hQs _ _ _ hr₁ o₁ q₁⟩

/-! ### The ranking rule -/

/-- Output of a computing input in a non-trigger interaction of two computing agents. -/
def CompOK (s t : AgentState n) : Prop :=
  t.role ≠ .Resetting ∧ (s.role = .Settled → t.role = .Settled) ∧
    (t.role = .Unsettled →
      s.role = .Unsettled ∧ t.errorcount + 1 = s.errorcount ∧ 1 ≤ t.errorcount)

/-- Output of an input in an interaction without propagating participant. -/
def DormOK (s t : AgentState n) : Prop :=
  t.role = .Resetting →
    s.role = .Resetting ∧ t.resetcount = 0 ∧ t.delaytimer + 1 = s.delaytimer ∧ 1 ≤ t.delaytimer

/-- **Two computing agents** (Parts 2–4 of the ranking rule, P2 Lemma 2.7). -/
theorem rankDelta_comp {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role ≠ .Resetting) (hb : b.role ≠ .Resetting) :
    TrigPair Rmax (rankDeltaOSSR Rmax Emax Dmax hn (a, b)) ∨
      (CompOK a (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
        CompOK b (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2) := by
  simp only [rankDeltaOSSR]
  rw [if_neg (by tauto)]
  split_ifs <;> simp_all [TrigPair, CompOK] <;> omega

theorem resetOSSR_role_ne {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).role ≠ .Resetting := by
  unfold resetOSSR
  cases s.leader <;> simp

theorem processAgent_dormOK {Emax Dmax : ℕ} {hn : 0 < n} (s₀ s : AgentState n) (o : ℕ)
    (pr : Bool) (hrole : s.role = s₀.role) (hdt : s.delaytimer = s₀.delaytimer)
    (hrc : s.role = .Resetting → s.resetcount = 0 ∧ o = 0) :
    DormOK s₀ (processAgent Emax Dmax hn s o pr) := by
  by_cases hR : s.role = .Resetting
  · obtain ⟨h1, h2⟩ := hrc hR
    subst h2
    by_cases hc : s.delaytimer - 1 = 0 ∨ pr = false
    · have : processAgent Emax Dmax hn s 0 pr =
          resetOSSR Emax hn { s with delaytimer := s.delaytimer - 1 } := by
        rcases hc with hc | hc
        · simp [processAgent, hR, h1, hc]
        · simp [processAgent, hR, h1, hc]
      rw [this]
      intro h
      exact absurd h (resetOSSR_role_ne _)
    · push Not at hc
      have hpr : pr = true := by simpa using hc.2
      have : processAgent Emax Dmax hn s 0 pr = { s with delaytimer := s.delaytimer - 1 } := by
        simp [processAgent, hR, h1, hc.1, hpr]
      rw [this]
      intro _
      refine ⟨hrole.symm.trans hR, h1, ?_, ?_⟩ <;> dsimp only <;> omega
  · rw [processAgent_not_resetting hR]
    intro h
    exact absurd h hR

theorem prDedup_dormOK {s₀ s₁ : AgentState n} {p : AgentState n × AgentState n}
    (h₀ : DormOK s₀ p.1) (h₁ : DormOK s₁ p.2) :
    DormOK s₀ (prDedup p).1 ∧ DormOK s₁ (prDedup p).2 := by
  obtain ⟨D1, D2, D3, D4⟩ := prDedup_fields p
  refine ⟨D1 ▸ h₀, fun h => ?_⟩
  rw [D2] at h
  rw [D3, D4]
  exact h₁ h

/-- **No propagating participant, at least one Resetting** (Part 1, P2 Lemma 2.4). -/
theorem rankDelta_dorm {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : effRc a = 0) (hb : effRc b = 0) (h : a.role = .Resetting ∨ b.role = .Resetting) :
    DormOK a (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
      DormOK b (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  rw [rankDeltaOSSR_eq_of_resetting h]
  apply prDedup_dormOK
  · rw [propagateReset_eq]
    have hrec : prRecruit Dmax a b = (a, b) := by
      unfold prRecruit
      rw [if_neg, if_neg]
      · rintro ⟨h1, h2, -⟩
        rw [effRc_of_resetting h1] at hb; omega
      · rintro ⟨h1, h2, -⟩
        rw [effRc_of_resetting h1] at ha; omega
    rw [hrec]
    dsimp only
    apply processAgent_dormOK
    · unfold prSync; split_ifs <;> rfl
    · unfold prSync; split_ifs <;> rfl
    · intro hR
      have hR' : a.role = .Resetting := by unfold prSync at hR; split_ifs at hR <;> exact hR
      have ha0 : a.resetcount = 0 := by rw [effRc_of_resetting hR'] at ha; exact ha
      refine ⟨?_, ha0⟩
      unfold prSync
      split_ifs with hab
      · have hb0 : b.resetcount = 0 := by rw [effRc_of_resetting hab.2] at hb; exact hb
        simp [ha0, hb0]
      · exact ha0
  · rw [propagateReset_eq]
    have hrec : prRecruit Dmax a b = (a, b) := by
      unfold prRecruit
      rw [if_neg, if_neg]
      · rintro ⟨h1, h2, -⟩
        rw [effRc_of_resetting h1] at hb; omega
      · rintro ⟨h1, h2, -⟩
        rw [effRc_of_resetting h1] at ha; omega
    rw [hrec]
    dsimp only
    apply processAgent_dormOK
    · unfold prSync; split_ifs <;> rfl
    · unfold prSync; split_ifs <;> rfl
    · intro hR
      have hR' : b.role = .Resetting := by unfold prSync at hR; split_ifs at hR <;> exact hR
      have hb0 : b.resetcount = 0 := by rw [effRc_of_resetting hR'] at hb; exact hb
      refine ⟨?_, hb0⟩
      unfold prSync
      split_ifs with hab
      · have ha0 : a.resetcount = 0 := by rw [effRc_of_resetting hab.1] at ha; exact ha
        simp [ha0, hb0]
      · exact hb0

/-- **Effective resetcounts** with the trigger made explicit (P2 Lemma 2.1). -/
theorem rankDelta_rc {Rmax Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n) :
    TrigPair Rmax (rankDeltaOSSR Rmax Emax Dmax hn (a, b)) ∨
      (effRc (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 = max (effRc a - 1) (effRc b - 1) ∧
        effRc (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 = max (effRc a - 1) (effRc b - 1)) := by
  by_cases h : a.role = .Resetting ∨ b.role = .Resetting
  · right
    rw [rankDeltaOSSR_eq_of_resetting h]
    obtain ⟨h1, h2⟩ := effRc_prDedup (propagateReset Emax Dmax hn a b)
    obtain ⟨h3, h4⟩ := effRc_propagateReset (Emax := Emax) (Dmax := Dmax) (hn := hn) a b
    exact ⟨h1.trans h3, h2.trans h4⟩
  · push Not at h
    have hm : max (effRc a - 1) (effRc b - 1) = 0 := by
      simp [effRc_of_not_resetting h.1, effRc_of_not_resetting h.2]
    rw [hm]
    rcases rankDelta_comp (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) h.1 h.2 with
      hT | ⟨c₀, c₁⟩
    · exact Or.inl hT
    · exact Or.inr ⟨effRc_of_not_resetting c₀.1, effRc_of_not_resetting c₁.1⟩

/-- **Collision detection**: two Settled states with equal ranks trigger. -/
theorem rankDelta_collision {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Settled) (hb : b.role = .Settled) (hab : a.rank = b.rank) :
    TrigPair Rmax (rankDeltaOSSR Rmax Emax Dmax hn (a, b)) := by
  have h1 : ¬(a.role = .Resetting ∨ b.role = .Resetting) := by rw [ha, hb]; decide
  have h2 : a.role = .Settled ∧ b.role = .Settled ∧ a.rank = b.rank := ⟨ha, hb, hab⟩
  unfold rankDeltaOSSR
  dsimp only []
  rw [if_neg h1, if_pos h2]
  simp [TrigPair]

/-! ### Steps of the paper instance -/

section Steps

variable {hn : 0 < n}

/-- The ranking rule of the paper instance. -/
noncomputable abbrev rd40 (n : ℕ) (hn : 0 < n) :
    AgentState n × AgentState n → AgentState n × AgentState n :=
  rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn

theorem pem40_delta (C : Config (AgentState n) Opinion n) (i j : Fin n) :
    (PEM40 n hn).δ (C i, C j) =
      transitionPEM n 40 (rmaxPaper n) (rd40 n hn) (((C i).1, (C i).2), ((C j).1, (C j).2)) :=
  rfl

theorem step_fst (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) :
    (C.step (PEM40 n hn) i j) i = (((PEM40 n hn).δ (C i, C j)).1, (C i).2) := by
  simp [Config.step, hij]

theorem step_snd (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) :
    (C.step (PEM40 n hn) i j) j = (((PEM40 n hn).δ (C i, C j)).2, (C j).2) := by
  simp [Config.step, hij, Ne.symm hij]

/-- A trigger at the pair `(i, j)` lands in `PT_L`. -/
theorem ptl_of_trig (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j)
    (h : TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j))) :
    PTL (C.step (PEM40 n hn) i j) := by
  refine ⟨⟨i, ?_, ?_⟩, ⟨i, ?_⟩⟩ <;> rw [step_fst C hij]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

/-- Lifting at the level of configurations. -/
theorem step_lift (Q : AgentState n → AgentState n → Prop)
    (hQc : ∀ s t t', SameCore t' t → Q s t → Q s t')
    (hQs : ∀ s t t', t.role = .Settled → t'.role = .Settled → Q s t → Q s t')
    (C : Config (AgentState n) Opinion n) (i j : Fin n)
    (h : TrigPair (rmaxPaper n) (rd40 n hn ((C i).1, (C j).1)) ∨
      (Q (C i).1 (rd40 n hn ((C i).1, (C j).1)).1 ∧ Q (C j).1 (rd40 n hn ((C i).1, (C j).1)).2)) :
    TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j)) ∨
      (Q (C i).1 ((PEM40 n hn).δ (C i, C j)).1 ∧ Q (C j).1 ((PEM40 n hn).δ (C i, C j)).2) := by
  rw [pem40_delta]
  exact transitionPEM_lift Q hQc hQs _ _ _ _ h

/-- **Effective resetcounts** of one step of the paper instance. -/
theorem step_rc (C : Config (AgentState n) Opinion n) (i j : Fin n) :
    TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j)) ∨
      (effRc ((PEM40 n hn).δ (C i, C j)).1 = max (effRc (C i).1 - 1) (effRc (C j).1 - 1) ∧
        effRc ((PEM40 n hn).δ (C i, C j)).2 = max (effRc (C i).1 - 1) (effRc (C j).1 - 1)) :=
  step_lift (fun _ t => effRc t = max (effRc (C i).1 - 1) (effRc (C j).1 - 1))
    (fun _ t t' hc h => by
      dsimp only at h ⊢
      rw [← h]; unfold effRc; rw [hc.1, hc.2.1])
    (fun _ t t' ht ht' h => by
      dsimp only at h ⊢
      rw [← h, effRc_of_not_resetting (s := t) (by rw [ht]; decide),
        effRc_of_not_resetting (s := t') (by rw [ht']; decide)])
    C i j (rankDelta_rc _ _)

/-- **No propagating participant** (P2 Corollary 2.5, one step). -/
theorem step_dorm (C : Config (AgentState n) Opinion n) (i j : Fin n)
    (hi : effRc (C i).1 = 0) (hj : effRc (C j).1 = 0) :
    TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j)) ∨
      (DormOK (C i).1 ((PEM40 n hn).δ (C i, C j)).1 ∧
        DormOK (C j).1 ((PEM40 n hn).δ (C i, C j)).2) := by
  apply step_lift DormOK
    (fun _ t t' hc h ht' => by
      obtain ⟨h1, h2, h3, h4⟩ := h (hc.1.symm.trans ht')
      exact ⟨h1, hc.2.1.trans h2, by rw [hc.2.2.2.1]; exact h3, by rw [hc.2.2.2.1]; exact h4⟩)
    (fun _ _ t' _ ht' _ h => absurd (h.symm.trans ht') (by decide))
  by_cases h : (C i).1.role = .Resetting ∨ (C j).1.role = .Resetting
  · exact Or.inr (rankDelta_dorm hi hj h)
  · push Not at h
    rcases rankDelta_comp (Rmax := rmaxPaper n) (Emax := 208 * n) (Dmax := 32 * n) (hn := hn)
      h.1 h.2 with hT | ⟨c₀, c₁⟩
    · exact Or.inl hT
    · exact Or.inr ⟨fun h' => absurd h' c₀.1, fun h' => absurd h' c₁.1⟩

/-- **Two computing agents** (P2 Lemma 2.7, one step). -/
theorem step_comp (C : Config (AgentState n) Opinion n) (i j : Fin n)
    (hi : (C i).1.role ≠ .Resetting) (hj : (C j).1.role ≠ .Resetting) :
    TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j)) ∨
      (CompOK (C i).1 ((PEM40 n hn).δ (C i, C j)).1 ∧
        CompOK (C j).1 ((PEM40 n hn).δ (C i, C j)).2) :=
  step_lift CompOK
    (fun _ t t' hc h => ⟨fun e => h.1 (hc.1.symm.trans e), fun hs => hc.1.trans (h.2.1 hs),
      fun hu => by
        obtain ⟨h1, h2, h3⟩ := h.2.2 (hc.1.symm.trans hu)
        exact ⟨h1, by rw [hc.2.2.2.2]; exact h2, by rw [hc.2.2.2.2]; exact h3⟩⟩)
    (fun _ _ t' _ ht' _ => ⟨by rw [ht']; decide, fun _ => ht', fun hu =>
      absurd (ht'.symm.trans hu) (by decide)⟩)
    C i j (rankDelta_comp hi hj)

/-- **Two Settled agents**: the outputs are Settled, or the step is a trigger. -/
theorem step_settled (C : Config (AgentState n) Opinion n) (i j : Fin n)
    (hi : (C i).1.role = .Settled) (hj : (C j).1.role = .Settled) :
    TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j)) ∨
      (((PEM40 n hn).δ (C i, C j)).1.role = .Settled ∧
        ((PEM40 n hn).δ (C i, C j)).2.role = .Settled) := by
  apply step_lift (fun _ t => t.role = .Settled) (fun _ _ _ hc h => hc.1.trans h)
    (fun _ _ _ _ ht' _ => ht')
  by_cases hr : (C i).1.rank = (C j).1.rank
  · exact Or.inl (rankDelta_collision hi hj hr)
  · have he : rd40 n hn ((C i).1, (C j).1) = ((C i).1, (C j).1) :=
      rankDeltaOSSR_settled_distinct_ranks hi hj hr
    rw [he]
    exact Or.inr ⟨hi, hj⟩

/-- **Collision**: two Settled agents with equal ranks trigger. -/
theorem step_collision (C : Config (AgentState n) Opinion n) (i j : Fin n)
    (hi : (C i).1.role = .Settled) (hj : (C j).1.role = .Settled)
    (hr : (C i).1.rank = (C j).1.rank) :
    TrigPair (rmaxPaper n) ((PEM40 n hn).δ (C i, C j)) := by
  rcases step_lift (hn := hn) (fun _ _ => False) (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h) C i j
    (Or.inl (rankDelta_collision hi hj hr)) with h | h
  · exact h
  · exact h.1.elim

end Steps

end Ripple.PopulationProtocol.SSEM

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `rankDeltaOSSR` on the configurations of the tree phase (P2 §2, Lemmas 2.4, 2.7)

Explicit outputs of `rankDeltaOSSR` for the interactions that occur in the tree phase of P3
Lemma 11 (no propagating agent, at most one leader, no errorcount about to expire):

* two dormant agents (`rd_RR`): both count their delay timer down and may wake;
* a dormant agent with a computing partner (`rd_RC`, `rd_CR`): the dormant agent wakes;
* a Settled and an Unsettled agent (`rd_SU_rec`, `rd_US_rec`): recruitment, or, when the Settled
  agent cannot recruit, an errorcount decrement (`rd_SU_dec`, `rd_US_dec`);
* two Unsettled agents (`rd_UU`): both errorcounts drop by one.

`rhoS` is the ranking projection (answer and timer erased) of P3 §1.2.
-/

import Ripple.PopulationProtocol.SSEM.Protocol.RankDelta

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-- The ranking projection of a state: answer and timer erased (P3 §1.2, `ρ`). -/
def rhoS (s : AgentState n) : AgentState n := { s with answer := .phi, timer := 0 }

@[simp] theorem rhoS_role (s : AgentState n) : (rhoS s).role = s.role := rfl
@[simp] theorem rhoS_rank (s : AgentState n) : (rhoS s).rank = s.rank := rfl
@[simp] theorem rhoS_leader (s : AgentState n) : (rhoS s).leader = s.leader := rfl
@[simp] theorem rhoS_resetcount (s : AgentState n) : (rhoS s).resetcount = s.resetcount := rfl
@[simp] theorem rhoS_children (s : AgentState n) : (rhoS s).children = s.children := rfl
@[simp] theorem rhoS_errorcount (s : AgentState n) : (rhoS s).errorcount = s.errorcount := rfl
@[simp] theorem rhoS_delaytimer (s : AgentState n) : (rhoS s).delaytimer = s.delaytimer := rfl

theorem rhoS_eq_iff {s t : AgentState n} :
    rhoS s = rhoS t ↔ s.role = t.role ∧ s.rank = t.rank ∧ s.leader = t.leader ∧
      s.resetcount = t.resetcount ∧ s.children = t.children ∧ s.errorcount = t.errorcount ∧
      s.delaytimer = t.delaytimer := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg AgentState.role h
    · simpa using congrArg AgentState.rank h
    · simpa using congrArg AgentState.leader h
    · simpa using congrArg AgentState.resetcount h
    · simpa using congrArg AgentState.children h
    · simpa using congrArg AgentState.errorcount h
    · simpa using congrArg AgentState.delaytimer h
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    cases s; cases t
    simp only [rhoS] at *
    subst h1 h2 h3 h4 h5 h6 h7
    rfl

@[simp] theorem rhoS_with_answer (s : AgentState n) (a : Answer) :
    rhoS { s with answer := a } = rhoS s := rfl
@[simp] theorem rhoS_with_timer (s : AgentState n) (t : ℕ) :
    rhoS { s with timer := t } = rhoS s := rfl
@[simp] theorem rhoS_rhoS (s : AgentState n) : rhoS (rhoS s) = rhoS s := rfl

/-! ### Explicit outputs -/

/-- A dormant agent after an interaction with a Resetting partner. -/
def dormStep (Emax : ℕ) (hn : 0 < n) (x : AgentState n) : AgentState n :=
  if x.delaytimer - 1 = 0 then resetOSSR Emax hn { x with delaytimer := x.delaytimer - 1 }
  else { x with delaytimer := x.delaytimer - 1 }

/-- A dormant agent after an interaction with a computing partner: it wakes. -/
def wakeStep (Emax : ℕ) (hn : 0 < n) (x : AgentState n) : AgentState n :=
  resetOSSR Emax hn { x with delaytimer := x.delaytimer - 1 }

theorem with_resetcount_zero {x : AgentState n} (h : x.resetcount = 0) :
    { x with resetcount := 0 } = x := by
  cases x; simp only at h; subst h; rfl

@[simp] theorem dormStep_leader {Emax : ℕ} {hn : 0 < n} (x : AgentState n) :
    (dormStep Emax hn x).leader = x.leader := by
  unfold dormStep resetOSSR
  split_ifs <;> cases x.leader <;> rfl

theorem propagateReset_RR {Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Resetting) (hb : b.role = .Resetting) (har : a.resetcount = 0)
    (hbr : b.resetcount = 0) :
    propagateReset Emax Dmax hn a b = (dormStep Emax hn a, dormStep Emax hn b) := by
  rcases a with ⟨ra, ka, la, ca, aa, ta, cha, ea, da⟩
  rcases b with ⟨rb, kb, lb, cb, ab, tb, chb, eb, db⟩
  simp only at ha hb har hbr
  subst ha hb har hbr
  unfold propagateReset processAgent dormStep
  simp

theorem rd_RR {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Resetting) (hb : b.role = .Resetting) (har : a.resetcount = 0)
    (hbr : b.resetcount = 0) (hL : ¬ (a.leader = .L ∧ b.leader = .L)) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) = (dormStep Emax hn a, dormStep Emax hn b) := by
  unfold rankDeltaOSSR
  dsimp only
  rw [if_pos (Or.inl ha), propagateReset_RR (Emax := Emax) (Dmax := Dmax) (hn := hn) ha hb har hbr]
  dsimp only
  rw [if_neg (by simp only [dormStep_leader]; exact fun h => hL ⟨h.1, h.2.1⟩)]

theorem rd_RC {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Resetting) (har : a.resetcount = 0) (hb : b.role ≠ .Resetting) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) = (wakeStep Emax hn a, b) := by
  unfold rankDeltaOSSR propagateReset processAgent wakeStep
  simp only [ha, har, true_or, if_true, lt_irrefl, false_and, if_false, hb, and_false,
    and_self]
  have hbb : (b.role == Role.Resetting) = false := by simpa using hb
  simp only [hbb, Bool.not_false, or_true, if_true]
  try (cases hla : a.leader <;> simp_all [resetOSSR])

theorem rd_CR {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role ≠ .Resetting) (hb : b.role = .Resetting) (hbr : b.resetcount = 0) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) = (a, wakeStep Emax hn b) := by
  unfold rankDeltaOSSR propagateReset processAgent wakeStep
  simp only [hb, hbr, or_true, if_true, lt_irrefl, false_and, if_false, ha, and_false,
    false_and]
  have haa : (a.role == Role.Resetting) = false := by simpa using ha
  simp only [haa, Bool.not_false, or_true, if_true]
  try (cases hlb : b.leader <;> simp_all [resetOSSR])

theorem rd_SU_rec {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Settled) (hb : b.role = .Unsettled) (hc : a.children < 2)
    (hlt : 2 * a.rank.val + a.children + 1 < n) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) =
      ({ a with children := a.children + 1 },
        { b with role := .Settled, children := 0, rank := ⟨_, hlt⟩ }) := by
  unfold rankDeltaOSSR
  simp [ha, hb, hc, hlt]

theorem rd_US_rec {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Unsettled) (hb : b.role = .Settled) (hc : b.children < 2)
    (hlt : 2 * b.rank.val + b.children + 1 < n) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) =
      ({ a with role := .Settled, children := 0, rank := ⟨_, hlt⟩ },
        { b with children := b.children + 1 }) := by
  unfold rankDeltaOSSR
  simp [ha, hb, hc, hlt]

theorem rd_SU_dec {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Settled) (hb : b.role = .Unsettled)
    (hno : ¬ (a.children < 2 ∧ 2 * a.rank.val + a.children + 1 < n))
    (he : 2 ≤ b.errorcount) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) = (a, { b with errorcount := b.errorcount - 1 }) := by
  have he' : b.errorcount - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR
  by_cases hc : a.children < 2
  · have hle : ¬ (2 * a.rank.val + a.children + 1 < n) := fun h => hno ⟨hc, h⟩
    simp [ha, hb, he', hc, hle]
  · simp [ha, hb, he', hc]

theorem rd_US_dec {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Unsettled) (hb : b.role = .Settled)
    (hno : ¬ (b.children < 2 ∧ 2 * b.rank.val + b.children + 1 < n))
    (he : 2 ≤ a.errorcount) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) = ({ a with errorcount := a.errorcount - 1 }, b) := by
  have he' : a.errorcount - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR
  by_cases hc : b.children < 2
  · have hle : ¬ (2 * b.rank.val + b.children + 1 < n) := fun h => hno ⟨hc, h⟩
    simp [ha, hb, he', hc, hle]
  · simp [ha, hb, he', hc]

theorem rd_UU {Rmax Emax Dmax : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : a.role = .Unsettled) (hb : b.role = .Unsettled)
    (hea : 2 ≤ a.errorcount) (heb : 2 ≤ b.errorcount) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) =
      ({ a with errorcount := a.errorcount - 1 }, { b with errorcount := b.errorcount - 1 }) := by
  have hea' : a.errorcount - 1 ≠ 0 := by omega
  have heb' : b.errorcount - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR
  simp [ha, hb, hea', heb']

/-! ### `rankDeltaOSSR` keeps the timers (P3 Lemma 1(a)) -/

theorem resetOSSR_timer {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).timer = s.timer := by
  unfold resetOSSR
  cases s.leader <;> rfl

theorem tr_processAgent_timer {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) :
    (processAgent Emax Dmax hn s oldRc pr).timer = s.timer := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2]
      simp only []
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_timer]
      · rw [if_neg h3]
    · rw [if_neg h2]
      simp only []
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_timer]
      · rw [if_neg h3]
  · rw [if_neg h1]

theorem tr_propagateReset_timer {Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n) :
    (propagateReset Emax Dmax hn a b).1.timer = a.timer ∧
    (propagateReset Emax Dmax hn a b).2.timer = b.timer := by
  unfold propagateReset
  constructor <;>
    simp only [tr_processAgent_timer] <;>
    split_ifs <;> rfl

theorem tr_rankDeltaOSSR_timer {Rmax Emax Dmax : ℕ} {hn : 0 < n} (s t : AgentState n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.timer = s.timer ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.timer = t.timer := by
  unfold rankDeltaOSSR
  dsimp only []
  split_ifs <;>
    simp_all [tr_propagateReset_timer]

end Ripple.PopulationProtocol.SSEM

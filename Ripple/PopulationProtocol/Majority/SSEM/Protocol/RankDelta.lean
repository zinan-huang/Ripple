/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete Ranking Subprotocol (OPTIMAL-SILENT-SSR)

This file defines the concrete `rankDeltaOSSR` implementing Protocol 3
from Burman, Chen, Chen, Doty, Nowak, Severson, Xu (PODC 2021):
"Time-Optimal Self-Stabilizing Leader Election in Population Protocols".

## Components

* `resetOSSR` — Protocol 4 (RESET subroutine for OPTIMAL-SILENT-SSR):
  Leaders become Settled at rank 1; followers become Unsettled.

* `propagateReset` — Protocol 2 (PROPAGATE-RESET):
  Epidemic-style reset propagation with resetcount synchronization
  and delaytimer-based dormancy.

* `rankDeltaOSSR` — Protocol 3 (OPTIMAL-SILENT-SSR):
  Binary-tree ranking with collision detection and error monitoring.

## Key property

`rankDeltaOSSR_settled_distinct_ranks`: when both agents are Settled
with distinct ranks, the protocol is the identity (no state change).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Protocol.State
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Silent

namespace SSEM

variable {n : ℕ}

/-! ### Protocol 4: RESET for OPTIMAL-SILENT-SSR -/

/-- Protocol 4 from Burman et al.: wake an agent from the Resetting role.
Leaders (leader = L) become Settled at rank 1 (0-indexed: rank 0).
Followers (leader = F) become Unsettled with errorcount initialized. -/
def resetOSSR (Emax : ℕ) (hn : 0 < n) (s : AgentState n) : AgentState n :=
  match s.leader with
  | .L => { s with role := .Settled, rank := ⟨0, hn⟩, children := 0 }
  | .F => { s with role := .Unsettled, errorcount := Emax }

/-! ### Protocol 2: PROPAGATE-RESET -/

/-- Process a dormant agent: decrement delaytimer or trigger resetOSSR.
Extracted from propagateReset Phase 3 for composability. -/
def processAgent (Emax Dmax : ℕ) (hn : 0 < n)
    (s : AgentState n) (oldRc : ℕ) (partnerResetting : Bool) : AgentState n :=
  if s.role = .Resetting ∧ s.resetcount = 0 then
    let s :=
      if 0 < oldRc then
        { s with delaytimer := Dmax }
      else
        { s with delaytimer := s.delaytimer - 1 }
    if s.delaytimer = 0 ∨ !partnerResetting then
      resetOSSR Emax hn s
    else s
  else s

theorem processAgent_rc_ne_zero {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} (hrc : s.resetcount ≠ 0) (oldRc : ℕ) (pr : Bool) :
    processAgent Emax Dmax hn s oldRc pr = s := by
  unfold processAgent; simp [hrc]

theorem processAgent_not_resetting {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} (hrs : s.role ≠ .Resetting) (oldRc : ℕ) (pr : Bool) :
    processAgent Emax Dmax hn s oldRc pr = s := by
  unfold processAgent; simp [hrs]

theorem processAgent_dormant_fresh_stays {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} {oldRc : ℕ} {partnerResetting : Bool}
    (hs : s.role = .Resetting) (hrc : s.resetcount = 0)
    (holdRc : 0 < oldRc) (hDmax : 0 < Dmax) (hPartner : partnerResetting = true) :
    (processAgent Emax Dmax hn s oldRc partnerResetting).role = .Resetting := by
  unfold processAgent
  simp only [hs, hrc, and_self, ite_true, holdRc, show ¬(Dmax = 0) from by omega,
    false_or, hPartner, Bool.not_true, Bool.false_eq_true, ite_false]

/-- Dormant agent with `oldRc = 0` (i.e. agent had rc=0 going into this step) but
sufficient delaytimer (≥ 2) and a Resetting partner: stays Resetting.
Used by `propagateReset_recruits` for the post-recruit agent (whose oldRc was 0). -/
theorem processAgent_oldRc_zero_partner_true_delay_gt_one_stays
    {Emax Dmax : ℕ} {hn : 0 < n} {s : AgentState n}
    (hs : s.role = .Resetting) (hrc : s.resetcount = 0)
    (hdt : 1 < s.delaytimer) :
    (processAgent Emax Dmax hn s 0 true).role = .Resetting := by
  unfold processAgent
  have hdt_ne : s.delaytimer - 1 ≠ 0 := by omega
  simp [hs, hrc, hdt_ne]

/-- When `processAgent` fires the fresh-dormant branch (rc=0 with oldRc > 0,
partner Resetting, Dmax > 0), it preserves `resetcount` (only `delaytimer`
gets reset to Dmax). -/
theorem processAgent_dormant_fresh_keeps_rc {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} {oldRc : ℕ} {partnerResetting : Bool}
    (hs : s.role = .Resetting) (hrc : s.resetcount = 0)
    (holdRc : 0 < oldRc) (hDmax : 0 < Dmax) (hPartner : partnerResetting = true) :
    (processAgent Emax Dmax hn s oldRc partnerResetting).resetcount = 0 := by
  unfold processAgent
  simp only [hs, hrc, and_self, ite_true, holdRc, show ¬(Dmax = 0) from by omega,
    false_or, hPartner, Bool.not_true, Bool.false_eq_true, ite_false]

/-- Symmetric to `_keeps_rc`: leader is preserved. -/
theorem processAgent_dormant_fresh_keeps_leader {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} {oldRc : ℕ} {partnerResetting : Bool}
    (hs : s.role = .Resetting) (hrc : s.resetcount = 0)
    (holdRc : 0 < oldRc) (hDmax : 0 < Dmax) (hPartner : partnerResetting = true) :
    (processAgent Emax Dmax hn s oldRc partnerResetting).leader = s.leader := by
  unfold processAgent
  simp only [hs, hrc, and_self, ite_true, holdRc, show ¬(Dmax = 0) from by omega,
    false_or, hPartner, Bool.not_true, Bool.false_eq_true, ite_false]

def propagateReset (Emax Dmax : ℕ) (hn : 0 < n)
    (a b : AgentState n) : AgentState n × AgentState n :=
  -- Phase 1: recruitment (line 1-2)
  let (a, b) :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  -- Save old resetcounts for "just became 0" check
  let oldRcA := a.resetcount
  let oldRcB := b.resetcount
  -- Phase 2: resetcount synchronization (lines 3-4)
  let (a, b) :=
    if a.role = .Resetting ∧ b.role = .Resetting then
      let newRc := max (a.resetcount - 1) (b.resetcount - 1)
      ({ a with resetcount := newRc }, { b with resetcount := newRc })
    else (a, b)
  -- Phase 3: dormant agent processing (lines 5-11)
  let aRes := b.role == .Resetting
  let bRes := a.role == .Resetting
  (processAgent Emax Dmax hn a oldRcA aRes, processAgent Emax Dmax hn b oldRcB bRes)

/-! ### Answer preservation for RESET / PROPAGATE-RESET -/

theorem resetOSSR_answer_preserved {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).answer = s.answer := by
  unfold resetOSSR
  cases s.leader <;> rfl

theorem processAgent_answer_preserved {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) :
    (processAgent Emax Dmax hn s oldRc pr).answer = s.answer := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2]
      simp only []
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_answer_preserved]
      · rw [if_neg h3]
    · rw [if_neg h2]
      simp only []
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_answer_preserved]
      · rw [if_neg h3]
  · rw [if_neg h1]

theorem propagateReset_answer_preserved {Emax Dmax : ℕ} {hn : 0 < n}
    (a b : AgentState n) :
    (propagateReset Emax Dmax hn a b).1.answer = a.answer ∧
    (propagateReset Emax Dmax hn a b).2.answer = b.answer := by
  unfold propagateReset
  constructor <;>
    simp only [processAgent_answer_preserved] <;>
    split_ifs <;> rfl

/-! ### Protocol 3: OPTIMAL-SILENT-SSR -/

/-- Protocol 3 from Burman et al.: the complete ranking subprotocol.

Parameters:
* `Rmax` — maximum resetcount (paper: R_max = 60 ln n)
* `Emax` — error counter for Unsettled agents (paper: E_max = Θ(n))
* `Dmax` — delay timer for dormant agents (paper: D_max = Θ(n))

The protocol has four parts:
1. **PROPAGATE-RESET** (lines 1-4): Handle Resetting agents, including
   leader deduplication.
2. **Collision detection** (lines 5-7): Two Settled agents with the
   same rank → both become Resetting.
3. **Binary-tree ranking** (lines 8-12): Settled agents recruit
   Unsettled agents as children in a binary tree.
4. **Error monitoring** (lines 13-18): Unsettled agents decrement
   errorcount; if it reaches 0, trigger reset. -/
def rankDeltaOSSR (Rmax Emax Dmax : ℕ) (hn : 0 < n)
    (pair : AgentState n × AgentState n) : AgentState n × AgentState n :=
  let (a, b) := pair
  -- Part 1: PROPAGATE-RESET + leader deduplication (lines 1-4)
  if a.role = .Resetting ∨ b.role = .Resetting then
    let (a, b) := propagateReset Emax Dmax hn a b
    let b := if a.leader = .L ∧ b.leader = .L ∧
                a.role = .Resetting ∧ b.role = .Resetting
             then { b with leader := .F }
             else b
    (a, b)
  -- Part 2: Collision detection (lines 5-7)
  else if a.role = .Settled ∧ b.role = .Settled ∧ a.rank = b.rank then
    ({ a with role := .Resetting, resetcount := Rmax, leader := .L },
     { b with role := .Resetting, resetcount := Rmax, leader := .L })
  else
    -- Part 3: Binary-tree ranking (lines 8-12)
    -- Try (a recruits b), then (b recruits a)
    if h_ab : a.role = .Settled ∧ b.role = .Unsettled ∧
       a.children < 2 ∧ 2 * a.rank.val + a.children + 1 < n then
      let childRank : Fin n := ⟨2 * a.rank.val + a.children + 1, h_ab.2.2.2⟩
      ({ a with children := a.children + 1 },
       { b with role := .Settled, children := 0, rank := childRank })
    else if h_ba : b.role = .Settled ∧ a.role = .Unsettled ∧
       b.children < 2 ∧ 2 * b.rank.val + b.children + 1 < n then
      let childRank : Fin n := ⟨2 * b.rank.val + b.children + 1, h_ba.2.2.2⟩
      ({ a with role := .Settled, children := 0, rank := childRank },
       { b with children := b.children + 1 })
    else
      -- Part 4: Error monitoring (lines 13-18)
      let a' :=
        if a.role = .Unsettled then
          let a'' := { a with errorcount := a.errorcount - 1 }
          if a''.errorcount = 0 then
            { a'' with role := .Resetting, resetcount := Rmax, leader := .L }
          else a''
        else a
      let b' :=
        if b.role = .Unsettled then
          let b'' := { b with errorcount := b.errorcount - 1 }
          if b''.errorcount = 0 then
            { b'' with role := .Resetting, resetcount := Rmax, leader := .L }
          else b''
        else b
      if (a'.role = .Resetting ∧ a.role = .Unsettled) ∨
         (b'.role = .Resetting ∧ b.role = .Unsettled) then
        ({ a' with role := .Resetting, resetcount := Rmax, leader := .L },
         { b' with role := .Resetting, resetcount := Rmax, leader := .L })
      else (a', b')

/-! ### Key property: identity on Settled pairs with distinct ranks -/

theorem rankDeltaOSSR_settled_distinct_ranks
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hne : s.rank ≠ t.rank) :
    rankDeltaOSSR Rmax Emax Dmax hn (s, t) = (s, t) := by
  have hsr : s.role ≠ .Resetting := by rw [hs]; decide
  have htr : t.role ≠ .Resetting := by rw [ht]; decide
  have hsu : s.role ≠ .Unsettled := by rw [hs]; decide
  have htu : t.role ≠ .Unsettled := by rw [ht]; decide
  unfold rankDeltaOSSR
  dsimp only []
  rw [if_neg (show ¬(s.role = .Resetting ∨ t.role = .Resetting) from
    fun h => h.elim hsr htr)]
  rw [if_neg (show ¬(s.role = .Settled ∧ t.role = .Settled ∧ s.rank = t.rank) from
    fun ⟨_, _, h⟩ => hne h)]
  rw [dif_neg (show ¬(s.role = .Settled ∧ t.role = .Unsettled ∧
    s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n) from
    fun ⟨_, h, _⟩ => htu h)]
  rw [dif_neg (show ¬(t.role = .Settled ∧ s.role = .Unsettled ∧
    t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n) from
    fun ⟨_, h, _⟩ => hsu h)]
  rw [if_neg (show ¬(s.role = .Unsettled) from hsu)]
  rw [if_neg (show ¬(t.role = .Unsettled) from htu)]
  rw [if_neg (show ¬((s.role = .Resetting ∧ s.role = .Unsettled) ∨
    (t.role = .Resetting ∧ t.role = .Unsettled)) from by
    intro h; cases h with
    | inl h => exact hsr h.1
    | inr h => exact htr h.1)]

/-! ### Key property: rerank preserves answers -/

theorem rankDeltaOSSR_answer_preserved
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (s t : AgentState n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.answer = s.answer ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.answer = t.answer := by
  unfold rankDeltaOSSR
  dsimp only []
  split_ifs <;>
    simp_all [propagateReset_answer_preserved]

/-! ### Stabilized wrapper satisfying `RankDeltaSettledFix`

The full `rankDeltaOSSR` resets on same-rank Settled pairs (collision
detection, Protocol 3 lines 5-7). This is correct protocol behavior
needed BEFORE stabilization, but `RankDeltaSettledFix` requires identity
on ALL Settled pairs.

`rankDeltaStable` is identity on Settled pairs by construction, and
delegates to `rankDeltaOSSR` otherwise. After ranking has stabilized
(InSrank: all Settled with unique ranks), `rankDeltaStable` and
`rankDeltaOSSR` are behaviorally identical — the collision case never
fires because ranks are unique. -/
def rankDeltaStable (Rmax Emax Dmax : ℕ) (hn : 0 < n)
    (pair : AgentState n × AgentState n) : AgentState n × AgentState n :=
  if pair.1.role = .Settled ∧ pair.2.role = .Settled then pair
  else rankDeltaOSSR Rmax Emax Dmax hn pair

theorem rankDeltaOSSR_satisfies_fix {Rmax Emax Dmax : ℕ} {hn : 0 < n} :
    RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn) :=
  fun _ _ hs ht hne => rankDeltaOSSR_settled_distinct_ranks hs ht hne

theorem rankDeltaStable_satisfies_fix {Rmax Emax Dmax : ℕ} {hn : 0 < n} :
    RankDeltaSettledFix (rankDeltaStable Rmax Emax Dmax hn) := by
  intro s t hs ht _
  simp only [rankDeltaStable, hs, ht, and_self, ite_true]

theorem rankDeltaStable_eq_rankDeltaOSSR_non_settled
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (h : ¬(s.role = .Settled ∧ t.role = .Settled)) :
    rankDeltaStable Rmax Emax Dmax hn (s, t) =
    rankDeltaOSSR Rmax Emax Dmax hn (s, t) := by
  simp only [rankDeltaStable, h, ite_false]

theorem rankDeltaStable_eq_of_distinct_ranks
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hne : s.rank ≠ t.rank) :
    rankDeltaStable Rmax Emax Dmax hn (s, t) = (s, t) := by
  simp only [rankDeltaStable, hs, ht, and_self, ite_true]

end SSEM

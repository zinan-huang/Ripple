/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transition Function for P_EM

Algorithm 1 from Kanaya et al. (2025), parameterized by a ranking
subprotocol (Optimal-Silent-SSR from Burman et al. PODC 2021).

The protocol has four phases:
1. Ranking: Execute the ranking subprotocol to assign unique ranks.
2. Swapping: Swap states so A-agents get lower ranks.
3. Decision: Median-ranked agent(s) decide the majority opinion.
4. Propagation: Median agent propagates answer; reset on disagreement.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Protocol
import Ripple.PopulationProtocol.Majority.SSEM.Protocol.State

namespace SSEM

/-- The ceiling half: ⌈n/2⌉. -/
def ceilHalf (n : ℕ) : ℕ := (n + 1) / 2

def opinionToAnswer : Opinion → Answer
  | .A => .outA
  | .B => .outB

/-- Phases 1-3 of Algorithm 1: rankDelta + answer clearing + timer init + epidemic.
Only `answer` and `timer` fields may change; all structural fields (role, leader,
rank, children, resetcount, delaytimer) are inherited from `rankDelta` output. -/
def transitionPEM_prePhase4 (n : ℕ) (trank : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n)
    (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    AgentState n × AgentState n :=
  let (r₀, r₁) := rankDelta (s₀, s₁)
  let a₀ := if r₀.role = .Resetting ∧ s₀.role ≠ .Resetting then
      { r₀ with answer := .phi }
    else r₀
  let a₁ := if r₁.role = .Resetting ∧ s₁.role ≠ .Resetting then
      { r₁ with answer := .phi }
    else r₁
  let a₀ := if a₀.role = .Settled ∧ s₀.role ≠ .Settled ∧ a₀.rank.val + 1 = ceilHalf n then
      { a₀ with timer := 7 * (trank + 4) }
    else a₀
  let a₁ := if a₁.role = .Settled ∧ s₁.role ≠ .Settled ∧ a₁.rank.val + 1 = ceilHalf n then
      { a₁ with timer := 7 * (trank + 4) }
    else a₁
  let (a₀, a₁) :=
    if a₀.role = .Resetting ∧ a₁.role = .Resetting then
      if a₀.answer = .phi ∧ a₁.answer ≠ .phi then
        ({ a₀ with answer := a₁.answer }, a₁)
      else if a₁.answer = .phi ∧ a₀.answer ≠ .phi then
        (a₀, { a₁ with answer := a₀.answer })
      else (a₀, a₁)
    else (a₀, a₁)
  (a₀, a₁)

/-- Phase 4a: swap B-lower-rank pairs (lines 10-11). Only reorders; no field changes. -/
def phase4_swap (a₀ a₁ : AgentState n) (x₀ x₁ : Opinion) :
    AgentState n × AgentState n :=
  if a₀.rank < a₁.rank ∧ x₀ = .B ∧ x₁ = .A then (a₁, a₀) else (a₀, a₁)

/-- Phase 4b: median decision (lines 12-18). Only changes `answer`. -/
def phase4_decide (n : ℕ) (b₀ b₁ : AgentState n) (x₀ x₁ : Opinion) :
    AgentState n × AgentState n :=
  if n % 2 = 0 then
    if b₀.rank.val + 1 = n / 2 ∧ b₁.rank.val + 1 = n / 2 + 1 then
      if x₀ = x₁ then ({ b₀ with answer := opinionToAnswer x₀ }, { b₁ with answer := opinionToAnswer x₀ })
      else ({ b₀ with answer := .outT }, { b₁ with answer := .outT })
    else if b₁.rank.val + 1 = n / 2 ∧ b₀.rank.val + 1 = n / 2 + 1 then
      if x₁ = x₀ then ({ b₀ with answer := opinionToAnswer x₁ }, { b₁ with answer := opinionToAnswer x₁ })
      else ({ b₀ with answer := .outT }, { b₁ with answer := .outT })
    else (b₀, b₁)
  else
    let b₀ := if b₀.rank.val + 1 = ceilHalf n then { b₀ with answer := opinionToAnswer x₀ } else b₀
    let b₁ := if b₁.rank.val + 1 = ceilHalf n then { b₁ with answer := opinionToAnswer x₁ } else b₁
    (b₀, b₁)

/-- Phase 4c: propagation (lines 19-24). May change `timer`, `answer`, `role`, `leader`, `resetcount`. -/
def phase4_propagate (n Rmax : ℕ) (b₀ b₁ : AgentState n) :
    AgentState n × AgentState n :=
  if b₀.rank.val + 1 = ceilHalf n then
    let b₀ := if b₁.rank.val + 1 = n then { b₀ with timer := b₀.timer - 1 } else b₀
    if b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer then
      ({ b₀ with role := .Resetting, leader := .L, resetcount := Rmax },
       { b₁ with answer := b₀.answer, role := .Resetting, leader := .L, resetcount := Rmax })
    else (b₀, b₁)
  else if b₁.rank.val + 1 = ceilHalf n then
    let b₁ := if b₀.rank.val + 1 = n then { b₁ with timer := b₁.timer - 1 } else b₁
    if b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer then
      ({ b₀ with answer := b₁.answer, role := .Resetting, leader := .L, resetcount := Rmax },
       { b₁ with role := .Resetting, leader := .L, resetcount := Rmax })
    else (b₀, b₁)
  else (b₀, b₁)

/-- Phase 4 of Algorithm 1: both-Settled guard + swap + decide + propagate. -/
def transitionPEM_phase4 (n Rmax : ℕ)
    (a : AgentState n × AgentState n) (x₀ x₁ : Opinion) :
    AgentState n × AgentState n :=
  let (a₀, a₁) := a
  if a₀.role = .Settled ∧ a₁.role = .Settled then
    let (b₀, b₁) := phase4_swap a₀ a₁ x₀ x₁
    let (b₀, b₁) := phase4_decide n b₀ b₁ x₀ x₁
    phase4_propagate n Rmax b₀ b₁
  else a

/-- Phase 4 is identity when NOT both Settled. -/
theorem transitionPEM_phase4_of_not_both_settled
    {n Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h : ¬(a.1.role = .Settled ∧ a.2.role = .Settled)) :
    transitionPEM_phase4 n Rmax a x₀ x₁ = a := by
  simp [transitionPEM_phase4, h]

/-! ### Phase 4 role invariant -/

/-- Role invariant used by Phase 4: role is either Settled or Resetting. -/
def RoleSettledOrResetting {n : ℕ} (s : AgentState n) : Prop :=
  s.role = .Settled ∨ s.role = .Resetting

/-- Pair version of `RoleSettledOrResetting`. -/
def PairRoleSettledOrResetting {n : ℕ} (p : AgentState n × AgentState n) : Prop :=
  RoleSettledOrResetting p.1 ∧ RoleSettledOrResetting p.2

theorem RoleSettledOrResetting.not_unsettled
    {n : ℕ} {s : AgentState n}
    (h : RoleSettledOrResetting s) :
    s.role ≠ .Unsettled := by
  rcases h with hs | hs <;> rw [hs] <;> decide

theorem transitionPEM_phase4_swap_role_ok
    {n : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h : PairRoleSettledOrResetting a) :
    PairRoleSettledOrResetting ((phase4_swap a.1 a.2 x₀ x₁)) := by
  rcases a with ⟨a₀, a₁⟩
  rcases h with ⟨h₀, h₁⟩
  unfold phase4_swap
  dsimp [PairRoleSettledOrResetting, RoleSettledOrResetting] at h₀ h₁ ⊢
  split_ifs
  · exact ⟨h₁, h₀⟩
  · exact ⟨h₀, h₁⟩

theorem transitionPEM_phase4_decision_role_ok
    {n : ℕ} {b : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h : PairRoleSettledOrResetting b) :
    PairRoleSettledOrResetting ((phase4_decide n b.1 b.2 x₀ x₁)) := by
  rcases b with ⟨b₀, b₁⟩
  rcases h with ⟨h₀, h₁⟩
  unfold phase4_decide
  dsimp [PairRoleSettledOrResetting, RoleSettledOrResetting] at h₀ h₁ ⊢
  split_ifs <;> simp [h₀, h₁]

theorem transitionPEM_phase4_propagation_role_ok
    {n Rmax : ℕ} {b : AgentState n × AgentState n}
    (h : PairRoleSettledOrResetting b) :
    PairRoleSettledOrResetting ((phase4_propagate n Rmax b.1 b.2)) := by
  rcases b with ⟨b₀, b₁⟩
  rcases h with ⟨h₀, h₁⟩
  unfold phase4_propagate
  dsimp [PairRoleSettledOrResetting, RoleSettledOrResetting] at h₀ h₁ ⊢
  split_ifs <;> simp [h₀, h₁]

theorem transitionPEM_phase4_role_ok_of_both_settled
    {n Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a.1.role = .Settled)
    (h₁ : a.2.role = .Settled) :
    PairRoleSettledOrResetting (transitionPEM_phase4 n Rmax a x₀ x₁) := by
  rcases a with ⟨a₀, a₁⟩
  dsimp at h₀ h₁
  let b := phase4_swap a₀ a₁ x₀ x₁
  let c := phase4_decide n b.1 b.2 x₀ x₁
  have ha : PairRoleSettledOrResetting (a₀, a₁) := ⟨Or.inl h₀, Or.inl h₁⟩
  have hb : PairRoleSettledOrResetting b := by
    simpa [b] using
      (transitionPEM_phase4_swap_role_ok (n := n) (a := (a₀, a₁))
        (x₀ := x₀) (x₁ := x₁) ha)
  have hc : PairRoleSettledOrResetting c := by
    simpa [c] using
      (transitionPEM_phase4_decision_role_ok (n := n) (b := b)
        (x₀ := x₀) (x₁ := x₁) hb)
  have hp : PairRoleSettledOrResetting (phase4_propagate n Rmax c.1 c.2) := by
    simpa using
      (transitionPEM_phase4_propagation_role_ok (n := n) (Rmax := Rmax)
        (b := c) hc)
  simpa [transitionPEM_phase4, h₀, h₁, b, c] using hp

theorem transitionPEM_phase4_role_settled_or_resetting
    {n Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a.1.role = .Settled)
    (h₁ : a.2.role = .Settled) :
    ((transitionPEM_phase4 n Rmax a x₀ x₁).1.role = .Settled ∨
      (transitionPEM_phase4 n Rmax a x₀ x₁).1.role = .Resetting) ∧
    ((transitionPEM_phase4 n Rmax a x₀ x₁).2.role = .Settled ∨
      (transitionPEM_phase4 n Rmax a x₀ x₁).2.role = .Resetting) := by
  simpa [PairRoleSettledOrResetting, RoleSettledOrResetting]
    using transitionPEM_phase4_role_ok_of_both_settled
      (n := n) (Rmax := Rmax) (a := a) (x₀ := x₀) (x₁ := x₁) h₀ h₁

theorem transitionPEM_phase4_not_unsettled_of_both_settled
    {n Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a.1.role = .Settled)
    (h₁ : a.2.role = .Settled) :
    (transitionPEM_phase4 n Rmax a x₀ x₁).1.role ≠ .Unsettled ∧
    (transitionPEM_phase4 n Rmax a x₀ x₁).2.role ≠ .Unsettled := by
  have h :=
    transitionPEM_phase4_role_ok_of_both_settled
      (n := n) (Rmax := Rmax) (a := a) (x₀ := x₀) (x₁ := x₁) h₀ h₁
  exact ⟨RoleSettledOrResetting.not_unsettled h.1,
         RoleSettledOrResetting.not_unsettled h.2⟩

private theorem phase4_swap_role_ok
    {a₀ a₁ : AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a₀.role = .Settled ∨ a₀.role = .Resetting)
    (h₁ : a₁.role = .Settled ∨ a₁.role = .Resetting) :
    ((phase4_swap a₀ a₁ x₀ x₁).1.role = .Settled ∨
     (phase4_swap a₀ a₁ x₀ x₁).1.role = .Resetting) ∧
    ((phase4_swap a₀ a₁ x₀ x₁).2.role = .Settled ∨
     (phase4_swap a₀ a₁ x₀ x₁).2.role = .Resetting) := by
  unfold phase4_swap; split_ifs
  · exact ⟨h₁, h₀⟩
  · exact ⟨h₀, h₁⟩

private theorem phase4_decide_role_ok
    {b₀ b₁ : AgentState n} {x₀ x₁ : Opinion}
    (h₀ : b₀.role = .Settled ∨ b₀.role = .Resetting)
    (h₁ : b₁.role = .Settled ∨ b₁.role = .Resetting) :
    ((phase4_decide n b₀ b₁ x₀ x₁).1.role = .Settled ∨
     (phase4_decide n b₀ b₁ x₀ x₁).1.role = .Resetting) ∧
    ((phase4_decide n b₀ b₁ x₀ x₁).2.role = .Settled ∨
     (phase4_decide n b₀ b₁ x₀ x₁).2.role = .Resetting) := by
  simp only [phase4_decide]; split_ifs <;> simp_all

private theorem phase4_propagate_role_ok
    {b₀ b₁ : AgentState n} {Rmax : ℕ}
    (h₀ : b₀.role = .Settled ∨ b₀.role = .Resetting)
    (h₁ : b₁.role = .Settled ∨ b₁.role = .Resetting) :
    ((phase4_propagate n Rmax b₀ b₁).1.role = .Settled ∨
     (phase4_propagate n Rmax b₀ b₁).1.role = .Resetting) ∧
    ((phase4_propagate n Rmax b₀ b₁).2.role = .Settled ∨
     (phase4_propagate n Rmax b₀ b₁).2.role = .Resetting) := by
  simp only [phase4_propagate]; split_ifs <;> simp_all

private theorem role_settled_or_resetting_not_unsettled
    {s : AgentState n} (h : s.role = .Settled ∨ s.role = .Resetting) :
    s.role ≠ .Unsettled := by
  rcases h with hs | hs <;> rw [hs] <;> decide

theorem transitionPEM_phase4_not_unsettled_of_both_settled_old
    {n Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (ha : a.1.role = .Settled ∧ a.2.role = .Settled) :
    (transitionPEM_phase4 n Rmax a x₀ x₁).1.role ≠ .Unsettled ∧
    (transitionPEM_phase4 n Rmax a x₀ x₁).2.role ≠ .Unsettled := by
  exact transitionPEM_phase4_not_unsettled_of_both_settled ha.1 ha.2

/-- The full P_EM transition function (Algorithm 1).
    Now defined as prePhase4 composed with phase4. -/
def transitionPEM (n : ℕ) (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) :
    ((AgentState n × Opinion) × (AgentState n × Opinion)) →
    (AgentState n × AgentState n) :=
  fun ⟨⟨s₀, x₀⟩, ⟨s₁, x₁⟩⟩ =>
    transitionPEM_phase4 n Rmax
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁) x₀ x₁

@[simp] theorem transitionPEM_eq {n : ℕ} {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} :
    transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁)) =
    transitionPEM_phase4 n Rmax
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁) x₀ x₁ := rfl

/-- The output function for P_EM. -/
def outputPEM (n : ℕ) : AgentState n × Opinion → Output :=
  fun ⟨s, _⟩ => agentOutput s

/-- The protocol P_EM as a Protocol instance, parameterized by the ranking
    subprotocol and constants. -/
def protocolPEM (n : ℕ) (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) :
    Protocol (AgentState n) Opinion Output where
  δ := transitionPEM n trank Rmax rankDelta
  π_out := outputPEM n

end SSEM

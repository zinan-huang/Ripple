/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P_EM on a finite, role-indexed state set (Kanaya et al. 2025, Theorem 4, state count)

Kanaya et al. (arXiv:2503.17652v1, §5.2) count the states of `P_EM` as the sum over the roles
of Optimal-Silent-SSR (Burman et al.) of the variables each role uses, times the `O(1)` values of
`answer` and `timer`. The Lean state `AgentState n` is a flat record with five `ℕ` counters, so
it is infinite. This file gives the finite count.

* `PEMFinState n T E R D` is a finite sum type with one summand per role (Settled agents of
  non-median rank, the Settled agent of median rank `⌈n/2⌉`, Unsettled, Resetting with
  `resetcount ≥ 1`, Resetting with `resetcount = 0`), each holding only the fields that role
  reads. `card_PEMFinState_le`: its cardinality is at most `24 n + 24 (T+1) + 8 (E+1) + 8 R +
  8 (D+1)`.
* `protocolPEMFin` is the protocol on `PEMFinState` that encodes the flat transition:
  decode both states, run `transitionPEM`, encode the results.
* `pemSimulation`: on the flat states whose counters lie in their ranges (`GoodPEM`), the
  encoding commutes with the transition and the output. The proof shows that the transition
  never reads a field that the role of its owner does not use (`relPEM`, preserved by the
  transition, `transitionPEM_relPEM`). This needs `1 ≤ Rmax`.
* `StateSimulation.solvesSilentSSEM`: a protocol simulated in this sense inherits silent
  self-stabilizing exact majority. Hence `P_EM_fin_solves_silent_SSEM_linear`, and the state
  bound `P_EM_fin_card_le` (`≤ 216 n + 712` at the parameters of the Lean instance,
  `trank = Rmax = Emax = Dmax = n`).

The timer is kept only at the median rank: every agent that becomes Settled at the median rank
has its timer set to `7 (trank + 4)` (Algorithm 1, lines 5–6), so the timer of any other agent
is never read. With the paper's `trank = O(1)` the count is the paper's; with the Lean instance
`trank = n` it is still `O(n)` because the timer is stored only at one rank.
-/

import Ripple.PopulationProtocol.SSEM.Convergence.SilentPEM
import Ripple.PopulationProtocol.SSEM.Protocol.Correctness

namespace Ripple.PopulationProtocol.SSEM

/-! ### Simulation of one protocol by another, and transport of silent SSEM -/

section Transport

variable {Q Q' : Type*} {n : ℕ}

/-- `P'` simulates `P` on the states satisfying `Good`: `Good` is closed under the transition,
every state of `P'` decodes to a good state of `P`, and on good states the encoding commutes
with the transition and preserves the output. -/
structure StateSimulation (P : Protocol Q Opinion Output) (P' : Protocol Q' Opinion Output) where
  Good : Q → Prop
  enc : Q → Q'
  emb : Q' → Q
  good_emb : ∀ q, Good (emb q)
  enc_emb : ∀ q, enc (emb q) = q
  good_δ : ∀ a b x y, Good a → Good b →
    Good (P.δ ((a, x), (b, y))).1 ∧ Good (P.δ ((a, x), (b, y))).2
  enc_δ : ∀ a b x y, Good a → Good b →
    P'.δ ((enc a, x), (enc b, y)) =
      (enc (P.δ ((a, x), (b, y))).1, enc (P.δ ((a, x), (b, y))).2)
  out : ∀ a x, Good a → P'.π_out (enc a, x) = P.π_out (a, x)

namespace StateSimulation

variable {P : Protocol Q Opinion Output} {P' : Protocol Q' Opinion Output}
  (S : StateSimulation P P')

include S

/-- Encode a configuration agentwise (inputs unchanged). -/
def encC (C : Config Q Opinion n) : Config Q' Opinion n := fun v => (S.enc (C v).1, (C v).2)

/-- Decode a configuration agentwise. -/
def embC (D : Config Q' Opinion n) : Config Q Opinion n := fun v => (S.emb (D v).1, (D v).2)

/-- Every agent of `C` is in a good state. -/
def GoodC (C : Config Q Opinion n) : Prop := ∀ v, S.Good (C v).1

theorem encC_embC (D : Config Q' Opinion n) : S.encC (S.embC D) = D := by
  funext v
  simp [encC, embC, S.enc_emb]

theorem goodC_embC (D : Config Q' Opinion n) : S.GoodC (S.embC D) := fun v => S.good_emb _

theorem goodC_step {C : Config Q Opinion n} (hC : S.GoodC C) (u v : Fin n) :
    S.GoodC (C.step P u v) := by
  intro w
  have h := S.good_δ (C u).1 (C v).1 (C u).2 (C v).2 (hC u) (hC v)
  simp only [Prod.mk.eta] at h
  by_cases huv : u = v
  · simp only [Config.step, huv, if_true]; exact hC w
  · have hvu : ¬v = u := fun e => huv e.symm
    by_cases hwu : w = u
    · subst hwu; simpa [Config.step, huv] using h.1
    · by_cases hwv : w = v
      · subst hwv; simpa [Config.step, huv, hvu] using h.2
      · simpa [Config.step, huv, hwu, hwv] using hC w

theorem encC_step {C : Config Q Opinion n} (hC : S.GoodC C) (u v : Fin n) :
    S.encC (C.step P u v) = (S.encC C).step P' u v := by
  have h := S.enc_δ (C u).1 (C v).1 (C u).2 (C v).2 (hC u) (hC v)
  simp only [Prod.mk.eta] at h
  funext w
  by_cases huv : u = v
  · simp [Config.step, huv]
  · have hvu : ¬v = u := fun e => huv e.symm
    by_cases hwu : w = u
    · subst hwu; simp [Config.step, huv, encC, h]
    · by_cases hwv : w = v
      · subst hwv; simp [Config.step, huv, hvu, encC, h]
      · simp [Config.step, huv, hwu, hwv, encC]

theorem goodC_execution {C : Config Q Opinion n} (hC : S.GoodC C) (γ : DetScheduler n) :
    ∀ t, S.GoodC (execution P C γ t)
  | 0 => hC
  | t + 1 => S.goodC_step (goodC_execution hC γ t) _ _

theorem encC_execution {C : Config Q Opinion n} (hC : S.GoodC C) (γ : DetScheduler n) :
    ∀ t, S.encC (execution P C γ t) = execution P' (S.encC C) γ t
  | 0 => rfl
  | t + 1 => by
      simp only [execution]
      rw [S.encC_step (S.goodC_execution hC γ t), encC_execution hC γ t]

theorem outputOf_encC {C : Config Q Opinion n} (hC : S.GoodC C) (w : Fin n) :
    (S.encC C).outputOf P' w = C.outputOf P w := by
  simp only [Config.outputOf, encC]
  rw [S.out _ _ (hC w)]

theorem agentsWithInput_encC (C : Config Q Opinion n) (x : Opinion) :
    (S.encC C).agentsWithInput x = C.agentsWithInput x := rfl

theorem isOutputStable_encC {C : Config Q Opinion n} (hC : S.GoodC C)
    (h : C.isOutputStable P) : (S.encC C).isOutputStable P' := by
  intro γ t w
  rw [← S.encC_execution hC γ t, S.outputOf_encC hC, S.outputOf_encC (S.goodC_execution hC γ t)]
  exact h γ t w

theorem exactMajoritySafe_encC {C : Config Q Opinion n} (hC : S.GoodC C)
    (h : ExactMajoritySafe P C Opinion.A Opinion.B Output.A Output.B Output.T) :
    ExactMajoritySafe P' (S.encC C) Opinion.A Opinion.B Output.A Output.B Output.T := by
  unfold ExactMajoritySafe at h ⊢
  simp only [S.agentsWithInput_encC, Config.allOutput, S.outputOf_encC hC] at h ⊢
  exact h

theorem isSilent_encC [DecidableEq Q] [DecidableEq Q'] {C : Config Q Opinion n}
    (hC : S.GoodC C) (h : C.isSilent P) : (S.encC C).isSilent P' := by
  intro u v
  rw [← S.encC_step hC, h u v]

/-- A simulated protocol inherits self-stabilizing exact majority. -/
theorem solvesSSEM [DecidableEq Q] [DecidableEq Q'] (h : SolvesSSEM P n) : SolvesSSEM P' n := by
  intro D
  obtain ⟨γ, t, hst, hmaj⟩ := h (S.embC D)
  have hG := S.goodC_execution (S.goodC_embC D) γ t
  have hE : execution P' D γ t = S.encC (execution P (S.embC D) γ t) := by
    rw [S.encC_execution (S.goodC_embC D), S.encC_embC]
  refine ⟨γ, t, ?_⟩
  show (execution P' D γ t).isOutputStable P' ∧ _
  rw [hE]
  exact ⟨S.isOutputStable_encC hG hst, S.exactMajoritySafe_encC hG hmaj⟩

/-- A simulated protocol inherits silence. -/
theorem silentProtocol [DecidableEq Q] [DecidableEq Q'] (h : SilentProtocol P n) :
    SilentProtocol P' n := by
  intro D
  obtain ⟨γ, t, hsil⟩ := h (S.embC D)
  refine ⟨γ, t, ?_⟩
  rw [← S.encC_embC D, ← S.encC_execution (S.goodC_embC D)]
  exact S.isSilent_encC (S.goodC_execution (S.goodC_embC D) γ t) hsil

/-- A simulated protocol inherits silent self-stabilizing exact majority. -/
theorem solvesSilentSSEM [DecidableEq Q] [DecidableEq Q'] (h : SolvesSilentSSEM P n) :
    SolvesSilentSSEM P' n :=
  ⟨S.solvesSSEM h.1, S.silentProtocol h.2⟩

end StateSimulation

end Transport

/-! ### The role-indexed finite state set -/

section FinState

variable {n : ℕ}

/-- The median rank `⌈n/2⌉` as an element of `Fin n` (0-indexed: `⌈n/2⌉ - 1`). -/
def medianRank (hn : 0 < n) : Fin n := ⟨ceilHalf n - 1, by unfold ceilHalf; omega⟩

/-- Clamp a natural number into `Fin (k + 1)`. -/
def finClamp (k x : ℕ) : Fin (k + 1) := ⟨min x k, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **Role-indexed state of P_EM.** One summand per role of Optimal-Silent-SSR, holding the
fields that role uses (`T` = timer range `7 (trank + 4)`, `E` = `Emax`, `R` = `Rmax`,
`D` = `Dmax`):
1. Settled, rank not the median: rank, children (`≤ 2`), leader, answer;
2. Settled at the median rank: children, leader, answer, timer (`≤ T`);
3. Unsettled: leader, answer, errorcount (`≤ E`);
4. Resetting, `resetcount = r + 1 ∈ [1, R]`: leader, answer, `r`;
5. Resetting, `resetcount = 0` (dormant): leader, answer, delaytimer (`≤ D`). -/
abbrev PEMFinState (n T E R D : ℕ) :=
  ({r : Fin n // r.val + 1 ≠ ceilHalf n} × Fin 3 × Leader × Answer) ⊕
  (Fin 3 × Leader × Answer × Fin (T + 1)) ⊕
  (Leader × Answer × Fin (E + 1)) ⊕
  (Leader × Answer × Fin R) ⊕
  (Leader × Answer × Fin (D + 1))

/-- Equality on `PEMFinState` is decidable (classically; only used as a parameter of the
silence predicates). -/
noncomputable instance (n T E R D : ℕ) : DecidableEq (PEMFinState n T E R D) := Classical.decEq _

theorem card_leader : Fintype.card Leader = 2 := by decide
theorem card_answer : Fintype.card Answer = 4 := by decide

/-- **State count.** `|PEMFinState| ≤ 24 n + 24 (T+1) + 8 (E+1) + 8 R + 8 (D+1)`. -/
theorem card_PEMFinState_le (n T E R D : ℕ) :
    Fintype.card (PEMFinState n T E R D) ≤
      24 * n + 24 * (T + 1) + 8 * (E + 1) + 8 * R + 8 * (D + 1) := by
  have hsub : Fintype.card {r : Fin n // r.val + 1 ≠ ceilHalf n} ≤ n := by
    simpa using Fintype.card_subtype_le (fun r : Fin n => r.val + 1 ≠ ceilHalf n)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_leader, card_answer]
  nlinarith [hsub]

/-- Encode a flat state into the role-indexed state (counters clamped to their ranges; on
`GoodPEM` states the clamps are the identity). -/
def encPEM (n T E R D : ℕ) (s : AgentState n) : PEMFinState n T E R D :=
  match s.role with
  | .Settled =>
    if h : s.rank.val + 1 = ceilHalf n then
      Sum.inr (Sum.inl (finClamp 2 s.children, s.leader, s.answer, finClamp T s.timer))
    else Sum.inl (⟨s.rank, h⟩, finClamp 2 s.children, s.leader, s.answer)
  | .Unsettled => Sum.inr (Sum.inr (Sum.inl (s.leader, s.answer, finClamp E s.errorcount)))
  | .Resetting =>
    if s.resetcount = 0 then
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (s.leader, s.answer, finClamp D s.delaytimer))))
    else if h' : s.resetcount - 1 < R then
      Sum.inr (Sum.inr (Sum.inr (Sum.inl (s.leader, s.answer, ⟨s.resetcount - 1, h'⟩))))
    else
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (s.leader, s.answer, finClamp D 0))))

/-- Decode a role-indexed state to its canonical flat state (unused fields set to `0`, rank of
a non-Settled agent set to `0`). -/
def embPEM {T E R D : ℕ} (hn : 0 < n) : PEMFinState n T E R D → AgentState n
  | Sum.inl (r, c, l, a) => ⟨.Settled, r.1, l, 0, a, 0, c.val, 0, 0⟩
  | Sum.inr (Sum.inl (c, l, a, t)) => ⟨.Settled, medianRank hn, l, 0, a, t.val, c.val, 0, 0⟩
  | Sum.inr (Sum.inr (Sum.inl (l, a, e))) => ⟨.Unsettled, ⟨0, hn⟩, l, 0, a, 0, 0, e.val, 0⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (l, a, r)))) =>
      ⟨.Resetting, ⟨0, hn⟩, l, r.val + 1, a, 0, 0, 0, 0⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (l, a, d)))) =>
      ⟨.Resetting, ⟨0, hn⟩, l, 0, a, 0, 0, 0, d.val⟩

theorem medianRank_spec (hn : 0 < n) : (medianRank hn).val + 1 = ceilHalf n := by
  simp only [medianRank]; unfold ceilHalf; omega

theorem encPEM_embPEM {T E R D : ℕ} (hn : 0 < n) (q : PEMFinState n T E R D) :
    encPEM n T E R D (embPEM hn q) = q := by
  rcases q with ⟨⟨r, hr⟩, c, l, a⟩ | ⟨c, l, a, t⟩ | ⟨l, a, e⟩ | ⟨l, a, r⟩ | ⟨l, a, d⟩
  · simp only [embPEM, encPEM, hr, dite_false]
    congr 1
    ext <;> simp [finClamp] <;> omega
  · simp only [embPEM, encPEM, medianRank_spec hn, dite_true]
    congr 2
    ext <;> simp [finClamp] <;> omega
  · simp only [embPEM, encPEM]
    congr 3
    ext <;> simp [finClamp] <;> omega
  · simp only [embPEM, encPEM, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, r.isLt,
      dite_true]
  · simp only [embPEM, encPEM, if_true]
    congr 4
    ext <;> simp [finClamp] <;> omega

/-- Flat states whose counters lie in their ranges. -/
def GoodPEM (T E R D : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ T ∧ s.resetcount ≤ R ∧ s.errorcount ≤ E ∧ s.delaytimer ≤ D ∧ s.children ≤ 2

theorem goodPEM_embPEM {T E R D : ℕ} (hn : 0 < n) (q : PEMFinState n T E R D) :
    GoodPEM T E R D (embPEM hn q) := by
  rcases q with ⟨⟨r, hr⟩, c, l, a⟩ | ⟨c, l, a, t⟩ | ⟨l, a, e⟩ | ⟨l, a, r⟩ | ⟨l, a, d⟩ <;>
    simp only [embPEM, GoodPEM] <;> omega

/-- **Agreement on the fields the role reads.** Two flat states are related if they have the
same role, leader and answer, and agree on: rank and children (Settled), the timer (Settled at
the median rank), errorcount (Unsettled), resetcount (Resetting), delaytimer (Resetting with
`resetcount = 0`). -/
def relPEM (s t : AgentState n) : Prop :=
  s.role = t.role ∧ s.leader = t.leader ∧ s.answer = t.answer ∧
  (s.role = .Settled → s.rank = t.rank ∧ s.children = t.children ∧
    (s.rank.val + 1 = ceilHalf n → s.timer = t.timer)) ∧
  (s.role = .Unsettled → s.errorcount = t.errorcount) ∧
  (s.role = .Resetting → s.resetcount = t.resetcount ∧
    (s.resetcount = 0 → s.delaytimer = t.delaytimer))

/-- `relPEM` without the timer clause (used between the ranking step and the timer update). -/
def relNT (s t : AgentState n) : Prop :=
  s.role = t.role ∧ s.leader = t.leader ∧ s.answer = t.answer ∧
  (s.role = .Settled → s.rank = t.rank ∧ s.children = t.children) ∧
  (s.role = .Unsettled → s.errorcount = t.errorcount) ∧
  (s.role = .Resetting → s.resetcount = t.resetcount ∧
    (s.resetcount = 0 → s.delaytimer = t.delaytimer))

theorem relPEM_embPEM_encPEM {T E R D : ℕ} (hn : 0 < n) {s : AgentState n}
    (hs : GoodPEM T E R D s) : relPEM s (embPEM hn (encPEM n T E R D s)) := by
  rcases s with ⟨role, rank, leader, rc, answer, timer, children, ec, dt⟩
  obtain ⟨ht, hr, he, hd, hc⟩ := hs
  simp only at ht hr he hd hc
  cases role
  · -- Resetting
    by_cases h0 : rc = 0
    · have e1 : min dt D = dt := by omega
      simp [relPEM, encPEM, embPEM, h0, finClamp, e1]
    · have h1 : rc - 1 < R := by omega
      have e2 : rc - 1 + 1 = rc := by omega
      simp [relPEM, encPEM, embPEM, h0, h1, e2]
  · -- Settled
    have e1 : min children 2 = children := by omega
    have e2 : min timer T = timer := by omega
    by_cases hm : rank.val + 1 = ceilHalf n
    · have e3 : medianRank hn = rank := by
        ext; simp only [medianRank]; unfold ceilHalf at hm ⊢; omega
      simp [relPEM, encPEM, embPEM, hm, finClamp, e1, e2, e3]
    · simp [relPEM, encPEM, embPEM, hm, finClamp, e1]
  · -- Unsettled
    have e1 : min ec E = ec := by omega
    simp [relPEM, encPEM, embPEM, finClamp, e1]

theorem encPEM_eq_of_relPEM {T E R D : ℕ} {s t : AgentState n}
    (hs : GoodPEM T E R D s) (ht : GoodPEM T E R D t) (h : relPEM s t) :
    encPEM n T E R D s = encPEM n T E R D t := by
  rcases s with ⟨role, rank, leader, rc, answer, timer, children, ec, dt⟩
  rcases t with ⟨role', rank', leader', rc', answer', timer', children', ec', dt'⟩
  obtain ⟨hrole, hl, ha, hS, hU, hR⟩ := h
  simp only at hrole hl ha hS hU hR
  subst hrole hl ha
  cases role
  · obtain ⟨hrc, hdt⟩ := hR rfl
    subst hrc
    by_cases h0 : rc = 0
    · simp [encPEM, h0, hdt h0]
    · simp [encPEM, h0]
  · obtain ⟨hk, hc, htm⟩ := hS rfl
    subst hk hc
    by_cases hm : rank.val + 1 = ceilHalf n
    · simp [encPEM, hm, htm hm]
    · simp [encPEM, hm]
  · simp [encPEM, hU rfl]

end FinState

/-! ### The transition reads only the fields of the role (brute-force case analysis) -/

section Respect

variable {n : ℕ} {Rmax Emax Dmax : ℕ} {hn : 0 < n}

/-! Pieces of `propagateReset`, named so that each can be treated separately. -/

/-- Phase 1 of PROPAGATE-RESET: recruitment. -/
def prRecruit (Dmax : ℕ) (a b : AgentState n) : AgentState n × AgentState n :=
  if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
    (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
  else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
    ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
  else (a, b)

/-- Phase 2 of PROPAGATE-RESET: resetcount synchronisation. -/
def prSync (a b : AgentState n) : AgentState n × AgentState n :=
  if a.role = .Resetting ∧ b.role = .Resetting then
    ({ a with resetcount := max (a.resetcount - 1) (b.resetcount - 1) },
     { b with resetcount := max (a.resetcount - 1) (b.resetcount - 1) })
  else (a, b)

/-- Leader deduplication after PROPAGATE-RESET. -/
def prDedup (p : AgentState n × AgentState n) : AgentState n × AgentState n :=
  (p.1, if p.1.leader = .L ∧ p.2.leader = .L ∧ p.1.role = .Resetting ∧ p.2.role = .Resetting
    then { p.2 with leader := .F } else p.2)

theorem propagateReset_eq (a b : AgentState n) :
    propagateReset Emax Dmax hn a b =
      (processAgent Emax Dmax hn (prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).1
          (prRecruit Dmax a b).1.resetcount
          ((prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).2.role == .Resetting),
        processAgent Emax Dmax hn (prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).2
          (prRecruit Dmax a b).2.resetcount
          ((prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).1.role == .Resetting)) := by
  simp only [propagateReset, prRecruit, prSync]

theorem rankDeltaOSSR_eq_of_resetting {a b : AgentState n}
    (h : a.role = .Resetting ∨ b.role = .Resetting) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) = prDedup (propagateReset Emax Dmax hn a b) := by
  simp only [rankDeltaOSSR]
  rw [if_pos h]
  simp only [prDedup]

theorem prRecruit_relNT {a b a' b' : AgentState n} (ha : relNT a a') (hb : relNT b b') :
    relNT (prRecruit Dmax a b).1 (prRecruit Dmax a' b').1 ∧
      relNT (prRecruit Dmax a b).2 (prRecruit Dmax a' b').2 := by
  rcases a with ⟨ra, ka, la, ca, aa, ta, cha, ea, da⟩
  rcases a' with ⟨ra', ka', la', ca', aa', ta', cha', ea', da'⟩
  rcases b with ⟨rb, kb, lb, cb, ab, tb, chb, eb, db⟩
  rcases b' with ⟨rb', kb', lb', cb', ab', tb', chb', eb', db'⟩
  obtain ⟨h1, h2, h3, hS, hU, hRs⟩ := ha
  obtain ⟨g1, g2, g3, gS, gU, gRs⟩ := hb
  simp only at h1 h2 h3 hS hU hRs g1 g2 g3 gS gU gRs
  subst h1 h2 h3 g1 g2 g3
  cases ra <;> cases rb <;> simp only [reduceCtorEq, forall_const, IsEmpty.forall_iff,
    false_implies] at hS hU hRs gS gU gRs <;> simp only [prRecruit] <;> split_ifs <;>
    simp_all [relNT]

theorem processAgent_relNT {s s' : AgentState n} {o o' : ℕ} {pr : Bool} (h : relNT s s')
    (ho : s.role = .Resetting → o = o') :
    relNT (processAgent Emax Dmax hn s o pr) (processAgent Emax Dmax hn s' o' pr) := by
  by_cases hr : s.role = .Resetting
  · have ho := ho hr
    subst ho
    rcases s with ⟨r, k, l, c, a, t, ch, e, d⟩
    rcases s' with ⟨r', k', l', c', a', t', ch', e', d'⟩
    obtain ⟨h1, h2, h3, -, -, hRs⟩ := h
    simp only at h1 h2 h3 hRs hr
    subst h1 h2 h3 hr
    obtain ⟨hc, hd⟩ := hRs rfl
    subst hc
    by_cases hc0 : c = 0
    · have hd := hd hc0
      subst hd hc0
      cases l <;> cases pr <;> simp only [processAgent, resetOSSR] <;> split_ifs <;>
        simp_all [relNT]
    · rw [processAgent_rc_ne_zero hc0, processAgent_rc_ne_zero hc0]
      exact ⟨rfl, rfl, rfl, fun h => by simp at h, fun h => by simp at h,
        fun _ => ⟨rfl, fun h => absurd h hc0⟩⟩
  · have hr' : s'.role ≠ .Resetting := h.1 ▸ hr
    rw [processAgent_not_resetting hr, processAgent_not_resetting hr']
    exact h

theorem prDedup_relNT {p p' : AgentState n × AgentState n} (h₀ : relNT p.1 p'.1)
    (h₁ : relNT p.2 p'.2) :
    relNT (prDedup p).1 (prDedup p').1 ∧ relNT (prDedup p).2 (prDedup p').2 := by
  refine ⟨h₀, ?_⟩
  obtain ⟨f1, f2, -⟩ := h₀
  obtain ⟨g1, g2, g3, gS, gU, gR⟩ := h₁
  have e : (p.1.leader = .L ∧ p.2.leader = .L ∧ p.1.role = .Resetting ∧ p.2.role = .Resetting) ↔
      (p'.1.leader = .L ∧ p'.2.leader = .L ∧ p'.1.role = .Resetting ∧
        p'.2.role = .Resetting) := by rw [f1, f2, g1, g2]
  simp only [prDedup]
  by_cases hc : p.1.leader = .L ∧ p.2.leader = .L ∧ p.1.role = .Resetting ∧ p.2.role = .Resetting
  · rw [if_pos hc, if_pos (e.mp hc)]
    exact ⟨g1, rfl, g3, gS, gU, gR⟩
  · rw [if_neg hc, if_neg (fun h => hc (e.mpr h))]
    exact ⟨g1, g2, g3, gS, gU, gR⟩

/-- Synchronisation followed by `processAgent`, for an agent whose partner is also
Resetting: the stale delaytimer of an agent whose resetcount drops to 0 is overwritten
(`oldRc > 0`), so the result is related although the intermediate state need not be. -/
theorem processAgent_sync_relNT {s s' : AgentState n} {m m' : ℕ} {pr pr' : Bool}
    (h : relNT s s') (hr : s.role = .Resetting) (hm : m = m') (hpr : pr = pr') :
    relNT (processAgent Emax Dmax hn { s with resetcount := m } s.resetcount pr)
      (processAgent Emax Dmax hn { s' with resetcount := m' } s'.resetcount pr') := by
  subst hm hpr
  rcases s with ⟨r, k, l, c, a, t, ch, e, d⟩
  rcases s' with ⟨r', k', l', c', a', t', ch', e', d'⟩
  obtain ⟨h1, h2, h3, -, -, hRs⟩ := h
  simp only at h1 h2 h3 hRs hr
  subst h1 h2 h3 hr
  obtain ⟨hc, hd⟩ := hRs rfl
  subst hc
  by_cases hc0 : c = 0
  · obtain rfl := hd hc0
    subst hc0
    cases l <;> cases pr <;> simp only [processAgent, resetOSSR] <;> split_ifs <;>
      simp_all [relNT]
  · have hc0' : 0 < c := Nat.pos_of_ne_zero hc0
    cases l <;> cases pr <;> simp only [processAgent, resetOSSR, hc0'] <;> split_ifs <;>
      simp_all [relNT]

theorem propagateReset_relNT {a b a' b' : AgentState n} (ha : relNT a a') (hb : relNT b b') :
    relNT (propagateReset Emax Dmax hn a b).1 (propagateReset Emax Dmax hn a' b').1 ∧
      relNT (propagateReset Emax Dmax hn a b).2 (propagateReset Emax Dmax hn a' b').2 := by
  rw [propagateReset_eq, propagateReset_eq]
  have h1 := prRecruit_relNT (Dmax := Dmax) ha hb
  generalize prRecruit Dmax a b = p at h1 ⊢
  generalize prRecruit Dmax a' b' = p' at h1 ⊢
  rcases p with ⟨x, y⟩
  rcases p' with ⟨x', y'⟩
  obtain ⟨hx, hy⟩ := h1
  simp only at hx hy ⊢
  by_cases hboth : x.role = .Resetting ∧ y.role = .Resetting
  · have hboth' : x'.role = .Resetting ∧ y'.role = .Resetting := by
      rw [← hx.1, ← hy.1]; exact hboth
    have hxc : x.resetcount = x'.resetcount := (hx.2.2.2.2.2 hboth.1).1
    have hyc : y.resetcount = y'.resetcount := (hy.2.2.2.2.2 hboth.2).1
    rw [prSync, prSync, if_pos hboth, if_pos hboth']
    dsimp only
    have hm : max (x.resetcount - 1) (y.resetcount - 1) =
        max (x'.resetcount - 1) (y'.resetcount - 1) := by rw [hxc, hyc]
    exact ⟨processAgent_sync_relNT hx hboth.1 hm (by rw [hy.1]),
      processAgent_sync_relNT hy hboth.2 hm (by rw [hx.1])⟩
  · have hboth' : ¬(x'.role = .Resetting ∧ y'.role = .Resetting) := by
      rw [← hx.1, ← hy.1]; exact hboth
    simp only [prSync, hboth, hboth', if_false]
    rw [← hx.1, ← hy.1]
    exact ⟨processAgent_relNT hx (fun hr => (hx.2.2.2.2.2 hr).1),
      processAgent_relNT hy (fun hr => (hy.2.2.2.2.2 hr).1)⟩

theorem rankDeltaOSSR_relNT (hR : 1 ≤ Rmax) {a b a' b' : AgentState n}
    (ha : relPEM a a') (hb : relPEM b b') :
    relNT (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1
        (rankDeltaOSSR Rmax Emax Dmax hn (a', b')).1 ∧
      relNT (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2
        (rankDeltaOSSR Rmax Emax Dmax hn (a', b')).2 := by
  have hNTa : relNT a a' := ⟨ha.1, ha.2.1, ha.2.2.1, fun h => ⟨(ha.2.2.2.1 h).1,
    (ha.2.2.2.1 h).2.1⟩, ha.2.2.2.2.1, ha.2.2.2.2.2⟩
  have hNTb : relNT b b' := ⟨hb.1, hb.2.1, hb.2.2.1, fun h => ⟨(hb.2.2.2.1 h).1,
    (hb.2.2.2.1 h).2.1⟩, hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  by_cases hres : a.role = .Resetting ∨ b.role = .Resetting
  · have hres' : a'.role = .Resetting ∨ b'.role = .Resetting := by rw [← ha.1, ← hb.1]; exact hres
    rw [rankDeltaOSSR_eq_of_resetting hres, rankDeltaOSSR_eq_of_resetting hres']
    have h := propagateReset_relNT (Emax := Emax) (Dmax := Dmax) (hn := hn) hNTa hNTb
    exact prDedup_relNT h.1 h.2
  · rcases a with ⟨ra, ka, la, ca, aa, ta, cha, ea, da⟩
    rcases a' with ⟨ra', ka', la', ca', aa', ta', cha', ea', da'⟩
    rcases b with ⟨rb, kb, lb, cb, ab, tb, chb, eb, db⟩
    rcases b' with ⟨rb', kb', lb', cb', ab', tb', chb', eb', db'⟩
    obtain ⟨h1, h2, h3, hS, hU, hRs⟩ := hNTa
    obtain ⟨g1, g2, g3, gS, gU, gRs⟩ := hNTb
    simp only at h1 h2 h3 hS hU hRs g1 g2 g3 gS gU gRs hres
    subst h1 h2 h3 g1 g2 g3
    clear ha hb
    cases ra <;> cases rb <;> simp only [reduceCtorEq, true_or, or_true, not_true_eq_false] at hres
    all_goals (try (obtain ⟨rfl, rfl⟩ := hS rfl))
    all_goals (try (obtain ⟨rfl, rfl⟩ := gS rfl))
    all_goals (try (obtain rfl := hU rfl))
    all_goals (try (obtain rfl := gU rfl))
    all_goals clear hS hU hRs gS gU gRs hres
    all_goals
      simp only [rankDeltaOSSR, reduceCtorEq, false_or, or_false, false_and, and_false,
        if_false, true_and, and_true]
      (repeat' ((try dsimp only); split_ifs)) <;> simp_all [relNT] <;> (try omega)
    all_goals (try contradiction)

theorem resetOSSR_timer' {Emax : ℕ} {hn : 0 < n} (s : AgentState n) :
    (resetOSSR Emax hn s).timer = s.timer := by
  unfold resetOSSR
  cases s.leader <;> rfl

theorem processAgent_timer {Emax Dmax : ℕ} {hn : 0 < n}
    (s : AgentState n) (oldRc : ℕ) (pr : Bool) :
    (processAgent Emax Dmax hn s oldRc pr).timer = s.timer := by
  unfold processAgent
  by_cases h1 : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos h1]
    by_cases h2 : 0 < oldRc
    · rw [if_pos h2]
      simp only []
      by_cases h3 : (Dmax = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_timer']
      · rw [if_neg h3]
    · rw [if_neg h2]
      simp only []
      by_cases h3 : (s.delaytimer - 1 = 0 ∨ (!pr) = true)
      · rw [if_pos h3, resetOSSR_timer']
      · rw [if_neg h3]
  · rw [if_neg h1]

theorem propagateReset_timer {Emax Dmax : ℕ} {hn : 0 < n} (a b : AgentState n) :
    (propagateReset Emax Dmax hn a b).1.timer = a.timer ∧
    (propagateReset Emax Dmax hn a b).2.timer = b.timer := by
  unfold propagateReset
  constructor <;>
    simp only [processAgent_timer] <;>
    split_ifs <;> rfl

theorem rankDeltaOSSR_timer (a b : AgentState n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1.timer = a.timer ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2.timer = b.timer := by
  unfold rankDeltaOSSR
  dsimp only []
  split_ifs <;>
    simp_all [propagateReset_timer]

/-- With `2 ≤ Dmax`, an agent that is Settled before PROPAGATE-RESET and Settled after it is
unchanged (if it is recruited into Resetting, it cannot wake in the same interaction). -/
theorem propagateReset_settled (hD : 2 ≤ Dmax) (a b : AgentState n) :
    ((propagateReset Emax Dmax hn a b).1.role = .Settled → a.role = .Settled →
        (propagateReset Emax Dmax hn a b).1.rank = a.rank) ∧
      ((propagateReset Emax Dmax hn a b).2.role = .Settled → b.role = .Settled →
        (propagateReset Emax Dmax hn a b).2.rank = b.rank) := by
  rcases a with ⟨ra, ka, la, ca, aa, ta, cha, ea, da⟩
  rcases b with ⟨rb, kb, lb, cb, ab, tb, chb, eb, db⟩
  rw [propagateReset_eq]
  cases ra <;> cases rb <;> simp only [prRecruit, prSync] <;>
    (repeat' ((try dsimp only); split_ifs)) <;>
    (try simp_all [processAgent, resetOSSR]) <;>
    (repeat' ((try dsimp only); split_ifs)) <;> (try simp_all) <;> omega

/-- An agent Settled before and after the ranking step keeps its rank (needs `2 ≤ Dmax`). -/
theorem rankDeltaOSSR_rank (hD : 2 ≤ Dmax) (a b : AgentState n) :
    ((rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1.role = .Settled → a.role = .Settled →
        (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1.rank = a.rank) ∧
      ((rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2.role = .Settled → b.role = .Settled →
        (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2.rank = b.rank) := by
  by_cases hres : a.role = .Resetting ∨ b.role = .Resetting
  · rw [rankDeltaOSSR_eq_of_resetting hres]
    have h := propagateReset_settled (Emax := Emax) (hn := hn) hD a b
    simp only [prDedup]
    refine ⟨h.1, ?_⟩
    split_ifs with hc
    · intro h2; exact absurd h2 (by rw [hc.2.2.2]; decide)
    · exact h.2
  · rcases a with ⟨ra, ka, la, ca, aa, ta, cha, ea, da⟩
    rcases b with ⟨rb, kb, lb, cb, ab, tb, chb, eb, db⟩
    simp only at hres
    cases ra <;> cases rb <;> simp only [reduceCtorEq, true_or, or_true, not_true_eq_false] at hres
    all_goals
      simp only [rankDeltaOSSR, reduceCtorEq, false_or, or_false, false_and, and_false,
        if_false, true_and, and_true]
      (repeat' ((try dsimp only); split_ifs)) <;> simp_all <;> (try contradiction)

theorem relPEM_with_answer {s s' : AgentState n} (h : relPEM s s') (x : Answer) :
    relPEM { s with answer := x } { s' with answer := x } :=
  ⟨h.1, h.2.1, rfl, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Per-agent part of `transitionPEM_prePhase4`: clear the answer of a newly Resetting agent,
start the timer of an agent newly Settled at the median rank. -/
def preAgent (n trank : ℕ) (s r : AgentState n) : AgentState n :=
  let a := if r.role = .Resetting ∧ s.role ≠ .Resetting then { r with answer := .phi } else r
  if a.role = .Settled ∧ s.role ≠ .Settled ∧ a.rank.val + 1 = ceilHalf n then
    { a with timer := 7 * (trank + 4) } else a

/-- Answer epidemic among Resetting agents (Algorithm 1, lines 7–8). -/
def preEpi (a₀ a₁ : AgentState n) : AgentState n × AgentState n :=
  if a₀.role = .Resetting ∧ a₁.role = .Resetting then
    if a₀.answer = .phi ∧ a₁.answer ≠ .phi then ({ a₀ with answer := a₁.answer }, a₁)
    else if a₁.answer = .phi ∧ a₀.answer ≠ .phi then (a₀, { a₁ with answer := a₀.answer })
    else (a₀, a₁)
  else (a₀, a₁)

theorem prePhase4_eq {trank : ℕ} {rd : AgentState n × AgentState n → AgentState n × AgentState n}
    (s₀ s₁ : AgentState n) (x₀ x₁ : Opinion) :
    transitionPEM_prePhase4 n trank rd s₀ s₁ x₀ x₁ =
      preEpi (preAgent n trank s₀ (rd (s₀, s₁)).1) (preAgent n trank s₁ (rd (s₀, s₁)).2) := by
  unfold transitionPEM_prePhase4 preEpi preAgent
  rcases rd (s₀, s₁) with ⟨r₀, r₁⟩
  first | rfl | (split_ifs <;> rfl)

theorem preAgent_relPEM {trank : ℕ} {s s' r r' : AgentState n} (hs : relPEM s s')
    (hr : relNT r r') (ht : r.timer = s.timer) (ht' : r'.timer = s'.timer)
    (hk : r.role = .Settled → s.role = .Settled → r.rank = s.rank) :
    relPEM (preAgent n trank s r) (preAgent n trank s' r') := by
  rcases r with ⟨q, k, l, c, a, t, ch, e, d⟩
  rcases r' with ⟨q', k', l', c', a', t', ch', e', d'⟩
  rcases s with ⟨p, m, v, w, y, u, z, o, g⟩
  rcases s' with ⟨p', m', v', w', y', u', z', o', g'⟩
  obtain ⟨f1, f2, f3, fS, fU, fR⟩ := hr
  obtain ⟨i1, -, -, iS, -, -⟩ := hs
  simp only at f1 f2 f3 fS fU fR i1 iS ht ht' hk
  subst f1 f2 f3 i1 ht ht'
  cases q <;> cases p <;> simp only [preAgent, reduceCtorEq, ne_eq, not_false_eq_true,
    not_true_eq_false, and_true, and_false, true_and, false_and, if_true, if_false]
  · -- Resetting, was Resetting
    exact ⟨rfl, rfl, rfl, fun h => by simp at h, fun h => by simp at h, fR⟩
  · exact ⟨rfl, rfl, rfl, fun h => by simp at h, fun h => by simp at h, fR⟩
  · exact ⟨rfl, rfl, rfl, fun h => by simp at h, fun h => by simp at h, fR⟩
  · -- Settled, was Resetting: newly Settled
    obtain ⟨rfl, rfl⟩ := fS rfl
    split_ifs
    · exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, fun _ => rfl⟩, fun h => by simp at h, fun h => by simp at h⟩
    · exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, fun h => absurd h ‹_›⟩, fun h => by simp at h,
        fun h => by simp at h⟩
  · -- Settled, was Settled
    obtain ⟨rfl, rfl⟩ := fS rfl
    have hkm : k = m := hk rfl rfl
    subst hkm
    obtain ⟨rfl, -, htm⟩ := iS rfl
    exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, htm⟩, fun h => by simp at h, fun h => by simp at h⟩
  · -- Settled, was Unsettled: newly Settled
    obtain ⟨rfl, rfl⟩ := fS rfl
    split_ifs
    · exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, fun _ => rfl⟩, fun h => by simp at h, fun h => by simp at h⟩
    · exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, fun h => absurd h ‹_›⟩, fun h => by simp at h,
        fun h => by simp at h⟩
  · exact ⟨rfl, rfl, rfl, fun h => by simp at h, fU, fun h => by simp at h⟩
  · exact ⟨rfl, rfl, rfl, fun h => by simp at h, fU, fun h => by simp at h⟩
  · exact ⟨rfl, rfl, rfl, fun h => by simp at h, fU, fun h => by simp at h⟩

theorem preEpi_relPEM {a b a' b' : AgentState n} (ha : relPEM a a') (hb : relPEM b b') :
    relPEM (preEpi a b).1 (preEpi a' b').1 ∧ relPEM (preEpi a b).2 (preEpi a' b').2 := by
  have e1 := ha.1
  have e2 := hb.1
  have e3 := ha.2.2.1
  have e4 := hb.2.2.1
  unfold preEpi
  by_cases c1 : a.role = .Resetting ∧ b.role = .Resetting
  · have c1' : a'.role = .Resetting ∧ b'.role = .Resetting := by rw [← e1, ← e2]; exact c1
    rw [if_pos c1, if_pos c1']
    by_cases c2 : a.answer = .phi ∧ b.answer ≠ .phi
    · have c2' : a'.answer = .phi ∧ b'.answer ≠ .phi := by rw [← e3, ← e4]; exact c2
      rw [if_pos c2, if_pos c2']
      refine ⟨?_, hb⟩
      show relPEM { a with answer := b.answer } { a' with answer := b'.answer }
      rw [← e4]; exact relPEM_with_answer ha _
    · have c2' : ¬(a'.answer = .phi ∧ b'.answer ≠ .phi) := by rw [← e3, ← e4]; exact c2
      rw [if_neg c2, if_neg c2']
      by_cases c3 : b.answer = .phi ∧ a.answer ≠ .phi
      · have c3' : b'.answer = .phi ∧ a'.answer ≠ .phi := by rw [← e3, ← e4]; exact c3
        rw [if_pos c3, if_pos c3']
        refine ⟨ha, ?_⟩
        show relPEM { b with answer := a.answer } { b' with answer := a'.answer }
        rw [← e3]; exact relPEM_with_answer hb _
      · have c3' : ¬(b'.answer = .phi ∧ a'.answer ≠ .phi) := by rw [← e3, ← e4]; exact c3
        rw [if_neg c3, if_neg c3']
        exact ⟨ha, hb⟩
  · have c1' : ¬(a'.role = .Resetting ∧ b'.role = .Resetting) := by rw [← e1, ← e2]; exact c1
    rw [if_neg c1, if_neg c1']
    exact ⟨ha, hb⟩

theorem prePhase4_relPEM (hR : 1 ≤ Rmax) (hD : 2 ≤ Dmax) {trank : ℕ} {x₀ x₁ : Opinion}
    {s₀ s₁ s₀' s₁' : AgentState n} (h₀ : relPEM s₀ s₀') (h₁ : relPEM s₁ s₁') :
    relPEM (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).1
        (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀' s₁' x₀ x₁).1 ∧
      relPEM (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀ s₁ x₀ x₁).2
        (transitionPEM_prePhase4 n trank (rankDeltaOSSR Rmax Emax Dmax hn) s₀' s₁' x₀ x₁).2 := by
  have hNT := rankDeltaOSSR_relNT (Emax := Emax) (Dmax := Dmax) (hn := hn) hR h₀ h₁
  have hT := rankDeltaOSSR_timer (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) s₀ s₁
  have hT' := rankDeltaOSSR_timer (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) s₀' s₁'
  have hK := rankDeltaOSSR_rank (Rmax := Rmax) (Emax := Emax) (hn := hn) hD s₀ s₁
  rw [prePhase4_eq, prePhase4_eq]
  exact preEpi_relPEM (preAgent_relPEM h₀ hNT.1 hT.1 hT'.1 hK.1)
    (preAgent_relPEM h₁ hNT.2 hT.2 hT'.2 hK.2)

theorem swap_relPEM {x₀ x₁ : Opinion} {a b a' b' : AgentState n} (ha : relPEM a a')
    (hb : relPEM b b') (hsa : a.role = .Settled) (hsb : b.role = .Settled) :
    relPEM (phase4_swap a b x₀ x₁).1 (phase4_swap a' b' x₀ x₁).1 ∧
      relPEM (phase4_swap a b x₀ x₁).2 (phase4_swap a' b' x₀ x₁).2 ∧
      (phase4_swap a b x₀ x₁).1.role = .Settled ∧ (phase4_swap a b x₀ x₁).2.role = .Settled := by
  have hka : a.rank = a'.rank := (ha.2.2.2.1 hsa).1
  have hkb : b.rank = b'.rank := (hb.2.2.2.1 hsb).1
  unfold phase4_swap
  rw [← hka, ← hkb]
  split_ifs
  · exact ⟨hb, ha, hsb, hsa⟩
  · exact ⟨ha, hb, hsa, hsb⟩

theorem decide_relPEM {x₀ x₁ : Opinion} {a b a' b' : AgentState n} (ha : relPEM a a')
    (hb : relPEM b b') (hsa : a.role = .Settled) (hsb : b.role = .Settled) :
    relPEM (phase4_decide n a b x₀ x₁).1 (phase4_decide n a' b' x₀ x₁).1 ∧
      relPEM (phase4_decide n a b x₀ x₁).2 (phase4_decide n a' b' x₀ x₁).2 ∧
      (phase4_decide n a b x₀ x₁).1.role = .Settled ∧
      (phase4_decide n a b x₀ x₁).2.role = .Settled := by
  have hka : a.rank = a'.rank := (ha.2.2.2.1 hsa).1
  have hkb : b.rank = b'.rank := (hb.2.2.2.1 hsb).1
  unfold phase4_decide
  dsimp only
  split_ifs <;> (try (exfalso; simp_all; done)) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
    first
    | exact relPEM_with_answer ha _
    | exact relPEM_with_answer hb _
    | exact ha
    | exact hb
    | exact hsa
    | exact hsb

theorem propagate_relPEM (hR : 1 ≤ Rmax) {a b a' b' : AgentState n} (ha : relPEM a a')
    (hb : relPEM b b') (hsa : a.role = .Settled) (hsb : b.role = .Settled) :
    relPEM (phase4_propagate n Rmax a b).1 (phase4_propagate n Rmax a' b').1 ∧
      relPEM (phase4_propagate n Rmax a b).2 (phase4_propagate n Rmax a' b').2 := by
  rcases a with ⟨ra, ka, la, ca, aa, ta, cha, ea, da⟩
  rcases a' with ⟨ra', ka', la', ca', aa', ta', cha', ea', da'⟩
  rcases b with ⟨rb, kb, lb, cb, ab, tb, chb, eb, db⟩
  rcases b' with ⟨rb', kb', lb', cb', ab', tb', chb', eb', db'⟩
  obtain ⟨h1, h2, h3, hS, -, -⟩ := ha
  obtain ⟨g1, g2, g3, gS, -, -⟩ := hb
  simp only at h1 h2 h3 hS g1 g2 g3 gS hsa hsb
  subst h1 h2 h3 g1 g2 g3 hsa hsb
  obtain ⟨rfl, rfl, ht⟩ := hS rfl
  obtain ⟨rfl, rfl, gt⟩ := gS rfl
  by_cases hma : ka.val + 1 = ceilHalf n
  · obtain rfl := ht hma
    by_cases hlb : kb.val + 1 = n
    · simp only [phase4_propagate, hma, hlb, if_true]
      split_ifs <;>
        refine ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩⟩ <;> intro h0 <;>
          first
          | (simp at h0; done)
          | exact ⟨rfl, rfl, fun _ => rfl⟩
          | exact ⟨rfl, rfl, gt⟩
          | exact ⟨rfl, rfl, ht⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hma⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hmb⟩
          | exact ⟨rfl, fun h1 => absurd (show Rmax = 0 from h1) (by omega)⟩
    · simp only [phase4_propagate, hma, hlb, if_true, if_false]
      split_ifs <;>
        refine ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩⟩ <;> intro h0 <;>
          first
          | (simp at h0; done)
          | exact ⟨rfl, rfl, fun _ => rfl⟩
          | exact ⟨rfl, rfl, gt⟩
          | exact ⟨rfl, rfl, ht⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hma⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hmb⟩
          | exact ⟨rfl, fun h1 => absurd (show Rmax = 0 from h1) (by omega)⟩
  · by_cases hmb : kb.val + 1 = ceilHalf n
    · obtain rfl := gt hmb
      by_cases hla : ka.val + 1 = n
      · simp only [phase4_propagate, hma, hmb, if_true, if_false]
        split_ifs <;>
          refine ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩⟩ <;> intro h0 <;>
          first
          | (simp at h0; done)
          | exact ⟨rfl, rfl, fun _ => rfl⟩
          | exact ⟨rfl, rfl, gt⟩
          | exact ⟨rfl, rfl, ht⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hma⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hmb⟩
          | exact ⟨rfl, fun h1 => absurd (show Rmax = 0 from h1) (by omega)⟩
      · simp only [phase4_propagate, hma, hmb, if_true, if_false]
        split_ifs <;>
          refine ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩⟩ <;> intro h0 <;>
          first
          | (simp at h0; done)
          | exact ⟨rfl, rfl, fun _ => rfl⟩
          | exact ⟨rfl, rfl, gt⟩
          | exact ⟨rfl, rfl, ht⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hma⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hmb⟩
          | exact ⟨rfl, fun h1 => absurd (show Rmax = 0 from h1) (by omega)⟩
    · simp only [phase4_propagate, hma, hmb, if_false]
      refine ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩⟩ <;> intro h0 <;>
          first
          | (simp at h0; done)
          | exact ⟨rfl, rfl, fun _ => rfl⟩
          | exact ⟨rfl, rfl, gt⟩
          | exact ⟨rfl, rfl, ht⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hma⟩
          | exact ⟨rfl, rfl, fun h1 => absurd h1 hmb⟩
          | exact ⟨rfl, fun h1 => absurd (show Rmax = 0 from h1) (by omega)⟩

theorem phase4_relPEM (hR : 1 ≤ Rmax) {x₀ x₁ : Opinion} {p p' : AgentState n × AgentState n}
    (h₀ : relPEM p.1 p'.1) (h₁ : relPEM p.2 p'.2) :
    relPEM (transitionPEM_phase4 n Rmax p x₀ x₁).1 (transitionPEM_phase4 n Rmax p' x₀ x₁).1 ∧
      relPEM (transitionPEM_phase4 n Rmax p x₀ x₁).2 (transitionPEM_phase4 n Rmax p' x₀ x₁).2 := by
  rcases p with ⟨a, b⟩
  rcases p' with ⟨a', b'⟩
  simp only at h₀ h₁
  by_cases hS2 : a.role = .Settled ∧ b.role = .Settled
  · have hS2' : a'.role = .Settled ∧ b'.role = .Settled := by
      rw [← h₀.1, ← h₁.1]; exact hS2
    have hsw := swap_relPEM (x₀ := x₀) (x₁ := x₁) h₀ h₁ hS2.1 hS2.2
    simp only [transitionPEM_phase4, hS2, hS2', and_self, if_true]
    generalize phase4_swap a b x₀ x₁ = q at hsw ⊢
    generalize phase4_swap a' b' x₀ x₁ = q' at hsw ⊢
    rcases q with ⟨c, d⟩
    rcases q' with ⟨c', d'⟩
    obtain ⟨hc, hd, hsc, hsd⟩ := hsw
    have hdc := decide_relPEM (x₀ := x₀) (x₁ := x₁) hc hd hsc hsd
    simp only
    generalize phase4_decide n c d x₀ x₁ = q at hdc ⊢
    generalize phase4_decide n c' d' x₀ x₁ = q' at hdc ⊢
    rcases q with ⟨e, f⟩
    rcases q' with ⟨e', f'⟩
    obtain ⟨he, hf, hse, hsf⟩ := hdc
    exact propagate_relPEM hR he hf hse hsf
  · have hS2' : ¬(a'.role = .Settled ∧ b'.role = .Settled) := by
      rw [← h₀.1, ← h₁.1]; exact hS2
    rw [transitionPEM_phase4_of_not_both_settled hS2,
      transitionPEM_phase4_of_not_both_settled hS2']
    exact ⟨h₀, h₁⟩

/-- **The transition reads only the fields of the role.** -/
theorem transitionPEM_relPEM (hR : 1 ≤ Rmax) (hD : 2 ≤ Dmax) {trank : ℕ} {x₀ x₁ : Opinion}
    {a b a' b' : AgentState n} (ha : relPEM a a') (hb : relPEM b b') :
    relPEM ((protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ ((a, x₀), (b, x₁))).1
        ((protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ ((a', x₀), (b', x₁))).1 ∧
      relPEM ((protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ ((a, x₀), (b, x₁))).2
        ((protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
          ((a', x₀), (b', x₁))).2 := by
  have hpre := prePhase4_relPEM (trank := trank) (x₀ := x₀) (x₁ := x₁) (Emax := Emax) (hn := hn)
    hR hD ha hb
  simp only [protocolPEM, transitionPEM_eq]
  exact phase4_relPEM hR hpre.1 hpre.2

/-! ### Counter ranges are preserved -/

theorem processAgent_goodPEM {T : ℕ} {s : AgentState n} {oldRc : ℕ} {pr : Bool}
    (hs : GoodPEM T Emax Rmax Dmax s) :
    GoodPEM T Emax Rmax Dmax (processAgent Emax Dmax hn s oldRc pr) := by
  rcases s with ⟨r, k, l, c, a, t, ch, e, d⟩
  simp only [GoodPEM] at hs
  cases l <;> simp only [processAgent, resetOSSR] <;>
    (repeat' ((try dsimp only); split_ifs)) <;> simp_all [GoodPEM] <;> omega

theorem prRecruit_goodPEM {T : ℕ} {a b : AgentState n}
    (ha : GoodPEM T Emax Rmax Dmax a) (hb : GoodPEM T Emax Rmax Dmax b) :
    GoodPEM T Emax Rmax Dmax (prRecruit Dmax a b).1 ∧
      GoodPEM T Emax Rmax Dmax (prRecruit Dmax a b).2 := by
  simp only [prRecruit]
  split_ifs <;> simp_all [GoodPEM]

theorem prSync_goodPEM {T : ℕ} {a b : AgentState n}
    (ha : GoodPEM T Emax Rmax Dmax a) (hb : GoodPEM T Emax Rmax Dmax b) :
    GoodPEM T Emax Rmax Dmax (prSync a b).1 ∧ GoodPEM T Emax Rmax Dmax (prSync a b).2 := by
  simp only [prSync]
  split_ifs <;> simp_all [GoodPEM, max_le_iff] <;> omega

theorem rankDeltaOSSR_goodPEM {T : ℕ} {a b : AgentState n}
    (ha : GoodPEM T Emax Rmax Dmax a) (hb : GoodPEM T Emax Rmax Dmax b) :
    GoodPEM T Emax Rmax Dmax (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
      GoodPEM T Emax Rmax Dmax (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  by_cases hres : a.role = .Resetting ∨ b.role = .Resetting
  · rw [rankDeltaOSSR_eq_of_resetting hres, propagateReset_eq]
    have h1 := prRecruit_goodPEM (Dmax := Dmax) ha hb
    have h2 := prSync_goodPEM h1.1 h1.2
    have h3 := processAgent_goodPEM (hn := hn) (oldRc := (prRecruit Dmax a b).1.resetcount)
      (pr := ((prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).2.role == .Resetting)) h2.1
    have h4 := processAgent_goodPEM (hn := hn) (oldRc := (prRecruit Dmax a b).2.resetcount)
      (pr := ((prSync (prRecruit Dmax a b).1 (prRecruit Dmax a b).2).1.role == .Resetting)) h2.2
    simp only [prDedup]
    refine ⟨h3, ?_⟩
    split_ifs
    · exact h4
    · exact h4
  · simp only [GoodPEM] at ha hb
    simp [rankDeltaOSSR, hres]
    repeat' split_ifs <;> simp_all [GoodPEM] <;> omega

theorem prePhase4_goodPEM {trank : ℕ} {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    {rd : AgentState n × AgentState n → AgentState n × AgentState n}
    (h : GoodPEM (7 * (trank + 4)) Emax Rmax Dmax (rd (s₀, s₁)).1 ∧
      GoodPEM (7 * (trank + 4)) Emax Rmax Dmax (rd (s₀, s₁)).2) :
    GoodPEM (7 * (trank + 4)) Emax Rmax Dmax (transitionPEM_prePhase4 n trank rd s₀ s₁ x₀ x₁).1 ∧
      GoodPEM (7 * (trank + 4)) Emax Rmax Dmax
        (transitionPEM_prePhase4 n trank rd s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rd (s₀, s₁) with ⟨r₀, r₁⟩
  simp only [hrd] at h ⊢
  repeat' split_ifs <;> simp_all [GoodPEM] <;> omega

theorem propagate_goodPEM {T : ℕ} {a b : AgentState n}
    (ha : GoodPEM T Emax Rmax Dmax a) (hb : GoodPEM T Emax Rmax Dmax b) :
    GoodPEM T Emax Rmax Dmax (phase4_propagate n Rmax a b).1 ∧
      GoodPEM T Emax Rmax Dmax (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, GoodPEM] at * <;> omega
      · simp [haMed, hbLast, hReset, GoodPEM] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, GoodPEM] at * <;> omega
      · simp [haMed, hbLast, hReset, GoodPEM] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, GoodPEM] at * <;> omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, GoodPEM] at * <;> omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, GoodPEM] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, GoodPEM] at * <;> omega
    · simp [haMed, hbMed, GoodPEM] at * <;> omega

theorem phase4_goodPEM {T : ℕ} {p : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : GoodPEM T Emax Rmax Dmax p.1) (h₁ : GoodPEM T Emax Rmax Dmax p.2) :
    GoodPEM T Emax Rmax Dmax (transitionPEM_phase4 n Rmax p x₀ x₁).1 ∧
      GoodPEM T Emax Rmax Dmax (transitionPEM_phase4 n Rmax p x₀ x₁).2 := by
  rcases p with ⟨a, b⟩
  by_cases hS : a.role = .Settled ∧ b.role = .Settled
  · simp only [transitionPEM_phase4, hS, and_self, if_true]
    have hsw : GoodPEM T Emax Rmax Dmax (phase4_swap a b x₀ x₁).1 ∧
        GoodPEM T Emax Rmax Dmax (phase4_swap a b x₀ x₁).2 := by
      unfold phase4_swap; split_ifs
      · exact ⟨h₁, h₀⟩
      · exact ⟨h₀, h₁⟩
    generalize phase4_swap a b x₀ x₁ = q at hsw ⊢
    rcases q with ⟨c, d⟩
    have hdc : GoodPEM T Emax Rmax Dmax (phase4_decide n c d x₀ x₁).1 ∧
        GoodPEM T Emax Rmax Dmax (phase4_decide n c d x₀ x₁).2 := by
      unfold phase4_decide; repeat' split_ifs <;> simp_all [GoodPEM]
    simp only
    generalize phase4_decide n c d x₀ x₁ = q at hdc ⊢
    rcases q with ⟨e, f⟩
    exact propagate_goodPEM hdc.1 hdc.2
  · rw [transitionPEM_phase4_of_not_both_settled hS]
    exact ⟨h₀, h₁⟩

theorem transitionPEM_goodPEM {trank : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : GoodPEM (7 * (trank + 4)) Emax Rmax Dmax a)
    (hb : GoodPEM (7 * (trank + 4)) Emax Rmax Dmax b) :
    GoodPEM (7 * (trank + 4)) Emax Rmax Dmax
        ((protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ ((a, x₀), (b, x₁))).1 ∧
      GoodPEM (7 * (trank + 4)) Emax Rmax Dmax
        ((protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
          ((a, x₀), (b, x₁))).2 := by
  have hrd := rankDeltaOSSR_goodPEM (hn := hn) ha hb
  have hpre := prePhase4_goodPEM (x₀ := x₀) (x₁ := x₁) (s₀ := a) (s₁ := b) hrd
  simp only [protocolPEM, transitionPEM_eq]
  exact phase4_goodPEM hpre.1 hpre.2

end Respect

/-! ### The finite protocol and its correctness -/

section FinProtocol

variable {n : ℕ}

/-- **P_EM on the finite role-indexed state set**: decode, apply `transitionPEM`, encode. -/
def protocolPEMFin (n trank Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (PEMFinState n (7 * (trank + 4)) Emax Rmax Dmax) Opinion Output where
  δ := fun p =>
    let r := (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)).δ
      ((embPEM hn p.1.1, p.1.2), (embPEM hn p.2.1, p.2.2))
    (encPEM n (7 * (trank + 4)) Emax Rmax Dmax r.1, encPEM n (7 * (trank + 4)) Emax Rmax Dmax r.2)
  π_out := fun p => outputPEM n (embPEM hn p.1, p.2)

/-- `protocolPEMFin` simulates the flat `P_EM` on the states with counters in range. -/
def pemSimulation {trank Rmax Emax Dmax : ℕ} (hn : 0 < n) (hR : 1 ≤ Rmax) (hD : 2 ≤ Dmax) :
    StateSimulation (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
      (protocolPEMFin n trank Rmax Emax Dmax hn) where
  Good := GoodPEM (7 * (trank + 4)) Emax Rmax Dmax
  enc := encPEM n (7 * (trank + 4)) Emax Rmax Dmax
  emb := embPEM hn
  good_emb := goodPEM_embPEM hn
  enc_emb := encPEM_embPEM hn
  good_δ := fun _ _ _ _ ha hb => transitionPEM_goodPEM ha hb
  enc_δ := by
    intro a b x y ha hb
    have hra := relPEM_embPEM_encPEM hn ha
    have hrb := relPEM_embPEM_encPEM hn hb
    have hrel := transitionPEM_relPEM (trank := trank) (x₀ := x) (x₁ := y) (Emax := Emax)
      (hn := hn) hR hD hra hrb
    have hg := transitionPEM_goodPEM (trank := trank) (x₀ := x) (x₁ := y) (hn := hn) ha hb
    have hg' := transitionPEM_goodPEM (trank := trank) (x₀ := x) (x₁ := y) (hn := hn)
      (goodPEM_embPEM hn (encPEM n (7 * (trank + 4)) Emax Rmax Dmax a))
      (goodPEM_embPEM hn (encPEM n (7 * (trank + 4)) Emax Rmax Dmax b))
    show (encPEM n _ Emax Rmax Dmax _, encPEM n _ Emax Rmax Dmax _) = _
    rw [encPEM_eq_of_relPEM hg.1 hg'.1 hrel.1, encPEM_eq_of_relPEM hg.2 hg'.2 hrel.2]
  out := by
    intro a x ha
    have h := (relPEM_embPEM_encPEM (T := 7 * (trank + 4)) (E := Emax) (R := Rmax) (D := Dmax)
      hn ha).2.2.1
    show agentOutput _ = agentOutput _
    simp only [agentOutput]
    rw [h]

/-- **Kanaya et al. Theorem 4, correctness and silence on a finite state set.** The finite
protocol `protocolPEMFin` (the Lean instance `trank = Rmax = n` of P_EM, encoded on the
role-indexed state set) is a silent self-stabilizing exact majority protocol for `n ≥ 4`. -/
theorem P_EM_fin_solves_silent_SSEM_linear [Inhabited (Fin n × Fin n)]
    {Emax Dmax : ℕ} {hn : 0 < n} (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    SolvesSilentSSEM (protocolPEMFin n n n Emax Dmax hn) n :=
  (pemSimulation (trank := n) (Emax := Emax) hn (by omega) (by omega)).solvesSilentSSEM
    (P_EM_solves_silent_SSEM_linear hn4 hEmax hDmax)

/-- **State count of the finite P_EM** at `Emax = Dmax = n`: at most `216 n + 712 ≤ 394 n`
states for `n ≥ 4` (Kanaya et al.: `O(n)` states). -/
theorem P_EM_fin_card_le (hn4 : 4 ≤ n) :
    Fintype.card (PEMFinState n (7 * (n + 4)) n n n) ≤ 394 * n := by
  have h := card_PEMFinState_le n (7 * (n + 4)) n n n
  omega

/-- **State count of P_EM (Kanaya et al. 2025, Theorem 4, the O(n)-states part), for the Lean
instance.** For every `n ≥ 4` the Lean P_EM instance (`trank = Rmax = Emax = Dmax = n`), run on
its role-indexed state set, is a protocol with at most `394 n` states that solves silent
self-stabilizing exact majority on `n` agents in the reachability sense (`SolvesSilentSSEM`;
the paper's probability-one Definition 1 implies it, `solvesSSEM_of_kanayaDefinition1`).
The paper takes `trank = O(1)`; with `trank = n` the timer is kept only at the median rank,
which keeps the count linear. The time bound of Theorem 4 is not part of this statement and
does not hold for this instance by the paper's argument (Lemma 11 gives `Θ(n²)` for the
countdown when `trank = n`); see `OPEN_PROBLEMS.md` §6.1. -/
theorem P_EM_fin_silent_SSEM_states [Inhabited (Fin n × Fin n)] {hn : 0 < n} (hn4 : 4 ≤ n) :
    SolvesSilentSSEM (protocolPEMFin n n n n n hn) n ∧
      Fintype.card (PEMFinState n (7 * (n + 4)) n n n) ≤ 394 * n :=
  ⟨P_EM_fin_solves_silent_SSEM_linear hn4 le_rfl le_rfl, P_EM_fin_card_le hn4⟩

/-- Non-vacuity at `n = 4`. -/
example : SolvesSilentSSEM (protocolPEMFin 4 4 4 4 4 (by norm_num)) 4 :=
  P_EM_fin_solves_silent_SSEM_linear le_rfl le_rfl le_rfl

end FinProtocol

end Ripple.PopulationProtocol.SSEM

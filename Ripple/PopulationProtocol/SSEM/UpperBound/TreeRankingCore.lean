/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The valid tree and its invariance (P2 Definition 2.8, Lemma 2.9(a))

Configurations are read through their ranking projections `k : Fin n → AgentState n`.

* `Asg k j`: rank `j` is held by a Settled agent (the assigned set `A` of P2 §2).
* `TreeCore k`: P2's `VT⁻` with one leader: no propagating agent; at most one leader; once a
  Settled agent exists, every Resetting agent is a follower; rank `0` is assigned or the leader is
  still dormant; Settled ranks are pairwise distinct; `A` is parent-closed; each Settled agent's
  `children` counts its assigned children, and `2j + 2 ∈ A → 2j + 1 ∈ A`.
* `kstep R k u v`: one interaction of `R` on `k` (as `Config.step`).

`treeCore_kstep`: for `R = rankDeltaOSSR`, if `TreeCore k` and no participant is an Unsettled
agent with errorcount `≤ 1`, then `TreeCore (kstep R k u v)` (P2 Lemma 2.9(a): no collision, no
expiry, the tree stays valid). `kstep_asg_mono`, `kstep_recruit_asg`, `kstep_rel` record how the
assigned set and the individual agents change. `TreeCore` is invariant under permutations of the
agents (`treeCore_comp_perm`), which covers the Phase-4 swap of P_EM.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingRd

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-! ### Definitions -/

/-- Rank `j` is held by a Settled agent. -/
def Asg (k : Fin n → AgentState n) (j : ℕ) : Prop :=
  ∃ w, (k w).role = .Settled ∧ (k w).rank.val = j

/-- The children counter `c` of rank `j` is consistent with the assigned set. -/
def ChildOK (k : Fin n → AgentState n) (j c : ℕ) : Prop :=
  (c = 0 ∧ ¬ Asg k (2 * j + 1) ∧ ¬ Asg k (2 * j + 2)) ∨
    (c = 1 ∧ Asg k (2 * j + 1) ∧ ¬ Asg k (2 * j + 2)) ∨
    (c = 2 ∧ Asg k (2 * j + 1) ∧ Asg k (2 * j + 2))

/-- The valid tree with one leader (P2 `VT⁻` plus the leader conditions of Lemma 2.9(a)). -/
structure TreeCore (k : Fin n → AgentState n) : Prop where
  noProp : ∀ v, (k v).role = .Resetting → (k v).resetcount = 0
  oneL : ∀ v w, (k v).leader = .L → (k w).leader = .L → v = w
  rootL : ∀ v w, (k v).role = .Settled → (k w).role = .Resetting → (k w).leader = .F
  hasRoot : Asg k 0 ∨ ∃ v, (k v).role = .Resetting ∧ (k v).leader = .L
  inj : ∀ v w, (k v).role = .Settled → (k w).role = .Settled → (k v).rank = (k w).rank → v = w
  parent : ∀ v, (k v).role = .Settled → 0 < (k v).rank.val →
    Asg k (((k v).rank.val - 1) / 2)
  child : ∀ v, (k v).role = .Settled → ChildOK k (k v).rank.val (k v).children

/-- Update one agent. -/
def upd (k : Fin n → AgentState n) (w : Fin n) (s : AgentState n) : Fin n → AgentState n :=
  fun x => if x = w then s else k x

@[simp] theorem upd_self (k : Fin n → AgentState n) (w : Fin n) (s : AgentState n) :
    upd k w s w = s := by simp [upd]

theorem upd_ne (k : Fin n → AgentState n) {w x : Fin n} (s : AgentState n) (h : x ≠ w) :
    upd k w s x = k x := by simp [upd, h]

/-- One interaction of the rule `R` on `k` (the same shape as `Config.step`). -/
def kstep (R : AgentState n × AgentState n → AgentState n × AgentState n)
    (k : Fin n → AgentState n) (u v : Fin n) : Fin n → AgentState n :=
  fun w => if w = u then (R (k u, k v)).1 else if w = v then (R (k u, k v)).2 else k w

theorem kstep_eq_upd (R : AgentState n × AgentState n → AgentState n × AgentState n)
    (k : Fin n → AgentState n) {u v : Fin n} (huv : u ≠ v) :
    kstep R k u v = upd (upd k u (R (k u, k v)).1) v (R (k u, k v)).2 := by
  funext w
  simp only [kstep, upd]
  by_cases hu : w = u
  · subst hu; simp [huv]
  · by_cases hv : w = v
    · subst hv; simp [hu]
    · simp [hu, hv]

/-! ### Basic facts -/

theorem asg_comp_perm (k : Fin n → AgentState n) (π : Equiv.Perm (Fin n)) (j : ℕ) :
    Asg (k ∘ π) j ↔ Asg k j :=
  ⟨fun ⟨w, h⟩ => ⟨π w, h⟩, fun ⟨w, h⟩ => ⟨π.symm w, by simpa using h⟩⟩

theorem childOK_comp_perm (k : Fin n → AgentState n) (π : Equiv.Perm (Fin n)) (j c : ℕ) :
    ChildOK (k ∘ π) j c ↔ ChildOK k j c := by
  simp only [ChildOK, asg_comp_perm]

theorem treeCore_comp_perm {k : Fin n → AgentState n} (h : TreeCore k)
    (π : Equiv.Perm (Fin n)) : TreeCore (k ∘ π) where
  noProp v hv := h.noProp (π v) hv
  oneL v w hv hw := π.injective (h.oneL _ _ hv hw)
  rootL v w hv hw := h.rootL (π v) (π w) hv hw
  hasRoot := by
    rcases h.hasRoot with h0 | ⟨v, hv⟩
    · exact Or.inl ((asg_comp_perm k π 0).mpr h0)
    · exact Or.inr ⟨π.symm v, by simpa using hv⟩
  inj v w hv hw hr := π.injective (h.inj _ _ hv hw hr)
  parent v hv hr := (asg_comp_perm k π _).mpr (h.parent (π v) hv hr)
  child v hv := (childOK_comp_perm k π _ _).mpr (h.child (π v) hv)

/-- With a Settled agent present, rank `0` is assigned. -/
theorem TreeCore.asg_zero {k : Fin n → AgentState n} (h : TreeCore k) {v : Fin n}
    (hv : (k v).role = .Settled) : Asg k 0 := by
  rcases h.hasRoot with h0 | ⟨w, hwR, hwL⟩
  · exact h0
  · have := h.rootL v w hv hwR
    rw [hwL] at this
    exact absurd this (by decide)

/-- The parent of an assigned rank `j > 0` is assigned. -/
theorem TreeCore.asg_parent {k : Fin n → AgentState n} (h : TreeCore k) {j : ℕ}
    (hj : Asg k j) (hj0 : 0 < j) : Asg k ((j - 1) / 2) := by
  obtain ⟨w, hw, hwr⟩ := hj
  have := h.parent w hw (by omega)
  rwa [hwr] at this

/-- The two children of an unassigned rank are unassigned. -/
theorem TreeCore.not_asg_child {k : Fin n → AgentState n} (h : TreeCore k) {j : ℕ}
    (hj : ¬ Asg k j) (c : ℕ) (hc : c < 2) : ¬ Asg k (2 * j + c + 1) := by
  intro hA
  have := h.asg_parent hA (by omega)
  have e : (2 * j + c + 1 - 1) / 2 = j := by omega
  rw [e] at this
  exact hj this

/-! ### Single moves -/

theorem asg_upd_nonSettled {k : Fin n → AgentState n} {w : Fin n} {s : AgentState n}
    (hw : (k w).role ≠ .Settled) (hs : s.role ≠ .Settled) (j : ℕ) :
    Asg (upd k w s) j ↔ Asg k j := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    by_cases hxw : x = w
    · subst hxw; simp at hx1; exact absurd hx1 hs
    · rw [upd_ne k s hxw] at hx1 hx2; exact ⟨x, hx1, hx2⟩
  · rintro ⟨x, hx1, hx2⟩
    by_cases hxw : x = w
    · subst hxw; exact absurd hx1 hw
    · exact ⟨x, by rw [upd_ne k s hxw]; exact hx1, by rw [upd_ne k s hxw]; exact hx2⟩

/-- **Move 1**: a non-Settled agent changes to a non-Settled state, keeping its leader bit,
and becomes (or stays) Resetting only if it was Resetting, with resetcount `0`. -/
theorem treeCore_upd_nonSettled {k : Fin n → AgentState n} (h : TreeCore k) (w : Fin n)
    (s : AgentState n) (hw : (k w).role ≠ .Settled) (hs : s.role ≠ .Settled)
    (hL : s.leader = (k w).leader)
    (hR : s.role = .Resetting → (k w).role = .Resetting ∧ s.resetcount = 0)
    (hRL : (k w).role = .Resetting → (k w).leader = .L → s.role = .Resetting) :
    TreeCore (upd k w s) := by
  have hA := asg_upd_nonSettled hw hs (k := k)
  have hlead : ∀ x, (upd k w s x).leader = (k x).leader := by
    intro x; by_cases hx : x = w
    · subst hx; simp [hL]
    · rw [upd_ne k s hx]
  have hset : ∀ x, (upd k w s x).role = .Settled → x ≠ w ∧ (k x).role = .Settled := by
    intro x hx
    by_cases hxw : x = w
    · subst hxw; simp at hx; exact absurd hx hs
    · rw [upd_ne k s hxw] at hx; exact ⟨hxw, hx⟩
  have hres : ∀ x, (upd k w s x).role = .Resetting → (k x).role = .Resetting := by
    intro x hx
    by_cases hxw : x = w
    · subst hxw; simp at hx; exact (hR hx).1
    · rwa [upd_ne k s hxw] at hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; simp at hx ⊢; exact (hR hx).2
    · rw [upd_ne k s hxw] at hx ⊢; exact h.noProp x hx
  · intro x y hx hy
    rw [hlead] at hx hy
    exact h.oneL x y hx hy
  · intro x y hx hy
    rw [hlead]
    exact h.rootL x y (hset x hx).2 (hres y hy)
  · rcases h.hasRoot with h0 | ⟨x, hxR, hxL⟩
    · exact Or.inl ((hA 0).mpr h0)
    · refine Or.inr ⟨x, ?_, by rw [hlead]; exact hxL⟩
      by_cases hxw : x = w
      · subst hxw; simp; exact hRL hxR hxL
      · rw [upd_ne k s hxw]; exact hxR
  · intro x y hx hy hr
    obtain ⟨hxw, hx'⟩ := hset x hx
    obtain ⟨hyw, hy'⟩ := hset y hy
    rw [upd_ne k s hxw, upd_ne k s hyw] at hr
    exact h.inj x y hx' hy' hr
  · intro x hx hr
    obtain ⟨hxw, hx'⟩ := hset x hx
    rw [upd_ne k s hxw] at hr ⊢
    exact (hA _).mpr (h.parent x hx' hr)
  · intro x hx
    obtain ⟨hxw, hx'⟩ := hset x hx
    rw [upd_ne k s hxw]
    have := h.child x hx'
    simp only [ChildOK, hA] at this ⊢
    exact this

/-- **Move 2**: the dormant leader wakes as the root (rank `0`, no children). -/
theorem treeCore_upd_wakeL {k : Fin n → AgentState n} (h : TreeCore k) (w : Fin n)
    (s : AgentState n) (hwR : (k w).role = .Resetting) (hwL : (k w).leader = .L)
    (hs : s.role = .Settled) (hs0 : s.rank.val = 0) (hsc : s.children = 0)
    (hsL : s.leader = .L) : TreeCore (upd k w s) := by
  have hnoS : ∀ x, (k x).role ≠ .Settled := by
    intro x hx
    have := h.rootL x w hx hwR
    rw [hwL] at this
    exact absurd this (by decide)
  have hA : ∀ j, Asg (upd k w s) j ↔ j = 0 := by
    intro j
    constructor
    · rintro ⟨x, hx1, hx2⟩
      by_cases hxw : x = w
      · subst hxw; simp at hx2; omega
      · rw [upd_ne k s hxw] at hx1; exact absurd hx1 (hnoS x)
    · rintro rfl; exact ⟨w, by simp [hs], by simp [hs0]⟩
  have hlead : ∀ x, (upd k w s x).leader = (k x).leader := by
    intro x; by_cases hx : x = w
    · subst hx; simp [hsL, hwL]
    · rw [upd_ne k s hx]
  have hset : ∀ x, (upd k w s x).role = .Settled → x = w := by
    intro x hx
    by_contra hxw
    rw [upd_ne k s hxw] at hx
    exact hnoS x hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; simp [hs] at hx
    · rw [upd_ne k s hxw] at hx ⊢; exact h.noProp x hx
  · intro x y hx hy
    rw [hlead] at hx hy
    exact h.oneL x y hx hy
  · intro x y _ hy
    by_cases hyw : y = w
    · subst hyw; simp [hs] at hy
    · rw [hlead]
      cases hl : (k y).leader
      · exact absurd (h.oneL y w hl hwL) hyw
      · rfl
  · exact Or.inl ((hA 0).mpr rfl)
  · intro x y hx hy _
    rw [hset x hx, hset y hy]
  · intro x hx hr
    have := hset x hx
    subst this
    simp [hs0] at hr
  · intro x hx
    have := hset x hx
    subst this
    rw [upd_self]
    unfold ChildOK
    rw [hs0, hsc]
    left
    refine ⟨rfl, ?_, ?_⟩ <;> rw [hA] <;> omega

/-- **Move 3**: recruitment. The Settled agent `p` (rank `r`, children `c < 2`) recruits the
Unsettled agent `q`, which becomes Settled with rank `2r + c + 1` and no children. -/
theorem treeCore_recruit {k : Fin n → AgentState n} (h : TreeCore k) {p q : Fin n}
    (hpq : p ≠ q) (hpS : (k p).role = .Settled) (hc : (k p).children < 2)
    (hqU : (k q).role = .Unsettled) (sp sq : AgentState n)
    (hsp_role : sp.role = .Settled) (hsp_rank : sp.rank = (k p).rank)
    (hsp_c : sp.children = (k p).children + 1) (hsp_L : sp.leader = (k p).leader)
    (hsq_role : sq.role = .Settled)
    (hsq_rank : sq.rank.val = 2 * (k p).rank.val + (k p).children + 1)
    (hsq_c : sq.children = 0) (hsq_L : sq.leader = (k q).leader) :
    TreeCore (upd (upd k p sp) q sq) := by
  have hchild := h.child p hpS
  set r := (k p).rank.val with hr
  set c := (k p).children with hcdef
  set j := 2 * r + c + 1 with hj
  set k₂ := upd (upd k p sp) q sq with hk₂
  have hqp : q ≠ p := fun e => hpq e.symm
  have hk₂p : k₂ p = sp := by rw [hk₂, upd_ne _ _ hpq, upd_self]
  have hk₂q : k₂ q = sq := by rw [hk₂, upd_self]
  have hk₂o : ∀ x, x ≠ p → x ≠ q → k₂ x = k x := by
    intro x hxp hxq; rw [hk₂, upd_ne _ _ hxq, upd_ne _ _ hxp]
  have hnj : ¬ Asg k j := by
    rcases hchild with ⟨hc0, h1, _⟩ | ⟨hc1, _, h2⟩ | ⟨hc2, _, _⟩
    · rw [hj, hc0]; simpa using h1
    · rw [hj, hc1]; simpa [show 2 * r + 1 + 1 = 2 * r + 2 by omega] using h2
    · omega
  -- every Settled agent of `k₂` other than `q` is Settled in `k` with the same rank
  have hold : ∀ x, x ≠ q → (k₂ x).role = .Settled →
      (k x).role = .Settled ∧ (k₂ x).rank = (k x).rank := by
    intro x hxq hx
    by_cases hxp : x = p
    · subst hxp; rw [hk₂p] at hx ⊢; exact ⟨hpS, hsp_rank⟩
    · rw [hk₂o x hxp hxq] at hx ⊢; exact ⟨hx, rfl⟩
  have hA : ∀ i, Asg k₂ i ↔ Asg k i ∨ i = j := by
    intro i
    constructor
    · rintro ⟨x, hx1, hx2⟩
      by_cases hxq : x = q
      · subst hxq; rw [hk₂q] at hx2; exact Or.inr (by rw [← hx2, hsq_rank])
      · obtain ⟨hx', hrk⟩ := hold x hxq hx1
        exact Or.inl ⟨x, hx', by rw [← hrk]; exact hx2⟩
    · rintro (⟨x, hx1, hx2⟩ | rfl)
      · have hxq : x ≠ q := by intro e; subst e; rw [hqU] at hx1; exact absurd hx1 (by decide)
        by_cases hxp : x = p
        · subst hxp; exact ⟨x, by rw [hk₂p]; exact hsp_role, by rw [hk₂p, hsp_rank]; exact hx2⟩
        · exact ⟨x, by rw [hk₂o x hxp hxq]; exact hx1, by rw [hk₂o x hxp hxq]; exact hx2⟩
      · exact ⟨q, by rw [hk₂q]; exact hsq_role, by rw [hk₂q]; exact hsq_rank⟩
  have hlead : ∀ x, (k₂ x).leader = (k x).leader := by
    intro x
    by_cases hxq : x = q
    · subst hxq; rw [hk₂q, hsq_L]
    · by_cases hxp : x = p
      · subst hxp; rw [hk₂p, hsp_L]
      · rw [hk₂o x hxp hxq]
  have hres : ∀ x, (k₂ x).role = .Resetting → x ≠ p ∧ x ≠ q ∧ (k x).role = .Resetting := by
    intro x hx
    have hxp : x ≠ p := by intro e; subst e; rw [hk₂p, hsp_role] at hx; exact absurd hx (by decide)
    have hxq : x ≠ q := by intro e; subst e; rw [hk₂q, hsq_role] at hx; exact absurd hx (by decide)
    rw [hk₂o x hxp hxq] at hx
    exact ⟨hxp, hxq, hx⟩
  have h0 : Asg k 0 := h.asg_zero hpS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxp, hxq, hx'⟩ := hres x hx
    rw [hk₂o x hxp hxq]; exact h.noProp x hx'
  · intro x y hx hy
    rw [hlead] at hx hy
    exact h.oneL x y hx hy
  · intro x y _ hy
    rw [hlead]
    exact h.rootL p y hpS (hres y hy).2.2
  · exact Or.inl ((hA 0).mpr (Or.inl h0))
  · intro x y hx hy hxy
    by_cases hxq : x = q
    · by_cases hyq : y = q
      · rw [hxq, hyq]
      · obtain ⟨hy', hyr⟩ := hold y hyq hy
        subst hxq
        exfalso; apply hnj
        refine ⟨y, hy', ?_⟩
        rw [← hyr, ← hxy, hk₂q, hsq_rank]
    · by_cases hyq : y = q
      · obtain ⟨hx', hxr⟩ := hold x hxq hx
        subst hyq
        exfalso; apply hnj
        refine ⟨x, hx', ?_⟩
        rw [← hxr, hxy, hk₂q, hsq_rank]
      · obtain ⟨hx', hxr⟩ := hold x hxq hx
        obtain ⟨hy', hyr⟩ := hold y hyq hy
        exact h.inj x y hx' hy' (by rw [← hxr, ← hyr, hxy])
  · intro x hx hr0
    by_cases hxq : x = q
    · subst hxq
      rw [hk₂q, hsq_rank]
      have e : (2 * r + c + 1 - 1) / 2 = r := by omega
      rw [e]
      exact (hA r).mpr (Or.inl ⟨p, hpS, rfl⟩)
    · obtain ⟨hx', hxr⟩ := hold x hxq hx
      rw [hxr] at hr0 ⊢
      exact (hA _).mpr (Or.inl (h.parent x hx' hr0))
  · intro x hx
    by_cases hxq : x = q
    · subst hxq
      rw [hk₂q, hsq_rank, hsq_c]
      left
      refine ⟨rfl, ?_, ?_⟩
      · rw [hA]; rintro (h1 | h1)
        · exact h.not_asg_child hnj 0 (by omega) (by rw [Nat.add_zero]; exact h1)
        · omega
      · rw [hA]; rintro (h1 | h1)
        · have e : 2 * j + 1 + 1 = 2 * j + 2 := by omega
          exact h.not_asg_child hnj 1 (by omega) (by rw [e]; exact h1)
        · omega
    · by_cases hxp : x = p
      · subst hxp
        rw [hk₂p, hsp_rank, hsp_c]
        simp only [ChildOK, hA]
        rcases hchild with ⟨hc0, h1, h2⟩ | ⟨hc1, h1, h2⟩ | ⟨hc2, _, _⟩
        · right; left
          refine ⟨by omega, Or.inr (by omega), ?_⟩
          rintro (h3 | h3)
          · exact h2 h3
          · omega
        · right; right
          refine ⟨by omega, Or.inl h1, Or.inr (by omega)⟩
        · omega
      · obtain ⟨hx', hxr⟩ := hold x hxq hx
        have hkx : k₂ x = k x := hk₂o x hxp hxq
        rw [hkx]
        have hrne : (k x).rank.val ≠ r := by
          intro e
          exact hxp (h.inj x p hx' hpS (Fin.ext e))
        have hc1 : ¬ (2 * (k x).rank.val + 1 = j) := by omega
        have hc2 : ¬ (2 * (k x).rank.val + 2 = j) := by omega
        have := h.child x hx'
        simp only [ChildOK, hA, hc1, hc2, or_false] at this ⊢
        exact this

/-! ### The tree step -/

/-- The per-agent relation of one tree-phase interaction (P2 Lemmas 2.4, 2.7). -/
structure StepRel (Emax : ℕ) (a a' : AgentState n) : Prop where
  settled : a.role = .Settled → a'.role = .Settled ∧ a'.rank = a.rank
  resetting : a'.role = .Resetting →
    a.role = .Resetting ∧ a'.resetcount = 0 ∧ a'.delaytimer + 1 = a.delaytimer
  unsettled : a'.role = .Unsettled →
    (a.role = .Unsettled ∧ a.errorcount ≤ a'.errorcount + 1) ∨
      (a.role = .Resetting ∧ a'.errorcount = Emax)
  computing : a.role ≠ .Resetting → a'.role ≠ .Resetting

theorem upd_eq_self (k : Fin n → AgentState n) (w : Fin n) : upd k w (k w) = k := by
  funext x; by_cases hx : x = w
  · subst hx; simp
  · rw [upd_ne k _ hx]

theorem upd_comm (k : Fin n → AgentState n) {u v : Fin n} (huv : u ≠ v) (a b : AgentState n) :
    upd (upd k u a) v b = upd (upd k v b) u a := by
  funext x
  simp only [upd]
  by_cases hu : x = u
  · subst hu; simp [huv]
  · simp [hu]

theorem kstep_fst (R : AgentState n × AgentState n → AgentState n × AgentState n)
    (k : Fin n → AgentState n) (u v : Fin n) : kstep R k u v u = (R (k u, k v)).1 := by
  simp [kstep]

theorem kstep_snd (R : AgentState n × AgentState n → AgentState n × AgentState n)
    (k : Fin n → AgentState n) {u v : Fin n} (huv : u ≠ v) :
    kstep R k u v v = (R (k u, k v)).2 := by
  simp [kstep, Ne.symm huv]

theorem kstep_other (R : AgentState n × AgentState n → AgentState n × AgentState n)
    (k : Fin n → AgentState n) {u v w : Fin n} (hu : w ≠ u) (hv : w ≠ v) :
    kstep R k u v w = k w := by
  simp [kstep, hu, hv]

section Wake

variable {Emax : ℕ} {hn : 0 < n}

/-- A dormant agent wakes (leader: root; follower: Unsettled). -/
theorem treeCore_upd_wake {k : Fin n → AgentState n} (h : TreeCore k) (w : Fin n)
    (hwR : (k w).role = .Resetting) (d : ℕ) :
    TreeCore (upd k w (resetOSSR Emax hn { k w with delaytimer := d })) := by
  cases hl : (k w).leader
  · apply treeCore_upd_wakeL h w _ hwR hl <;> simp [resetOSSR, hl]
  · apply treeCore_upd_nonSettled h w _ (by rw [hwR]; decide) <;> simp [resetOSSR, hl]

theorem treeCore_upd_dt {k : Fin n → AgentState n} (h : TreeCore k) (w : Fin n)
    (hwR : (k w).role = .Resetting) (d : ℕ) :
    TreeCore (upd k w { k w with delaytimer := d }) := by
  apply treeCore_upd_nonSettled h w _ (by rw [hwR]; decide) <;> simp [hwR, h.noProp w hwR]

theorem treeCore_upd_dormStep {k : Fin n → AgentState n} (h : TreeCore k) (w : Fin n)
    (hwR : (k w).role = .Resetting) : TreeCore (upd k w (dormStep Emax hn (k w))) := by
  unfold dormStep
  split_ifs
  · exact treeCore_upd_wake h w hwR _
  · exact treeCore_upd_dt h w hwR _

theorem stepRel_wake {a : AgentState n} (ha : a.role = .Resetting) (d : ℕ) :
    StepRel Emax a (resetOSSR Emax hn { a with delaytimer := d }) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cases hl : a.leader <;> simp [resetOSSR, hl, ha]

theorem stepRel_dormStep {a : AgentState n} (ha : a.role = .Resetting)
    (har : a.resetcount = 0) : StepRel Emax a (dormStep Emax hn a) := by
  unfold dormStep
  split_ifs with hd
  · exact stepRel_wake ha _
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ha, har] <;> omega

theorem stepRel_self {a : AgentState n} (ha : a.role ≠ .Resetting) : StepRel Emax a a :=
  ⟨fun h => ⟨h, rfl⟩, fun h => absurd h ha, fun h => Or.inl ⟨h, by omega⟩, fun _ => ha⟩

end Wake

theorem upd_upd_self_val (k : Fin n → AgentState n) {u v : Fin n} (hvu : v ≠ u)
    (x : AgentState n) : upd (upd k u x) v (k v) = upd k u x := by
  have : k v = upd k u x v := (upd_ne k x hvu).symm
  rw [this, upd_eq_self]

/-- `TreeCore` reads only the ranking projection. -/
theorem treeCore_rhoS (k : Fin n → AgentState n) :
    TreeCore (fun w => rhoS (k w)) ↔ TreeCore k :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩⟩

theorem treeCore_of_rhoS_perm {k₁ k₂ : Fin n → AgentState n} (π : Equiv.Perm (Fin n))
    (h : ∀ w, rhoS (k₁ w) = rhoS (k₂ (π w))) (h₂ : TreeCore k₂) : TreeCore k₁ := by
  rw [← treeCore_rhoS]
  have e : (fun w => rhoS (k₁ w)) = (fun w => rhoS (k₂ w)) ∘ π := funext h
  rw [e]
  exact treeCore_comp_perm ((treeCore_rhoS k₂).mpr h₂) π

theorem asg_of_rhoS_perm {k₁ k₂ : Fin n → AgentState n} (π : Equiv.Perm (Fin n))
    (h : ∀ w, rhoS (k₁ w) = rhoS (k₂ (π w))) (j : ℕ) : Asg k₁ j ↔ Asg k₂ j := by
  have e : ∀ w, (k₁ w).role = (k₂ (π w)).role ∧ (k₁ w).rank = (k₂ (π w)).rank := fun w =>
    ⟨(rhoS_eq_iff.mp (h w)).1, (rhoS_eq_iff.mp (h w)).2.1⟩
  constructor
  · rintro ⟨w, h1, h2⟩
    exact ⟨π w, (e w).1 ▸ h1, (e w).2 ▸ h2⟩
  · rintro ⟨w, h1, h2⟩
    refine ⟨π.symm w, ?_, ?_⟩
    · rw [(e _).1]; simpa using h1
    · rw [(e _).2]; simpa using h2

section KStep

variable {Rmax Emax Dmax : ℕ} {hn : 0 < n}

/-- **The tree step** (P2 Lemma 2.9(a) for one interaction): no collision and no expiry, the
tree stays valid, and each participant changes as `StepRel` says. -/
theorem treeCore_kstep {k : Fin n → AgentState n} (h : TreeCore k) {u v : Fin n} (huv : u ≠ v)
    (hu : (k u).role = .Unsettled → 2 ≤ (k u).errorcount)
    (hv : (k v).role = .Unsettled → 2 ≤ (k v).errorcount) :
    TreeCore (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v) ∧
      StepRel Emax (k u) (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v u) ∧
      StepRel Emax (k v) (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v v) := by
  have hvu : v ≠ u := Ne.symm huv
  rw [kstep_fst, kstep_snd _ _ huv, kstep_eq_upd _ _ huv]
  have hLL : ¬ ((k u).leader = .L ∧ (k v).leader = .L) := fun ⟨h1, h2⟩ => huv (h.oneL u v h1 h2)
  rcases hru : (k u).role with _ | _ | _ <;> rcases hrv : (k v).role with _ | _ | _
  -- R R
  · rw [rd_RR hru hrv (h.noProp u hru) (h.noProp v hrv) hLL]
    refine ⟨?_, stepRel_dormStep hru (h.noProp u hru), stepRel_dormStep hrv (h.noProp v hrv)⟩
    have h1 := treeCore_upd_dormStep (Emax := Emax) (hn := hn) h u hru
    have h2 := treeCore_upd_dormStep (Emax := Emax) (hn := hn) h1 v
      (by rw [upd_ne _ _ hvu]; exact hrv)
    rwa [upd_ne _ _ hvu] at h2
  -- R S
  · rw [rd_RC hru (h.noProp u hru) (by rw [hrv]; decide)]
    refine ⟨?_, stepRel_wake hru _, stepRel_self (by rw [hrv]; decide)⟩
    rw [upd_upd_self_val _ hvu]
    exact treeCore_upd_wake h u hru _
  -- R U
  · rw [rd_RC hru (h.noProp u hru) (by rw [hrv]; decide)]
    refine ⟨?_, stepRel_wake hru _, stepRel_self (by rw [hrv]; decide)⟩
    rw [upd_upd_self_val _ hvu]
    exact treeCore_upd_wake h u hru _
  -- S R
  · rw [rd_CR (by rw [hru]; decide) hrv (h.noProp v hrv)]
    refine ⟨?_, stepRel_self (by rw [hru]; decide), stepRel_wake hrv _⟩
    rw [upd_eq_self]
    exact treeCore_upd_wake h v hrv _
  -- S S
  · have hne : (k u).rank ≠ (k v).rank := fun e => huv (h.inj u v hru hrv e)
    rw [rankDeltaOSSR_settled_distinct_ranks hru hrv hne]
    refine ⟨?_, stepRel_self (by rw [hru]; decide), stepRel_self (by rw [hrv]; decide)⟩
    rw [upd_eq_self, upd_eq_self]
    exact h
  -- S U
  · by_cases hrec : (k u).children < 2 ∧ 2 * (k u).rank.val + (k u).children + 1 < n
    · rw [rd_SU_rec hru hrv hrec.1 hrec.2]
      refine ⟨?_, ?_, ?_⟩
      · exact treeCore_recruit h huv hru hrec.1 hrv _ _ (by simp [hru]) rfl rfl rfl rfl
          rfl rfl rfl
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hru]
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hrv]
    · rw [rd_SU_dec hru hrv hrec (hv hrv)]
      refine ⟨?_, stepRel_self (by rw [hru]; decide), ?_⟩
      · rw [upd_eq_self]
        exact treeCore_upd_nonSettled h v _ (by rw [hrv]; decide) (by simp [hrv]) rfl
          (by simp [hrv]) (by rw [hrv]; simp)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hrv] <;> omega
  -- U R
  · rw [rd_CR (by rw [hru]; decide) hrv (h.noProp v hrv)]
    refine ⟨?_, stepRel_self (by rw [hru]; decide), stepRel_wake hrv _⟩
    rw [upd_eq_self]
    exact treeCore_upd_wake h v hrv _
  -- U S
  · by_cases hrec : (k v).children < 2 ∧ 2 * (k v).rank.val + (k v).children + 1 < n
    · rw [rd_US_rec hru hrv hrec.1 hrec.2]
      refine ⟨?_, ?_, ?_⟩
      · rw [upd_comm _ huv]
        exact treeCore_recruit h hvu hrv hrec.1 hru _ _ (by simp [hrv]) rfl rfl rfl rfl
          rfl rfl rfl
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hru]
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hrv]
    · rw [rd_US_dec hru hrv hrec (hu hru)]
      refine ⟨?_, ?_, stepRel_self (by rw [hrv]; decide)⟩
      · rw [upd_upd_self_val _ hvu]
        exact treeCore_upd_nonSettled h u _ (by rw [hru]; decide) (by simp [hru]) rfl
          (by simp [hru]) (by rw [hru]; simp)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hru] <;> omega
  -- U U
  · rw [rd_UU hru hrv (hu hru) (hv hrv)]
    refine ⟨?_, ?_, ?_⟩
    · have h1 := treeCore_upd_nonSettled h u { k u with errorcount := (k u).errorcount - 1 }
        (by rw [hru]; decide) (by simp [hru]) rfl (by simp [hru]) (by rw [hru]; simp)
      have h2 := treeCore_upd_nonSettled h1 v { k v with errorcount := (k v).errorcount - 1 }
        (by rw [upd_ne _ _ hvu, hrv]; decide) (by simp [hrv]) (by rw [upd_ne _ _ hvu])
        (by simp [hrv]) (by rw [upd_ne _ _ hvu, hrv]; simp)
      exact h2
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hru] <;> omega
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hrv] <;> omega

/-- Assigned ranks stay assigned. -/
theorem kstep_asg_mono {k : Fin n → AgentState n} {u v : Fin n} (huv : u ≠ v)
    (hsu : StepRel Emax (k u) (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v u))
    (hsv : StepRel Emax (k v) (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v v)) {j : ℕ}
    (hj : Asg k j) : Asg (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v) j := by
  obtain ⟨w, hw, hwr⟩ := hj
  by_cases hwu : w = u
  · subst hwu
    exact ⟨w, (hsu.settled hw).1, by rw [(hsu.settled hw).2]; exact hwr⟩
  · by_cases hwv : w = v
    · subst hwv
      exact ⟨w, (hsv.settled hw).1, by rw [(hsv.settled hw).2]; exact hwr⟩
    · exact ⟨w, by rw [kstep_other _ _ hwu hwv]; exact hw,
        by rw [kstep_other _ _ hwu hwv]; exact hwr⟩

/-- A recruitment assigns the recruit rank `2r + c + 1` (either order of the pair). -/
theorem kstep_recruit_asg {k : Fin n → AgentState n} {u v : Fin n} (huv : u ≠ v)
    (hrec : ((k u).role = .Settled ∧ (k v).role = .Unsettled ∧ (k u).children < 2 ∧
        2 * (k u).rank.val + (k u).children + 1 < n) ∨
      ((k v).role = .Settled ∧ (k u).role = .Unsettled ∧ (k v).children < 2 ∧
        2 * (k v).rank.val + (k v).children + 1 < n)) :
    Asg (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v)
      (if (k u).role = .Settled then 2 * (k u).rank.val + (k u).children + 1
        else 2 * (k v).rank.val + (k v).children + 1) := by
  rcases hrec with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · refine ⟨v, ?_, ?_⟩
    · rw [kstep_snd _ _ huv, rd_SU_rec h1 h2 h3 h4]
    · rw [kstep_snd _ _ huv, rd_SU_rec h1 h2 h3 h4, if_pos h1]
  · refine ⟨u, ?_, ?_⟩
    · rw [kstep_fst, rd_US_rec h2 h1 h3 h4]
    · rw [kstep_fst, rd_US_rec h2 h1 h3 h4, if_neg (by rw [h2]; decide)]

theorem wakeStep_settled {x : AgentState n} (h : (wakeStep Emax hn x).role = .Settled) :
    (wakeStep Emax hn x).rank.val = 0 := by
  unfold wakeStep resetOSSR at *
  cases hl : x.leader <;> simp_all

theorem dormStep_settled {x : AgentState n} (h : (dormStep Emax hn x).role = .Settled)
    (hx : x.role = .Resetting) : (dormStep Emax hn x).rank.val = 0 := by
  unfold dormStep resetOSSR at *
  split_ifs at * <;> cases hl : x.leader <;> simp_all

/-- A newly Settled participant is the root (rank `0`) or was recruited by its partner. -/
theorem kstep_newSettled {k : Fin n → AgentState n} (h : TreeCore k) {u v : Fin n}
    (huv : u ≠ v) (hu : (k u).role = .Unsettled → 2 ≤ (k u).errorcount)
    (hv : (k v).role = .Unsettled → 2 ≤ (k v).errorcount) :
    ((kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v u).role = .Settled →
        (k u).role ≠ .Settled →
        (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v u).rank.val = 0 ∨
          ((k v).role = .Settled ∧
            (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v u).rank.val =
              2 * (k v).rank.val + (k v).children + 1 ∧
            (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v v).rank = (k v).rank)) ∧
      ((kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v v).role = .Settled →
        (k v).role ≠ .Settled →
        (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v v).rank.val = 0 ∨
          ((k u).role = .Settled ∧
            (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v v).rank.val =
              2 * (k u).rank.val + (k u).children + 1 ∧
            (kstep (rankDeltaOSSR Rmax Emax Dmax hn) k u v u).rank = (k u).rank)) := by
  rw [kstep_fst, kstep_snd _ _ huv]
  have hLL : ¬ ((k u).leader = .L ∧ (k v).leader = .L) := fun ⟨h1, h2⟩ => huv (h.oneL u v h1 h2)
  rcases hru : (k u).role with _ | _ | _ <;> rcases hrv : (k v).role with _ | _ | _
  · rw [rd_RR hru hrv (h.noProp u hru) (h.noProp v hrv) hLL]
    exact ⟨fun h1 _ => Or.inl (dormStep_settled h1 hru),
      fun h1 _ => Or.inl (dormStep_settled h1 hrv)⟩
  · rw [rd_RC hru (h.noProp u hru) (by rw [hrv]; decide)]
    exact ⟨fun h1 _ => Or.inl (wakeStep_settled h1), fun _ h2 => absurd rfl h2⟩
  · rw [rd_RC hru (h.noProp u hru) (by rw [hrv]; decide)]
    exact ⟨fun h1 _ => Or.inl (wakeStep_settled h1), fun h1 _ => by
      rw [hrv] at h1; exact absurd h1 (by decide)⟩
  · rw [rd_CR (by rw [hru]; decide) hrv (h.noProp v hrv)]
    exact ⟨fun _ h2 => absurd rfl h2, fun h1 _ => Or.inl (wakeStep_settled h1)⟩
  · exact ⟨fun _ h2 => absurd rfl h2, fun _ h2 => absurd rfl h2⟩
  · by_cases hrec : (k u).children < 2 ∧ 2 * (k u).rank.val + (k u).children + 1 < n
    · rw [rd_SU_rec hru hrv hrec.1 hrec.2]
      exact ⟨fun _ h2 => absurd rfl h2, fun _ _ => Or.inr ⟨rfl, rfl, rfl⟩⟩
    · rw [rd_SU_dec hru hrv hrec (hv hrv)]
      exact ⟨fun _ h2 => absurd rfl h2, fun h1 _ => by simp [hrv] at h1⟩
  · rw [rd_CR (by rw [hru]; decide) hrv (h.noProp v hrv)]
    exact ⟨fun h1 _ => by rw [hru] at h1; exact absurd h1 (by decide),
      fun h1 _ => Or.inl (wakeStep_settled h1)⟩
  · by_cases hrec : (k v).children < 2 ∧ 2 * (k v).rank.val + (k v).children + 1 < n
    · rw [rd_US_rec hru hrv hrec.1 hrec.2]
      exact ⟨fun _ _ => Or.inr ⟨rfl, rfl, rfl⟩, fun _ h2 => absurd rfl h2⟩
    · rw [rd_US_dec hru hrv hrec (hu hru)]
      exact ⟨fun h1 _ => by simp [hru] at h1, fun _ h2 => absurd rfl h2⟩
  · rw [rd_UU hru hrv (hu hru) (hv hrv)]
    exact ⟨fun h1 _ => by simp [hru] at h1, fun h1 _ => by simp [hrv] at h1⟩

end KStep

end Ripple.PopulationProtocol.SSEM

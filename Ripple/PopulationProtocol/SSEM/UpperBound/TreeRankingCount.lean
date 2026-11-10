/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Counting recruiters and Unsettled agents in a valid tree (P2 Lemma 6.1)

For a valid tree (`TreeCore`) in which every agent is computing:

* `card_unsAg`: the Unsettled agents are as many as the unassigned ranks;
* `card_uns_ge`: on every level `d ≤ topL n`, `unasg k d · uL n d ≤ U` (the subtrees of the
  unassigned level-`d` ranks are unassigned; on complete levels each has `2^(H-d) - 1` ranks);
* `card_unasg_le_rec`: if every level below `d` is fully assigned and rank `0` is assigned, the
  `unasg k d` unassigned ranks of level `d` have at least `unasg k d / 2` recruiters (`Rec k d`),
  each of which assigns an unassigned level-`d` rank when it meets an Unsettled agent.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingLevels

namespace Ripple.PopulationProtocol.SSEM

open scoped BigOperators

variable {n : ℕ}

section Count

open Classical

/-- Every agent is computing. -/
def AllCompK (k : Fin n → AgentState n) : Prop := ∀ w, (k w).role ≠ .Resetting

/-- The Unsettled agents. -/
noncomputable def unsAg (k : Fin n → AgentState n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => (k w).role = .Unsettled)

/-- All unassigned ranks `< n`. -/
noncomputable def unasgAll (k : Fin n → AgentState n) : Finset ℕ :=
  (Finset.range n).filter (fun r => ¬ Asg k r)

theorem card_unsAg {k : Fin n → AgentState n} (h : TreeCore k) (hc : AllCompK k) :
    (unsAg k).card = (unasgAll k).card := by
  set Sag := Finset.univ.filter (fun w : Fin n => (k w).role = .Settled)
  have h1 : Sag.card + (unsAg k).card = n := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n))) (fun w : Fin n => (k w).role = .Settled)
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : Finset.univ.filter (fun w : Fin n => ¬ (k w).role = .Settled) = unsAg k := by
      ext w
      simp only [unsAg, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hc w
      constructor
      · intro hS; cases hr : (k w).role
        · exact absurd hr this
        · exact absurd hr hS
        · rfl
      · intro hU; rw [hU]; decide
    rw [e] at this
    exact this
  have h2 : Sag.card = ((Finset.range n).filter (fun r => Asg k r)).card := by
    apply Finset.card_bij (fun w _ => (k w).rank.val)
    · intro w hw
      simp only [Sag, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨(k w).rank.isLt, w, hw, rfl⟩
    · intro w₁ hw₁ w₂ hw₂ he
      simp only [Sag, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
      exact h.inj w₁ w₂ hw₁ hw₂ (Fin.ext he)
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨w, hw, hwr⟩ := hr.2
      exact ⟨w, by simp [Sag, hw], hwr⟩
  have h3 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.range n) (fun r => Asg k r)
  rw [Finset.card_range] at h3
  unfold unasgAll
  omega

/-- Unassigned ranks `< n` on levels `≥ d`. -/
noncomputable def unasgGe (k : Fin n → AgentState n) (d : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun r => 2 ^ d ≤ r + 1 ∧ ¬ Asg k r)

theorem card_unasgGe_split (k : Fin n → AgentState n) (d : ℕ) :
    (unasgGe k d).card = unasg k d + (unasgGe k (d + 1)).card := by
  have he : unasgGe k d = unasgSet k d ∪ unasgGe k (d + 1) := by
    ext r
    simp only [unasgGe, unasgSet, InLevel, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range]
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_succ d)
    constructor
    · rintro ⟨hr, h1, h2⟩
      by_cases h3 : r + 1 < 2 ^ (d + 1)
      · exact Or.inl ⟨hr, ⟨h1, h3⟩, h2⟩
      · exact Or.inr ⟨hr, by omega, h2⟩
    · rintro (⟨hr, ⟨h1, _⟩, h2⟩ | ⟨hr, h1, h2⟩)
      · exact ⟨hr, h1, h2⟩
      · exact ⟨hr, by omega, h2⟩
  rw [he, Finset.card_union_of_disjoint]
  · rfl
  · rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [unasgGe, unasgSet, InLevel, Finset.mem_filter] at h1 h2
    omega

/-- Doubling: the children of the unassigned ranks of level `d` are unassigned, on a complete
level. -/
theorem two_mul_unasg_le {k : Fin n → AgentState n} (h : TreeCore k) {d : ℕ}
    (hd : d + 2 ≤ topL n) : 2 * unasg k d ≤ unasg k (d + 1) := by
  have hc : (unasgSet k d ×ˢ Finset.range 2).card = unasg k d * 2 := by
    rw [Finset.card_product, Finset.card_range]; rfl
  rw [mul_comm, ← hc]
  apply Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => 2 * x.1 + x.2 + 1)
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_unasgSet] at hx1
    have hl := inLevel_child hx1.2.1 hx2
    rw [Finset.mem_coe, mem_unasgSet]
    exact ⟨lt_of_inLevel_complete (by omega) hl, hl, h.not_asg_child hx1.2.2 x.2 hx2⟩
  · intro x hx y hy he
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx hy
    simp only at he
    ext <;> omega

theorem unasgGe_ge {k : Fin n → AgentState n} (h : TreeCore k) :
    ∀ m d, d + m + 1 = topL n → unasg k d * (2 ^ (m + 1) - 1) ≤ (unasgGe k d).card := by
  intro m
  induction m with
  | zero =>
    intro d _
    rw [card_unasgGe_split]; simp
  | succ m ih =>
    intro d hd
    rw [card_unasgGe_split]
    have h1 := ih (d + 1) (by omega)
    have h2 := two_mul_unasg_le h (d := d) (by omega)
    obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (m + 1) = Q + 1 := ⟨2 ^ (m + 1) - 1, by
      have := Nat.one_le_two_pow (n := m + 1); omega⟩
    have hQ2 : 2 ^ (m + 1 + 1) = 2 * Q + 2 := by rw [pow_succ, hQ]; ring
    rw [hQ] at h1
    rw [hQ2]
    simp only [Nat.add_sub_cancel] at h1 ⊢
    have : 2 * Q + 2 - 1 = 2 * Q + 1 := by omega
    rw [this]
    nlinarith

theorem unasgGe_subset (k : Fin n → AgentState n) (d : ℕ) : unasgGe k d ⊆ unasgAll k := by
  intro r hr
  simp only [unasgGe, unasgAll, Finset.mem_filter] at hr ⊢
  exact ⟨hr.1, hr.2.2⟩

/-- **Unsettled agents per unassigned rank** (P2 Lemma 6.1, "U ≥ i (2^(h-d) - 1)"). -/
theorem card_uns_ge {k : Fin n → AgentState n} (h : TreeCore k) (hc : AllCompK k) {d : ℕ}
    (hd : d ≤ topL n) : (unasg k d : ℝ) * uL n d ≤ (unsAg k).card := by
  rw [card_unsAg h hc]
  unfold uL
  split_ifs with hlt
  · have h1 := unasgGe_ge h (topL n - d - 1) d (by omega)
    have h2 := Finset.card_le_card (unasgGe_subset k d)
    have e : topL n - d - 1 + 1 = topL n - d := by omega
    rw [e] at h1
    have h3 : (unasg k d * (2 ^ (topL n - d) - 1) : ℕ) ≤ (unasgAll k).card := h1.trans h2
    have h4 : ((2 ^ (topL n - d) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (topL n - d) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num
    rw [← h4]
    exact_mod_cast h3
  · rw [mul_one]
    have : unasgSet k d ⊆ unasgAll k := by
      intro r hr
      rw [mem_unasgSet] at hr
      simp only [unasgAll, Finset.mem_filter, Finset.mem_range]
      exact ⟨hr.1, hr.2.2⟩
    exact_mod_cast Finset.card_le_card this

/-! ### Recruiters -/

/-- The rank a Settled agent would recruit next. -/
def recTarget (k : Fin n → AgentState n) (p : Fin n) : ℕ :=
  2 * (k p).rank.val + (k p).children + 1

/-- Recruiters of level `d`: Settled agents whose next recruit rank is an unassigned rank
`< n` of level `d`. -/
noncomputable def Rec (k : Fin n → AgentState n) (d : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => (k p).role = .Settled ∧ (k p).children < 2 ∧
    recTarget k p < n ∧ InLevel d (recTarget k p) ∧ ¬ Asg k (recTarget k p))

theorem mem_Rec {k : Fin n → AgentState n} {d : ℕ} {p : Fin n} :
    p ∈ Rec k d ↔ (k p).role = .Settled ∧ (k p).children < 2 ∧
      recTarget k p < n ∧ InLevel d (recTarget k p) ∧ ¬ Asg k (recTarget k p) := by
  simp [Rec]

/-- **Recruiters on the least incomplete level** (P2 Lemma 6.1: `≥ ⌈i/2⌉` distinct parents). -/
theorem card_unasg_le_rec {k : Fin n → AgentState n} (h : TreeCore k) (h0 : Asg k 0)
    {d : ℕ} (hmin : ∀ d', d' < d → unasg k d' = 0) : unasg k d ≤ 2 * (Rec k d).card := by
  obtain ⟨w₀, -, -⟩ := id h0
  have hn0 : 0 < n := Fin.pos w₀
  -- the holder of the parent rank
  let f : ℕ → Fin n := fun r =>
    if hA : Asg k ((r - 1) / 2) then hA.choose else ⟨0, hn0⟩
  have hpar : ∀ r ∈ unasgSet k d, ∃ d', d = d' + 1 ∧ Asg k ((r - 1) / 2) := by
    intro r hr
    rw [mem_unasgSet] at hr
    obtain ⟨hrn, hl, hra⟩ := hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hra h0
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := by
      rcases d with _ | d'
      · exfalso; have := hl.2; simp at this; omega
      · exact ⟨d', rfl⟩
    refine ⟨d', rfl, ?_⟩
    by_contra hq
    have hz := hmin d' (by omega)
    have : (r - 1) / 2 ∈ unasgSet k d' :=
      mem_unasgSet.mpr ⟨by omega, inLevel_parent hl, hq⟩
    unfold unasg at hz
    rw [Finset.card_eq_zero] at hz
    rw [hz] at this
    exact absurd this (Finset.notMem_empty _)
  have hf : ∀ r ∈ unasgSet k d, (k (f r)).role = .Settled ∧ (k (f r)).rank.val = (r - 1) / 2 := by
    intro r hr
    obtain ⟨_, _, hA⟩ := hpar r hr
    have e : f r = hA.choose := by simp only [f, dif_pos hA]
    rw [e]
    exact hA.choose_spec
  have hmaps : ∀ r ∈ unasgSet k d, f r ∈ Rec k d := by
    intro r hr
    obtain ⟨d', hd, _⟩ := hpar r hr
    obtain ⟨hpS, hpr⟩ := hf r hr
    rw [mem_unasgSet] at hr
    obtain ⟨hrn, hl, hra⟩ := hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hra h0
    set p := f r
    set q := (r - 1) / 2 with hq
    have hr12 : r = 2 * q + 1 ∨ r = 2 * q + 2 := by omega
    have hpl : InLevel d' q := by rw [hd] at hl; exact inLevel_parent hl
    have hch := h.child p hpS
    rw [hpr] at hch
    rw [mem_Rec]
    unfold recTarget
    rw [hpr]
    rcases hch with ⟨hc0, h1, h2⟩ | ⟨hc1, h1, h2⟩ | ⟨hc2, h1, h2⟩
    · rw [hc0]
      refine ⟨hpS, by omega, by omega, ?_, by simpa using h1⟩
      rw [hd]; simpa using inLevel_child hpl (c := 0) (by norm_num)
    · rw [hc1]
      have hr2 : r = 2 * q + 2 := by
        rcases hr12 with e | e
        · exfalso; rw [e] at hra; exact hra h1
        · exact e
      refine ⟨hpS, by omega, by omega, ?_, ?_⟩
      · rw [show 2 * q + 1 + 1 = r by omega]; exact hl
      · rw [show 2 * q + 1 + 1 = 2 * q + 2 by omega]; exact h2
    · exfalso
      rcases hr12 with e | e
      · rw [e] at hra; exact hra h1
      · rw [e] at hra; exact hra h2
  have hfib : ∀ p ∈ Rec k d, ((unasgSet k d).filter (fun r => f r = p)).card ≤ 2 := by
    intro p _
    refine le_trans (Finset.card_le_card (t := {2 * (k p).rank.val + 1,
      2 * (k p).rank.val + 2}) ?_) Finset.card_le_two
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, hfp⟩ := hr
    obtain ⟨hpS, hpr⟩ := hf r hr
    rw [hfp] at hpr
    have hr0 : r ≠ 0 := by
      rintro rfl; rw [mem_unasgSet] at hr; exact hr.2.2 h0
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib

end Count

end Ripple.PopulationProtocol.SSEM

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Swap Phase: Misordered-Pair Potential

In an `Srank` configuration (all agents Settled, ranks bijective), the
"swap" phase of P_EM rearranges agent states so that A-input agents
have lower ranks than B-input agents — i.e., the configuration enters
`Sswap`.

We measure progress by the count of *misordered pairs*:

  > A pair `(u, v)` is misordered iff
  > `(C u).2 = .B ∧ (C v).2 = .A ∧ (C u).1.rank < (C v).1.rank`.

This file establishes the foundational potential function:

  * `MisorderedPair` — the predicate on agent pairs.
  * `misorderedSet`, `misorderedCount` — the witness Finset and its
    cardinality (a decidable potential).
  * `mem_misorderedSet`, `misorderedCount_eq_zero_iff` — basic
    rewriting lemmas.
  * `exists_misordered_of_pos_count` — extracting an explicit witness
    when the count is positive.

The `Srank ∧ no-misorder ⟹ Sswap` characterization and the deterministic
scheduler driving the potential to zero are layered on top of these.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Sets
import Mathlib.Data.Fintype.Prod

namespace SSEM

variable {n : ℕ}

/-- An ordered pair of agents `(u, v)` is *misordered* in `C` iff
`(C u).2 = .B`, `(C v).2 = .A`, and the rank of `u` is strictly less
than the rank of `v`. The protocol's swap rule (Algorithm 1, lines
10–11) fires precisely on misordered pairs. -/
def MisorderedPair (C : Config (AgentState n) Opinion n) (uv : Fin n × Fin n) : Prop :=
  (C uv.1).2 = Opinion.B ∧ (C uv.2).2 = Opinion.A ∧ (C uv.1).1.rank < (C uv.2).1.rank

instance (C : Config (AgentState n) Opinion n) (uv : Fin n × Fin n) :
    Decidable (MisorderedPair C uv) := by
  unfold MisorderedPair
  exact instDecidableAnd

/-- The set of misordered pairs in `C`. -/
def misorderedSet (C : Config (AgentState n) Opinion n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (MisorderedPair C)

/-- The count of misordered pairs — a decidable potential function. -/
def misorderedCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (misorderedSet C).card

theorem mem_misorderedSet {C : Config (AgentState n) Opinion n} {uv : Fin n × Fin n} :
    uv ∈ misorderedSet C ↔ MisorderedPair C uv := by
  unfold misorderedSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The count is zero iff there are no misordered pairs. -/
theorem misorderedCount_eq_zero_iff (C : Config (AgentState n) Opinion n) :
    misorderedCount C = 0 ↔ ∀ u v, ¬ MisorderedPair C (u, v) := by
  unfold misorderedCount
  rw [Finset.card_eq_zero]
  constructor
  · intro h u v hM
    have hmem : (u, v) ∈ misorderedSet C := mem_misorderedSet.mpr hM
    rw [h] at hmem
    exact (by simp : (u, v) ∉ (∅ : Finset (Fin n × Fin n))) hmem
  · intro h
    apply Finset.ext
    intro uv
    constructor
    · intro hmem
      exact (h uv.1 uv.2 (mem_misorderedSet.mp hmem)).elim
    · intro hmem
      exact (Finset.notMem_empty _ hmem).elim

/-- If the misordered count is positive, then a misordered pair exists. -/
theorem exists_misordered_of_pos_count {C : Config (AgentState n) Opinion n}
    (h : 0 < misorderedCount C) :
    ∃ u v : Fin n, MisorderedPair C (u, v) := by
  unfold misorderedCount at h
  obtain ⟨⟨u, v⟩, huv⟩ := Finset.card_pos.mp h
  exact ⟨u, v, mem_misorderedSet.mp huv⟩

/-- Contrapositive: under `Sswap` (which we'll establish from no-misorder
under `Srank` separately), the misordered count is zero. -/
theorem misorderedCount_eq_zero_of_InSswap {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C) :
    misorderedCount C = 0 := by
  rw [misorderedCount_eq_zero_iff]
  intro u v hM
  obtain ⟨huB, hvA, hlt⟩ := hM
  have huRank : nAOf C ≤ (C u).1.rank.val := by
    by_contra hlt'
    push_neg at hlt'
    have : (C u).2 = Opinion.A := (hSwap.input_rank u).mpr hlt'
    rw [this] at huB; cases huB
  have hvRank : (C v).1.rank.val < nAOf C := (hSwap.input_rank v).mp hvA
  have : (C u).1.rank.val < (C v).1.rank.val := hlt
  omega

/-! ### Cardinality lemmas for the no-misorder ⟹ Sswap direction

We need that under the bijective rank function, the count of agents with
rank value below a threshold `k ≤ n` is exactly `k`.  The proof uses an
explicit `Fin k ↪ Fin n` embedding combined with the rank bijection.
-/

/-- Auxiliary: cardinality of `{i : Fin n | i.val < k}` is exactly `k`
when `k ≤ n`. -/
private theorem card_Fin_filter_val_lt {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  classical
  -- Instead of Finset.map, use card-of-image with the natural embedding.
  let toFin : Fin k → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hinj : Function.Injective toFin := by
    intro i j h
    have : i.val = j.val := by
      have := congrArg Fin.val h
      exact this
    exact Fin.ext this
  have himg : (Finset.univ : Finset (Fin k)).image toFin
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    apply Finset.ext
    intro i
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hfj⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      have : (toFin j).val = i.val := congrArg Fin.val hfj
      have hj : j.val < k := j.isLt
      have hjval : j.val = i.val := this
      exact hjval ▸ hj
    · rintro ⟨_, hi⟩
      refine ⟨⟨i.val, hi⟩, Finset.mem_univ _, ?_⟩
      apply Fin.eq_of_val_eq
      rfl
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]

/-- The rank function being a bijection lets us translate filter cardinalities. -/
private theorem card_filter_rank_lt {C : Config (AgentState n) Opinion n}
    (hRank : InSrank C) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).card = k := by
  classical
  have hinj : Function.Injective (fun u : Fin n => (C u).1.rank) := hRank.ranks_inj
  have hsurj : Function.Surjective (fun u : Fin n => (C u).1.rank) :=
    Finite.injective_iff_surjective.mp hinj
  -- The image of the filter under `rank` equals the target Fin-filter.
  have himg : (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).image
                (fun u => (C u).1.rank)
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hi
      obtain ⟨u, hu⟩ := hsurj i
      refine ⟨u, ?_, hu⟩
      rw [show (C u).1.rank.val = i.val from congrArg Fin.val hu]; exact hi
  rw [← Finset.card_image_of_injective _ hinj, himg, card_Fin_filter_val_lt hk]

/-- An `Srank` configuration with no misordered pairs is in `Sswap`. -/
theorem InSswap_of_InSrank_of_count_zero {C : Config (AgentState n) Opinion n}
    (hRank : InSrank C) (h0 : misorderedCount C = 0) :
    InSswap C := by
  classical
  have hno_mis := (misorderedCount_eq_zero_iff C).mp h0
  -- Set up SA and SR for cardinality comparison.
  let SA : Finset (Fin n) := Finset.univ.filter (fun w => (C w).2 = Opinion.A)
  let SR : Finset (Fin n) := Finset.univ.filter (fun w => (C w).1.rank.val < nAOf C)
  have hSA_card : SA.card = nAOf C := rfl
  have hSR_card : SR.card = nAOf C :=
    card_filter_rank_lt hRank (by have := nAOf_add_nBOf C; omega)
  -- Show SA ⊆ SR via no-misorder counting.
  have hSA_sub : SA ⊆ SR := by
    intro w hw
    simp only [SA, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [SR, Finset.mem_filter, Finset.mem_univ, true_and]
    -- For each B-input agent u: rank u > rank w (no-misorder + ranks_inj).
    have hB_rank_gt : ∀ u, (C u).2 = Opinion.B → (C w).1.rank.val < (C u).1.rank.val := by
      intro u huB
      have hno := hno_mis u w
      have hne : u ≠ w := fun heq => by rw [heq] at huB; rw [hw] at huB; cases huB
      have hrank_ne : (C u).1.rank ≠ (C w).1.rank := fun heq => hne (hRank.ranks_inj heq)
      by_contra hcon
      push_neg at hcon
      have hle : (C u).1.rank.val ≤ (C w).1.rank.val := hcon
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hno ⟨huB, hw, hlt⟩
      · exact hrank_ne (Fin.ext heq)
    -- B-input agents inject into ranks > rank w.
    let SB : Finset (Fin n) := Finset.univ.filter (fun u => (C u).2 = Opinion.B)
    have hSB_card : SB.card = nBOf C := rfl
    have hSB_sub : SB ⊆ Finset.univ.filter (fun u => (C w).1.rank.val < (C u).1.rank.val) := by
      intro u hu
      simp only [SB, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hB_rank_gt u hu
    -- Card of {u : rank u > rank w} ≤ n - rank w.val - 1, which we get via
    -- `card_filter_rank_lt` on the complement.
    have hsum := nAOf_add_nBOf C
    have hwlt : (C w).1.rank.val < n := (C w).1.rank.isLt
    -- Via complement: filter (rank > t) = univ \ filter (rank ≤ t).
    -- Use n - filter(rank ≤ t).card = filter(rank > t).card.
    have hcomp_card :
        (Finset.univ.filter (fun u : Fin n => (C w).1.rank.val < (C u).1.rank.val)).card
        + (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val ≤ (C w).1.rank.val)).card
        = n := by
      have hunion : Finset.univ.filter (fun u : Fin n => (C w).1.rank.val < (C u).1.rank.val)
           ∪ Finset.univ.filter (fun u : Fin n => (C u).1.rank.val ≤ (C w).1.rank.val)
           = Finset.univ := by
        ext u
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        omega
      have hdisj : Disjoint
          (Finset.univ.filter (fun u : Fin n => (C w).1.rank.val < (C u).1.rank.val))
          (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val ≤ (C w).1.rank.val)) := by
        rw [Finset.disjoint_filter]
        intros _ _ hlt hle; omega
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hunion] at hcu
      have hu : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
      omega
    have hle_card : (Finset.univ.filter
        (fun u : Fin n => (C u).1.rank.val ≤ (C w).1.rank.val)).card
        = (C w).1.rank.val + 1 := by
      have hbound : (C w).1.rank.val + 1 ≤ n := by omega
      have heq : (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val ≤ (C w).1.rank.val))
               = Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < (C w).1.rank.val + 1) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [heq, card_filter_rank_lt hRank hbound]
    have hgt_card :
        (Finset.univ.filter (fun u : Fin n => (C w).1.rank.val < (C u).1.rank.val)).card
        = n - (C w).1.rank.val - 1 := by omega
    have hSB_card_le : SB.card ≤ n - (C w).1.rank.val - 1 := by
      rw [← hgt_card]; exact Finset.card_le_card hSB_sub
    rw [hSB_card] at hSB_card_le
    omega
  -- |SA| = |SR| and SA ⊆ SR, so SA = SR.
  have hSA_eq_SR : SA = SR :=
    Finset.eq_of_subset_of_card_le hSA_sub (by rw [hSA_card, hSR_card])
  refine { allSettled := hRank.allSettled, ranks_inj := hRank.ranks_inj, input_rank := ?_ }
  intro v
  constructor
  · intro hA
    have hmem : v ∈ SA := by
      simp only [SA, Finset.mem_filter, Finset.mem_univ, true_and]; exact hA
    rw [hSA_eq_SR] at hmem
    simp only [SR, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  · intro hR
    have hmem : v ∈ SR := by
      simp only [SR, Finset.mem_filter, Finset.mem_univ, true_and]; exact hR
    rw [← hSA_eq_SR] at hmem
    simp only [SA, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem

end SSEM

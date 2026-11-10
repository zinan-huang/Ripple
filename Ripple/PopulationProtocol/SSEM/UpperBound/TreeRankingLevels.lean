/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heap levels and the tree-ranking potential (P2 Lemma 6.1, B41)

Ranks `0, …, n-1` form a heap; rank `r` is on level `d` when `2^d ≤ r + 1 < 2^(d+1)`
(`InLevel`). `unasg k d` is the number of unassigned ranks `< n` on level `d`, and the potential
of P2 Lemma 6.1 in additive form is

`phiT k = Σ_{d ≤ H} H2(unasg k d) / uL d`,  `H2 i = Σ_{j=1}^{i} 1/j²`,
`uL d = 2^(H-d) - 1` for `d < H`, `uL H = 1`, `H = ⌊log₂ (n+1)⌋`

(levels `0, …, H-1` are complete). Facts proved here, for a valid tree with all agents computing:

* `phiT_mono`, `phiT_drop`: `phiT` does not increase when the assigned set grows, and drops by
  `1/(i² uL d)` when an unassigned rank of level `d` (with `i` unassigned ranks there) is assigned;
* `card_uns_ge`: the number `U` of Unsettled agents is at least `i · uL d` for every level `d`
  (P2: the subtrees of the unassigned level-`d` ranks are unassigned and disjoint);
* `card_unasg_le_rec`: on the least incomplete level `d₀`, the `i` unassigned ranks have at least
  `i / 2` distinct recruiters (their parents);
* `phiT_le`: `phiT k ≤ (7/4) (55/21)` (from `H2 ≤ 7/4` and `Σ_k 1/(2^k - 1) ≤ 34/21`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingCore
import Ripple.PopulationProtocol.SSEM.UpperBound.EpochCompose

namespace Ripple.PopulationProtocol.SSEM

open scoped BigOperators

variable {n : ℕ}

/-! ### Levels -/

/-- Rank `r` is on heap level `d`. -/
def InLevel (d r : ℕ) : Prop := 2 ^ d ≤ r + 1 ∧ r + 1 < 2 ^ (d + 1)

instance (d : ℕ) : DecidablePred (InLevel d) := fun _ => instDecidableAnd

theorem inLevel_unique {d d' r : ℕ} (h : InLevel d r) (h' : InLevel d' r) : d = d' := by
  rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
  · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show d + 1 ≤ d' by omega)
    have := h.2; have := h'.1; omega
  · exact heq
  · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show d' + 1 ≤ d by omega)
    have := h.1; have := h'.2; omega

theorem inLevel_log (r : ℕ) : InLevel (Nat.log 2 (r + 1)) r :=
  ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- The last complete level is `topL n - 1`. -/
def topL (n : ℕ) : ℕ := Nat.log 2 (n + 1)

theorem two_pow_topL_le (n : ℕ) : 2 ^ topL n ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)

theorem lt_two_pow_topL (n : ℕ) : n + 1 < 2 ^ (topL n + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem inLevel_le_topL {d r : ℕ} (hr : r < n) (h : InLevel d r) : d ≤ topL n := by
  by_contra hd
  have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show topL n + 1 ≤ d by omega)
  have := lt_two_pow_topL n
  have := h.1
  omega

/-- Levels below `topL n` are complete. -/
theorem lt_of_inLevel_complete {d r : ℕ} (hd : d + 1 ≤ topL n) (h : InLevel d r) : r < n := by
  have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hd
  have := two_pow_topL_le n
  have := h.2
  omega

theorem inLevel_child {d r c : ℕ} (h : InLevel d r) (hc : c < 2) :
    InLevel (d + 1) (2 * r + c + 1) := by
  obtain ⟨h1, h2⟩ := h
  constructor <;> rw [pow_succ] <;> omega

theorem inLevel_parent {d r : ℕ} (h : InLevel (d + 1) r) : InLevel d ((r - 1) / 2) := by
  obtain ⟨h1, h2⟩ := h
  rw [pow_succ] at h1
  rw [pow_succ, pow_succ] at h2
  have := Nat.one_le_two_pow (n := d)
  constructor
  · have : (r - 1) / 2 + 1 = (r + 1) / 2 := by omega
    rw [this]; omega
  · rw [pow_succ]; omega

/-! ### Unassigned ranks per level -/

section Count

open Classical in
/-- The unassigned ranks `< n` on level `d`. -/
noncomputable def unasgSet (k : Fin n → AgentState n) (d : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun r => InLevel d r ∧ ¬ Asg k r)

/-- The number of unassigned ranks on level `d`. -/
noncomputable def unasg (k : Fin n → AgentState n) (d : ℕ) : ℕ := (unasgSet k d).card

theorem mem_unasgSet {k : Fin n → AgentState n} {d r : ℕ} :
    r ∈ unasgSet k d ↔ r < n ∧ InLevel d r ∧ ¬ Asg k r := by
  classical
  simp [unasgSet]

theorem unasg_mono {k k' : Fin n → AgentState n} (hmono : ∀ j, Asg k j → Asg k' j) (d : ℕ) :
    unasg k' d ≤ unasg k d := by
  apply Finset.card_le_card
  intro r hr
  rw [mem_unasgSet] at hr ⊢
  exact ⟨hr.1, hr.2.1, fun h => hr.2.2 (hmono r h)⟩

theorem unasg_lt {k k' : Fin n → AgentState n} (hmono : ∀ j, Asg k j → Asg k' j) {d r : ℕ}
    (hr : r < n) (hl : InLevel d r) (hk : ¬ Asg k r) (hk' : Asg k' r) :
    unasg k' d + 1 ≤ unasg k d := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [mem_unasgSet] at hx ⊢
    exact ⟨hx.1, hx.2.1, fun h => hx.2.2 (hmono x h)⟩
  · have := hsub (mem_unasgSet.mpr ⟨hr, hl, hk⟩)
    exact (mem_unasgSet.mp this).2.2 hk'

/-! ### The potential -/

/-- `H2 i = Σ_{j=1}^{i} 1/j²`. -/
noncomputable def H2 (i : ℕ) : ℝ := ∑ j ∈ Finset.range i, 1 / ((j : ℝ) + 1) ^ 2

theorem H2_succ (i : ℕ) : H2 (i + 1) = H2 i + 1 / ((i : ℝ) + 1) ^ 2 := by
  unfold H2; rw [Finset.sum_range_succ]

theorem H2_nonneg (i : ℕ) : 0 ≤ H2 i :=
  Finset.sum_nonneg fun j _ => by positivity

theorem H2_mono {i j : ℕ} (h : i ≤ j) : H2 i ≤ H2 j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => by positivity

theorem H2_le (i : ℕ) : H2 i ≤ 7 / 4 := by
  have key : ∀ i, 2 ≤ i → H2 i ≤ 7 / 4 - 1 / (i : ℝ) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => unfold H2; norm_num [Finset.sum_range_succ]
    | succ m hm ih =>
      rw [H2_succ]
      have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have : 1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      push_cast at this ⊢
      linarith
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i <;> unfold H2 <;> norm_num [Finset.sum_range_succ]
  · have := key i hi
    have : 0 ≤ 1 / (i : ℝ) := by positivity
    linarith

/-- The weight of level `d`: the minimal number of unassigned ranks per unassigned level-`d`
rank. -/
noncomputable def uL (n d : ℕ) : ℝ := if d < topL n then (2 : ℝ) ^ (topL n - d) - 1 else 1

theorem one_le_uL (n d : ℕ) : 1 ≤ uL n d := by
  unfold uL
  split_ifs with h
  · have : (2 : ℝ) ≤ 2 ^ (topL n - d) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (topL n - d) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  · exact le_rfl

/-- The tree-ranking potential (divided by `n (n-1)`). -/
noncomputable def phiT (k : Fin n → AgentState n) : ℝ :=
  ∑ d ∈ Finset.range (topL n + 1), H2 (unasg k d) / uL n d

theorem phiT_nonneg (k : Fin n → AgentState n) : 0 ≤ phiT k :=
  Finset.sum_nonneg fun d _ => div_nonneg (H2_nonneg _) (by linarith [one_le_uL n d])

theorem phiT_mono {k k' : Fin n → AgentState n} (hmono : ∀ j, Asg k j → Asg k' j) :
    phiT k' ≤ phiT k :=
  Finset.sum_le_sum fun d _ =>
    div_le_div_of_nonneg_right (H2_mono (unasg_mono hmono d)) (by linarith [one_le_uL n d])

theorem phiT_drop {k k' : Fin n → AgentState n} (hmono : ∀ j, Asg k j → Asg k' j) {d r : ℕ}
    (hr : r < n) (hl : InLevel d r) (hk : ¬ Asg k r) (hk' : Asg k' r) :
    phiT k' + 1 / ((unasg k d : ℝ) ^ 2 * uL n d) ≤ phiT k := by
  have hd : d ∈ Finset.range (topL n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (inLevel_le_topL hr hl))
  have hlt := unasg_lt hmono hr hl hk hk'
  have hu := one_le_uL n d
  unfold phiT
  rw [← Finset.add_sum_erase _ _ hd, ← Finset.add_sum_erase _ _ hd]
  have hrest : ∑ x ∈ (Finset.range (topL n + 1)).erase d, H2 (unasg k' x) / uL n x ≤
      ∑ x ∈ (Finset.range (topL n + 1)).erase d, H2 (unasg k x) / uL n x :=
    Finset.sum_le_sum fun x _ =>
      div_le_div_of_nonneg_right (H2_mono (unasg_mono hmono x)) (by linarith [one_le_uL n x])
  have hterm : H2 (unasg k' d) / uL n d + 1 / ((unasg k d : ℝ) ^ 2 * uL n d) ≤
      H2 (unasg k d) / uL n d := by
    obtain ⟨m, hm⟩ : ∃ m, unasg k d = m + 1 := ⟨unasg k d - 1, by omega⟩
    have h1 : H2 (unasg k' d) ≤ H2 m := H2_mono (by omega)
    rw [hm, H2_succ]
    push_cast
    rw [show 1 / (((m : ℝ) + 1) ^ 2 * uL n d) = (1 / ((m : ℝ) + 1) ^ 2) / uL n d by
      rw [div_div]]
    rw [← add_div, div_le_div_iff_of_pos_right (by linarith)]
    linarith
  linarith

/-- `g H = Σ_{d < H} 1/(2^(H-d) - 1) = Σ_{k=1}^{H} 1/(2^k - 1)`. -/
noncomputable def gSum (H : ℕ) : ℝ := ∑ d ∈ Finset.range H, 1 / ((2 : ℝ) ^ (H - d) - 1)

theorem gSum_succ (H : ℕ) : gSum (H + 1) = gSum H + 1 / ((2 : ℝ) ^ (H + 1) - 1) := by
  unfold gSum
  rw [Finset.sum_range_succ']
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [show H + 1 - (d + 1) = H - d by omega]

theorem gSum_le (H : ℕ) : gSum H + (8 / 7) / 2 ^ H ≤ 34 / 21 := by
  have key : ∀ H, 2 ≤ H → gSum H + (8 / 7) / 2 ^ H ≤ 34 / 21 := by
    intro H hH
    induction H, hH using Nat.le_induction with
    | base => unfold gSum; norm_num [Finset.sum_range_succ]
    | succ m hm ih =>
      rw [gSum_succ]
      have h4 : (4 : ℝ) ≤ 2 ^ m := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
      have hp : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      rw [hp]
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      have hx : 1 / (2 * (2 : ℝ) ^ m - 1) ≤ (4 / 7) / 2 ^ m := by
        rw [div_le_div_iff₀ (by linarith) hpos]
        nlinarith
      have hy : (8 / 7) / (2 * (2 : ℝ) ^ m) = (4 / 7) / 2 ^ m := by
        field_simp; ring
      have hz : (8 / 7) / (2 : ℝ) ^ m = (4 / 7) / 2 ^ m + (4 / 7) / 2 ^ m := by ring
      rw [hy]
      linarith
  rcases Nat.lt_or_ge H 2 with hH | hH
  · interval_cases H <;> unfold gSum <;> norm_num [Finset.sum_range_succ]
  · exact key H hH

theorem sum_inv_uL_le (n : ℕ) :
    ∑ d ∈ Finset.range (topL n + 1), 1 / uL n d ≤ 55 / 21 := by
  rw [Finset.sum_range_succ]
  have e1 : 1 / uL n (topL n) = 1 := by unfold uL; simp
  have e2 : ∑ d ∈ Finset.range (topL n), 1 / uL n d = gSum (topL n) := by
    unfold gSum
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_range] at hd
    unfold uL
    rw [if_pos hd]
  rw [e1, e2]
  have := gSum_le (topL n)
  have : (0 : ℝ) ≤ (8 / 7) / 2 ^ topL n := by positivity
  linarith

/-- **The initial potential**: `phiT ≤ (7/4)(55/21) = 55/12`. -/
theorem phiT_le (k : Fin n → AgentState n) : phiT k ≤ 55 / 12 := by
  unfold phiT
  calc ∑ d ∈ Finset.range (topL n + 1), H2 (unasg k d) / uL n d
      ≤ ∑ d ∈ Finset.range (topL n + 1), (7 / 4) * (1 / uL n d) := by
        apply Finset.sum_le_sum
        intro d _
        have hu := one_le_uL n d
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right (H2_le _) (by positivity)
    _ = (7 / 4) * ∑ d ∈ Finset.range (topL n + 1), 1 / uL n d := by rw [Finset.mul_sum]
    _ ≤ (7 / 4) * (55 / 21) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_uL_le n) (by norm_num)
    _ = 55 / 12 := by norm_num

end Count

end Ripple.PopulationProtocol.SSEM

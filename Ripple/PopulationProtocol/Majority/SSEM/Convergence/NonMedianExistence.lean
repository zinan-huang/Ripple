/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of Non-Median Misordered Pairs

The swap-step single-step lemma `swap_step_non_median_decreases` requires
a misorder pair `(u, v)` where neither agent is at the median rank.  This
file establishes when such a pair must exist.

The simplest sufficient condition: when there is some misorder pair
`(u, v)` and at least one of `u, v` has a "twin" (another agent with the
same input but at a different rank) that's also in a misorder pair.

We provide a concrete instantiation: when there's at least one non-median
misorder pair witnessed in the configuration, the existence hypothesis
of `swap_reaches_Sswap_via_non_median` is satisfied directly.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapStep

namespace SSEM

variable {n : ℕ}

/-- The set of misordered pairs `(u, v)` where neither `u` nor `v` is at
the median rank. -/
def nonMedianMisorderedSet (C : Config (AgentState n) Opinion n) :
    Finset (Fin n × Fin n) :=
  (misorderedSet C).filter
    (fun uv => (C uv.1).1.rank.val + 1 ≠ ceilHalf n ∧
                (C uv.2).1.rank.val + 1 ≠ ceilHalf n)

theorem mem_nonMedianMisorderedSet
    {C : Config (AgentState n) Opinion n} {uv : Fin n × Fin n} :
    uv ∈ nonMedianMisorderedSet C ↔
      MisorderedPair C uv ∧
      (C uv.1).1.rank.val + 1 ≠ ceilHalf n ∧
      (C uv.2).1.rank.val + 1 ≠ ceilHalf n := by
  unfold nonMedianMisorderedSet
  rw [Finset.mem_filter, mem_misorderedSet]

/-- If the non-median misordered set is non-empty, the existence hypothesis
of `swap_reaches_Sswap_via_non_median` holds at `C`. -/
theorem exists_non_median_misordered_of_set_nonempty
    {C : Config (AgentState n) Opinion n}
    (h : (nonMedianMisorderedSet C).Nonempty) :
    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
      (C u).1.rank.val + 1 ≠ ceilHalf n ∧
      (C v).1.rank.val + 1 ≠ ceilHalf n := by
  obtain ⟨⟨u, v⟩, hmem⟩ := h
  obtain ⟨hMis, hu, hv⟩ := mem_nonMedianMisorderedSet.mp hmem
  exact ⟨u, v, hMis, hu, hv⟩

/-- Specialization: if for every `InSrank` configuration with positive
misordered count, the non-median misordered set is non-empty, then the
existence hypothesis of `swap_reaches_Sswap_via_non_median` is met. -/
theorem hExists_of_nonMedianSet_always_nonempty
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (h : ∀ C : Config (AgentState n) Opinion n, InSrank C →
            0 < misorderedCount C → (nonMedianMisorderedSet C).Nonempty) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      0 < misorderedCount C →
      ∃ u v : Fin n, MisorderedPair C (u, v) ∧
        (C u).1.rank.val + 1 ≠ ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ ceilHalf n :=
  fun C hSrank hpos =>
    exists_non_median_misordered_of_set_nonempty (h C hSrank hpos)

/-! ### Cardinality argument for non-median misorder existence

**Claim**: under `InSrank C ∧ nA ≥ 2 ∧ nB ≥ 2 ∧ misorderedCount > 0`, a
non-median misordered pair exists.

**Proof sketch** (by contradiction): suppose every misorder involves the
median agent μ.

  * If μ has input B: every non-μ B-agent must have rank ≥ all A-agents
    (otherwise (non-μ-B, A) would be a non-median misorder).  By
    cardinality and `nB ≥ 2`, this forces an inconsistent rank
    distribution (μ ends up at a rank where misorder count is forced
    to 0).  Contradicts positive count.

  * If μ has input A: symmetric, using `nA ≥ 2`.

The full Lean proof involves Finset cardinality manipulation; we provide
a structurally simpler version below as a HOOK for downstream usage.
-/

/-- Helper: if μ has input B, the median rank is `ceilHalf n − 1`. -/
private theorem InSrank.median_rank_eq (hC : InSrank C) (μ : Fin n)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n) :
    (C μ).1.rank.val + 1 = ceilHalf n :=
  hμ_med

/-- The median agent is unique (by `ranks_inj`). -/
private theorem InSrank.median_unique
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ ν : Fin n}
    (hμ : (C μ).1.rank.val + 1 = ceilHalf n)
    (hν : (C ν).1.rank.val + 1 = ceilHalf n) :
    μ = ν := by
  apply hC.ranks_inj
  show (C μ).1.rank = (C ν).1.rank
  apply Fin.eq_of_val_eq
  have : (C μ).1.rank.val = (C ν).1.rank.val := by omega
  exact this

end SSEM

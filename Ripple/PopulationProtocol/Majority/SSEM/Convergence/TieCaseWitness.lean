/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Witness for Even-n Tie Case

When `nA = nB` (exact tie) and the median is wrong, we construct the
median-pair witness with disagreeing inputs needed by
`decision_step_at_median_pair_even_tie_decreases`.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.DecisionTieCase
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.MedianWitnesses

namespace SSEM

variable {n : ℕ}

/-- At InSswap with tie (nA = nB), the lower median has input A and the
upper median has input B — their inputs disagree. -/
theorem evenCase_witness_when_median_wrong_tie
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0) (hn4 : 4 ≤ n)
    (hTie : nAOf C = nBOf C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                 (C μ).1.answer ≠ majorityAnswer C) :
    ∃ u v : Fin n, u ≠ v ∧
      (C u).1.rank.val + 1 = n / 2 ∧
      (C v).1.rank.val + 1 = n / 2 + 1 ∧
      (C u).2 ≠ (C v).2 ∧
      ((C u).1.answer ≠ majorityAnswer C ∨
       (C v).1.answer ≠ majorityAnswer C) := by
  have h_n_pos : 0 < n := by omega
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have h_lower_lt : n / 2 - 1 < n := by omega
  have h_upper_lt : n / 2 < n := by omega
  have ⟨u, hu_rank⟩ := hC.toInSrank.exists_at_rank h_n_pos (⟨n / 2 - 1, h_lower_lt⟩ : Fin n)
  have ⟨v, hv_rank⟩ := hC.toInSrank.exists_at_rank h_n_pos (⟨n / 2, h_upper_lt⟩ : Fin n)
  have huv : u ≠ v := by
    intro h_eq; rw [h_eq] at hu_rank
    have h1 : (C v).1.rank.val = n / 2 - 1 := by rw [hu_rank]
    have h2 : (C v).1.rank.val = n / 2 := by rw [hv_rank]
    omega
  have hu_med : (C u).1.rank.val + 1 = n / 2 := by
    rw [hu_rank]; simp; omega
  have hv_upper : (C v).1.rank.val + 1 = n / 2 + 1 := by rw [hv_rank]
  have h_nA : nAOf C = n / 2 := by have := nAOf_add_nBOf C; omega
  have h_inputs_disagree : (C u).2 ≠ (C v).2 := by
    have hu_A : (C u).2 = Opinion.A := (hC.input_rank u).mpr (by omega)
    have hv_B : (C v).2 = Opinion.B := by
      have h_not_A : ¬ ((C v).1.rank.val < nAOf C) := by omega
      exact match h : (C v).2 with
        | .A => absurd ((hC.input_rank v).mp h) h_not_A
        | .B => rfl
    rw [hu_A, hv_B]; exact fun h => Opinion.noConfusion h
  -- The wrong agent is at the median rank (ceilHalf n = n/2 for even n).
  -- The lower median u has rank n/2 - 1, and rank.val + 1 = n/2 = ceilHalf n.
  -- So the wrong agent μ satisfying h_med_wrong is u (same rank).
  obtain ⟨μ, hμ_rank, hμ_wrong⟩ := h_med_wrong
  have hμ_is_u : μ = u := by
    apply hC.ranks_inj; apply Fin.eq_of_val_eq
    have h1 : (C μ).1.rank.val = ceilHalf n - 1 := by omega
    have h2 : (C u).1.rank.val = n / 2 - 1 := by
      have := congrArg Fin.val hu_rank; simp at this; omega
    rw [h1, hceil, h2]
  refine ⟨u, v, huv, hu_med, hv_upper, h_inputs_disagree, ?_⟩
  left; rw [← hμ_is_u]; exact hμ_wrong

end SSEM

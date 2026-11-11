import Ripple.PopulationProtocol.SSEM.UpperBound.PaperInstance

/-!
# Exact state counts of the finite-state P_EM protocol

`card_PEMFinState_le` and `card_PEMPaperFin_le` bound the state type from above; the
sum-type cardinality is exact, and these theorems give it.
-/

namespace Ripple.PopulationProtocol.SSEM

/-- There are `n - 1` non-median ranks, with truncated subtraction also
covering `n = 0`. No population-positivity hypothesis is exported. -/
private theorem card_PEM_nonmedian_ranks (n : ℕ) :
    Fintype.card {r : Fin n // r.val + 1 ≠ ceilHalf n} = n - 1 := by
  classical
  cases n with
  | zero => simp
  | succ n =>
      let m : Fin (n + 1) := medianRank (Nat.succ_pos n)
      have hm : m.val + 1 = ceilHalf (n + 1) :=
        medianRank_spec (Nat.succ_pos n)
      have hmem : ∀ r : Fin (n + 1),
          r ∈ (Finset.univ.erase m) ↔ r.val + 1 ≠ ceilHalf (n + 1) := by
        intro r
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hne heq
          apply hne
          apply Fin.ext
          omega
        · intro hne heq
          apply hne
          simpa only [heq] using hm
      calc
        Fintype.card {r : Fin (n + 1) // r.val + 1 ≠ ceilHalf (n + 1)} =
            (Finset.univ.erase m).card :=
          Fintype.card_of_subtype _ hmem
        _ = (n + 1) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ m),
            Finset.card_univ, Fintype.card_fin]

/-- Exact cardinality of the existing finite role-indexed state type.
The first summand counts non-median settled ranks, hence `n - 1`, not `n`. -/
theorem card_PEMFinState_eq (n T E R D : ℕ) :
    Fintype.card (PEMFinState n T E R D) =
      24 * (n - 1) + 24 * (T + 1) + 8 * (E + 1) + 8 * R + 8 * (D + 1) := by
  classical
  simp only [PEMFinState, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, card_PEM_nonmedian_ranks, card_leader, card_answer]
  ring

/-- Exact cardinality of the paper-parameter instance, with no assumptions
on `n`, `trank`, `e`, or `d` beyond their natural-number types. -/
theorem card_PEMPaperFin_eq (n trank e d : ℕ) :
    Fintype.card
        (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) =
      24 * (n - 1) + 24 * (7 * (trank + 4) + 1) + 8 * (e * n + 1) +
        8 * rmaxPaper n + 8 * (d * n + 1) :=
  card_PEMFinState_eq n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)

end Ripple.PopulationProtocol.SSEM

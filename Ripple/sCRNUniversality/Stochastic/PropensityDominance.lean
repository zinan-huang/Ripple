/-
  Propensity dominance for parallel-composed CRNs.
-/
import Ripple.sCRNUniversality.Stochastic.Propensity

open Classical

namespace Ripple.sCRNUniversality.Stochastic

open scoped BigOperators

universe u v

variable {S : Type u} [Fintype S]

noncomputable def sigmaErasePropensitySum
    {A : Type v} [Fintype A]
    (Ns : A → Network S) (a₀ : A) (i₀ : (Ns a₀).I) (z : State S) : NNRat :=
  letI : DecidableEq A := Classical.decEq _
  letI : ∀ a, DecidableEq ((Ns a).I) := fun a => Classical.decEq _
  (Finset.univ (α := (Network.sigma Ns).I)).erase ⟨a₀, i₀⟩ |>.sum
    (fun j => ((Network.sigma Ns).rxn j).propensity z)

theorem sigma_propensity_dominance_of_quasi_and_bound
    {A : Type v} [Fintype A]
    (Ns : A → Network S) (a₀ : A) (i₀ : (Ns a₀).I) (z : State S)
    (ε : NNRat)
    (hQuasi : ∀ j : (Ns a₀).I, j ≠ i₀ → ¬ (Ns a₀).EnabledAt z j)
    (hPos : ∀ a i, ((Ns a).rxn i).hasPositiveRate)
    (hOtherBound : ∀ a : A, a ≠ a₀ → (Ns a).totalPropensity z ≤ ε) :
    sigmaErasePropensitySum Ns a₀ i₀ z ≤
      (Fintype.card A - 1) * ε := by
  unfold sigmaErasePropensitySum
  -- After unfold, the goal has letI with Classical.decEq inside.
  -- All sub-proofs must use the same instances.
  -- Decompose: erase sum ≤ sigma sum ≤ totalPropensity sum ≤ bound
  have hsigma_eq : ((Finset.univ.erase a₀).sigma (fun (_ : A) => Finset.univ)).sum
      (fun (x : Sigma fun a => (Ns a).I) => ((Ns x.1).rxn x.2).propensity z) =
      (Finset.univ.erase a₀).sum (fun a => (Ns a).totalPropensity z) :=
    Finset.sum_sigma _ _ _
  have h_sub : (Finset.univ.erase (⟨a₀, i₀⟩ : (Network.sigma Ns).I)).sum
      (fun j => ((Network.sigma Ns).rxn j).propensity z) ≤
      ((Finset.univ.erase a₀).sigma (fun (_ : A) => Finset.univ)).sum
        (fun j => ((Network.sigma Ns).rxn j).propensity z) := by
    apply Finset.sum_le_sum_of_ne_zero
    intro ⟨a, j⟩ hmem hne
    simp only [Finset.mem_sigma, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
    intro heq
    exfalso; apply hne; subst heq
    rw [Network.sigma_rxn]
    exact Reaction.propensity_eq_zero_of_not_enabled
      (hQuasi j (fun hji => absurd (hji ▸ hmem) (Finset.notMem_erase _ _)))
  have hsig_conv : ((Finset.univ.erase a₀).sigma (fun (_ : A) => Finset.univ)).sum
      (fun j => ((Network.sigma Ns).rxn j).propensity z) =
      ((Finset.univ.erase a₀).sigma (fun (_ : A) => Finset.univ)).sum
        (fun (x : Sigma fun a => (Ns a).I) => ((Ns x.1).rxn x.2).propensity z) :=
    Finset.sum_congr rfl (fun ⟨a, j⟩ _ => by simp [Network.sigma_rxn])
  have h1 := le_trans h_sub (le_of_eq (hsig_conv.trans hsigma_eq))
  have h2 : (Finset.univ.erase a₀).sum (fun a => (Ns a).totalPropensity z) ≤
      (Fintype.card A - 1) * ε := by
    calc (Finset.univ.erase a₀).sum (fun a => (Ns a).totalPropensity z)
        ≤ (Finset.univ.erase a₀).sum (fun _ => ε) :=
          Finset.sum_le_sum fun a ha => hOtherBound a (Finset.ne_of_mem_erase ha)
      _ = (Fintype.card A - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a₀),
            Finset.card_univ, nsmul_eq_mul]
          norm_cast
  -- Bridge the DecidableEq diamond between the goal and h1
  have key := le_trans h1 h2
  convert key using 2
  congr 1
  funext a b; exact Subsingleton.elim _ _

end Ripple.sCRNUniversality.Stochastic

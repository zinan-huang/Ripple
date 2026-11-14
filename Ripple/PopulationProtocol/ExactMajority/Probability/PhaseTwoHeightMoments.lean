import Ripple.PopulationProtocol.ExactMajority.Probability.Phase0Window

/-!
# Exact weighted participation of a distinguished class

The responder of a selected class member ranges over C-1 other class members,
so the two orientations contribute exactly 2(C-1)/(n(n-1)) times the class
weight. This includes C=0 and C=1 without a division by C.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem sumOf_eq_sum_count (c : Config Λ) (g : Λ → ℝ≥0∞) :
    Config.sumOf g c = ∑ a : Λ, g a * (c.count a : ℝ≥0∞) := by
  classical
  symm
  unfold Config.sumOf
  rw [Finset.sum_multiset_map_count c g]
  rw [← Finset.sum_subset (Finset.subset_univ c.toFinset)
    (fun a _ ha => by
      rw [Multiset.mem_toFinset] at ha
      rw [Config.count, Multiset.count_eq_zero_of_notMem ha]
      simp)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Config.count, nsmul_eq_mul, mul_comm]

theorem weighted_first_count (c : Config Λ) (g : Λ → ℝ≥0∞) :
    (∑ p : Λ × Λ, g p.1 * (c.interactionCount p.1 p.2 : ℝ≥0∞)) =
      Config.sumOf g c * ((c.card - 1 : ℕ) : ℝ≥0∞) := by
  classical
  rw [show (Finset.univ : Finset (Λ × Λ)) = Finset.univ ×ˢ Finset.univ
    from Finset.univ_product_univ.symm, Finset.sum_product]
  have hinner (a : Λ) :
      (∑ b : Λ, g a * (c.interactionCount a b : ℝ≥0∞)) =
        (g a * (c.count a : ℝ≥0∞)) * ((c.card - 1 : ℕ) : ℝ≥0∞) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, Config.sum_interactionCount_right, Nat.cast_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.sum_mul,
    ← sumOf_eq_sum_count]

theorem interactionCount_swap (c : Config Λ) (a b : Λ) :
    c.interactionCount a b = c.interactionCount b a := by
  unfold Config.interactionCount
  by_cases h : a = b
  · subst b
    rfl
  · rw [if_neg h, if_neg (Ne.symm h), mul_comm]

theorem weighted_second_count (c : Config Λ) (g : Λ → ℝ≥0∞) :
    (∑ p : Λ × Λ, g p.2 * (c.interactionCount p.1 p.2 : ℝ≥0∞)) =
      Config.sumOf g c * ((c.card - 1 : ℕ) : ℝ≥0∞) := by
  rw [← weighted_first_count c g]
  rw [← Equiv.sum_comp (Equiv.prodComm Λ Λ)
    (fun p : Λ × Λ => g p.1 * (c.interactionCount p.1 p.2 : ℝ≥0∞))]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [interactionCount_swap]

theorem filtered_interactionCount (c : Config Λ) (P : Λ → Prop) [DecidablePred P]
    (a b : Λ) :
    Config.interactionCount (c.filter P) a b =
      if P a ∧ P b then c.interactionCount a b else 0 := by
  by_cases ha : P a
  · by_cases hb : P b
    · simp [Config.interactionCount, Config.count, Multiset.count_filter, ha, hb]
    · by_cases heq : a = b
      · subst b
        exact (hb ha).elim
      · simp [Config.interactionCount, Config.count, Multiset.count_filter, ha, hb, heq]
  · by_cases heq : a = b
    · subst b
      simp [Config.interactionCount, Config.count, Multiset.count_filter, ha]
    · simp [Config.interactionCount, Config.count, Multiset.count_filter, ha, heq]

theorem sumOf_filter_eq_of_supported (c : Config Λ) (P : Λ → Prop) [DecidablePred P]
    (g : Λ → ℝ≥0∞) (hg : ∀ a, ¬ P a → g a = 0) :
    Config.sumOf g (c.filter P) = Config.sumOf g c := by
  rw [sumOf_eq_sum_count, sumOf_eq_sum_count]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P a
  · simp [Config.count, Multiset.count_filter, ha]
  · simp [Config.count, Multiset.count_filter, ha, hg a ha]

theorem selected_class_weight_sum (c : Config Λ) (P : Λ → Prop) [DecidablePred P]
    (g : Λ → ℝ≥0∞) (hg : ∀ a, ¬ P a → g a = 0) :
    (∑ p : Λ × Λ,
        (if P p.1 ∧ P p.2 then g p.1 + g p.2 else 0) *
          c.interactionProb p.1 p.2) =
      (2 * ((c.countP P - 1 : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)) *
        Config.sumOf g c := by
  classical
  let d := c.filter P
  have hdcard : d.card = c.countP P :=
    (Multiset.countP_eq_card_filter P c).symm
  have hterm (p : Λ × Λ) :
      (if P p.1 ∧ P p.2 then g p.1 + g p.2 else 0) *
          c.interactionProb p.1 p.2 =
        ((g p.1 + g p.2) * (Config.interactionCount d p.1 p.2 : ℝ≥0∞)) /
          (c.totalPairs : ℝ≥0∞) := by
    dsimp only [d]
    rw [filtered_interactionCount]
    by_cases hp : P p.1 ∧ P p.2
    · simp only [if_pos hp, Config.interactionProb, mul_div_assoc]
    · simp only [if_neg hp, Nat.cast_zero, zero_mul, mul_zero, zero_div, ENNReal.zero_div]
  have hsum :
      (∑ p : Λ × Λ, (g p.1 + g p.2) *
        (Config.interactionCount d p.1 p.2 : ℝ≥0∞)) =
        2 * ((d.card - 1 : ℕ) : ℝ≥0∞) * Config.sumOf g d := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, weighted_first_count, weighted_second_count]
    ring
  calc (∑ p : Λ × Λ,
        (if P p.1 ∧ P p.2 then g p.1 + g p.2 else 0) *
          c.interactionProb p.1 p.2) =
      ∑ p : Λ × Λ, ((g p.1 + g p.2) *
        (Config.interactionCount d p.1 p.2 : ℝ≥0∞)) / (c.totalPairs : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun p _ => hterm p)
    _ = (∑ p : Λ × Λ, (g p.1 + g p.2) *
        (Config.interactionCount d p.1 p.2 : ℝ≥0∞)) / (c.totalPairs : ℝ≥0∞) := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    _ = (2 * ((d.card - 1 : ℕ) : ℝ≥0∞) * Config.sumOf g d) /
        (c.totalPairs : ℝ≥0∞) := by rw [hsum]
    _ = (2 * ((c.countP P - 1 : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)) *
        Config.sumOf g c := by
      rw [hdcard, sumOf_filter_eq_of_supported c P g hg]
      simp only [div_eq_mul_inv]
      ring

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

end

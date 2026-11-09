/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Running a protocol along a scheduler prefix

The uniform-scheduler chain is a deterministic function of an i.i.d. sequence of scheduler
pairs (the random-mapping representation). This file makes that explicit for finite windows:

* `runPrefix P C₀ K σ` is the configuration after the `K` interactions of the prefix `σ`;
* `probNotHitBy_le_prefixMass`: the probability of not having hit `Goal` within `K` steps is
  at most the product-measure mass of the prefixes whose final configuration is not in `Goal`;
* `schedulerPrefix_lintegral_prod`: the product measure factorizes on product integrands, the
  engine of first-moment and exponential-moment bounds over prefix events.

Window statements of the form "from `C₀`, within `K` interactions, every prefix outside a set of
small product mass ends in `Goal`" are thereby reduced to deterministic statements about
`runPrefix` plus a computation in the product measure.
-/

import Ripple.PopulationProtocol.SSEM.Probability.SchedulerTrace

namespace Ripple.PopulationProtocol.SSEM
namespace Probability

open scoped BigOperators ENNReal
open PMF

variable {Q X Y : Type*} {n : ℕ}

/-- The configuration reached from `C₀` by the `K` interactions of the prefix `σ`. -/
def runPrefix (P : Protocol Q X Y) (C₀ : Config Q X n) :
    (K : ℕ) → SchedulerPrefix n K → Config Q X n
  | 0, _ => C₀
  | K + 1, σ => (runPrefix P C₀ K (Fin.init σ)).step P (σ (Fin.last K)).1 (σ (Fin.last K)).2

@[simp] theorem runPrefix_zero (P : Protocol Q X Y) (C₀ : Config Q X n)
    (σ : SchedulerPrefix n 0) : runPrefix P C₀ 0 σ = C₀ := rfl

theorem runPrefix_succ (P : Protocol Q X Y) (C₀ : Config Q X n) (K : ℕ)
    (σ : SchedulerPrefix n (K + 1)) :
    runPrefix P C₀ (K + 1) σ =
      (runPrefix P C₀ K (Fin.init σ)).step P (σ (Fin.last K)).1 (σ (Fin.last K)).2 := rfl

@[simp] theorem runPrefix_snoc (P : Protocol Q X Y) (C₀ : Config Q X n) (K : ℕ)
    (σ : SchedulerPrefix n K) (p : Fin n × Fin n) :
    runPrefix P C₀ (K + 1) (Fin.snoc σ p) = (runPrefix P C₀ K σ).step P p.1 p.2 := by
  rw [runPrefix_succ, Fin.init_snoc, Fin.snoc_last]

/-- On the support of the coupled trace, the configuration is the run of the prefix, and a
false hit flag means the current configuration is not in `Goal`. -/
theorem schedulerTraceDist_support_run (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ (K : ℕ) (S : SchedulerTraceState Q X n K),
      S ∈ (schedulerTraceDist P hn C₀ Goal K).support →
        S.1.1 = runPrefix P C₀ K S.2 ∧ (S.1.2 = false → ¬ Goal S.1.1)
  | 0, S, hS => by
      classical
      rw [schedulerTraceDist, PMF.support_pure, Set.mem_singleton_iff] at hS
      subst hS
      refine ⟨rfl, ?_⟩
      intro h
      simpa using h
  | K + 1, S, hS => by
      classical
      rw [schedulerTraceDist, PMF.mem_support_bind_iff] at hS
      obtain ⟨S', hS', hS⟩ := hS
      obtain ⟨ih1, -⟩ := schedulerTraceDist_support_run P hn C₀ Goal K S' hS'
      unfold schedulerTraceStepDist at hS
      rw [PMF.support_map] at hS
      obtain ⟨p, -, rfl⟩ := hS
      refine ⟨?_, ?_⟩
      · simp only [runPrefix_snoc, ← ih1]
      · intro h
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
        exact h.2

/-- **Prefix bound for the not-hit probability.** -/
theorem probNotHitBy_le_prefixMass (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (K : ℕ) :
    probNotHitBy P hn C₀ Goal K ≤
      (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ | ¬ Goal (runPrefix P C₀ K σ)} := by
  classical
  set μ := schedulerTraceDist P hn C₀ Goal K
  rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure, ← schedulerTraceDist_map_hitFlag,
    ← schedulerTraceDist_map_prefix P hn C₀ Goal K, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  rintro S ⟨hS, hsupp⟩
  obtain ⟨hrun, hflag⟩ := schedulerTraceDist_support_run P hn C₀ Goal K S hsupp
  have hS' : S.1.2 = false := hS
  show ¬ Goal (runPrefix P C₀ K S.2)
  rw [← hrun]
  exact hflag hS'

/-- **Factorization of the product measure** on product integrands. -/
theorem schedulerPrefix_sum_prod (hn : 2 ≤ n) (K : ℕ)
    (f : Fin K → Fin n × Fin n → ENNReal) :
    ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * ∏ t, f t (σ t) =
      ∏ t : Fin K, ∑ p : Fin n × Fin n, uniformPair n hn p * f t p := by
  classical
  have hprod :=
    (Finset.prod_univ_sum
      (R := ENNReal)
      (ι := Fin K)
      (κ := fun _ : Fin K => Fin n × Fin n)
      (t := fun _ : Fin K => (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun t p => uniformPair n hn p * f t p)).symm
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  apply Finset.sum_congr rfl
  intro σ _
  rw [schedulerPrefixPMF_apply, schedulerPrefixWeight, ← Finset.prod_mul_distrib]

/-- The product-measure mass of a set, as a finite sum. -/
theorem schedulerPrefix_toOuterMeasure_eq_sum (hn : 2 ≤ n) (K : ℕ)
    (B : Set (SchedulerPrefix n K)) [DecidablePred (· ∈ B)] :
    (schedulerPrefixPMF n hn K).toOuterMeasure B =
      ∑ σ : SchedulerPrefix n K, if σ ∈ B then schedulerPrefixPMF n hn K σ else 0 := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : σ ∈ B
  · rw [Set.indicator_of_mem h, if_pos h]
  · rw [Set.indicator_of_notMem h, if_neg h]

/-- **Exponential Markov bound in the product measure**: if every prefix in `B` satisfies
`1 ≤ ∏ t, f t (σ t)`, the mass of `B` is at most the product of the one-step means. -/
theorem schedulerPrefix_mass_le_prod (hn : 2 ≤ n) (K : ℕ)
    (B : Set (SchedulerPrefix n K)) (f : Fin K → Fin n × Fin n → ENNReal)
    (hB : ∀ σ ∈ B, 1 ≤ ∏ t, f t (σ t)) :
    (schedulerPrefixPMF n hn K).toOuterMeasure B ≤
      ∏ t : Fin K, ∑ p : Fin n × Fin n, uniformPair n hn p * f t p := by
  classical
  rw [schedulerPrefix_toOuterMeasure_eq_sum, ← schedulerPrefix_sum_prod]
  apply Finset.sum_le_sum
  intro σ _
  by_cases h : σ ∈ B
  · rw [if_pos h]
    calc schedulerPrefixPMF n hn K σ = schedulerPrefixPMF n hn K σ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_left' (hB σ h) _
  · rw [if_neg h]
    exact zero_le


/-- One more coordinate of the product measure: sum over the last pair. -/
theorem schedulerPrefix_sum_succ (hn : 2 ≤ n) (K : ℕ) (G : SchedulerPrefix n (K + 1) → ENNReal) :
    ∑ τ, schedulerPrefixPMF n hn (K + 1) τ * G τ =
      ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ *
        ∑ p : Fin n × Fin n, uniformPair n hn p * G (Fin.snoc σ p) := by
  classical
  have hsnoc : ∀ x : (Fin n × Fin n) × SchedulerPrefix n K,
      (Fin.snocEquiv (fun _ => Fin n × Fin n)) x = Fin.snoc x.2 x.1 := fun _ => rfl
  rw [← (Fin.snocEquiv (fun _ => Fin n × Fin n)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hsnoc]
  simp only [schedulerPrefixPMF_apply, schedulerPrefixWeight, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [mul_assoc]

/-- **Prefix supermartingale bound.** If `F` has the one-step bound
`E[F (σ, p)] ≤ ρ F σ` under a fresh scheduler pair, its expectation after `K` steps is at most
`ρ ^ K F ∅`. -/
theorem schedulerPrefix_expect_le_pow (hn : 2 ≤ n) (F : ∀ K, SchedulerPrefix n K → ENNReal)
    (ρ : ENNReal)
    (hstep : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) ≤ ρ * F K σ) :
    ∀ K, ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * F K σ ≤
      ρ ^ K * F 0 (fun t => Fin.elim0 t)
  | 0 => by
      rw [pow_zero, one_mul, Fintype.sum_unique, schedulerPrefixPMF_apply,
        schedulerPrefixWeight, Fin.prod_univ_zero, one_mul]
      rw [Subsingleton.elim (default : SchedulerPrefix n 0) (fun t => Fin.elim0 t)]
  | K + 1 => by
      rw [schedulerPrefix_sum_succ]
      calc ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ *
              ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p)
          ≤ ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * (ρ * F K σ) :=
            Finset.sum_le_sum fun σ _ => mul_le_mul_left' (hstep K σ) _
        _ = ρ * ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * F K σ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ _
            ring
        _ ≤ ρ * (ρ ^ K * F 0 (fun t => Fin.elim0 t)) :=
            mul_le_mul_left' (schedulerPrefix_expect_le_pow hn F ρ hstep K) _
        _ = ρ ^ (K + 1) * F 0 (fun t => Fin.elim0 t) := by ring

/-- **Markov's inequality** in the product measure. -/
theorem schedulerPrefix_markov (hn : 2 ≤ n) (K : ℕ) (F : SchedulerPrefix n K → ENNReal)
    (a : ENNReal) :
    a * (schedulerPrefixPMF n hn K).toOuterMeasure {σ | a ≤ F σ} ≤
      ∑ σ, schedulerPrefixPMF n hn K σ * F σ := by
  classical
  rw [schedulerPrefix_toOuterMeasure_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  by_cases h : σ ∈ {σ | a ≤ F σ}
  · rw [if_pos h, mul_comm]
    exact mul_le_mul_left' (show a ≤ F σ from h) _
  · rw [if_neg h, mul_zero]
    exact zero_le

/-- Row sums of the scheduler: a fixed initiator has probability `1/n`. -/
theorem uniformPair_row_sum (hn : 2 ≤ n) (a : Fin n) :
    ∑ b : Fin n, uniformPair n hn (a, b) = (n : ENNReal)⁻¹ := by
  classical
  have h1 : ∀ b, uniformPair n hn (a, b) =
      if b = a then 0 else ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
    intro b
    by_cases hb : b = a
    · rw [if_pos hb, hb, uniformPair_apply_self]
    · rw [if_neg hb, uniformPair_apply_of_ne n hn (Ne.symm hb)]
  simp only [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun b : Fin n => ¬ b = a).card = n - 1 := by
    rw [Finset.filter_ne' Finset.univ a, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : ((n - 1 : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)),
    mul_comm ((n : ENNReal)⁻¹), ← mul_assoc,
    ENNReal.mul_inv_cancel hm0 (ENNReal.natCast_ne_top _), one_mul]

/-- Column sums of the scheduler: a fixed responder has probability `1/n`. -/
theorem uniformPair_col_sum (hn : 2 ≤ n) (b : Fin n) :
    ∑ a : Fin n, uniformPair n hn (a, b) = (n : ENNReal)⁻¹ := by
  classical
  have : ∀ a, uniformPair n hn (a, b) = uniformPair n hn (b, a) := by
    intro a
    by_cases h : a = b
    · rw [h]
    · rw [uniformPair_apply_of_ne n hn h, uniformPair_apply_of_ne n hn (Ne.symm h)]
  simp only [this]
  exact uniformPair_row_sum hn b

/-- **Endpoint average**: `E[f(u) + f(v)] = (2/n) Σ f` for the uniform pair `(u, v)`. -/
theorem uniformPair_sum_endpoints (hn : 2 ≤ n) (f : Fin n → ENNReal) :
    ∑ p : Fin n × Fin n, uniformPair n hn p * (f p.1 + f p.2) =
      2 * (n : ENNReal)⁻¹ * ∑ w, f w := by
  classical
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hA : ∑ a : Fin n, ∑ b : Fin n, uniformPair n hn (a, b) * f a =
      (n : ENNReal)⁻¹ * ∑ w, f w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_mul, uniformPair_row_sum]
  have hB : ∑ a : Fin n, ∑ b : Fin n, uniformPair n hn (a, b) * f b =
      (n : ENNReal)⁻¹ * ∑ w, f w := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_mul, uniformPair_col_sum]
  simp only at hA hB ⊢
  rw [hA, hB, two_mul, add_mul]

end Probability
end Ripple.PopulationProtocol.SSEM

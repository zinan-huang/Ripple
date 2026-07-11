/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additive Drift Hitting-Time Bound

An abstract additive-drift theorem for the expected hitting-time API.  The
proof works only with the hit-flag Markov chain and one-step PMF interface; it
does not unfold any protocol-specific transition behavior.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime

namespace SSEM
namespace Probability

open scoped BigOperators ENNReal
open PMF

variable {Q X Y : Type*} {n : ℕ}

private noncomputable def pmfExpected {α : Type*}
    (μ : PMF α) (f : α → ENNReal) : ENNReal :=
  ∑' a : α, μ a * f a

private theorem pmfExpected_pure {α : Type*} (a : α) (f : α → ENNReal) :
    pmfExpected (PMF.pure a) f = f a := by
  unfold pmfExpected
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    rw [PMF.pure_apply_of_ne a b hb]
    simp

private theorem pmfExpected_bind {α β : Type*}
    (μ : PMF α) (F : α → PMF β) (f : β → ENNReal) :
    pmfExpected (μ.bind F) f =
      ∑' a : α, μ a * pmfExpected (F a) f := by
  unfold pmfExpected
  simp only [PMF.bind_apply]
  calc
    ∑' b : β, (∑' a : α, μ a * F a b) * f b
        = ∑' b : β, ∑' a : α, μ a * F a b * f b := by
            apply tsum_congr
            intro b
            rw [ENNReal.tsum_mul_right]
    _ = ∑' a : α, ∑' b : β, μ a * F a b * f b :=
          ENNReal.tsum_comm
    _ = ∑' a : α, μ a * ∑' b : β, F a b * f b := by
          apply tsum_congr
          intro a
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro b
          rw [mul_assoc]

private theorem pmfExpected_map {α β : Type*}
    (μ : PMF α) (g : α → β) (f : β → ENNReal) :
    pmfExpected (μ.map g) f =
      ∑' a : α, μ a * f (g a) := by
  rw [← PMF.bind_pure_comp, pmfExpected_bind]
  apply tsum_congr
  intro a
  change μ a * pmfExpected (PMF.pure (g a)) f = μ a * f (g a)
  rw [pmfExpected_pure]

private noncomputable def falsePotential
    (φ : Config Q X n → ℕ) (S : Config Q X n × Bool) : ENNReal :=
  if S.2 = false then (φ S.1 : ENNReal) else 0

private noncomputable def tailPotential
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (φ : Config Q X n → ℕ) (t : ℕ) : ENNReal :=
  pmfExpected (hitFlagDist P hn C₀ Goal t) (falsePotential φ)

private noncomputable def oneStepPotential
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (φ : Config Q X n → ℕ) (C : Config Q X n) : ENNReal :=
  pmfExpected (stepDist P hn C) fun D => (φ D : ENNReal)

private theorem probNotHitBy_eq_pmfExpected_false
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal t =
      pmfExpected (hitFlagDist P hn C₀ Goal t)
        (fun S : Config Q X n × Bool =>
          if S.2 = false then (1 : ENNReal) else 0) := by
  unfold probNotHitBy pmfExpected
  apply tsum_congr
  intro S
  by_cases hS : S.2 = false <;> simp [hS]

private theorem tailPotential_zero_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (φ : Config Q X n → ℕ) (hGoal : ¬ Goal C₀) :
    tailPotential P hn C₀ Goal φ 0 = (φ C₀ : ENNReal) := by
  classical
  unfold tailPotential
  rw [hitFlagDist]
  simp [pmfExpected_pure, falsePotential, hGoal]

private theorem hitFlagDist_support_false_region_until_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Region : Config Q X n → Prop)
    (hReg₀ : Region C₀)
    (hRegStep : ∀ C : Config Q X n, Region C → ¬ Goal C →
      ∀ i j : Fin n, Region (C.step P i j) ∨ Goal (C.step P i j)) :
    ∀ t : ℕ, ∀ C : Config Q X n,
      (C, false) ∈ (hitFlagDist P hn C₀ Goal t).support → Region C
  | 0, C => by
      classical
      intro hmem
      rw [hitFlagDist, PMF.support_pure] at hmem
      have hC : C = C₀ := by
        simpa using congrArg Prod.fst hmem
      exact hC.symm ▸ hReg₀
  | t + 1, C => by
      classical
      intro hmem
      rw [hitFlagDist, PMF.mem_support_bind_iff] at hmem
      obtain ⟨S, hS, hstep⟩ := hmem
      rcases S with ⟨D, b⟩
      rw [hitFlagStepDist, PMF.support_map] at hstep
      obtain ⟨E, hE, hEq⟩ := hstep
      have hCE : C = E := by
        simpa using (congrArg Prod.fst hEq).symm
      subst C
      cases b
      · have hnotGoalE : ¬ Goal E := by
          intro hGoalE
          have hfalse := congrArg Prod.snd hEq
          simp [hGoalE] at hfalse
        have hRegD :
            Region D :=
          hitFlagDist_support_false_region_until_goal
            P hn C₀ Goal Region hReg₀ hRegStep t D hS
        have hnotGoalD : ¬ Goal D := by
          intro hGoalD
          have hzero :=
            hitFlagDist_apply_false_of_goal P hn C₀ D Goal hGoalD t
          rw [PMF.mem_support_iff] at hS
          exact hS hzero
        rw [stepDist, PMF.support_map] at hE
        obtain ⟨pair, _hpair_mem, hpair_eq⟩ := hE
        rw [← hpair_eq]
        rcases hRegStep D hRegD hnotGoalD pair.1 pair.2 with hReg' | hGoal'
        · exact hReg'
        · exact False.elim (hnotGoalE (by simpa [hpair_eq] using hGoal'))
      · have hfalse := congrArg Prod.snd hEq
        simp at hfalse

private theorem hitFlagStep_falsePotential_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop) (φ : Config Q X n → ℕ)
    (S : Config Q X n × Bool) :
    pmfExpected (hitFlagStepDist P hn Goal S) (falsePotential φ) ≤
      if S.2 = false then oneStepPotential P hn φ S.1 else 0 := by
  classical
  rcases S with ⟨C, b⟩
  cases b
  · unfold hitFlagStepDist oneStepPotential
    rw [pmfExpected_map]
    apply ENNReal.tsum_le_tsum
    intro D
    by_cases hGoalD : Goal D
    · simp [falsePotential, hGoalD]
    · simp [falsePotential, hGoalD]
  · unfold hitFlagStepDist
    rw [pmfExpected_map]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.2
    intro D
    simp [falsePotential]

private theorem tailPotential_succ_le_stepPotential
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (φ : Config Q X n → ℕ) (t : ℕ) :
    tailPotential P hn C₀ Goal φ (t + 1) ≤
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then oneStepPotential P hn φ S.1 else 0) := by
  unfold tailPotential
  rw [hitFlagDist, pmfExpected_bind]
  apply ENNReal.tsum_le_tsum
  intro S
  exact mul_le_mul_right
    (hitFlagStep_falsePotential_le P hn Goal φ S)
    (hitFlagDist P hn C₀ Goal t S)

private theorem eps_mul_probNotHitBy_eq_tsum
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (ε : ENNReal) (t : ℕ) :
    ε * probNotHitBy P hn C₀ Goal t =
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then ε else 0) := by
  rw [probNotHitBy_eq_pmfExpected_false P hn C₀ Goal t]
  unfold pmfExpected
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro S
  by_cases hS : S.2 = false <;> simp [hS, mul_comm]

private theorem stepPotential_add_eps_tsum_le_tailPotential
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Region : Config Q X n → Prop)
    (φ : Config Q X n → ℕ) (ε : ENNReal)
    (hReg₀ : Region C₀)
    (hRegStep : ∀ C : Config Q X n, Region C → ¬ Goal C →
      ∀ i j : Fin n, Region (C.step P i j) ∨ Goal (C.step P i j))
    (hDrift : ∀ C : Config Q X n, Region C → ¬ Goal C →
      (∑' D : Config Q X n, stepDist P hn C D * (φ D : ENNReal)) + ε ≤
        (φ C : ENNReal))
    (t : ℕ) :
    (∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then oneStepPotential P hn φ S.1 + ε else 0)) ≤
      tailPotential P hn C₀ Goal φ t := by
  unfold tailPotential pmfExpected falsePotential
  apply ENNReal.tsum_le_tsum
  intro S
  rcases S with ⟨C, b⟩
  cases b
  · by_cases hGoalC : Goal C
    · rw [hitFlagDist_apply_false_of_goal P hn C₀ C Goal hGoalC t]
      simp
    · by_cases hmass : hitFlagDist P hn C₀ Goal t (C, false) = 0
      · rw [hmass]
        simp
      · have hmem : (C, false) ∈ (hitFlagDist P hn C₀ Goal t).support := by
          rw [PMF.mem_support_iff]
          exact hmass
        have hRegC :
            Region C :=
          hitFlagDist_support_false_region_until_goal
            P hn C₀ Goal Region hReg₀ hRegStep t C hmem
        have hdriftC :
            oneStepPotential P hn φ C + ε ≤ (φ C : ENNReal) := by
          simpa [oneStepPotential, pmfExpected] using
            hDrift C hRegC hGoalC
        exact mul_le_mul_right hdriftC
          (hitFlagDist P hn C₀ Goal t (C, false))
  · simp

private theorem tailPotential_succ_add_eps_prob_le_tailPotential
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Region : Config Q X n → Prop)
    (φ : Config Q X n → ℕ) (ε : ENNReal)
    (hReg₀ : Region C₀)
    (hRegStep : ∀ C : Config Q X n, Region C → ¬ Goal C →
      ∀ i j : Fin n, Region (C.step P i j) ∨ Goal (C.step P i j))
    (hDrift : ∀ C : Config Q X n, Region C → ¬ Goal C →
      (∑' D : Config Q X n, stepDist P hn C D * (φ D : ENNReal)) + ε ≤
        (φ C : ENNReal))
    (t : ℕ) :
    tailPotential P hn C₀ Goal φ (t + 1) +
        ε * probNotHitBy P hn C₀ Goal t ≤
      tailPotential P hn C₀ Goal φ t := by
  have htail :=
    tailPotential_succ_le_stepPotential P hn C₀ Goal φ t
  have hsum :
      (∑' S : Config Q X n × Bool,
          hitFlagDist P hn C₀ Goal t S *
            (if S.2 = false then oneStepPotential P hn φ S.1 else 0)) +
        ε * probNotHitBy P hn C₀ Goal t =
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then oneStepPotential P hn φ S.1 + ε else 0) := by
    rw [eps_mul_probNotHitBy_eq_tsum P hn C₀ Goal ε t]
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro S
    by_cases hS : S.2 = false <;>
      simp [hS, mul_add, add_comm]
  calc
    tailPotential P hn C₀ Goal φ (t + 1) +
        ε * probNotHitBy P hn C₀ Goal t
        ≤
      (∑' S : Config Q X n × Bool,
          hitFlagDist P hn C₀ Goal t S *
            (if S.2 = false then oneStepPotential P hn φ S.1 else 0)) +
        ε * probNotHitBy P hn C₀ Goal t := by
          exact add_le_add htail le_rfl
    _ =
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then oneStepPotential P hn φ S.1 + ε else 0) := hsum
    _ ≤ tailPotential P hn C₀ Goal φ t :=
      stepPotential_add_eps_tsum_le_tailPotential
        P hn C₀ Goal Region φ ε hReg₀ hRegStep hDrift t

private theorem finite_tail_sum_mul_eps_le_initial_potential
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Region : Config Q X n → Prop)
    (φ : Config Q X n → ℕ) (ε : ENNReal)
    (hReg₀ : Region C₀)
    (hRegStep : ∀ C : Config Q X n, Region C → ¬ Goal C →
      ∀ i j : Fin n, Region (C.step P i j) ∨ Goal (C.step P i j))
    (hDrift : ∀ C : Config Q X n, Region C → ¬ Goal C →
      (∑' D : Config Q X n, stepDist P hn C D * (φ D : ENNReal)) + ε ≤
        (φ C : ENNReal))
    (hGoal₀ : ¬ Goal C₀) :
    ∀ T : ℕ,
      (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε ≤
        (φ C₀ : ENNReal) := by
  intro T
  have hmain :
      tailPotential P hn C₀ Goal φ T +
          (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε ≤
        tailPotential P hn C₀ Goal φ 0 := by
    induction T with
    | zero =>
        simp
    | succ T ih =>
        have hstep :=
          tailPotential_succ_add_eps_prob_le_tailPotential
            P hn C₀ Goal Region φ ε hReg₀ hRegStep hDrift T
        calc
          tailPotential P hn C₀ Goal φ (T + 1) +
              (∑ t ∈ Finset.range (T + 1),
                probNotHitBy P hn C₀ Goal t) * ε
              =
            (tailPotential P hn C₀ Goal φ (T + 1) +
                ε * probNotHitBy P hn C₀ Goal T) +
              (∑ t ∈ Finset.range T,
                probNotHitBy P hn C₀ Goal t) * ε := by
                rw [Finset.sum_range_succ, add_mul]
                rw [mul_comm
                  (probNotHitBy P hn C₀ Goal T) ε]
                simp [add_comm, add_assoc]
          _ ≤ tailPotential P hn C₀ Goal φ T +
              (∑ t ∈ Finset.range T,
                probNotHitBy P hn C₀ Goal t) * ε := by
                exact add_le_add hstep le_rfl
          _ ≤ tailPotential P hn C₀ Goal φ 0 := ih
  have htail_nonneg :
      (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε ≤
        tailPotential P hn C₀ Goal φ T +
          (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε :=
    le_add_of_nonneg_left zero_le
  calc
    (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε
        ≤ tailPotential P hn C₀ Goal φ T +
          (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε :=
          htail_nonneg
    _ ≤ tailPotential P hn C₀ Goal φ 0 := hmain
    _ = (φ C₀ : ENNReal) :=
          tailPotential_zero_of_not_goal P hn C₀ Goal φ hGoal₀

/-- Additive-drift hitting-time bound.

If, until the first hit of `Goal`, the chain remains in `Region` and the
one-step expected potential drops by at least `ε`, then the expected hitting
time is at most the initial potential divided by `ε`.
-/
theorem expectedHittingTime_le_of_drift
    {Q X Y : Type*} {n : ℕ} [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Region : Config Q X n → Prop)
    [DecidablePred Goal] [DecidablePred Region]
    (φ : Config Q X n → ℕ) (ε : ENNReal) (hε0 : 0 < ε) (hεtop : ε ≠ ⊤)
    (hReg0 : Region C₀)
    (hZeroGoal : ∀ C, Region C → φ C = 0 → Goal C)
    (hRegStep : ∀ C, Region C → ¬ Goal C → ∀ i j : Fin n,
        Region (C.step P i j) ∨ Goal (C.step P i j))
    (hDrift : ∀ C, Region C → ¬ Goal C →
        (∑' D : Config Q X n, (stepDist P hn C D) * (φ D : ENNReal)) + ε ≤
          (φ C : ENNReal)) :
    expectedHittingTime P hn C₀ Goal ≤ ((φ C₀ : ENNReal)) / ε := by
  classical
  by_cases hGoal₀ : Goal C₀
  · rw [expectedHittingTime_eq_zero_of_goal P hn C₀ Goal hGoal₀]
    exact zero_le
  · have hε_ne_zero : ε ≠ 0 := ne_of_gt hε0
    have _hφ0 : φ C₀ ≠ 0 := by
      intro hφ0
      exact hGoal₀ (hZeroGoal C₀ hReg0 hφ0)
    rw [expectedHittingTime, ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro T
    have hmul :
        (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t) * ε ≤
          (φ C₀ : ENNReal) :=
      finite_tail_sum_mul_eps_le_initial_potential
        P hn C₀ Goal Region φ ε hReg0 hRegStep hDrift hGoal₀ T
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl hε_ne_zero) (Or.inl hεtop)).2 hmul

end Probability
end SSEM

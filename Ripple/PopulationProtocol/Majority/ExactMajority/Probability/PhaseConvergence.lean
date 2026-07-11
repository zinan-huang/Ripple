/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase Convergence for ExactMajority Protocols
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain
import Mathlib.Probability.Kernel.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- A finite power of a Markov kernel assigns mass at most one to every set.

Mathlib does not provide an `IsMarkovKernel (K ^ t)` instance here, so we prove
only the needed bound directly from `(K ^ t) x univ = 1`. -/
private theorem kernel_pow_apply_le_one
    {Ω : Type*} [MeasurableSpace Ω] {K : Kernel Ω Ω} [IsMarkovKernel K]
    (t : ℕ) (x : Ω) (S : Set Ω) :
    (K ^ t) x S ≤ 1 := by
  have h_univ : (K ^ t) x Set.univ = 1 := by
    induction t with
    | zero =>
        simp only [pow_zero]
        change Kernel.id x Set.univ = 1
        rw [Kernel.id_apply]
        simp
    | succ t ih =>
        have h_meas_univ : MeasurableSet (Set.univ : Set Ω) := MeasurableSet.univ
        rw [Kernel.pow_succ_apply_eq_lintegral K t x h_meas_univ]
        calc ∫⁻ y, K y Set.univ ∂((K ^ t) x)
            = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂((K ^ t) x) := by
                apply lintegral_congr_ae
                filter_upwards with y
                haveI : IsProbabilityMeasure (K y) :=
                  (inferInstance : IsMarkovKernel K).isProbabilityMeasure y
                simpa using (measure_univ (μ := K y))
          _ = 1 := by
                rw [lintegral_const, ih, one_mul]
  calc (K ^ t) x S
      ≤ (K ^ t) x Set.univ := measure_mono (Set.subset_univ S)
    _ = 1 := h_univ

private theorem ennreal_coe_nnreal_sum_finset {ι : Type*} (s : Finset ι)
    (f : ι → ℝ≥0) :
    ((∑ i ∈ s, f i : ℝ≥0) : ℝ≥0∞) = ∑ i ∈ s, (f i : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

private theorem ennreal_coe_nnreal_sum {ι : Type*} [Fintype ι] (f : ι → ℝ≥0) :
    ((∑ i, f i : ℝ≥0) : ℝ≥0∞) = ∑ i, (f i : ℝ≥0∞) := by
  classical
  simpa using ennreal_coe_nnreal_sum_finset (Finset.univ : Finset ι) f

/-- A phase converges if, starting from `Pre`, it reaches a stable `Post` 
    within time `t` with failure probability at most `ε`. -/
structure PhaseConvergence {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] (K : Kernel Ω Ω) where
  Pre : Ω → Prop
  Post : Ω → Prop
  t : ℕ
  ε : ℝ≥0
  -- Post must be monotonically preserved by the entire kernel K
  post_absorbing : ∀ x, Post x → K x {y | Post y} = 1
  -- If we start in Pre, after t steps, we are in Post w.h.p.
  convergence : ∀ x, Pre x → (K ^ t) x {y | ¬Post y} ≤ (ε : ℝ≥0∞)

/-- Two-phase composition via union bound.

Proof idea (Chapman-Kolmogorov + set decomposition):
1. K^(t1+t2) decomposes as ∫ K^t2(y, ·) d(K^t1)(x₀, y).
2. Split the integral over {Post1 y} ∪ {¬Post1 y}:
   - On {Post1}: h_chain gives Pre2, so K^t2(y, ¬Post2) ≤ ε2.
     Integral ≤ ε2 · (K^t1)(x₀, Post1) ≤ ε2.
   - On {¬Post1}: K^t2(y, ¬Post2) ≤ 1 (probability).
     Integral ≤ (K^t1)(x₀, ¬Post1) ≤ ε1.
3. Total ≤ ε1 + ε2. -/
theorem compose_two_phases
    {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] {K : Kernel Ω Ω}
    [IsMarkovKernel K]
    (phase1 phase2 : PhaseConvergence K)
    (h_chain : ∀ x, phase1.Post x → phase2.Pre x)
    (x₀ : Ω) (hx₀ : phase1.Pre x₀) :
    (K ^ (phase1.t + phase2.t)) x₀ {y | ¬phase2.Post y} ≤ (phase1.ε + phase2.ε : ℝ≥0∞) := by
  -- 1. Chapman-Kolmogorov decomposition
  have h_decomp : (K ^ (phase1.t + phase2.t)) x₀ {y | ¬phase2.Post y} =
      ∫⁻ y, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀) := by
    exact Kernel.pow_add_apply_eq_lintegral K phase1.t phase2.t x₀
      (DiscreteMeasurableSpace.forall_measurableSet (α := Ω) _)
  rw [h_decomp]

  -- 2. Split the integral over {Post1} and {¬Post1}
  have h_meas : MeasurableSet {y | phase1.Post y} := by exact DiscreteMeasurableSpace.forall_measurableSet _
  have h_split : ∫⁻ y, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀) =
      (∫⁻ y in {y | phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀)) +
      (∫⁻ y in {y | ¬phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀)) := by
    have h_compl : {y | ¬phase1.Post y} = {y | phase1.Post y}ᶜ := Set.ext fun x => by simp
    rw [h_compl, ← lintegral_add_compl _ h_meas]
  rw [h_split]

  -- 3. Bound on {Post1} (convergence of phase 2)
  have h_bound1 : ∫⁻ y in {y | phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀) ≤ phase2.ε := by
    have h_le_eps : ∀ y ∈ {y | phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ≤ (phase2.ε : ℝ≥0∞) := fun y hy => phase2.convergence y (h_chain y hy)
    calc ∫⁻ y in {y | phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀)
      _ ≤ ∫⁻ _ in {y | phase1.Post y}, (phase2.ε : ℝ≥0∞) ∂((K ^ phase1.t) x₀) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem h_meas] with y hy
        exact h_le_eps y hy
      _ ≤ (phase2.ε : ℝ≥0∞) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        calc (phase2.ε : ℝ≥0∞) * ((K ^ phase1.t) x₀ {y | phase1.Post y})
            ≤ (phase2.ε : ℝ≥0∞) * 1 := by
              gcongr
              exact kernel_pow_apply_le_one (K := K) phase1.t x₀ {y | phase1.Post y}
          _ = _ := mul_one _

  -- 4. Bound on {¬Post1} (failure of phase 1)
  have h_bound2 : ∫⁻ y in {y | ¬phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀) ≤ phase1.ε := by
    calc ∫⁻ y in {y | ¬phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀)
      _ ≤ ∫⁻ _ in {y | ¬phase1.Post y}, 1 ∂((K ^ phase1.t) x₀) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem h_meas.compl] with y _
        exact kernel_pow_apply_le_one (K := K) phase2.t y {y' | ¬phase2.Post y'}
      _ = ((K ^ phase1.t) x₀ {y | ¬phase1.Post y}) := by
        rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
      _ ≤ (phase1.ε : ℝ≥0∞) := phase1.convergence x₀ hx₀

  -- 5. Combine the bounds
  have h_add : (phase2.ε : ℝ≥0∞) + (phase1.ε : ℝ≥0∞) = (phase1.ε + phase2.ε : ℝ≥0∞) := by
    push_cast
    exact add_comm _ _
  calc (∫⁻ y in {y | phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀)) +
       (∫⁻ y in {y | ¬phase1.Post y}, (K ^ phase2.t) y {y' | ¬phase2.Post y'} ∂((K ^ phase1.t) x₀))
    _ ≤ (phase2.ε : ℝ≥0∞) + (phase1.ε : ℝ≥0∞) := add_le_add h_bound1 h_bound2
    _ = (phase1.ε + phase2.ε : ℝ≥0∞) := h_add

theorem compose_n_phases
    {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] {K : Kernel Ω Ω}
    [IsMarkovKernel K]
    {m : ℕ} (hm : m > 0)
    (phases : Fin m → PhaseConvergence K)
    (h_chain : ∀ (i : Fin m) (hi : i.val + 1 < m), 
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (x₀ : Ω) (hx₀ : (phases ⟨0, hm⟩).Pre x₀) :
    (K ^ (∑ i : Fin m, (phases i).t)) x₀ {y | ¬(phases ⟨m - 1, by omega⟩).Post y} ≤ 
      (∑ i : Fin m, ((phases i).ε : ℝ≥0∞)) := by
  revert hm phases h_chain x₀ hx₀
  induction m with
  | zero =>
      intro hm phases h_chain x₀ hx₀
      omega
  | succ m' ih =>
    intro hm phases h_chain x₀ hx₀
    by_cases hm'_pos : 0 < m'
    · -- Inductive step: compose prefix of length `m'` with the last phase.
      let prefix_phases : Fin m' → PhaseConvergence K := fun i => phases i.castSucc
      let prefix_last : Fin m' := ⟨m' - 1, by omega⟩
      let last : Fin (Nat.succ m') := ⟨m', Nat.lt_succ_self m'⟩
      have h_prefix_chain :
          ∀ (i : Fin m') (hi : i.val + 1 < m'),
            ∀ x, (prefix_phases i).Post x →
              (prefix_phases ⟨i.val + 1, hi⟩).Pre x := by
        intro i hi x hx
        have hi' : (i.castSucc : Fin (Nat.succ m')).val + 1 < Nat.succ m' :=
          Nat.lt_trans hi (Nat.lt_succ_self m')
        have h := h_chain i.castSucc hi' x (by simpa [prefix_phases] using hx)
        have hidx :
            (⟨(i.castSucc : Fin (Nat.succ m')).val + 1, hi'⟩ :
                Fin (Nat.succ m')) =
              Fin.castSucc (⟨i.val + 1, hi⟩ : Fin m') := by
          ext
          rfl
        simpa [prefix_phases, hidx] using h
      let prefix_conv : PhaseConvergence K := {
        Pre := (prefix_phases ⟨0, hm'_pos⟩).Pre
        Post := (prefix_phases prefix_last).Post
        t := ∑ i : Fin m', (prefix_phases i).t
        ε := ∑ i : Fin m', (prefix_phases i).ε
        post_absorbing := by
          intro x hx
          exact (prefix_phases prefix_last).post_absorbing x hx
        convergence := by
          intro x hx
          have h_ih := ih hm'_pos prefix_phases h_prefix_chain x hx
          have hε :
              ((∑ i : Fin m', (prefix_phases i).ε : ℝ≥0) : ℝ≥0∞) =
                ∑ i : Fin m', ((prefix_phases i).ε : ℝ≥0∞) :=
            ennreal_coe_nnreal_sum (fun i : Fin m' => (prefix_phases i).ε)
          rw [hε]
          simpa [prefix_last] using h_ih
      }
      have hx_prefix : prefix_conv.Pre x₀ := by
        have hidx : (⟨0, hm⟩ : Fin (Nat.succ m')) =
            Fin.castSucc (⟨0, hm'_pos⟩ : Fin m') := by
          ext
          rfl
        change (phases (Fin.castSucc (⟨0, hm'_pos⟩ : Fin m'))).Pre x₀
        rw [← hidx]
        exact hx₀
      have h_last_chain : ∀ x, prefix_conv.Post x → (phases last).Pre x := by
        intro x hx
        let prev : Fin (Nat.succ m') := Fin.castSucc prefix_last
        have hprev_next : prev.val + 1 < Nat.succ m' := by
          simp [prev, prefix_last]
          omega
        have hprev_post : (phases prev).Post x := by
          change (phases (Fin.castSucc prefix_last)).Post x
          simpa [prefix_conv, prefix_phases, prev] using hx
        have h := h_chain prev hprev_next x hprev_post
        have hidx : (⟨prev.val + 1, hprev_next⟩ : Fin (Nat.succ m')) = last := by
          ext
          simp [prev, prefix_last, last]
          omega
        simpa [hidx] using h
      have h_compose :=
        compose_two_phases (K := K) prefix_conv (phases last) h_last_chain x₀ hx_prefix
      have ht_split :
          (∑ i : Fin (Nat.succ m'), (phases i).t) =
            prefix_conv.t + (phases last).t := by
        simpa [prefix_conv, prefix_phases, last] using
          (Fin.sum_univ_castSucc (fun i : Fin (Nat.succ m') => (phases i).t))
      have he_split :
          (∑ i : Fin (Nat.succ m'), ((phases i).ε : ℝ≥0∞)) =
            (prefix_conv.ε : ℝ≥0∞) + ((phases last).ε : ℝ≥0∞) := by
        have hprefix_eps :
            ((∑ i : Fin m', (prefix_phases i).ε : ℝ≥0) : ℝ≥0∞) =
              ∑ i : Fin m', ((prefix_phases i).ε : ℝ≥0∞) :=
          ennreal_coe_nnreal_sum (fun i : Fin m' => (prefix_phases i).ε)
        simpa [prefix_conv, prefix_phases, last, hprefix_eps] using
          (Fin.sum_univ_castSucc
            (fun i : Fin (Nat.succ m') => ((phases i).ε : ℝ≥0∞)))
      have hpost :
          (phases ⟨Nat.succ m' - 1, by omega⟩).Post = (phases last).Post := by
        congr 1
      have h_compose' :
          (K ^ (prefix_conv.t + (phases last).t)) x₀ {y | ¬(phases last).Post y} ≤
            (prefix_conv.ε : ℝ≥0∞) + ((phases last).ε : ℝ≥0∞) := by
        have hε_add :
            (prefix_conv.ε + (phases last).ε : ℝ≥0∞) =
              (prefix_conv.ε : ℝ≥0∞) + ((phases last).ε : ℝ≥0∞) := by
          push_cast
          rfl
        simpa [hε_add] using h_compose
      simpa [ht_split, he_split, hpost] using h_compose'
    · -- Base case: m = 1
      have hm1 : m' = 0 := by omega
      subst m'
      simpa using (phases ⟨0, hm⟩).convergence x₀ hx₀

end ExactMajority

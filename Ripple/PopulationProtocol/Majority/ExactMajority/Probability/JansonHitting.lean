/-
# Janson Hitting-Time Wrapper for Population Protocols

Bridge from the Janson geometric tail bounds (JansonGeometric.lean, 0 sorry)
to protocol-level hitting-time convergence.

The idea: if a protocol has k "milestones" and at each step the probability
of hitting the next milestone is at least p_i, then the total time to
complete all milestones is a sum of geometric waiting times. Janson's tail
bound then gives exponential concentration.

This file provides the wrapper that connects the generic Janson machinery
to the PhaseConvergence structure, enabling each Doty phase to be proved
via waiting-time concentration rather than single-step descent.

Reference: Doty et al. §4 (Theorems 4.2, 4.3, Corollary 4.4).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonGeometric
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergence
import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift
import Mathlib.Probability.Kernel.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

attribute [local instance] Classical.propDecidable

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- A milestone structure for a population protocol phase.

A phase has `k` milestones (events). At each step, if milestone `i` has not
been reached, the probability of reaching it is at least `p i`.
When all milestones are reached, the phase postcondition holds. -/
structure MilestonePhase (P : Protocol Λ) where
  k : ℕ
  milestone : Fin k → Config Λ → Prop
  p : Fin k → ℝ
  hp_pos : ∀ i, 0 < p i
  hp_le_one : ∀ i, p i ≤ 1
  milestone_monotone : ∀ i c c',
    milestone i c → c' ∈ (P.stepDistOrSelf c).support → milestone i c'
  progress : ∀ i c,
    (∀ j < i, milestone j c) → ¬milestone i c →
    (P.stepDistOrSelf c).toMeasure {c' | milestone i c'} ≥
      ENNReal.ofReal (p i)

/-- The postcondition of a milestone phase: all milestones reached. -/
def MilestonePhase.Post {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (mp : MilestonePhase P) (c : Config Λ) : Prop :=
  ∀ i, mp.milestone i c

/-- The postcondition is absorbing: once all milestones are reached,
they stay reached (because each milestone is monotone). -/
theorem MilestonePhase.post_absorbing {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (mp : MilestonePhase P) (c : Config Λ) :
    mp.Post c → P.transitionKernel c {c' | mp.Post c'} = 1 := by
  intro hPost
  change (P.stepDistOrSelf c).toMeasure {c' | mp.Post c'} = 1
  have h_meas : MeasurableSet {c' : Config Λ | mp.Post c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  rw [(P.stepDistOrSelf c).toMeasure_apply_eq_one_iff h_meas]
  intro c' hc'
  intro i
  exact mp.milestone_monotone i c c' (hPost i) hc'

/-- Mean waiting time for the milestone phase. -/
noncomputable def MilestonePhase.meanTime {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (mp : MilestonePhase P) : ℝ :=
  ∑ i : Fin mp.k, (mp.p i)⁻¹

/-- The minimum milestone probability. -/
noncomputable def MilestonePhase.pMin {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (mp : MilestonePhase P) : ℝ :=
  ⨅ i : Fin mp.k, mp.p i

/-! ### MGF-based tail bound machinery (from DiscreteChernoff)

The following definitions and lemmas provide the MGF potential framework
for proving milestone hitting-time concentration. -/

noncomputable def geometricProductMGF (k : ℕ) (p : Fin k → ℝ) (s : ℝ) : ℝ :=
  ∏ i : Fin k, (p i * Real.exp s) / (1 - (1 - p i) * Real.exp s)

/-! ### Auxiliary lemmas for the MGF-based tail bound -/

private theorem geometricProductMGF_factor_pos {k : ℕ} {p : Fin k → ℝ} {s : ℝ}
    (hp_pos : ∀ i : Fin k, 0 < p i)
    (hs_valid : ∀ i : Fin k, (1 - p i) * Real.exp s < 1) (i : Fin k) :
    0 < (p i * Real.exp s) / (1 - (1 - p i) * Real.exp s) := by
  apply div_pos
  · exact mul_pos (hp_pos i) (Real.exp_pos s)
  · linarith [hs_valid i]

private theorem geometricProductMGF_pos {k : ℕ} {p : Fin k → ℝ} {s : ℝ}
    (hp_pos : ∀ i : Fin k, 0 < p i)
    (hs_valid : ∀ i : Fin k, (1 - p i) * Real.exp s < 1) :
    0 < geometricProductMGF k p s :=
  Finset.prod_pos fun i _ => geometricProductMGF_factor_pos hp_pos hs_valid i

private theorem geometricProductMGF_factor_ge_one {k : ℕ} {p : Fin k → ℝ} {s : ℝ}
    (hp_pos : ∀ i : Fin k, 0 < p i)
    (hp_le_one : ∀ i : Fin k, p i ≤ 1)
    (hs_pos : 0 < s)
    (hs_valid : ∀ i : Fin k, (1 - p i) * Real.exp s < 1) (i : Fin k) :
    1 ≤ (p i * Real.exp s) / (1 - (1 - p i) * Real.exp s) := by
  rw [le_div_iff₀ (by linarith [hs_valid i]), one_mul]
  -- Need: 1 - (1-p_i)*e^s ≤ p_i*e^s
  -- i.e., 1 ≤ p_i*e^s + (1-p_i)*e^s = e^s
  have : p i * Real.exp s + (1 - p i) * Real.exp s = Real.exp s := by ring
  linarith [Real.add_one_le_exp s]

private theorem geometricProductMGF_ge_one {k : ℕ} {p : Fin k → ℝ} {s : ℝ}
    (hp_pos : ∀ i : Fin k, 0 < p i)
    (hp_le_one : ∀ i : Fin k, p i ≤ 1)
    (hs_pos : 0 < s)
    (hs_valid : ∀ i : Fin k, (1 - p i) * Real.exp s < 1) :
    1 ≤ geometricProductMGF k p s :=
  Finset.one_le_prod fun i _ =>
    geometricProductMGF_factor_ge_one hp_pos hp_le_one hs_pos hs_valid i

private theorem log_geometricProductMGF_eq {k : ℕ} {p : Fin k → ℝ} {s : ℝ}
    (hp_pos : ∀ i : Fin k, 0 < p i)
    (hs_valid : ∀ i : Fin k, (1 - p i) * Real.exp s < 1) :
    Real.log (geometricProductMGF k p s) =
      ∑ i : Fin k, (s + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp s)) := by
  unfold geometricProductMGF
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h_eq : p i * Real.exp s / (1 - (1 - p i) * Real.exp s) =
        Real.exp s * p i * (1 - (1 - p i) * Real.exp s)⁻¹ := by
      rw [div_eq_mul_inv, mul_comm (p i) (Real.exp s), mul_assoc]
    rw [h_eq]
    exact shifted_geometric_mgf_closedForm_log_eq (hp_pos i) (hs_valid i)
  · intro i _
    exact (geometricProductMGF_factor_pos hp_pos hs_valid i).ne'

/-! ### Partial MGF potential for the geometric decay framework -/

/-- The set of milestones not yet reached at configuration c. -/
private noncomputable def unreachedMilestones {P : Protocol Λ}
    (mp : MilestonePhase P) (c : Config Λ) :
    Finset (Fin mp.k) :=
  Finset.filter (fun i => ¬mp.milestone i c) Finset.univ

/-- The partial MGF: product of MGF factors over unreached milestones. -/
private noncomputable def partialMGF {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) (c : Config Λ) : ℝ :=
  ∏ i ∈ unreachedMilestones mp c,
    (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s)

/-- The partial MGF is positive. -/
private theorem partialMGF_pos {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (c : Config Λ) :
    0 < partialMGF mp s c :=
  Finset.prod_pos fun i _ => geometricProductMGF_factor_pos mp.hp_pos hs_valid i

/-- The partial MGF is ≥ 1 when Post does not hold (at least one unreached milestone). -/
private theorem partialMGF_ge_one_of_not_post {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ)
    (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (c : Config Λ)
    (hc : ¬mp.Post c) :
    1 ≤ partialMGF mp s c := by
  have hne : (unreachedMilestones mp c).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hc
    intro i
    by_contra hi
    have : i ∈ unreachedMilestones mp c :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    rw [h] at this; simp at this
  exact Finset.one_le_prod fun i hi =>
    geometricProductMGF_factor_ge_one mp.hp_pos mp.hp_le_one hs_pos hs_valid i

/-- At config c₀ where no milestones are reached, the partial MGF equals the full MGF. -/
private theorem partialMGF_eq_full_of_none_reached {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ)
    (c₀ : Config Λ) (hPre : ∀ i : Fin mp.k, ¬mp.milestone i c₀) :
    partialMGF mp s c₀ = geometricProductMGF mp.k mp.p s := by
  have h_eq : unreachedMilestones mp c₀ = Finset.univ := by
    ext i
    simp only [unreachedMilestones, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hPre i
  unfold partialMGF geometricProductMGF
  rw [h_eq]

/-- The truncated potential for the geometric decay framework:
    0 when Post holds, ofReal(partialMGF) when Post does not hold. -/
private noncomputable def truncMGFPotential {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) :
    Config Λ → ℝ≥0∞ :=
  fun c => if mp.Post c then 0 else ENNReal.ofReal (partialMGF mp s c)

private theorem truncMGFPotential_measurable {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) :
    Measurable (truncMGFPotential mp s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- Milestone monotonicity for the partial MGF: if c' is reachable from c in one step,
then unreachedMilestones(c') ⊆ unreachedMilestones(c), so partialMGF(c') ≤ partialMGF(c). -/
private theorem partialMGF_mono_of_support {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ)
    (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c c' : Config Λ)
    (hsupp : c' ∈ (P.stepDistOrSelf c).support) :
    partialMGF mp s c' ≤ partialMGF mp s c := by
  unfold partialMGF
  apply Finset.prod_le_prod_of_subset_of_one_le
  · -- unreached(c') ⊆ unreached(c)
    intro i hi
    simp only [unreachedMilestones, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro h_reached_c
    exact hi (mp.milestone_monotone i c c' h_reached_c hsupp)
  · -- factors are nonneg
    intro i _
    exact le_of_lt (geometricProductMGF_factor_pos mp.hp_pos hs_valid i)
  · -- factors not in smaller set are ≥ 1
    intro i _ _
    exact geometricProductMGF_factor_ge_one mp.hp_pos mp.hp_le_one hs_pos hs_valid i

/-- If milestone j is reached in c', the partial MGF drops the j-th factor. -/
private theorem partialMGF_drop_reached {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ)
    (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c c' : Config Λ) (j : Fin mp.k)
    (hj_unreached : j ∈ unreachedMilestones mp c)
    (hj_reached : mp.milestone j c')
    (hsupp : c' ∈ (P.stepDistOrSelf c).support) :
    partialMGF mp s c' ≤
      partialMGF mp s c /
        ((mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s)) := by
  have hfj_pos : 0 < (mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s) :=
    geometricProductMGF_factor_pos mp.hp_pos hs_valid j
  rw [le_div_iff₀ hfj_pos]
  -- Need: partialMGF(c') · f_j ≤ partialMGF(c)
  have h_sub : unreachedMilestones mp c' ⊆ (unreachedMilestones mp c).erase j := by
    intro i hi
    simp only [unreachedMilestones, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [Finset.mem_erase]
    constructor
    · intro h_eq; rw [h_eq] at hi; exact hi hj_reached
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h_reached_c
      exact hi (mp.milestone_monotone i c c' h_reached_c hsupp)
  have h_nonneg : ∀ i ∈ unreachedMilestones mp c',
      0 ≤ (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s) :=
    fun i _ => le_of_lt (geometricProductMGF_factor_pos mp.hp_pos hs_valid i)
  have h_ge_one : ∀ i ∈ (unreachedMilestones mp c).erase j,
      i ∉ unreachedMilestones mp c' →
      1 ≤ (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s) :=
    fun i _ _ => geometricProductMGF_factor_ge_one mp.hp_pos mp.hp_le_one hs_pos hs_valid i
  have h_prod_sub : partialMGF mp s c' ≤
      ∏ i ∈ (unreachedMilestones mp c).erase j,
        (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s) :=
    Finset.prod_le_prod_of_subset_of_one_le h_sub h_nonneg h_ge_one
  calc partialMGF mp s c' *
        ((mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s))
      ≤ (∏ i ∈ (unreachedMilestones mp c).erase j,
          (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s)) *
        ((mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s)) := by gcongr
    _ = ∏ i ∈ insert j ((unreachedMilestones mp c).erase j),
          (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s) := by
          rw [Finset.prod_insert (by simp [Finset.mem_erase])]; ring
    _ = partialMGF mp s c := by congr 1; exact Finset.insert_erase hj_unreached

/-- The algebraic contraction identity:
(1 - p_j) + p_j / f_j = exp(-s) where f_j = p_j · exp(s) / (1 - (1-p_j)·exp(s)). -/
private theorem mgf_contraction_identity (p s : ℝ) (hp_pos : 0 < p)
    (hs_valid : (1 - p) * Real.exp s < 1) :
    (1 - p) + p * ((1 - (1 - p) * Real.exp s) / (p * Real.exp s)) = Real.exp (-s) := by
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hexp_ne : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp
  rw [Real.exp_neg]
  field_simp [hp_ne, hexp_ne]
  ring

/-- The first unreached milestone index. -/
private noncomputable def firstUnreached' {P : Protocol Λ}
    (mp : MilestonePhase P) (c : Config Λ)
    (hne : (unreachedMilestones mp c).Nonempty) : Fin mp.k :=
  (unreachedMilestones mp c).min' hne

private theorem unreachedMilestones_nonempty_of_not_post {P : Protocol Λ}
    (mp : MilestonePhase P)
    (c : Config Λ) (hc : ¬mp.Post c) :
    (unreachedMilestones mp c).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  apply hc
  intro i
  by_contra hi
  have : i ∈ unreachedMilestones mp c :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  rw [h] at this; simp at this

private theorem firstUnreached_spec {P : Protocol Λ}
    (mp : MilestonePhase P) (c : Config Λ)
    (hc : ¬mp.Post c) :
    ¬mp.milestone (firstUnreached' mp c (unreachedMilestones_nonempty_of_not_post mp c hc)) c := by
  have := Finset.min'_mem _ (unreachedMilestones_nonempty_of_not_post mp c hc)
  simp only [firstUnreached', unreachedMilestones, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

private theorem firstUnreached_minimal {P : Protocol Λ}
    (mp : MilestonePhase P) (c : Config Λ)
    (hc : ¬mp.Post c) (i : Fin mp.k)
    (hi : i < firstUnreached' mp c (unreachedMilestones_nonempty_of_not_post mp c hc)) :
    mp.milestone i c := by
  by_contra h_not
  have h_mem : i ∈ unreachedMilestones mp c :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_not⟩
  have := Finset.min'_le _ _ h_mem
  exact absurd (lt_of_lt_of_le hi this) (lt_irrefl _)

private theorem firstUnreached_in_unreached {P : Protocol Λ}
    (mp : MilestonePhase P) (c : Config Λ)
    (hc : ¬mp.Post c) :
    firstUnreached' mp c (unreachedMilestones_nonempty_of_not_post mp c hc) ∈ unreachedMilestones mp c :=
  Finset.min'_mem _ _

/-- Pointwise bound on partialMGF under the kernel. -/
private theorem partialMGF_pointwise_bound {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config Λ) (hc : ¬mp.Post c)
    (j : Fin mp.k) (hj_unreached : j ∈ unreachedMilestones mp c) :
    ∀ᵐ c' ∂(P.stepDistOrSelf c).toMeasure,
      ENNReal.ofReal (partialMGF mp s c') ≤
        if mp.milestone j c' then
          ENNReal.ofReal (partialMGF mp s c /
            ((mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s)))
        else
          ENNReal.ofReal (partialMGF mp s c) := by
  rw [ae_iff]
  set badSet := {c' | ¬(ENNReal.ofReal (partialMGF mp s c') ≤
      if mp.milestone j c' then
        ENNReal.ofReal (partialMGF mp s c /
          ((mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s)))
      else ENNReal.ofReal (partialMGF mp s c))} with hbadSet_def
  suffices h : Disjoint (P.stepDistOrSelf c).support badSet by
    have h_meas : MeasurableSet badSet := DiscreteMeasurableSpace.forall_measurableSet _
    rw [PMF.toMeasure_apply_eq_zero_iff (p := P.stepDistOrSelf c) h_meas]
    exact h
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  apply hbad
  by_cases hm : mp.milestone j c'
  · simp only [hm, ite_true]
    exact ENNReal.ofReal_le_ofReal
      (partialMGF_drop_reached mp s hs_pos hs_valid c c' j hj_unreached hm hsupp)
  · simp only [hm, ite_false]
    exact ENNReal.ofReal_le_ofReal
      (partialMGF_mono_of_support mp s hs_pos hs_valid c c' hsupp)

/-- One-step contraction of the ENNReal partial MGF potential. -/
private theorem partialMGF_one_step_contraction {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config Λ) (hc : ¬mp.Post c) :
    ∫⁻ c', ENNReal.ofReal (partialMGF mp s c') ∂(P.transitionKernel c) ≤
      ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (partialMGF mp s c) := by
  set j := firstUnreached' mp c (unreachedMilestones_nonempty_of_not_post mp c hc) with hj_def
  have hj_unreached := firstUnreached_spec mp c hc
  have hj_minimal := firstUnreached_minimal mp c hc
  have hj_in := firstUnreached_in_unreached mp c hc
  set Mj := {c' : Config Λ | mp.milestone j c'} with hMj_def
  have hMj_meas : MeasurableSet Mj := DiscreteMeasurableSpace.forall_measurableSet _
  set Φc := partialMGF mp s c with hΦc_def
  set fj := (mp.p j * Real.exp s) / (1 - (1 - mp.p j) * Real.exp s) with hfj_def
  have hΦc_pos : 0 < Φc := partialMGF_pos mp s hs_valid c
  have hfj_pos : 0 < fj := geometricProductMGF_factor_pos mp.hp_pos hs_valid j
  have hfj_ge_one : 1 ≤ fj :=
    geometricProductMGF_factor_ge_one mp.hp_pos mp.hp_le_one hs_pos hs_valid j
  change ∫⁻ c', ENNReal.ofReal (partialMGF mp s c') ∂(P.stepDistOrSelf c).toMeasure ≤ _
  have h_bound := partialMGF_pointwise_bound mp s hs_pos hs_valid c hc j hj_in
  calc ∫⁻ c', ENNReal.ofReal (partialMGF mp s c') ∂(P.stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if mp.milestone j c' then ENNReal.ofReal (Φc / fj)
          else ENNReal.ofReal Φc) ∂(P.stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        exact h_bound
    _ = (∫⁻ c' in Mj, ENNReal.ofReal (Φc / fj) ∂(P.stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Mjᶜ, ENNReal.ofReal Φc ∂(P.stepDistOrSelf c).toMeasure) := by
        rw [← lintegral_add_compl _ hMj_meas]
        congr 1
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hMj_meas] with c' hc'
          simp only [Set.mem_setOf_eq, Mj] at hc'
          simp [hc']
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hMj_meas.compl] with c' hc'
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Mj] at hc'
          simp [hc']
    _ = ENNReal.ofReal (Φc / fj) * (P.stepDistOrSelf c).toMeasure Mj +
        ENNReal.ofReal Φc * (P.stepDistOrSelf c).toMeasure Mjᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal Φc := by
        set q := (P.stepDistOrSelf c).toMeasure Mj with hq_def
        set qc := (P.stepDistOrSelf c).toMeasure Mjᶜ with hqc_def
        have hq_ge : q ≥ ENNReal.ofReal (mp.p j) := by
          apply mp.progress j c
          · intro i hi; exact hj_minimal i hi
          · exact hj_unreached
        haveI : IsProbabilityMeasure (P.stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        have hq_le_one : q ≤ 1 := by
          calc q ≤ (P.stepDistOrSelf c).toMeasure Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hMj_meas hq_ne_top
          rw [show (P.stepDistOrSelf c).toMeasure Set.univ = 1 from measure_univ] at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have hpj_le_qr : mp.p j ≤ qr := by
          have h1 : ENNReal.ofReal (mp.p j) ≤ ENNReal.ofReal qr := by rwa [← hq_ofReal]
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have hΦc_div_fj_nonneg : 0 ≤ Φc / fj := div_nonneg hΦc_pos.le hfj_pos.le
        have hΦc_nonneg : (0 : ℝ) ≤ Φc := hΦc_pos.le
        have hexp_neg_s_nonneg : (0 : ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
        have lhs_eq : ENNReal.ofReal (Φc / fj) * q + ENNReal.ofReal Φc * qc =
            ENNReal.ofReal (Φc / fj * qr + Φc * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hΦc_div_fj_nonneg,
              ← ENNReal.ofReal_mul hΦc_nonneg,
              ← ENNReal.ofReal_add (mul_nonneg hΦc_div_fj_nonneg hqr_nonneg)
                (mul_nonneg hΦc_nonneg h1mqr_nonneg)]
        have rhs_eq : ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal Φc =
            ENNReal.ofReal (Real.exp (-s) * Φc) := by
          rw [← ENNReal.ofReal_mul hexp_neg_s_nonneg]
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        have hfj_ne : fj ≠ 0 := hfj_pos.ne'
        have hpj_pos := mp.hp_pos j
        have h_factor : Φc / fj * qr + Φc * (1 - qr) = Φc * ((1 - qr) + qr / fj) := by
          field_simp; ring
        have h_rhs_factor : Real.exp (-s) * Φc = Φc * Real.exp (-s) := by ring
        rw [h_factor, h_rhs_factor]
        apply mul_le_mul_of_nonneg_left _ hΦc_nonneg
        have h_inv_fj : (1 - (1 - mp.p j) * Real.exp s) / (mp.p j * Real.exp s) = 1 / fj := by
          rw [hfj_def]; field_simp
        have h_identity := mgf_contraction_identity (mp.p j) s hpj_pos (hs_valid j)
        rw [h_inv_fj] at h_identity
        have h_identity' : 1 - mp.p j * (1 - 1 / fj) = Real.exp (-s) := by linarith
        have h_rewrite : (1 - qr) + qr / fj = 1 - qr * (1 - 1 / fj) := by field_simp; ring
        rw [h_rewrite, ← h_identity']
        have h_coeff_nonneg : 0 ≤ 1 - 1 / fj := by
          rw [sub_nonneg, div_le_one hfj_pos]; exact hfj_ge_one
        linarith [mul_le_mul_of_nonneg_right hpj_le_qr h_coeff_nonneg]

/-- One-step contraction of the partial MGF potential under the kernel. -/
private theorem truncMGFPotential_contracts {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config Λ) :
    ∫⁻ c', truncMGFPotential mp s c' ∂(P.transitionKernel c) ≤
      ENNReal.ofReal (Real.exp (-s)) * truncMGFPotential mp s c := by
  by_cases hc : mp.Post c
  · -- Post c: truncated potential = 0, need ∫ ≤ 0. By absorbing, K(c,{Post}) = 1.
    simp only [truncMGFPotential, if_pos hc, mul_zero]
    have h_ae : (fun c' => if mp.Post c' then (0 : ℝ≥0∞)
        else ENNReal.ofReal (partialMGF mp s c')) =ᵐ[P.transitionKernel c] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | mp.Post y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have h1 := mp.post_absorbing c hc
        have h_meas : MeasurableSet {y | mp.Post y} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        have h_ne_top : P.transitionKernel c {y | mp.Post y} ≠ ⊤ := by
          rw [h1]; exact ENNReal.one_ne_top
        calc P.transitionKernel c {y | mp.Post y}ᶜ
            = P.transitionKernel c Set.univ - P.transitionKernel c {y | mp.Post y} :=
              measure_compl h_meas h_ne_top
          _ = 1 - 1 := by rw [measure_univ, h1]
          _ = 0 := tsub_self _
      · intro y hy
        exact if_pos hy
    exact le_of_eq (lintegral_eq_zero_of_ae_eq_zero h_ae)
  · -- ¬Post c: need ∫ Φ̃ ≤ exp(-s) · Φ(c)
    simp only [truncMGFPotential, if_neg hc]
    calc ∫⁻ c', (if mp.Post c' then 0
            else ENNReal.ofReal (partialMGF mp s c')) ∂(P.transitionKernel c)
        ≤ ∫⁻ c', ENNReal.ofReal (partialMGF mp s c') ∂(P.transitionKernel c) := by
          apply lintegral_mono
          intro c'
          by_cases hc' : mp.Post c'
          · simp [hc']
          · simp [hc']
      _ ≤ ENNReal.ofReal (Real.exp (-s)) *
          ENNReal.ofReal (partialMGF mp s c) :=
        partialMGF_one_step_contraction mp s hs_pos hs_valid c hc

/-- {¬Post} ⊆ {1 ≤ Φ̃}: the truncated MGF potential is ≥ 1 on ¬Post configs. -/
private theorem not_post_subset_ge_one {P : Protocol Λ}
    (mp : MilestonePhase P) (s : ℝ) (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) :
    {c | ¬mp.Post c} ⊆ {c | 1 ≤ truncMGFPotential mp s c} := by
  intro c hc
  simp only [Set.mem_setOf_eq] at hc ⊢
  rw [show truncMGFPotential mp s c = ENNReal.ofReal (partialMGF mp s c) from
    if_neg hc]
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (partialMGF_ge_one_of_not_post mp s hs_pos hs_valid c hc)

/-- Milestone tail bound via MGF. -/
theorem milestone_tail_bound_via_mgf {P : Protocol Λ}
    (mp : MilestonePhase P)
    (c₀ : Config Λ)
    (hPre : ∀ i : Fin mp.k, ¬mp.milestone i c₀)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (t : ℕ) :
    (P.transitionKernel ^ t) c₀ {c | ¬mp.Post c} ≤
      ENNReal.ofReal (Real.exp (-s * t) * geometricProductMGF mp.k mp.p s) := by
  by_cases hk : mp.k = 0
  · have : {c : Config Λ | ¬mp.Post c} = ∅ := by
      ext c; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro i; exact absurd i.2 (by omega)
    simp [this]
  have hk_pos : 0 < mp.k := Nat.pos_of_ne_zero hk
  haveI : Nonempty (Fin mp.k) := ⟨⟨0, hk_pos⟩⟩
  have hMGF_pos := geometricProductMGF_pos mp.hp_pos hs_valid
  have hexp_s_pos : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have h_subset := not_post_subset_ge_one mp s hs_pos hs_valid
  have h_decay := PopProtoCommon.measure_potential_ge_one
    P.transitionKernel (truncMGFPotential mp s) (truncMGFPotential_measurable mp s)
    (ENNReal.ofReal (Real.exp (-s)))
    (truncMGFPotential_contracts mp s hs_pos hs_valid)
    t c₀
  calc (P.transitionKernel ^ t) c₀ {c | ¬mp.Post c}
      ≤ (P.transitionKernel ^ t) c₀ {c | 1 ≤ truncMGFPotential mp s c} :=
        measure_mono h_subset
    _ ≤ ENNReal.ofReal (Real.exp (-s)) ^ t * truncMGFPotential mp s c₀ := h_decay
    _ = ENNReal.ofReal (Real.exp (-s)) ^ t *
        ENNReal.ofReal (geometricProductMGF mp.k mp.p s) := by
          congr 1
          show truncMGFPotential mp s c₀ = _
          have hNotPost : ¬mp.Post c₀ := fun h => absurd (h ⟨0, hk_pos⟩) (hPre ⟨0, hk_pos⟩)
          rw [show truncMGFPotential mp s c₀ =
              ENNReal.ofReal (partialMGF mp s c₀) from if_neg hNotPost]
          congr 1
          exact partialMGF_eq_full_of_none_reached mp s c₀ hPre
    _ = ENNReal.ofReal (Real.exp (-s * t)) *
        ENNReal.ofReal (geometricProductMGF mp.k mp.p s) := by
          congr 1
          rw [← ENNReal.ofReal_pow hexp_s_pos.le]
          congr 1
          rw [show -s * (t : ℝ) = (t : ℝ) * (-s) from by ring, Real.exp_nat_mul]
    _ = ENNReal.ofReal (Real.exp (-s * t) * geometricProductMGF mp.k mp.p s) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

private theorem milestonePhase_pMin_pos {P : Protocol Λ}
    (mp : MilestonePhase P) (hk : 0 < mp.k) :
    0 < mp.pMin := by
  unfold MilestonePhase.pMin
  haveI : Nonempty (Fin mp.k) := ⟨⟨0, hk⟩⟩
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_min_image Finset.univ mp.p
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have h_eq : ⨅ i, mp.p i = mp.p j₀ := le_antisymm
    (ciInf_le ⟨0, fun x ⟨j, hj⟩ => hj ▸ le_of_lt (mp.hp_pos j)⟩ j₀)
    (le_ciInf fun i => hj₀ i (Finset.mem_univ i))
  rw [h_eq]; exact mp.hp_pos j₀

private theorem milestonePhase_pMin_le {P : Protocol Λ}
    (mp : MilestonePhase P) (i : Fin mp.k) :
    mp.pMin ≤ mp.p i :=
  ciInf_le ⟨0, fun _ ⟨j, hj⟩ => hj ▸ le_of_lt (mp.hp_pos j)⟩ i

/-- The Janson exponential tail from MGF. -/
theorem janson_exponential_tail_from_mgf {P : Protocol Λ}
    (mp : MilestonePhase P)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (t : ℝ) (ht : lam * mp.meanTime ≤ t)
    (s : ℝ) (hs_opt : s = mp.pMin * (1 - 1 / lam)) :
    Real.exp (-s * t) * geometricProductMGF mp.k mp.p s ≤
      Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam)) := by
  -- Handle k = 0: product = 1, meanTime = 0, RHS = exp(0) = 1
  by_cases hk : mp.k = 0
  · have h_fin_empty : (Finset.univ : Finset (Fin mp.k)) = ∅ := by
      ext ⟨i, hi⟩; omega
    have h_prod : geometricProductMGF mp.k mp.p s = 1 := by
      simp [geometricProductMGF, h_fin_empty]
    have h_mean : mp.meanTime = 0 := by
      simp [MilestonePhase.meanTime, h_fin_empty]
    have h_rhs : Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam)) = 1 := by
      rw [h_mean, mul_zero, zero_mul, Real.exp_zero]
    have hpmin_zero : mp.pMin = 0 := by
      unfold MilestonePhase.pMin
      have : IsEmpty (Fin mp.k) := by rw [hk]; exact inferInstance
      simp [iInf, Set.range_eq_empty, Real.sInf_empty]
    have hs_zero : s = 0 := by rw [hs_opt, hpmin_zero]; ring
    rw [h_prod, mul_one, h_rhs, hs_zero, neg_zero, zero_mul, Real.exp_zero]
  -- Handle lam = 1: s = 0, MGF(0) = ∏ p/p = 1
  by_cases hlam_eq : lam = 1
  · subst hlam_eq
    have hs_zero : s = 0 := by rw [hs_opt]; simp
    subst hs_zero
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, Real.log_one, sub_self, mul_zero]
    unfold geometricProductMGF
    apply Finset.prod_le_one
    · intro i _
      apply div_nonneg
      · exact mul_nonneg (mp.hp_pos i).le (Real.exp_pos 0).le
      · have : (1 - (1 - mp.p i) * Real.exp 0) = mp.p i := by
          rw [Real.exp_zero, mul_one]; ring
        rw [this]; exact (mp.hp_pos i).le
    · intro i _
      have h1 : (1 - (1 - mp.p i) * Real.exp 0) = mp.p i := by
        rw [Real.exp_zero, mul_one]; ring
      have h2 : mp.p i * Real.exp 0 = mp.p i := by rw [Real.exp_zero, mul_one]
      rw [h1, h2]
      exact (div_le_one (mp.hp_pos i)).mpr le_rfl
  -- Main case: k > 0, lam > 1
  have hk_pos : 0 < mp.k := Nat.pos_of_ne_zero hk
  have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hlam_gt : 1 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_eq)
  haveI : Nonempty (Fin mp.k) := ⟨⟨0, hk_pos⟩⟩
  have hpmin_pos : 0 < mp.pMin := milestonePhase_pMin_pos mp hk_pos
  have hpmin_le := milestonePhase_pMin_le mp
  have h_coeff_pos : 0 < 1 - 1 / lam := by
    rw [sub_pos, div_lt_one hlam_pos]; exact hlam_gt
  have hs_pos : 0 < s := by rw [hs_opt]; exact mul_pos hpmin_pos h_coeff_pos
  have hs_valid : ∀ i : Fin mp.k, (1 - mp.p i) * Real.exp s < 1 := by
    intro i
    have hsi : s ≤ mp.p i := by
      calc s = mp.pMin * (1 - 1 / lam) := hs_opt
        _ ≤ mp.pMin * 1 := by
            apply mul_le_mul_of_nonneg_left _ hpmin_pos.le
            linarith [div_pos one_pos hlam_pos]
        _ = mp.pMin := mul_one _
        _ ≤ mp.p i := hpmin_le i
    have hne : (-s : ℝ) ≠ 0 := by linarith
    calc (1 - mp.p i) * Real.exp s
        ≤ (1 - s) * Real.exp s := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos s).le; linarith
      _ < 1 := by
          have h1 : 1 - s < Real.exp (-s) := by linarith [Real.add_one_lt_exp hne]
          have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos s)
          rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have hprod_pos : 0 < geometricProductMGF mp.k mp.p s :=
    geometricProductMGF_pos mp.hp_pos hs_valid
  have h_exp_mono : Real.exp (-s * t) ≤ Real.exp (-s * (lam * mp.meanTime)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left ht (by linarith))
  have hs_conv : s = (1 - lam⁻¹) * mp.pMin := by rw [hs_opt]; ring
  have hpoint : ∀ i : Fin mp.k,
      s + Real.log (mp.p i) - Real.log (1 - (1 - mp.p i) * Real.exp s) ≤
        s * lam * (mp.p i)⁻¹ -
          mp.pMin * (mp.p i)⁻¹ * (lam - 1 - Real.log lam) :=
    fun i => shifted_geometric_mgf_closedForm_log_le_upper_janson_point
      (hp_pos := mp.hp_pos i) (hpmin_nonneg := hpmin_pos.le)
      (hpmin_le := hpmin_le i) (hlam_ge_one := hlam) (ht := hs_conv)
  have hlog_sum :
      ∑ i : Fin mp.k, (s + Real.log (mp.p i) -
        Real.log (1 - (1 - mp.p i) * Real.exp s)) ≤
      ∑ i : Fin mp.k, (s * lam * (mp.p i)⁻¹ -
        mp.pMin * (mp.p i)⁻¹ * (lam - 1 - Real.log lam)) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have h_sum_eq :
      ∑ i : Fin mp.k, (s * lam * (mp.p i)⁻¹ -
        mp.pMin * (mp.p i)⁻¹ * (lam - 1 - Real.log lam)) =
      s * lam * mp.meanTime - mp.pMin * mp.meanTime * (lam - 1 - Real.log lam) := by
    unfold MilestonePhase.meanTime
    have h_factor : ∀ i : Fin mp.k,
        s * lam * (mp.p i)⁻¹ - mp.pMin * (mp.p i)⁻¹ * (lam - 1 - Real.log lam) =
        (s * lam - mp.pMin * (lam - 1 - Real.log lam)) * (mp.p i)⁻¹ := fun i => by ring
    simp_rw [h_factor, ← Finset.mul_sum]
    ring
  have h_combined_log :
      -s * (lam * mp.meanTime) +
        ∑ i : Fin mp.k, (s + Real.log (mp.p i) -
          Real.log (1 - (1 - mp.p i) * Real.exp s)) ≤
      -mp.pMin * mp.meanTime * (lam - 1 - Real.log lam) := by
    linarith [hlog_sum.trans (le_of_eq h_sum_eq)]
  have h_exp_prod :
      Real.exp (-s * (lam * mp.meanTime)) * geometricProductMGF mp.k mp.p s ≤
        Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam)) := by
    have h_lhs_pos := mul_pos (Real.exp_pos (-s * (lam * mp.meanTime))) hprod_pos
    rw [← Real.log_le_iff_le_exp h_lhs_pos]
    calc Real.log (Real.exp (-s * (lam * mp.meanTime)) *
            geometricProductMGF mp.k mp.p s)
        = -s * (lam * mp.meanTime) +
            Real.log (geometricProductMGF mp.k mp.p s) := by
          rw [Real.log_mul (Real.exp_pos _).ne' hprod_pos.ne', Real.log_exp]
      _ = -s * (lam * mp.meanTime) +
          ∑ i : Fin mp.k, (s + Real.log (mp.p i) -
            Real.log (1 - (1 - mp.p i) * Real.exp s)) := by
          rw [log_geometricProductMGF_eq mp.hp_pos hs_valid]
      _ ≤ -mp.pMin * mp.meanTime * (lam - 1 - Real.log lam) := h_combined_log
  calc Real.exp (-s * t) * geometricProductMGF mp.k mp.p s
      ≤ Real.exp (-s * (lam * mp.meanTime)) * geometricProductMGF mp.k mp.p s :=
      mul_le_mul_of_nonneg_right h_exp_mono hprod_pos.le
    _ ≤ Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam)) := h_exp_prod

private theorem kernel_pow_le_one {P : Protocol Λ}
    [IsMarkovKernel P.transitionKernel]
    (t : ℕ) (x : Config Λ) (S : Set (Config Λ)) :
    (P.transitionKernel ^ t) x S ≤ 1 := by
  calc (P.transitionKernel ^ t) x S ≤ (P.transitionKernel ^ t) x Set.univ := measure_mono (Set.subset_univ S)
    _ ≤ 1 := by
        induction t with
        | zero =>
            rw [show P.transitionKernel ^ 0 = Kernel.id from pow_zero P.transitionKernel, Kernel.id_apply]
            haveI : MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac x) :=
              MeasureTheory.Measure.dirac.isProbabilityMeasure
            exact prob_le_one
        | succ t ih =>
            rw [Kernel.pow_succ_apply_eq_lintegral P.transitionKernel t x MeasurableSet.univ]
            calc ∫⁻ y, P.transitionKernel y Set.univ ∂((P.transitionKernel ^ t) x)
                ≤ ∫⁻ _ : Config Λ, (1 : ℝ≥0∞) ∂((P.transitionKernel ^ t) x) := by
                    apply lintegral_mono; intro y
                    haveI : IsProbabilityMeasure (P.transitionKernel y) :=
                      (inferInstance : IsMarkovKernel P.transitionKernel).isProbabilityMeasure y
                    simp [measure_univ]
              _ = (P.transitionKernel ^ t) x Set.univ := by simp
              _ ≤ 1 := ih

/-- **Milestone hitting-time concentration via Janson.**

If the protocol has k milestones with per-step probabilities p_i,
then the probability of NOT completing all milestones within
λ · μ_T steps is at most exp(-p_min · μ_T · (λ-1-log λ)).

This is the bridge from JansonGeometric.lean's pure probability
result to the protocol level. -/
theorem milestone_hitting_time_bound
    {P : Protocol Λ}
    (mp : MilestonePhase P)
    (c₀ : Config Λ)
    (hPre : ∀ i : Fin mp.k, ¬mp.milestone i c₀)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (t : ℕ) (ht : (lam * mp.meanTime) ≤ (t : ℝ)) :
    (P.transitionKernel ^ t) c₀ {c | ¬mp.Post c} ≤
      ENNReal.ofReal (Real.exp (-mp.pMin * mp.meanTime *
        (lam - 1 - Real.log lam))) := by
  by_cases hk : mp.k = 0
  · have : {c : Config Λ | ¬mp.Post c} = ∅ := by
      ext c; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro i; exact absurd i.2 (by omega)
    simp [this]
  by_cases hlam_eq : lam = 1
  · have hzero : -mp.pMin * mp.meanTime * (lam - 1 - Real.log lam) = 0 := by
      rw [hlam_eq, Real.log_one]; ring
    rw [hzero, Real.exp_zero, ENNReal.ofReal_one]
    exact kernel_pow_le_one t c₀ _
  · have hlam_gt : 1 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_eq)
    have hk_pos : 0 < mp.k := Nat.pos_of_ne_zero hk
    let s : ℝ := mp.pMin * (1 - 1 / lam)
    have hpmin_pos : 0 < mp.pMin := milestonePhase_pMin_pos mp hk_pos
    have hs_pos : 0 < s := by
      apply mul_pos hpmin_pos
      have : 1 / lam < 1 := by
        rw [div_lt_one (show (0 : ℝ) < lam by linarith)]; exact hlam_gt
      linarith
    have hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1 := by
      intro i
      have hsi : s ≤ mp.p i := by
        calc s = mp.pMin * (1 - 1 / lam) := rfl
          _ ≤ mp.pMin * 1 := by
              apply mul_le_mul_of_nonneg_left _ hpmin_pos.le
              linarith [div_pos one_pos (show (0 : ℝ) < lam by linarith)]
          _ = mp.pMin := mul_one _
          _ ≤ mp.p i := milestonePhase_pMin_le mp i
      have hne : (-s : ℝ) ≠ 0 := by linarith
      calc (1 - mp.p i) * Real.exp s
          ≤ (1 - s) * Real.exp s := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos s).le; linarith
        _ < 1 := by
            have h1 : 1 - s < Real.exp (-s) := by linarith [Real.add_one_lt_exp hne]
            have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos s)
            rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
    have h_tail := milestone_tail_bound_via_mgf mp c₀ hPre s hs_pos hs_valid t
    have h_opt := janson_exponential_tail_from_mgf mp lam hlam (t : ℝ) ht s rfl
    exact le_trans h_tail (ENNReal.ofReal_le_ofReal h_opt)

/-- Corollary: for any ε > 0, choosing t = C · μ_T / p_min · log(1/ε)
ensures the failure probability is at most ε.

This instantiates a PhaseConvergence from a MilestonePhase. -/
theorem milestone_to_phase_convergence
    (mp : MilestonePhase P)
    (Pre : Config Λ → Prop)
    (hPre_impl : ∀ c, Pre c → ∀ i, ¬mp.milestone i c)
    (n : ℕ) (hn : 2 ≤ n)
    (t : ℕ) (ε : ℝ≥0)
    (hε : 0 < ε)
    (ht : (2 * mp.meanTime) ≤ (t : ℝ))
    (hε_bound : Real.exp (-mp.pMin * mp.meanTime *
      (2 - 1 - Real.log 2)) ≤ (ε : ℝ)) :
    ∀ c₀, Pre c₀ →
      (P.transitionKernel ^ t) c₀ {c | ¬mp.Post c} ≤ (ε : ℝ≥0∞) := by
  intro c₀ hPre₀
  have hPre_milestones := hPre_impl c₀ hPre₀
  calc (P.transitionKernel ^ t) c₀ {c | ¬mp.Post c}
      ≤ ENNReal.ofReal (Real.exp (-mp.pMin * mp.meanTime *
          (2 - 1 - Real.log 2))) :=
        milestone_hitting_time_bound mp c₀ hPre_milestones 2 (by norm_num) t ht
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hε_bound
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- Build a `PhaseConvergence` from a `MilestonePhase`.

This is the key bridge: a MilestonePhase (whose progress is analyzed via
Janson's geometric tail bound) produces a PhaseConvergence (which composes
with other phases via union bound). -/
noncomputable def MilestonePhase.toPhaseConvergence
    (mp : MilestonePhase P)
    (Pre : Config Λ → Prop)
    (hPre_impl : ∀ c, Pre c → ∀ i, ¬mp.milestone i c)
    (t : ℕ) (ε : ℝ≥0)
    (hε_pos : 0 < ε)
    (ht : (2 * mp.meanTime) ≤ (t : ℝ))
    (hε_bound : Real.exp (-mp.pMin * mp.meanTime *
      (2 - 1 - Real.log 2)) ≤ (ε : ℝ)) :
    PhaseConvergence P.transitionKernel where
  Pre := Pre
  Post := mp.Post
  t := t
  ε := ε
  post_absorbing := fun c hc => mp.post_absorbing c hc
  convergence := fun c₀ hPre₀ =>
    milestone_to_phase_convergence mp Pre hPre_impl 2 (by omega)
      t ε hε_pos ht hε_bound c₀ hPre₀

end ExactMajority

/-
# Drift-Based Hitting-Time Wrapper for Population Protocols

Bridge from the geometric drift bounds to PhaseConvergence.

Key idea: if Φ contracts with rate r inside {¬Post}, and Post is absorbing
under K, then the truncated potential Φ̃(c) = if ¬Post c then Φ(c) else 0
contracts GLOBALLY under K. This is because K sends Post states to Post
(absorbing), where Φ̃ = 0.

Then `measure_potential_ge_one` from PopProtoCommon gives
  K^t(c₀, {¬Post}) ≤ r^t · Φ̃(c₀) ≤ r^t · M ≤ ε.

No absorbed kernel needed. The truncation + absorbing Post does all the work.

Reference: PopProtoCommon/GeometricDrift.lean (lintegral_geometric_decay,
measure_potential_ge_one).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale
import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- A drift phase: Φ contracts inside {¬Post} with rate r, Post is absorbing.

This handles both "global drift" (Φ contracts everywhere) and "regional drift"
(Φ contracts only where ¬Post) in one structure. Stuck states outside
{¬Post} are in Post and absorbing — they contribute 0 to the truncated
potential, so they don't obstruct the bound. -/
structure DriftPhase (P : Protocol Λ) where
  Pre : Config Λ → Prop
  Post : Config Λ → Prop
  Φ : Config Λ → ℝ≥0∞
  hΦ : Measurable Φ
  r : ℝ≥0∞
  M : ℝ≥0∞
  post_iff : ∀ c, Post c ↔ Φ c < 1
  hdrift : ∀ c, ¬Post c →
    ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c
  hM : ∀ c, Pre c → Φ c ≤ M
  post_absorbing : ∀ c, Post c →
    P.transitionKernel c {y | Post y} = 1

/-- The truncated potential: Φ on {¬Post}, 0 on {Post}. -/
noncomputable def DriftPhase.truncPotential {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (dp : DriftPhase P) (c : Config Λ) : ℝ≥0∞ :=
  if dp.Post c then 0 else dp.Φ c

private theorem truncPotential_measurable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (dp : DriftPhase P) :
    Measurable dp.truncPotential := by
  apply Measurable.ite
  · exact DiscreteMeasurableSpace.forall_measurableSet _
  · exact measurable_const
  · exact dp.hΦ

/-- The truncated potential contracts under K globally.
- Inside {¬Post}: K is the kernel, Φ̃ ≤ Φ, so ∫ Φ̃ ≤ ∫ Φ ≤ r · Φ = r · Φ̃.
- Inside {Post}: K(c, {Post}) = 1, Φ̃ = 0 on {Post}, so ∫ Φ̃ = 0 = r · 0 = r · Φ̃. -/
theorem DriftPhase.truncPotential_contracts {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} [IsMarkovKernel P.transitionKernel]
    (dp : DriftPhase P) (c : Config Λ) :
    ∫⁻ c', dp.truncPotential c' ∂(P.transitionKernel c) ≤
      dp.r * dp.truncPotential c := by
  by_cases hc : dp.Post c
  · -- Case: c ∈ Post. truncPotential c = 0, so RHS = r·0 = 0.
    simp only [DriftPhase.truncPotential, if_pos hc, mul_zero]
    -- Need: ∫⁻ truncPotential dK(c) = 0. Since K(c, {Post}) = 1 and truncPotential = 0 on Post.
    have h_ae : dp.truncPotential =ᵐ[P.transitionKernel c] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | dp.Post y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have h1 := dp.post_absorbing c hc
        have h_meas : MeasurableSet {y | dp.Post y} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        have h_ne_top : P.transitionKernel c {y | dp.Post y} ≠ ⊤ := by
          rw [h1]; exact ENNReal.one_ne_top
        calc P.transitionKernel c {y | dp.Post y}ᶜ
            = P.transitionKernel c Set.univ - P.transitionKernel c {y | dp.Post y} :=
              measure_compl h_meas h_ne_top
          _ = 1 - 1 := by rw [measure_univ, h1]
          _ = 0 := tsub_self _
      · intro y hy
        change dp.truncPotential y = (0 : ℝ≥0∞)
        exact if_pos hy
    exact le_of_eq (lintegral_eq_zero_of_ae_eq_zero h_ae)
  · -- Case: c ∉ Post. truncPotential c = Φ c. Show ∫ truncPotential ≤ r · Φ c.
    simp only [DriftPhase.truncPotential, if_neg hc]
    calc ∫⁻ c', (if dp.Post c' then 0 else dp.Φ c') ∂(P.transitionKernel c)
        ≤ ∫⁻ c', dp.Φ c' ∂(P.transitionKernel c) := by
          apply lintegral_mono
          intro c'
          by_cases hc' : dp.Post c'
          · simp [hc']
          · simp [hc']
      _ ≤ dp.r * dp.Φ c := dp.hdrift c hc

/-- {¬Post} = {1 ≤ Φ̃}: the truncated potential is ≥ 1 exactly on {¬Post}. -/
theorem DriftPhase.not_post_eq_ge_one {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} (dp : DriftPhase P) :
    {c | ¬dp.Post c} = {c | 1 ≤ dp.truncPotential c} := by
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hc
    change 1 ≤ dp.truncPotential c
    rw [show dp.truncPotential c = dp.Φ c from if_neg hc]
    exact not_lt.mp ((dp.post_iff c).not.mp hc)
  · intro h1
    intro hpost
    have : dp.truncPotential c = 0 := if_pos hpost
    have h0 : dp.truncPotential c = 0 := if_pos hpost
    rw [h0] at h1
    exact absurd h1 (by simp)

/-- Build PhaseConvergence from DriftPhase via truncated potential. -/
noncomputable def DriftPhase.toPhaseConvergence {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} [IsMarkovKernel P.transitionKernel]
    (dp : DriftPhase P)
    (t : ℕ) (ε : ℝ≥0)
    (hbound : dp.r ^ t * dp.M ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence P.transitionKernel where
  Pre := dp.Pre
  Post := dp.Post
  t := t
  ε := ε
  post_absorbing := dp.post_absorbing
  convergence := by
    intro c₀ hPre
    -- Step 1: {¬Post} = {1 ≤ Φ̃}
    have h_eq := dp.not_post_eq_ge_one
    rw [show {y | ¬dp.Post y} = {y | 1 ≤ dp.truncPotential y} from h_eq]
    -- Step 2: Apply measure_potential_ge_one with the truncated potential
    have h_decay := PopProtoCommon.measure_potential_ge_one
      P.transitionKernel dp.truncPotential (truncPotential_measurable dp)
      dp.r (dp.truncPotential_contracts) t c₀
    -- Step 3: Chain the bounds
    calc (P.transitionKernel ^ t) c₀ {y | 1 ≤ dp.truncPotential y}
        ≤ dp.r ^ t * dp.truncPotential c₀ := h_decay
      _ ≤ dp.r ^ t * dp.Φ c₀ := by
          gcongr
          simp only [DriftPhase.truncPotential]
          split_ifs <;> simp
      _ ≤ dp.r ^ t * dp.M := by gcongr; exact dp.hM c₀ hPre
      _ ≤ (ε : ℝ≥0∞) := hbound

end ExactMajority

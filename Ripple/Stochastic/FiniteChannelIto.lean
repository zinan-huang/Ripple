/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry, Raphael Coelho
-/
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-channel Hilbert space assembly

The finite-channel integral is the sum of the scalar integral operators. Its squared norm
is the sum of their squared norms once their ranges are pairwise orthogonal. Orthogonality
on dense simple-integrand ranges extends by continuity in each argument.

This module supplies that functional-analytic assembly, including the expectation formula
for its actual `L²` output representative. It does not establish Brownian orthogonality:
that requires the weighted cross-increment identity for the common filtration.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace Ripple.Stochastic.FiniteChannelIto

section Hilbert

variable {ι : Type*} {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The inner product of a finite orthogonal sum with itself has only diagonal terms. -/
theorem inner_finsetSum_self (s : Finset ι) (v : ι → V)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    inner ℝ (∑ i ∈ s, v i) (∑ i ∈ s, v i) = ∑ i ∈ s, inner ℝ (v i) (v i) := by
  classical
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  exact Finset.sum_eq_single i
    (fun j hj hji => horth i hi j hj hji.symm)
    (fun hni => False.elim (hni hi))

/-- Pythagoras for a finite orthogonal family, without a cardinality loss. -/
theorem norm_sq_finsetSum (s : Finset ι) (v : ι → V)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, v i‖ ^ 2 = inner ℝ (∑ i ∈ s, v i) (∑ i ∈ s, v i) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ i ∈ s, inner ℝ (v i) (v i) := inner_finsetSum_self s v horth
    _ = ∑ i ∈ s, ‖v i‖ ^ 2 := by simp only [real_inner_self_eq_norm_sq]

variable {E D : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Cross orthogonality on two dense sets extends to their continuous scalar integral maps.
The simple-integrand cross identity is an explicit hypothesis, rather than a field containing
the full completed isometry. -/
theorem inner_eq_zero_of_denseRange {α β : Type*} {a : α → E} {b : β → D}
    (ha : DenseRange a) (hb : DenseRange b) (I : E →L[ℝ] V) (J : D →L[ℝ] V)
    (hcross : ∀ u w, inner ℝ (I (a u)) (J (b w)) = 0) (x : E) (y : D) :
    inner ℝ (I x) (J y) = 0 := by
  apply ha.induction_on (p := fun z => inner ℝ (I z) (J y) = 0) x
    (isClosed_eq (continuous_inner.comp (I.continuous.prodMk continuous_const))
      continuous_const)
  intro u
  exact hb.induction_on (p := fun z => inner ℝ (I (a u)) (J z) = 0) y
    (isClosed_eq (continuous_inner.comp (continuous_const.prodMk J.continuous))
      continuous_const)
    (hcross u)

end Hilbert

section Assembly

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Sum the channelwise integral maps, allowing different scalar integrand spaces. -/
noncomputable def finiteChannelIntegral (I : ∀ i, E i →L[ℝ] V) (H : ∀ i, E i) : V :=
  ∑ i, I i (H i)

/-- Exact finite-channel isometry, conditional on scalar isometries and cross orthogonality. -/
theorem finiteChannelIntegral_norm_sq (I : ∀ i, E i →L[ℝ] V)
    (hisometry : ∀ i x, ‖I i x‖ = ‖x‖)
    (hcross : ∀ i j, i ≠ j → ∀ x y, inner ℝ (I i x) (I j y) = 0)
    (H : ∀ i, E i) :
    ‖finiteChannelIntegral I H‖ ^ 2 = ∑ i, ‖H i‖ ^ 2 := by
  unfold finiteChannelIntegral
  rw [norm_sq_finsetSum Finset.univ (fun i => I i (H i))
    (fun i _ j _ hij => hcross i j hij (H i) (H j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hisometry]

/-- Dense simple-integrand cross orthogonality is enough for the completed finite-channel
isometry. The stochastic input is confined to `hsimple`; its construction remains separate. -/
theorem finiteChannelIntegral_norm_sq_of_denseRange
    {S : ι → Type*} (simple : ∀ i, S i → E i)
    (hdense : ∀ i, DenseRange (simple i)) (I : ∀ i, E i →L[ℝ] V)
    (hisometry : ∀ i x, ‖I i x‖ = ‖x‖)
    (hsimple : ∀ i j, i ≠ j → ∀ u v,
      inner ℝ (I i (simple i u)) (I j (simple j v)) = 0)
    (H : ∀ i, E i) :
    ‖finiteChannelIntegral I H‖ ^ 2 = ∑ i, ‖H i‖ ^ 2 := by
  apply finiteChannelIntegral_norm_sq I hisometry
    (fun i j hij x y => inner_eq_zero_of_denseRange (hdense i) (hdense j)
      (I i) (I j) (hsimple i j hij) x y)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Expectation form for the actual representative of the assembled `L²` element.
Identifying each domain norm with the predictable time-space energy is a separate bridge. -/
theorem finiteChannelIntegral_secondMoment
    (I : ∀ i, E i →L[ℝ] Lp ℝ 2 μ)
    (hisometry : ∀ i x, ‖I i x‖ = ‖x‖)
    (hcross : ∀ i j, i ≠ j → ∀ x y, inner ℝ (I i x) (I j y) = 0)
    (H : ∀ i, E i) :
    ∫ ω, ((finiteChannelIntegral I H : Lp ℝ 2 μ) : Ω → ℝ) ω ^ 2 ∂μ = ∑ i, ‖H i‖ ^ 2 := by
  have h := real_inner_self_eq_norm_sq (finiteChannelIntegral I H)
  rw [L2.inner_def] at h
  have hs : (∫ ω, ((finiteChannelIntegral I H : Lp ℝ 2 μ) : Ω → ℝ) ω ^ 2 ∂μ) =
      ‖finiteChannelIntegral I H‖ ^ 2 := by
    simpa only [RCLike.inner_apply, conj_trivial, pow_two] using h
  exact hs.trans (finiteChannelIntegral_norm_sq I hisometry hcross H)

end Assembly

end Ripple.Stochastic.FiniteChannelIto

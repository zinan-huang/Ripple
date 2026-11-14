-- Ripple/LPP/NAPLayerCopyDynamics.lean
import Ripple.LPP.NAPLayerCopy
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Exact dynamics of disjoint protocol layers

The generic weighted-protocol field is polynomial, hence Lipschitz on compact balls.
This supplies uniqueness on every interval [0,T], with no a-priori bound on either
solution. Equal initialization of q layers then gives the exact trajectory v/q.

Uniqueness below is equality on nonnegative times. Values at negative times are
not constrained by a derivative assumption on [0,infinity).
-/

namespace Ripple
namespace NAPTransport
namespace LayerCopy

open Set Filter Topology Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The balance field of every finite weighted protocol is continuously differentiable. -/
theorem field_contDiff (w : WProtocol S) : ContDiff ℝ 1 (field w) := by
  apply contDiff_pi.mpr
  intro s
  unfold field
  fun_prop

/-- A finite weighted protocol has a Lipschitz balance field on every closed ball.
No nonnegativity or NAP premise is required for this polynomial fact. -/
theorem field_lipschitzOnWith (w : WProtocol S) (R : ℝ) :
    ∃ K, LipschitzOnWith K (field w) (Metric.closedBall 0 R) :=
  (field_contDiff w).contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall 0 R) (isCompact_closedBall 0 R)

/-- Two solutions of the same weighted-protocol ODE with the same initial point
agree on [0,T]. Compactness supplies the bounds required by ODE uniqueness. -/
theorem field_solution_unique_Icc (w : WProtocol S) {T : ℝ}
    {u v : ℝ → S → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt u (field w (u t)) (Icc 0 T) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt v (field w (v t)) (Icc 0 T) t)
    (hzero : u 0 = v 0) :
    EqOn u v (Icc 0 T) := by
  classical
  rcases lt_or_ge 0 T with hT | hT
  · have huc : ContinuousOn u (Icc 0 T) :=
      fun t ht => (hu t ht).continuousWithinAt
    have hvc : ContinuousOn v (Icc 0 T) :=
      fun t ht => (hv t ht).continuousWithinAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
    obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hvc
    obtain ⟨K, hK⟩ := field_lipschitzOnWith w (max M N)
    let vf : ℝ → (S → ℝ) → S → ℝ := fun _ => field w
    let region : ℝ → Set (S → ℝ) :=
      fun _ => Metric.closedBall 0 (max M N)
    have hL : ∀ t ∈ Ico (0 : ℝ) T,
        LipschitzOnWith K (vf t) (region t) := fun _ _ => hK
    have huRight : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt u (vf t (u t)) (Ici t) t :=
      fun t ht => hasDerivWithinAt_Icc_to_Ici' ht (hu t ⟨ht.1, ht.2.le⟩)
    have hvRight : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt v (vf t (v t)) (Ici t) t :=
      fun t ht => hasDerivWithinAt_Icc_to_Ici' ht (hv t ⟨ht.1, ht.2.le⟩)
    have huRegion : ∀ t ∈ Ico (0 : ℝ) T, u t ∈ region t := by
      intro t ht
      simp only [region, Metric.mem_closedBall, dist_zero_right]
      exact (hM t ⟨ht.1, ht.2.le⟩).trans (le_max_left _ _)
    have hvRegion : ∀ t ∈ Ico (0 : ℝ) T, v t ∈ region t := by
      intro t ht
      simp only [region, Metric.mem_closedBall, dist_zero_right]
      exact (hN t ⟨ht.1, ht.2.le⟩).trans (le_max_right _ _)
    exact ODE_solution_unique_of_mem_Icc_right
      hL huc huRight huRegion hvc hvRight hvRegion hzero
  · intro t ht
    have htzero : t = 0 := le_antisymm (le_trans ht.2 hT) ht.1
    rw [htzero]
    exact hzero

/-- Global uniqueness on nonnegative times for the generic weighted-protocol field. -/
theorem field_solution_unique (w : WProtocol S) {u v : ℝ → S → ℝ}
    (hu : ∀ t, 0 ≤ t → HasDerivWithinAt u (field w (u t)) (Ici 0) t)
    (hv : ∀ t, 0 ≤ t → HasDerivWithinAt v (field w (v t)) (Ici 0) t)
    (hzero : u 0 = v 0) :
    ∀ t, 0 ≤ t → u t = v t := by
  intro t ht
  have heq : EqOn u v (Icc (0 : ℝ) t) :=
    field_solution_unique_Icc w
      (fun s hs => (hu s hs.1).mono (fun a ha => ha.1))
      (fun s hs => (hv s hs.1).mono (fun a ha => ha.1)) hzero
  exact heq ⟨ht, le_rfl⟩

/-- Dividing every coordinate by q transports a solution to the q-layer copy field.
The statement holds within an arbitrary time set. -/
theorem diagonal_hasDerivWithinAt (w : WProtocol S) (q : ℕ) (hq : 0 < q)
    {v : ℝ → S → ℝ} {U : Set ℝ} {t : ℝ}
    (hv : HasDerivWithinAt v (field w (v t)) U t) :
    HasDerivWithinAt (fun u => diagonal q (v u))
      (field (copyProtocol w q) (diagonal q (v t))) U t := by
  rw [hasDerivWithinAt_pi]
  intro p
  change HasDerivWithinAt (fun u => v u p.1 / (q : ℝ))
    (field (copyProtocol w q) (diagonal q (v t)) p) U t
  rw [field_copy_diagonal w q hq (v t) p]
  exact (hasDerivWithinAt_pi.mp hv p.1).div_const (q : ℝ)

/-- The exact equal-layer trajectory solves the copied system for all nonnegative times. -/
theorem diagonal_solution (w : WProtocol S) (q : ℕ) (hq : 0 < q)
    {v : ℝ → S → ℝ}
    (hv : ∀ t, 0 ≤ t → HasDerivWithinAt v (field w (v t)) (Ici 0) t) :
    ∀ t, 0 ≤ t → HasDerivWithinAt (fun u => diagonal q (v u))
      (field (copyProtocol w q) (diagonal q (v t))) (Ici 0) t :=
  fun t ht => diagonal_hasDerivWithinAt w q hq (hv t ht)

/-- Every copied solution from the equal-copy initial point agrees with the exact
equal-copy trajectory on every [0,T]. There is no extra uniqueness or boundedness premise. -/
theorem copy_solution_unique_Icc (w : WProtocol S) (q : ℕ) (hq : 0 < q)
    {v : ℝ → S → ℝ}
    (hv : ∀ t, 0 ≤ t → HasDerivWithinAt v (field w (v t)) (Ici 0) t)
    {T : ℝ} {u : ℝ → S × Fin q → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt u (field (copyProtocol w q) (u t)) (Icc 0 T) t)
    (hzero : u 0 = diagonal q (v 0)) :
    EqOn u (fun t => diagonal q (v t)) (Icc 0 T) := by
  refine field_solution_unique_Icc (copyProtocol w q) hu ?_ hzero
  intro t ht
  exact (diagonal_hasDerivWithinAt w q hq (hv t ht.1)).mono
    (fun a ha => ha.1)

/-- Equality at every nonnegative time, for any solution from the copied initial point. -/
theorem copy_solution_unique (w : WProtocol S) (q : ℕ) (hq : 0 < q)
    {v : ℝ → S → ℝ}
    (hv : ∀ t, 0 ≤ t → HasDerivWithinAt v (field w (v t)) (Ici 0) t)
    {u : ℝ → S × Fin q → ℝ}
    (hu : ∀ t, 0 ≤ t →
      HasDerivWithinAt u (field (copyProtocol w q) (u t)) (Ici 0) t)
    (hzero : u 0 = diagonal q (v 0)) :
    ∀ t, 0 ≤ t → u t = diagonal q (v t) :=
  field_solution_unique (copyProtocol w q) hu (diagonal_solution w q hq hv) hzero

/-- The mass of each layer has derivative zero along every copied solution. -/
theorem layer_mass_hasDerivWithinAt (w : WProtocol S) (q : ℕ)
    {z : ℝ → S × Fin q → ℝ} {U : Set ℝ} {t : ℝ}
    (hz : HasDerivWithinAt z (field (copyProtocol w q) (z t)) U t)
    (i : Fin q) :
    HasDerivWithinAt (fun u => ∑ s, z u (s, i)) 0 U t := by
  have hsum : HasDerivWithinAt (fun u => ∑ s, z u (s, i))
      (∑ s, field (copyProtocol w q) (z t) (s, i)) U t :=
    HasDerivWithinAt.fun_sum
      (fun s _ => hasDerivWithinAt_pi.mp hz (s, i))
  simpa only [sum_field_copyProtocol] using hsum

/-- Actual conservation of each layer's mass on nonnegative times, for arbitrary
initial copy allocations. Equal initialization is unnecessary for conservation. -/
theorem layer_mass_constant (w : WProtocol S) (q : ℕ)
    {z : ℝ → S × Fin q → ℝ}
    (hz : ∀ t, 0 ≤ t →
      HasDerivWithinAt z (field (copyProtocol w q) (z t)) (Ici 0) t)
    (i : Fin q) (t : ℝ) (ht : 0 ≤ t) :
    (∑ s, z t (s, i)) = ∑ s, z 0 (s, i) := by
  let f : ℝ → ℝ := fun u => ∑ s, z u (s, i)
  have hf : ∀ u ∈ Ici (0 : ℝ),
      HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Ici 0) u := by
    intro u hu
    simpa only [f, ContinuousLinearMap.toSpanSingleton_zero] using
      (layer_mass_hasDerivWithinAt w q (hz u hu) i).hasFDerivWithinAt
  have hbound : ‖f t - f 0‖ ≤ 0 := by
    simpa only [zero_mul] using
      (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasFDerivWithin_le (C := (0 : ℝ))
        hf (fun u hu => by simp) (Set.mem_Ici.mpr (le_refl (0 : ℝ))) ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbound)

end LayerCopy
end NAPTransport
end Ripple

-- Ripple/LPP/NAPLayerCopyExample.lean
/-
  A nonzero two-state protocol: 2A -> A+B and 2B -> A+B, both at rate one.
  Its symmetric rational initial point is stationary, and its marked A-mass is 1/2.
  The examples below use both marked slack and unmarked slack in the layer compiler.
-/

import Ripple.LPP.NAPLayerCopyPipeline

namespace Ripple
namespace NAPTransport
namespace LayerCopy
namespace Example

open Set Filter Topology Finset

private theorem pure_indices_ne :
    MI.pow 2 2 (0 : Fin 2) ≠ MI.pow 2 2 (1 : Fin 2) := by
  intro h
  have he := congrArg (fun μ : MI 2 2 => (μ.1 0 : ℕ)) h
  norm_num [MI.pow, MI.ofFun_val] at he

/-- The two symmetric homodimer transfers, as an explicit quadratic coefficient table. -/
noncomputable def symmetricPP : QuadPP 2 where
  coef j μ :=
    (if μ = MI.pow 2 2 (0 : Fin 2) then (if j = 0 then -1 else 1) else 0) +
    (if μ = MI.pow 2 2 (1 : Fin 2) then (if j = 0 then 1 else -1) else 0)
  conservative := by
    intro μ
    by_cases ha : μ = MI.pow 2 2 (0 : Fin 2) <;>
      by_cases hb : μ = MI.pow 2 2 (1 : Fin 2) <;>
        simp [Fin.sum_univ_two, ha, hb, pure_indices_ne, pure_indices_ne.symm]
  sign := by
    intro j μ hneg
    fin_cases j
    · by_cases ha : μ = MI.pow 2 2 (0 : Fin 2)
      · subst μ
        norm_num [MI.pow, MI.ofFun_val]
      · by_cases hb : μ = MI.pow 2 2 (1 : Fin 2) <;>
          norm_num [ha, hb, pure_indices_ne, pure_indices_ne.symm] at hneg
    · by_cases hb : μ = MI.pow 2 2 (1 : Fin 2)
      · subst μ
        norm_num [MI.pow, MI.ofFun_val]
      · by_cases ha : μ = MI.pow 2 2 (0 : Fin 2) <;>
          norm_num [ha, hb, pure_indices_ne, pure_indices_ne.symm] at hneg

/-- The example is a nonzero coefficient table, not an empty protocol. -/
theorem symmetricPP_coefficient :
    symmetricPP.coef (0 : Fin 2) (MI.pow 2 2 (0 : Fin 2)) = -1 := by
  simp [symmetricPP, pure_indices_ne]

/-- The field is (x_B^2-x_A^2, x_A^2-x_B^2). -/
theorem symmetricPP_field (x : Fin 2 → ℝ) (j : Fin 2) :
    quadFun 2 symmetricPP x j =
      (if j = 0 then -1 else 1) * x 0 ^ 2 +
      (if j = 0 then 1 else -1) * x 1 ^ 2 := by
  have hc (μ : MI 2 2) :
      (symmetricPP.coef j μ : ℝ) =
        (if μ = MI.pow 2 2 (0 : Fin 2) then
          (if j = 0 then -1 else 1) else 0) +
        (if μ = MI.pow 2 2 (1 : Fin 2) then
          (if j = 0 then 1 else -1) else 0) := by
    by_cases ha : μ = MI.pow 2 2 (0 : Fin 2) <;>
      by_cases hb : μ = MI.pow 2 2 (1 : Fin 2) <;>
        by_cases hj : j = 0 <;>
          simp [symmetricPP, ha, hb, hj, pure_indices_ne, pure_indices_ne.symm]
  calc
    quadFun 2 symmetricPP x j =
        (∑ μ : MI 2 2, if μ = MI.pow 2 2 (0 : Fin 2) then
          (if j = 0 then -1 else 1) * mono2 2 x μ else 0) +
        (∑ μ : MI 2 2, if μ = MI.pow 2 2 (1 : Fin 2) then
          (if j = 0 then 1 else -1) * mono2 2 x μ else 0) := by
      unfold quadFun
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro μ _
      rw [hc μ]
      by_cases ha : μ = MI.pow 2 2 (0 : Fin 2) <;>
        by_cases hb : μ = MI.pow 2 2 (1 : Fin 2) <;>
          simp [ha, hb, add_mul]
    _ = (if j = 0 then -1 else 1) * mono2 2 x (MI.pow 2 2 (0 : Fin 2)) +
        (if j = 0 then 1 else -1) * mono2 2 x (MI.pow 2 2 (1 : Fin 2)) := by simp
    _ = _ := by
      simp [mono2, MI.pow, MI.ofFun_val, Fin.prod_univ_two]

/-- Equal rational proportions of the two species. -/
noncomputable def halfState : Fin 2 → ℝ := fun _ => 1 / 2

theorem halfState_simplex :
    (∀ j, 0 ≤ halfState j) ∧ ∑ j, halfState j = 1 := by
  constructor
  · intro j
    norm_num [halfState]
  · norm_num [halfState, Fin.sum_univ_two]

theorem halfState_stationary : quadFun 2 symmetricPP halfState = 0 := by
  funext j
  rw [symmetricPP_field]
  by_cases hj : j = 0 <;> norm_num [halfState, hj]

theorem halfState_ode (t : ℝ) :
    HasDerivAt (fun _ : ℝ => halfState) (quadFun 2 symmetricPP halfState) t := by
  rw [halfState_stationary]
  exact hasDerivAt_const t halfState

theorem halfState_markedMass :
    ∑ j ∈ ({0} : Finset (Fin 2)), halfState j = (1 : ℝ) / 2 := by
  simp [halfState]

theorem halfState_rightMass :
    ∑ j ∈ ({1} : Finset (Fin 2)), halfState j = (1 : ℝ) / 2 := by
  simp [halfState]

theorem singleton_right_unmarked :
    ({1} : Finset (Fin 2)) ⊆ ({0} : Finset (Fin 2))ᶜ := by
  intro j hj
  have heq : j = 1 := Finset.mem_singleton.mp hj
  subst j
  simp


/-- A rational scaling factor strictly between zero and one. -/
theorem half_scaling_pos : (0 : ℚ) < 1 / 2 := by norm_num

theorem half_scaling_lt_one : (1 / 2 : ℚ) < 1 := by norm_num

/-- The marked species can be shrunk: the new slack coordinate is then marked. -/
theorem marked_slack_compilation :
    Nonempty (MarkedCompilation 2 symmetricPP {0} {0} true
      (1 / 2) half_scaling_pos halfState) := by
  exact pp_to_nap_layer_copy_of_common_mark 2 symmetricPP {0} {0} true
    (common_mark_of_marked_subset 2 {0} {0} (by intro j hj; exact hj))
    (1 / 2) half_scaling_pos half_scaling_lt_one
    halfState halfState_simplex.1 halfState_simplex.2
    (by rw [halfState_markedMass]; norm_num)

/-- The unmarked species can instead be shrunk: the new slack coordinate is unmarked. -/
theorem unmarked_slack_compilation :
    Nonempty (MarkedCompilation 2 symmetricPP {0} {1} false
      (1 / 2) half_scaling_pos halfState) := by
  exact pp_to_nap_layer_copy_of_common_mark 2 symmetricPP {0} {1} false
    (common_mark_of_unmarked_subset 2 {0} {1} singleton_right_unmarked)
    (1 / 2) half_scaling_pos half_scaling_lt_one
    halfState halfState_simplex.1 halfState_simplex.2
    (by rw [halfState_rightMass]; norm_num)

/-- The source selected by the actual producer is the explicit stationary solution. -/
theorem compiled_half_source {J : Finset (Fin 2)} {b : Bool}
    (C : MarkedCompilation 2 symmetricPP {0} J b
      (1 / 2) half_scaling_pos halfState)
    (t : ℝ) (ht : 0 ≤ t) : C.source t = halfState := by
  have heq := C.source_unique (fun _ : ℝ => halfState) rfl
    (fun s _ => halfState_ode s) t ht
  exact heq.symm

/-- The copied protocol's genuine marked subset has mass one half at every
nonnegative time, for either permitted slack marking. -/
theorem compiled_half_readout {J : Finset (Fin 2)} {b : Bool}
    (C : MarkedCompilation 2 symmetricPP {0} J b
      (1 / 2) half_scaling_pos halfState)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ p ∈ copyMarkedSet 2 {0} b,
      copiedTrajectory 2 J (1 / 2) C.source C.clock t p) = (1 : ℝ) / 2 := by
  calc
    (∑ p ∈ copyMarkedSet 2 {0} b,
        copiedTrajectory 2 J (1 / 2) C.source C.clock t p)
        = ∑ j ∈ ({0} : Finset (Fin 2)), C.source (C.clock t) j := C.readout t ht
    _ = ∑ j ∈ ({0} : Finset (Fin 2)), halfState j := by
      rw [compiled_half_source C (C.clock t) (C.clock_nonneg_deriv t ht).1]
    _ = (1 : ℝ) / 2 := halfState_markedMass

/-- The instantiated copied marked readout computes one half. -/
theorem compiled_half_limit {J : Finset (Fin 2)} {b : Bool}
    (C : MarkedCompilation 2 symmetricPP {0} J b
      (1 / 2) half_scaling_pos halfState) :
    Tendsto (fun t => ∑ p ∈ copyMarkedSet 2 {0} b,
      copiedTrajectory 2 J (1 / 2) C.source C.clock t p)
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  have h : Tendsto (fun _ : ℝ => (1 : ℝ) / 2) atTop (𝓝 ((1 : ℝ) / 2)) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (compiled_half_readout C t ht).symm

/-- The same marked value holds for every solution from the constructed copied
initial point, by the compiled ODE uniqueness theorem. -/
theorem compiled_half_any_solution {J : Finset (Fin 2)} {b : Bool}
    (C : MarkedCompilation 2 symmetricPP {0} J b
      (1 / 2) half_scaling_pos halfState)
    (u : ℝ → MI (2 + 1) 3 × Fin 3 → ℝ)
    (hu : ∀ t, 0 ≤ t →
      HasDerivWithinAt u (field (copyProtocol C.baseProtocol 3) (u t)) (Ici 0) t)
    (hu0 : u 0 = copiedInitial 2 J (1 / 2) halfState) :
    ∀ t, 0 ≤ t → (∑ p ∈ copyMarkedSet 2 {0} b, u t p) = (1 : ℝ) / 2 := by
  intro t ht
  rw [C.copy_unique u hu hu0 t ht]
  exact compiled_half_readout C t ht

/-- Non-vacuity with marked slack: the producer constructs a nonnegative NAP,
its unique copied solution, and a genuine marked subset computing one half. -/
theorem marked_slack_example :
    ∃ C : MarkedCompilation 2 symmetricPP {0} {0} true
        (1 / 2) half_scaling_pos halfState,
      (∀ t, 0 ≤ t →
        (∑ p ∈ copyMarkedSet 2 {0} true,
          copiedTrajectory 2 {0} (1 / 2) C.source C.clock t p) = (1 : ℝ) / 2) ∧
      Tendsto (fun t => ∑ p ∈ copyMarkedSet 2 {0} true,
        copiedTrajectory 2 {0} (1 / 2) C.source C.clock t p)
        atTop (𝓝 ((1 : ℝ) / 2)) := by
  obtain ⟨C⟩ := marked_slack_compilation
  exact ⟨C, compiled_half_readout C, compiled_half_limit C⟩

/-- Non-vacuity with unmarked slack, for the same explicit nonzero source PP. -/
theorem unmarked_slack_example :
    ∃ C : MarkedCompilation 2 symmetricPP {0} {1} false
        (1 / 2) half_scaling_pos halfState,
      (∀ t, 0 ≤ t →
        (∑ p ∈ copyMarkedSet 2 {0} false,
          copiedTrajectory 2 {1} (1 / 2) C.source C.clock t p) = (1 : ℝ) / 2) ∧
      Tendsto (fun t => ∑ p ∈ copyMarkedSet 2 {0} false,
        copiedTrajectory 2 {1} (1 / 2) C.source C.clock t p)
        atTop (𝓝 ((1 : ℝ) / 2)) := by
  obtain ⟨C⟩ := unmarked_slack_compilation
  exact ⟨C, compiled_half_readout C, compiled_half_limit C⟩

end Example
end LayerCopy
end NAPTransport
end Ripple

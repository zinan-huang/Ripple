/-
  Ripple.Kurtz.JumpModel — Density-Dependent Jump Model for CTMCs

  Abstracts the transition structure of a density-dependent CTMC as a
  typed jump model with:
  - `gamma a i`: coordinate change in species i when reaction a fires
  - `lambda a z`: rate of reaction a at density state z

  This decouples the algebraic bracket computation (JumpBracket.lean)
  from the stochastic process construction (existing Kurtz.Defs).
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace Ripple.Kurtz

open Finset

/-- The standard simplex in ℝ^ι (nonneg + sum = 1). -/
def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1}

/-- A density-dependent jump model specifying how each reaction type
    changes species densities and at what rate.

    Parameters:
    - ι: species index type
    - α: reaction index type
    - gamma a i: change in density of species i when reaction a fires (scaled by 1/N)
    - lambda a z: rate of reaction a at density z (already density-dependent)
    - J: ℓ² bound on jump vectors
    - LambdaMax: uniform bound on rates over the simplex -/
structure DensityJumpModel (ι α : Type*) [Fintype ι] [Fintype α] where
  gamma : α → ι → ℝ
  lambda : α → (ι → ℝ) → ℝ
  J : ℝ
  LambdaMax : ℝ
  lambda_nonneg : ∀ a z, 0 ≤ lambda a z
  lambda_bound : ∀ a z, z ∈ simplexSet ι → lambda a z ≤ LambdaMax
  jump_bound_l2 : ∀ a,
    ∑ i : ι, (gamma a i) ^ 2 ≤ J ^ 2
  J_nonneg : 0 ≤ J
  LambdaMax_nonneg : 0 ≤ LambdaMax

/-- The ℓ∞ jump bound, derived from ℓ² bound. For a single coordinate,
    |gamma a i| ≤ J. -/
theorem DensityJumpModel.gamma_linf_le
    {ι α : Type*} [Fintype ι] [Fintype α]
    (m : DensityJumpModel ι α) (a : α) (i : ι) :
    |m.gamma a i| ≤ m.J := by
  have hsingle : (m.gamma a i) ^ 2 ≤ ∑ j : ι, (m.gamma a j) ^ 2 := by
    simpa using (Finset.single_le_sum (s := Finset.univ)
      (f := fun j : ι => (m.gamma a j) ^ 2)
      (by intro j hj; exact sq_nonneg (m.gamma a j))
      (Finset.mem_univ i))
  exact abs_le_of_sq_le_sq (hsingle.trans (m.jump_bound_l2 a)) m.J_nonneg

end Ripple.Kurtz

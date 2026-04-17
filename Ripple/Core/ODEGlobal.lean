/-
  Ripple.Core.ODEGlobal — Global ODE existence from local Picard-Lindelöf.

  Mathlib provides local Picard-Lindelöf (`IsPicardLindelof.exists_eq_…`) and
  global *uniqueness* (`ODE_solution_unique…`), but not the classical
  "bounded + locally Lipschitz ⇒ global solution" extension theorem.

  This file isolates that Mathlib gap in one narrow axiom
  (`locally_lipschitz_bounded_global_ode`). The CRN-specific corollary
  `crn_simplex_global_ode_solution'` will be derived from it plus the
  forward-invariance of the simplex (pending: needs a local version of
  `crn_nonneg_invariance` + conservation).
-/

import Ripple.Core.PIVP
import Ripple.LPP.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add

open Set Filter Topology

namespace Ripple

/-!
## Narrow Mathlib-gap axiom: global existence from local Lipschitz + a priori bound.

The hypothesis `h_invariant` says: every putative local solution starting at
`y₀` on any half-open interval `[0, T)` is uniformly bounded by `M`.
Combined with local Picard-Lindelöf on closed balls this lets one iterate
local solutions into a global one by compactness (standard ODE textbook
argument; see e.g. Hirsch–Smale–Devaney §17).

Mathlib has local Picard (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`)
and global uniqueness via Grönwall but NOT this extension step.
-/
axiom locally_lipschitz_bounded_global_ode
    {d : ℕ} (f : (Fin d → ℝ) → Fin d → ℝ) (y₀ : Fin d → ℝ)
    (_h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (_hM : 0 < M)
    (_h_invariant : ∀ (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin d → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ M) :
    ∃ y : ℝ → Fin d → ℝ, y 0 = y₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt y (f (y t)) t

/-!
## Simplex sup-norm bound.

On `Fin d → ℝ` with the sup norm, the simplex
`{x | x ≥ 0 ∧ ∑ xᵢ = 1}` lies in the closed unit ball.
-/
lemma simplex_norm_le_one {d : ℕ} (x : Fin d → ℝ)
    (h_nn : ∀ i, 0 ≤ x i) (h_sum : ∑ i, x i = 1) :
    ‖x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_of_nonneg (h_nn i)]
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (f := x)
            (fun j _ => h_nn j) (Finset.mem_univ i)
    _ = 1 := h_sum

/-!
## Conservation gives constant total for local solutions.
-/
lemma conservative_local_sum_const {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (h_cons : IsConservative field) (T : ℝ) (_hT : 0 < T)
    (y : ℝ → Fin d → ℝ)
    (h_ode : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (field (y t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, ∑ i, y t i = ∑ i, y 0 i := by
  -- Let g(s) = ∑ i, y s i. On Ico 0 T we have g'(s) = ∑ i, (y · i)'(s)
  --   = ∑ i, field(y s) i = 0 by conservation.
  -- Apply `constant_of_has_deriv_right_zero` on Icc 0 t for each t ∈ Ico 0 T.
  intro t ht
  set g : ℝ → ℝ := fun s => ∑ i, y s i with hg
  -- Pointwise derivative of each component of y.
  have hyi : ∀ s ∈ Ico (0 : ℝ) T, ∀ i, HasDerivAt (fun s => y s i) (field (y s) i) s := by
    intro s hs i
    exact hasDerivAt_pi.mp (h_ode s hs) i
  -- Sum derivative at a single s ∈ Ico 0 T.
  have hg_sum : ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivAt g (∑ i, field (y s) i) s := by
    intro s hs
    have := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d)))
      (A := fun i s => y s i) (A' := fun i => field (y s) i)
      (fun i _ => hyi s hs i)
    simpa [g] using this
  -- g has derivative 0 at every point of Ico 0 t.
  have hg_deriv : ∀ s ∈ Ico (0 : ℝ) t, HasDerivAt g 0 s := by
    intro s hs
    have hs' : s ∈ Ico (0 : ℝ) T :=
      ⟨hs.1, lt_of_lt_of_le hs.2 ht.2.le⟩
    have h_sum := hg_sum s hs'
    rw [h_cons (y s)] at h_sum
    exact h_sum
  -- g is continuous on Icc 0 t (HasDerivAt at every point of Icc 0 t).
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) t) := by
    intro s hs
    have hs_lt_T : s < T := lt_of_le_of_lt hs.2 ht.2
    have hs' : s ∈ Ico (0 : ℝ) T := ⟨hs.1, hs_lt_T⟩
    exact (hg_sum s hs').continuousAt.continuousWithinAt
  -- Apply constant_of_has_deriv_right_zero.
  have h_const : ∀ x ∈ Icc (0 : ℝ) t, g x = g 0 := by
    apply constant_of_has_deriv_right_zero hg_cont
    intro s hs
    exact (hg_deriv s hs).hasDerivWithinAt
  exact h_const t ⟨ht.1, le_refl t⟩

/-!
## CRN forward-invariance of non-negativity for local solutions.

Pending: local-solution version of `crn_nonneg_invariance` (the squared-negative-mass
+ Grönwall argument carries over; needs the interval restricted to [0, T) rather
than [0, ∞)).
-/
lemma crn_local_nonneg {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (_crn : IsCRNImplementable d field)
    (_h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖field x - field y‖ ≤ L * ‖x - y‖)
    (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin d → ℝ)
    (_h_init_nn : ∀ i, 0 ≤ y 0 i)
    (_h_ode : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (field (y t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, 0 ≤ y t i := by
  -- Mirror of `crn_nonneg_invariance` but for the local half-open interval.
  -- Squared-negative-mass functional F(t) = ∑_i min(y t i, 0)^2 satisfies
  -- F(0) = 0 and F'(t) ≤ K·F(t) via the CRN structure; Grönwall ⇒ F ≡ 0.
  sorry

/-!
## Main theorem: CRN systems on the simplex have global ODE solutions.

Proof: local-simplex invariance (non-negativity + conservation ⇒ sup-norm ≤ 1)
feeds the narrow `locally_lipschitz_bounded_global_ode` axiom.
-/
noncomputable def crn_simplex_global_ode_solution' {d : ℕ} (P : PIVP d)
    (h_crn : IsCRNImplementable d P.field)
    (h_cons : IsConservative P.field)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖)
    (h_init_nn : ∀ i, 0 ≤ P.init i)
    (h_init_simplex : ∑ i, P.init i = 1) :
    PIVP.Solution P := by
  have h_inv : ∀ (T : ℝ) (_hT : 0 < T) (y : ℝ → Fin d → ℝ),
      y 0 = P.init →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (P.field (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ 1 := by
    intro T hT y hy0 hode t ht
    have hinit_y : ∀ i, 0 ≤ y 0 i := fun i => by rw [hy0]; exact h_init_nn i
    have h_nn : ∀ i, 0 ≤ y t i :=
      fun i => crn_local_nonneg h_crn h_lip T hT y hinit_y hode t ht i
    have h_sum : ∑ i, y t i = 1 := by
      have h_const := conservative_local_sum_const h_cons T hT y hode t ht
      rw [h_const, hy0]; exact h_init_simplex
    exact simplex_norm_le_one (y t) h_nn h_sum
  have h :=
    locally_lipschitz_bounded_global_ode P.field P.init h_lip 1 one_pos h_inv
  exact {
    trajectory := Classical.choose h
    init_cond := (Classical.choose_spec h).1
    is_solution := (Classical.choose_spec h).2
  }

end Ripple


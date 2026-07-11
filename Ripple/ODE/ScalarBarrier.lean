/-
  Ripple.ODE.ScalarBarrier — generic Picard-uniqueness barriers for
  autonomous scalar ODEs.

  ## Motivation

  Many CRN-computable-number proofs pin a scalar coordinate `z : ℝ → ℝ`
  inside an invariant interval by comparing it, via Picard uniqueness,
  against a constant solution at a zero of the field.  The argument is
  always the same:

    * If `f(c) = 0` then `ẑ(t) ≡ c` solves `z' = f(z)`.
    * If a real solution `z` ever crossed `c`, the intermediate value
      theorem would give a crossing time `t*`, and Picard uniqueness on
      `[0, t*]` would force `z ≡ c`, contradicting the initial datum.
    * Locally Lipschitz `f` on every bounded box is enough to apply
      Mathlib's `ODE_solution_unique_of_mem_Icc_left`.

  This file captures the pattern once as
  `scalar_ode_barrier_above` / `scalar_ode_barrier_below`, so any future
  conifold/attractor/Frobenius argument (the Apéry conifold `z₁`, Dottie,
  the ζ(3) Frobenius program) can reuse it without re-threading thirty
  lines of compact-box bookkeeping.

  The existing ζ(3) scalar proof in `Ripple.Number.ApreyScalarZ` was the
  first concrete consumer; it used this pattern twice — once against the
  upper barrier `z ≡ z₁`, once against `z ≡ 0`.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace Ripple
namespace ODE

open Real Set

/-! ## Shared compact-box bookkeeping

    The key technical step for applying `ODE_solution_unique_of_mem_Icc_left`
    on a bounded interval `[0, T]` is producing a *closed box*
    `Icc (-M) M` that contains both the solution's range and the
    reference constant `c`, together with a Lipschitz constant for `f`
    on that box.  Both barrier directions go through the same box. -/

section Box

variable {z : ℝ → ℝ} {T : ℝ}

/-- Choose a box `Icc (-M) M` that contains `z([0, T])` and the point `c`.
Returns `M` and the three key facts: `0 ≤ M`, `c ∈ Icc (-M) M`, and the
pointwise membership `∀ t ∈ [0, T], z t ∈ Icc (-M) M`. -/
private lemma exists_compact_box
    (hT_nn : 0 ≤ T)
    (hz_cont : ContinuousOn z (Icc (0 : ℝ) T))
    (c : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ c ∈ Icc (-M) M ∧
      ∀ t ∈ Icc (0 : ℝ) T, z t ∈ Icc (-M) M := by
  have h_compact : IsCompact (Icc (0 : ℝ) T) := isCompact_Icc
  have h_nonempty : (Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_refl _, hT_nn⟩⟩
  obtain ⟨a_max, _, h_max⟩ := h_compact.exists_isMaxOn h_nonempty hz_cont
  obtain ⟨a_min, _, h_min⟩ := h_compact.exists_isMinOn h_nonempty hz_cont
  refine ⟨max (max |z a_max| |z a_min|) |c| + 1, ?_, ?_, ?_⟩
  · have : 0 ≤ max (max |z a_max| |z a_min|) |c| := by positivity
    linarith
  · refine ⟨?_, ?_⟩
    · have h1 : -|c| ≤ c := neg_abs_le _
      have h2 : |c| ≤ max (max |z a_max| |z a_min|) |c| := le_max_right _ _
      linarith
    · have h1 : c ≤ |c| := le_abs_self _
      have h2 : |c| ≤ max (max |z a_max| |z a_min|) |c| := le_max_right _ _
      linarith
  · intro t ht
    have hmax_bd : z t ≤ z a_max := h_max ht
    have hmin_bd : z a_min ≤ z t := h_min ht
    refine ⟨?_, ?_⟩
    · have h1 : -|z a_min| ≤ z a_min := neg_abs_le _
      have h2 : |z a_min| ≤ max |z a_max| |z a_min| := le_max_right _ _
      have h3 : |z a_min| ≤ max (max |z a_max| |z a_min|) |c| :=
        le_trans h2 (le_max_left _ _)
      linarith
    · have h1 : z a_max ≤ |z a_max| := le_abs_self _
      have h2 : |z a_max| ≤ max |z a_max| |z a_min| := le_max_left _ _
      have h3 : |z a_max| ≤ max (max |z a_max| |z a_min|) |c| :=
        le_trans h2 (le_max_left _ _)
      linarith

end Box

/-! ## Shared Picard-uniqueness core

    Given a crossing time `t_star ∈ [0, T]` with `z t_star = c`, the
    constant solution `ẑ ≡ c` (which solves `z' = f(z)` because `f c = 0`)
    and the solution `z` agree at `t_star`.  Picard backward uniqueness on
    `[0, t_star]` then forces them to agree on the whole interval, in
    particular at `t = 0`. -/

/-- Core Picard-uniqueness step: crossing at `t_star` forces `z 0 = c`. -/
private lemma crossing_forces_initial_eq
    (f : ℝ → ℝ) (z : ℝ → ℝ) (c : ℝ) (t_star : ℝ)
    (hfc : f c = 0)
    (hf_lip : ∀ M : ℝ, 0 ≤ M → ∃ L : NNReal, LipschitzOnWith L f (Icc (-M) M))
    (ht_star_nn : 0 ≤ t_star)
    (hz_cont : ContinuousOn z (Icc (0 : ℝ) t_star))
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (f (z t)) t)
    (hz_star : z t_star = c) :
    z 0 = c := by
  obtain ⟨M, hM_nn, hM_c, hz_in_box⟩ :=
    exists_compact_box ht_star_nn hz_cont c
  obtain ⟨L, hL⟩ := hf_lip M hM_nn
  have h_eq : EqOn z (fun _ : ℝ => c) (Icc (0 : ℝ) t_star) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ x => f x) (s := fun _ => Icc (-M) M)
      (K := L) (a := 0) (b := t_star)
    · intro t _; exact hL
    · exact hz_cont
    · intro t ht
      exact (hz_ode t (le_of_lt ht.1)).hasDerivWithinAt
    · intro t ht
      exact hz_in_box t ⟨le_of_lt ht.1, ht.2⟩
    · exact continuousOn_const
    · intro t _
      exact (hasDerivAt_const t c).hasDerivWithinAt.congr_deriv hfc.symm
    · intro _ _; exact hM_c
    · exact hz_star
  exact h_eq ⟨le_refl _, ht_star_nn⟩

/-! ## Upper / lower barriers -/

/-- **Scalar ODE upper barrier.**  If `f(c) = 0`, `f` is locally Lipschitz
on every closed box `Icc (-M) M`, and a solution `z` of `z' = f(z)` on
`[0, ∞)` starts strictly below `c`, then `z(t) ≤ c` for all `t ≥ 0`.

The barrier is established by Picard backward uniqueness: if `z` ever
crossed `c`, IVT would give a crossing time `t*`, and Picard uniqueness
would force `z ≡ c` on `[0, t*]`, contradicting the strict initial
inequality. -/
theorem scalar_ode_barrier_above
    (f : ℝ → ℝ) (c : ℝ)
    (hfc : f c = 0)
    (hf_lip : ∀ M : ℝ, 0 ≤ M → ∃ L : NNReal, LipschitzOnWith L f (Icc (-M) M))
    (z : ℝ → ℝ)
    (hz_init : z 0 < c)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (f (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → z t ≤ c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT_nn, hzT⟩ := hcon
  have hz_cont_T : ContinuousOn z (Icc (0 : ℝ) T) := fun t ht =>
    ((hz_ode t ht.1).continuousAt).continuousWithinAt
  -- IVT: a crossing `t_star ∈ [0, T]` with `z t_star = c`.
  have h_lo : z 0 ≤ c := le_of_lt hz_init
  have h_hi : c ≤ z T := le_of_lt hzT
  obtain ⟨t_star, ht_star_mem, hz_star⟩ :=
    intermediate_value_Icc hT_nn hz_cont_T ⟨h_lo, h_hi⟩
  obtain ⟨ht_star_nn, ht_star_le_T⟩ := ht_star_mem
  have hz_cont : ContinuousOn z (Icc (0 : ℝ) t_star) :=
    hz_cont_T.mono (Icc_subset_Icc_right ht_star_le_T)
  -- Picard core: `z 0 = c`, contradicting the strict initial inequality.
  have h_at_zero : z 0 = c :=
    crossing_forces_initial_eq f z c t_star hfc hf_lip ht_star_nn
      hz_cont hz_ode hz_star
  linarith

/-- **Scalar ODE lower barrier.**  Symmetric version of
`scalar_ode_barrier_above`: if `f(c) = 0`, `f` is locally Lipschitz on
every box, and `z(0) > c`, then `z(t) ≥ c` for all `t ≥ 0`.

Proof is identical mutatis mutandis; only the direction of the
intermediate value theorem flips (`intermediate_value_Icc'`). -/
theorem scalar_ode_barrier_below
    (f : ℝ → ℝ) (c : ℝ)
    (hfc : f c = 0)
    (hf_lip : ∀ M : ℝ, 0 ≤ M → ∃ L : NNReal, LipschitzOnWith L f (Icc (-M) M))
    (z : ℝ → ℝ)
    (hz_init : c < z 0)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (f (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → c ≤ z t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT_nn, hzT⟩ := hcon
  have hz_cont_T : ContinuousOn z (Icc (0 : ℝ) T) := fun t ht =>
    ((hz_ode t ht.1).continuousAt).continuousWithinAt
  -- IVT (reversed order): a crossing `t_star ∈ [0, T]` with `z t_star = c`.
  have h_lo : z T ≤ c := le_of_lt hzT
  have h_hi : c ≤ z 0 := le_of_lt hz_init
  obtain ⟨t_star, ht_star_mem, hz_star⟩ :=
    intermediate_value_Icc' hT_nn hz_cont_T ⟨h_lo, h_hi⟩
  obtain ⟨ht_star_nn, ht_star_le_T⟩ := ht_star_mem
  have hz_cont : ContinuousOn z (Icc (0 : ℝ) t_star) :=
    hz_cont_T.mono (Icc_subset_Icc_right ht_star_le_T)
  have h_at_zero : z 0 = c :=
    crossing_forces_initial_eq f z c t_star hfc hf_lip ht_star_nn
      hz_cont hz_ode hz_star
  linarith

/-! ## Weak (non-strict) initial-value variants

    In practice the hypothesis `z(0) < c` often comes from an open
    interval like `z₀ ∈ (a, b)`; the strict version above is what gets
    used.  Still, for completeness we record the non-strict variants:
    if `z(0) ≤ c` then `z(t) ≤ c` for all `t ≥ 0` (and symmetrically).

    These follow from the strict versions by case-splitting on whether
    `z(0) = c` (in which case Picard uniqueness makes `z` identically
    `c`, so the conclusion is trivial) or `z(0) < c`. -/

/-- **Non-strict upper barrier.**  Weakens the initial hypothesis to
`z 0 ≤ c`.  If equality holds at `t = 0`, Picard uniqueness identifies
`z` with the constant solution `ẑ ≡ c` for all time. -/
theorem scalar_ode_barrier_above_nonstrict
    (f : ℝ → ℝ) (c : ℝ)
    (hfc : f c = 0)
    (hf_lip : ∀ M : ℝ, 0 ≤ M → ∃ L : NNReal, LipschitzOnWith L f (Icc (-M) M))
    (z : ℝ → ℝ)
    (hz_init : z 0 ≤ c)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (f (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → z t ≤ c := by
  rcases lt_or_eq_of_le hz_init with hlt | heq
  · exact scalar_ode_barrier_above f c hfc hf_lip z hlt hz_ode
  · -- Initial condition `z 0 = c`.  Use Picard uniqueness against
    -- `ẑ ≡ c` on each interval `[0, T]`, `T > 0`.
    intro t ht
    rcases lt_or_eq_of_le ht with htpos | ht0
    · have hz_cont_T : ContinuousOn z (Icc (0 : ℝ) t) := fun s hs =>
        ((hz_ode s hs.1).continuousAt).continuousWithinAt
      obtain ⟨M, hM_nn, hM_c, hz_in_box⟩ :=
        exists_compact_box (le_of_lt htpos) hz_cont_T c
      obtain ⟨L, hL⟩ := hf_lip M hM_nn
      have h_eq : EqOn z (fun _ : ℝ => c) (Icc (0 : ℝ) t) := by
        apply ODE_solution_unique_of_mem_Icc_right
          (v := fun _ x => f x) (s := fun _ => Icc (-M) M)
          (K := L) (a := 0) (b := t)
        · intro s _; exact hL
        · exact hz_cont_T
        · intro s hs
          exact (hz_ode s hs.1).hasDerivWithinAt
        · intro s hs
          exact hz_in_box s ⟨hs.1, le_of_lt hs.2⟩
        · exact continuousOn_const
        · intro s _
          exact (hasDerivAt_const s c).hasDerivWithinAt.congr_deriv hfc.symm
        · intro _ _; exact hM_c
        · exact heq
      have : z t = c := h_eq ⟨le_of_lt htpos, le_refl _⟩
      linarith
    · rw [← ht0]; linarith

/-- **Non-strict lower barrier.**  Weakens the initial hypothesis to
`c ≤ z 0`. -/
theorem scalar_ode_barrier_below_nonstrict
    (f : ℝ → ℝ) (c : ℝ)
    (hfc : f c = 0)
    (hf_lip : ∀ M : ℝ, 0 ≤ M → ∃ L : NNReal, LipschitzOnWith L f (Icc (-M) M))
    (z : ℝ → ℝ)
    (hz_init : c ≤ z 0)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (f (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → c ≤ z t := by
  rcases lt_or_eq_of_le hz_init with hlt | heq
  · exact scalar_ode_barrier_below f c hfc hf_lip z hlt hz_ode
  · intro t ht
    rcases lt_or_eq_of_le ht with htpos | ht0
    · have hz_cont_T : ContinuousOn z (Icc (0 : ℝ) t) := fun s hs =>
        ((hz_ode s hs.1).continuousAt).continuousWithinAt
      obtain ⟨M, hM_nn, hM_c, hz_in_box⟩ :=
        exists_compact_box (le_of_lt htpos) hz_cont_T c
      obtain ⟨L, hL⟩ := hf_lip M hM_nn
      have h_eq : EqOn z (fun _ : ℝ => c) (Icc (0 : ℝ) t) := by
        apply ODE_solution_unique_of_mem_Icc_right
          (v := fun _ x => f x) (s := fun _ => Icc (-M) M)
          (K := L) (a := 0) (b := t)
        · intro s _; exact hL
        · exact hz_cont_T
        · intro s hs
          exact (hz_ode s hs.1).hasDerivWithinAt
        · intro s hs
          exact hz_in_box s ⟨hs.1, le_of_lt hs.2⟩
        · exact continuousOn_const
        · intro s _
          exact (hasDerivAt_const s c).hasDerivWithinAt.congr_deriv hfc.symm
        · intro _ _; exact hM_c
        · exact heq.symm
      have : z t = c := h_eq ⟨le_of_lt htpos, le_refl _⟩
      linarith
    · rw [← ht0]; linarith

end ODE
end Ripple

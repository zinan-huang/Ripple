import Mathlib

/-!
# Scalar exterior-region barriers and coordinatewise box forward-invariance

Reusable a-priori-bound infrastructure for the finite-time ODE engine (`Ripple.Core.ODEFiniteTime`):
to discharge a `FiniteHorizonBound` one needs to bound each coordinate of an arbitrary solution on
`[0,T)`.  For coordinates confined to a box, the right tool is a **forward-invariance barrier**.

IMPORTANT (subtlety surfaced by the ChatGPT pbook audit): the naive *face-only* condition
`g t = b → g' t ≤ 0` is FALSE as an invariance criterion — `g t = t³`, `b = 0` satisfies it at the only
nonnegative contact `t = 0` (`g'(0) = 0 ≤ 0`) yet `g 1 = 1 > 0` (tangential escape).  The correct,
provable hypothesis is the **exterior-region** form: `b ≤ g t → g' t ≤ 0` (whenever the trajectory is
at or above the wall, its velocity is nonpositive).  Proven via Mathlib's strict fencing lemma
`image_le_of_deriv_right_lt_deriv_boundary'` with the tilted barrier `Bε(s) = b + ε·(s+1)`.

These give the coordinatewise box invariant `box_forward_invariant_of_exterior_inward` for DECOUPLED
boxes.  (A coupled system whose face condition needs other coordinates bounded — e.g. a contraction
pair `z ↔ u` — requires the joint first-exit Nagumo argument instead; that is a separate extension.)
-/

noncomputable section

namespace Ripple

open Set
open scoped Topology

/-- **Scalar upper barrier (exterior-region form).**  If `g 0 ≤ b` and whenever `g` is at or above the
wall `b` its (right) derivative is `≤ 0`, then `g` stays `≤ b` on `[0,T]`. -/
theorem scalar_upper_barrier_exterior_on_Icc
    {T b : ℝ} (hT : 0 ≤ T)
    (g gp : ℝ → ℝ)
    (hg0 : g 0 ≤ b)
    (hcont : ContinuousOn g (Icc (0 : ℝ) T))
    (hderiv : ∀ t : ℝ, t ∈ Ico (0 : ℝ) T → HasDerivWithinAt g (gp t) (Ici t) t)
    (hbar : ∀ t : ℝ, t ∈ Ico (0 : ℝ) T → b ≤ g t → gp t ≤ 0) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) T → g t ≤ b := by
  intro t ht
  by_contra hnot
  have hgt : b < g t := lt_of_not_ge hnot
  have ht1 : 0 < t + 1 := by linarith [ht.1]
  let ε : ℝ := (g t - b) / (2 * (t + 1))
  have hε : 0 < ε := by
    have hnum : 0 < g t - b := sub_pos.mpr hgt
    have hden : 0 < 2 * (t + 1) := by positivity
    exact div_pos hnum hden
  have hε_bound : g t ≤ b + ε * (t + 1) := by
    have hBcont : ContinuousOn (fun s : ℝ => b + ε * (s + 1)) (Icc (0 : ℝ) T) := by fun_prop
    have hBderiv : ∀ s : ℝ, s ∈ Ico (0 : ℝ) T →
        HasDerivWithinAt (fun r : ℝ => b + ε * (r + 1)) ε (Ici s) s := by
      intro s hs
      have h : HasDerivAt (fun r : ℝ => b + ε * (r + 1)) ε s := by
        simpa using (((hasDerivAt_id s).add_const (1 : ℝ)).const_mul ε).const_add b
      exact h.hasDerivWithinAt
    have hstart : g 0 ≤ b + ε * (0 + 1) := by nlinarith [hg0, hε]
    have hstrict : ∀ s : ℝ, s ∈ Ico (0 : ℝ) T →
        g s = b + ε * (s + 1) → gp s < ε := by
      intro s hs hcontact
      have hs1 : 0 < s + 1 := by linarith [hs.1]
      have hb_lt_g : b < g s := by rw [hcontact]; nlinarith [hε, hs1]
      have hgp_nonpos : gp s ≤ 0 := hbar s hs (le_of_lt hb_lt_g)
      linarith [hgp_nonpos, hε]
    exact image_le_of_deriv_right_lt_deriv_boundary'
      (f := g) (f' := gp) (a := (0 : ℝ)) (b := T)
      (B := fun s : ℝ => b + ε * (s + 1)) (B' := fun _s : ℝ => ε)
      hcont hderiv hstart hBcont hBderiv hstrict ht
  have hmul : ε * (t + 1) = (g t - b) / 2 := by
    have hε_def : ε = (g t - b) / (2 * (t + 1)) := rfl
    rw [hε_def]; field_simp
  rw [hmul] at hε_bound
  nlinarith

/-- **Scalar lower barrier (exterior-region form).**  Mirror of the upper barrier via `-g`. -/
theorem scalar_lower_barrier_exterior_on_Icc
    {T a : ℝ} (hT : 0 ≤ T)
    (g gp : ℝ → ℝ)
    (hg0 : a ≤ g 0)
    (hcont : ContinuousOn g (Icc (0 : ℝ) T))
    (hderiv : ∀ t : ℝ, t ∈ Ico (0 : ℝ) T → HasDerivWithinAt g (gp t) (Ici t) t)
    (hbar : ∀ t : ℝ, t ∈ Ico (0 : ℝ) T → g t ≤ a → 0 ≤ gp t) :
    ∀ t : ℝ, t ∈ Icc (0 : ℝ) T → a ≤ g t := by
  have hupper : ∀ t : ℝ, t ∈ Icc (0 : ℝ) T → (-g t) ≤ -a := by
    apply scalar_upper_barrier_exterior_on_Icc (T := T) (b := -a) hT
      (fun t : ℝ => -g t) (fun t : ℝ => -gp t)
    · linarith
    · exact hcont.neg
    · exact fun t ht => (hderiv t ht).neg
    · intro t ht hle
      have hga : g t ≤ a := by linarith
      have hgp : 0 ≤ gp t := hbar t ht hga
      linarith
  intro t ht
  have h := hupper t ht
  linarith

/-- **Coordinatewise box forward-invariance (exterior-region / DECOUPLED form).**  If the trajectory
starts in the box `∏ᵢ [lo i, hi i]` and at every coordinate the exterior-region inward condition holds
(velocity `≤ 0` whenever at/above the upper wall, `≥ 0` whenever at/below the lower wall), it stays in
the box.  Reduces coordinatewise to the scalar barriers. -/
theorem box_forward_invariant_of_exterior_inward
    {ι : Type*} [Fintype ι]
    (lo hi : ι → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (x : ℝ → ι → ℝ) (F : ℝ → (ι → ℝ) → ι → ℝ)
    (hx0 : ∀ i, x 0 i ∈ Icc (lo i) (hi i))
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (F t (x t)) t)
    (hlower : ∀ t : ℝ, 0 ≤ t → ∀ i, x t i ≤ lo i → 0 ≤ F t (x t) i)
    (hupper : ∀ t : ℝ, 0 ≤ t → ∀ i, hi i ≤ x t i → F t (x t) i ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ i, x t i ∈ Icc (lo i) (hi i) := by
  intro T hT i
  have hcont_i : ContinuousOn (fun t : ℝ => x t i) (Icc (0 : ℝ) T) := by
    intro t ht
    have hcoord : HasDerivAt (fun s : ℝ => x s i) ((F t (x t)) i) t := by
      simpa using (hasDerivAt_pi.mp (hderiv t ht.1)) i
    exact hcoord.continuousAt.continuousWithinAt
  have hderiv_i : ∀ t : ℝ, t ∈ Ico (0 : ℝ) T →
      HasDerivWithinAt (fun s : ℝ => x s i) ((F t (x t)) i) (Ici t) t := by
    intro t ht
    have hcoord : HasDerivAt (fun s : ℝ => x s i) ((F t (x t)) i) t := by
      simpa using (hasDerivAt_pi.mp (hderiv t ht.1)) i
    exact hcoord.hasDerivWithinAt
  have hupper_i : x T i ≤ hi i := by
    apply scalar_upper_barrier_exterior_on_Icc (T := T) (b := hi i) hT
      (fun t : ℝ => x t i) (fun t : ℝ => F t (x t) i)
    · exact (hx0 i).2
    · exact hcont_i
    · exact hderiv_i
    · exact fun t ht hhi => hupper t ht.1 i hhi
    · exact ⟨hT, le_rfl⟩
  have hlower_i : lo i ≤ x T i := by
    apply scalar_lower_barrier_exterior_on_Icc (T := T) (a := lo i) hT
      (fun t : ℝ => x t i) (fun t : ℝ => F t (x t) i)
    · exact (hx0 i).1
    · exact hcont_i
    · exact hderiv_i
    · exact fun t ht hlo => hlower t ht.1 i hlo
    · exact ⟨hT, le_rfl⟩
  exact ⟨hlower_i, hupper_i⟩

end Ripple

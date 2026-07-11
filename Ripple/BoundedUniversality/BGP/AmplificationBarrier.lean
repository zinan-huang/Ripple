/-
Ripple.BoundedUniversality.BGP.AmplificationBarrier
---------------------------------
Snap-ball overlap impossibility: if two configurations have overlapping
snap balls (r₀-balls in L∞) but their step-encodings diverge at some
coordinate beyond 2*ηstep, then the snap condition is unsatisfiable
for ANY function F (polynomial or otherwise).

This is the abstract barrier that prevents robust polynomial tracking
of expanding operations (like pop with multiplier B > 1 on a fractional
stack encoding).  Concretely:

* **Bounded machines**: the lattice separation condition (2*r₀ < sep in
  `RobustRealExtension`) prevents the overlapping-ball scenario from
  arising — distinct configs' snap balls are disjoint.  This is exactly
  why the BCGH construction succeeds for bounded stacks despite pop
  having multiplier B = 6.

* **Unbounded machines**: configs differing deep in a stack have
  arbitrarily small encoding differences Θ(1/B^n), so any fixed r₀ > 0
  eventually admits overlapping pairs.  At those pairs the pop
  operation amplifies the difference by B > 1, violating the 2*ηstep
  bound below.  This barrier (combined with the packing theorem
  `Ripple.BoundedUniversality.GPAC.Impossibility.packing_finite` which kills the lattice
  encoding itself) is what makes robust tracking of unbounded-space
  computation impossible in fixed dimension.

The proof is the triangle inequality: at the midpoint of two
overlapping balls, the snap function must be ηstep-close to BOTH
step-targets simultaneously, so the targets are at most 2*ηstep apart.
-/

import Mathlib

namespace Ripple.BoundedUniversality.BGP

/-! ## Core triangle inequality -/

/-- **Snap triangle.** If a value v is ηstep-close to both a and b,
then a and b are 2*ηstep-close.  This is the one-dimensional core of
the snap-ball overlap argument. -/
theorem snap_triangle {v a b ηstep : ℝ}
    (h₁ : |v - a| ≤ ηstep) (h₂ : |v - b| ≤ ηstep) :
    |a - b| ≤ 2 * ηstep :=
  calc |a - b|
      = |(a - v) + (v - b)| := by congr 1; ring
    _ ≤ |a - v| + |v - b| := abs_add_le _ _
    _ = |v - a| + |v - b| := by rw [abs_sub_comm (a := a)]
    _ ≤ ηstep + ηstep := add_le_add h₁ h₂
    _ = 2 * ηstep := by ring

/-! ## Snap-ball overlap bound -/

/-- **Snap-overlap step bound.** If two encoded configurations have
L∞-overlapping r₀-balls (every coordinate difference ≤ 2*r₀), then
the snap condition forces their step-encodings to be coordinatewise
within 2*ηstep.

The function `Feval` is arbitrary — no polynomiality, continuity, or
other regularity is assumed.  The proof constructs the coordinate-wise
midpoint as the witness in the overlap.

For the connection to `RobustRealExtension`: there `Feval x i` is
`MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (F i)`, and the snap condition
is the `snap` field.  The lattice separation condition `two_r₀_lt_sep`
ensures `h_overlap` can never hold for distinct configurations, so this
theorem degenerates to vacuous truth INSIDE `RobustRealExtension` — it
gains force only when separation is absent (unbounded machines). -/
theorem snap_overlap_step_bound
    {d : ℕ} (Feval : (Fin d → ℝ) → Fin d → ℝ)
    {enc₁ enc₂ step₁ step₂ : Fin d → ℝ}
    {r₀ ηstep : ℝ}
    (h_overlap : ∀ j, |enc₁ j - enc₂ j| ≤ 2 * r₀)
    (h_snap₁ : ∀ (x : Fin d → ℝ), (∀ j, |x j - enc₁ j| ≤ r₀) →
      ∀ i, |Feval x i - step₁ i| ≤ ηstep)
    (h_snap₂ : ∀ (x : Fin d → ℝ), (∀ j, |x j - enc₂ j| ≤ r₀) →
      ∀ i, |Feval x i - step₂ i| ≤ ηstep) :
    ∀ i, |step₁ i - step₂ i| ≤ 2 * ηstep := by
  intro i
  -- The midpoint of the two encodings lies in both r₀-balls.
  set x : Fin d → ℝ := fun j => (enc₁ j + enc₂ j) / 2 with hxdef
  have hx₁ : ∀ j, |x j - enc₁ j| ≤ r₀ := by
    intro j
    have heq : x j - enc₁ j = (enc₂ j - enc₁ j) / 2 := by
      simp only [hxdef]; ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_sub_comm]
    linarith [h_overlap j]
  have hx₂ : ∀ j, |x j - enc₂ j| ≤ r₀ := by
    intro j
    have heq : x j - enc₂ j = (enc₁ j - enc₂ j) / 2 := by
      simp only [hxdef]; ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [h_overlap j]
  -- Apply snap for both configs at the midpoint, then triangle.
  exact snap_triangle (h_snap₁ x hx₁ i) (h_snap₂ x hx₂ i)

/-! ## Amplification barrier (impossibility) -/

/-- **Amplification barrier.**  If two encoded configurations have
overlapping r₀-balls but their step-encodings diverge beyond 2*ηstep
at some coordinate, then no function can satisfy the snap condition
simultaneously for both.

This is the ABSTRACT reason why pop (multiplier B > 1) prevents robust
polynomial tracking when the encoding has insufficient separation.
For a fractional base-B stack encoding:
* pop amplifies the step-encoding difference by B,
* the snap condition limits it to 2*ηstep < 2*r₀,
* so close configs (|enc diff| ≤ 2*r₀) with B*|enc diff| > 2*ηstep
  are impossible to track, and such configs exist when stacks are
  unbounded.

The function `Feval` is completely arbitrary; the impossibility is
purely metric, not algebraic. -/
theorem no_snap_if_step_amplifies
    {d : ℕ} (Feval : (Fin d → ℝ) → Fin d → ℝ)
    {enc₁ enc₂ step₁ step₂ : Fin d → ℝ}
    {r₀ ηstep : ℝ}
    (h_overlap : ∀ j, |enc₁ j - enc₂ j| ≤ 2 * r₀)
    (h_snap₁ : ∀ (x : Fin d → ℝ), (∀ j, |x j - enc₁ j| ≤ r₀) →
      ∀ i, |Feval x i - step₁ i| ≤ ηstep)
    (h_snap₂ : ∀ (x : Fin d → ℝ), (∀ j, |x j - enc₂ j| ≤ r₀) →
      ∀ i, |Feval x i - step₂ i| ≤ ηstep)
    {i : Fin d}
    (h_diverge : 2 * ηstep < |step₁ i - step₂ i|) :
    False :=
  absurd (snap_overlap_step_bound Feval h_overlap h_snap₁ h_snap₂ i)
    (not_le.mpr h_diverge)

/-! ## Specialisation to polynomial evaluation

The following restates the barrier for the MvPolynomial evaluation
used in `RobustRealExtension.snap`, so the connection is explicit. -/

/-- Polynomial-evaluation specialisation of `no_snap_if_step_amplifies`.
`F` is a tuple of multivariate polynomials over ℚ, evaluated at a real
point via `algebraMap ℚ ℝ`.  The theorem says: no choice of `F` can
simultaneously snap two configurations whose r₀-balls overlap if their
step-encodings diverge at some coordinate. -/
theorem no_poly_snap_if_step_amplifies
    {d : ℕ} (F : Fin d → MvPolynomial (Fin d) ℚ)
    {enc₁ enc₂ step₁ step₂ : Fin d → ℝ}
    {r₀ ηstep : ℝ}
    (h_overlap : ∀ j, |enc₁ j - enc₂ j| ≤ 2 * r₀)
    (h_snap₁ : ∀ (x : Fin d → ℝ), (∀ j, |x j - enc₁ j| ≤ r₀) →
      ∀ i, |MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (F i) - step₁ i| ≤ ηstep)
    (h_snap₂ : ∀ (x : Fin d → ℝ), (∀ j, |x j - enc₂ j| ≤ r₀) →
      ∀ i, |MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (F i) - step₂ i| ≤ ηstep)
    {i : Fin d}
    (h_diverge : 2 * ηstep < |step₁ i - step₂ i|) :
    False :=
  no_snap_if_step_amplifies
    (fun x i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (F i))
    h_overlap h_snap₁ h_snap₂ h_diverge

end Ripple.BoundedUniversality.BGP

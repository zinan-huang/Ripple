/-
  Ripple.Kurtz.StrongApprox.SignChange — a function on `(0,∞)` whose derivative changes sign
  once (from `−` to `+`) and which vanishes at both ends is nonpositive

  This is the "one sign change" step of the Serov–Zubkov / direct Poisson intersections.

  Hypotheses: `Δ` continuous on `(0,∞)`, differentiable away from one point `k` with
  `Δ' = w · σ`, `w > 0`, and the set `{σ < 0}` is an initial segment of `(0,∞)`; `Δ → 0` at `0⁺`
  and at `+∞`.  Conclusion: `Δ ≤ 0` on `(0,∞)`.  Differentiability at `k` is not needed: the
  monotonicity is glued across `k` using continuity.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Set Filter Topology

/-- Gluing two antitone pieces at a common point. -/
theorem antitoneOn_glue {f : ℝ → ℝ} {a k b : ℝ} (hak : a < k) (hkb : k ≤ b)
    (h1 : AntitoneOn f (Ioc a k)) (h2 : AntitoneOn f (Icc k b)) : AntitoneOn f (Ioc a b) := by
  intro x hx y hy hxy
  rcases le_or_gt y k with hyk | hyk
  · exact h1 ⟨hx.1, hxy.trans hyk⟩ ⟨hy.1, hyk⟩ hxy
  · rcases le_or_gt k x with hkx | hkx
    · exact h2 ⟨hkx, hx.2⟩ ⟨hkx.trans hxy, hy.2⟩ hxy
    · calc f y ≤ f k := h2 ⟨le_rfl, hkb⟩ ⟨hyk.le, hy.2⟩ hyk.le
        _ ≤ f x := h1 ⟨hx.1, hkx.le⟩ ⟨hak, le_rfl⟩ hkx.le

/-- Gluing two monotone pieces at a common point. -/
theorem monotoneOn_glue {f : ℝ → ℝ} {a k : ℝ} (hak : a ≤ k)
    (h1 : MonotoneOn f (Icc a k)) (h2 : MonotoneOn f (Ici k)) : MonotoneOn f (Ici a) := by
  intro x hx y hy hxy
  rcases le_or_gt y k with hyk | hyk
  · exact h1 ⟨hx, hxy.trans hyk⟩ ⟨hy, hyk⟩ hxy
  · rcases le_or_gt k x with hkx | hkx
    · exact h2 hkx (hkx.trans hxy) hxy
    · calc f x ≤ f k := h1 ⟨hx, hkx.le⟩ ⟨hak, le_rfl⟩ hkx.le
        _ ≤ f y := h2 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hyk.le) hyk.le

/-- Antitone on a convex set from `HasDerivAt` with nonpositive derivative at every interior
point (the interior avoiding a given exceptional point is handled by the caller). -/
theorem antitoneOn_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn f D) (hderiv : ∀ x ∈ interior D, HasDerivAt f (f' x) x)
    (hnonpos : ∀ x ∈ interior D, f' x ≤ 0) : AntitoneOn f D :=
  antitoneOn_of_deriv_nonpos hD hcont
    (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hderiv x hx).deriv]; exact hnonpos x hx)

theorem monotoneOn_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn f D) (hderiv : ∀ x ∈ interior D, HasDerivAt f (f' x) x)
    (hnonneg : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D :=
  monotoneOn_of_deriv_nonneg hD hcont
    (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hderiv x hx).deriv]; exact hnonneg x hx)

/-- The one-sign-change lemma. -/
theorem le_zero_of_sign_change {Δ σ w : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hcont : ContinuousOn Δ (Ioi 0))
    (hderiv : ∀ x, 0 < x → x ≠ k → HasDerivAt Δ (w x * σ x) x)
    (hw : ∀ x, 0 < x → 0 < w x)
    (hσ : ∀ x y, 0 < x → x < y → σ y < 0 → σ x < 0)
    (h0 : Tendsto Δ (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto Δ atTop (𝓝 0)) :
    ∀ x, 0 < x → Δ x ≤ 0 := by
  intro x hx
  -- derivative sign on pieces
  have hneg : ∀ D : Set ℝ, Convex ℝ D → D ⊆ Ioi 0 → k ∉ interior D →
      (∀ y ∈ interior D, σ y < 0) → AntitoneOn Δ D := by
    intro D hD hD0 hkD hs
    refine antitoneOn_of_hasDerivAt_nonpos (f' := fun y => w y * σ y) hD (hcont.mono hD0)
      (fun y hy => ?_) (fun y hy => ?_)
    · exact hderiv y (hD0 (interior_subset hy)) (fun h => hkD (h ▸ hy))
    · exact mul_nonpos_of_nonneg_of_nonpos (hw y (hD0 (interior_subset hy))).le (hs y hy).le
  have hpos : ∀ D : Set ℝ, Convex ℝ D → D ⊆ Ioi 0 → k ∉ interior D →
      (∀ y ∈ interior D, 0 ≤ σ y) → MonotoneOn Δ D := by
    intro D hD hD0 hkD hs
    refine monotoneOn_of_hasDerivAt_nonneg (f' := fun y => w y * σ y) hD (hcont.mono hD0)
      (fun y hy => ?_) (fun y hy => ?_)
    · exact hderiv y (hD0 (interior_subset hy)) (fun h => hkD (h ▸ hy))
    · exact mul_nonneg (hw y (hD0 (interior_subset hy))).le (hs y hy)
  by_cases hs : σ x < 0
  · -- `Δ` is antitone on `(0, x]`, hence `Δ x ≤ Δ ε` for small `ε`, and `Δ ε → 0`.
    have hanti : AntitoneOn Δ (Ioc 0 x) := by
      have hsx : ∀ y, 0 < y → y < x → σ y < 0 := fun y hy hyx => hσ y x hy hyx hs
      rcases le_or_gt x k with hxk | hkx
      · apply hneg _ (convex_Ioc 0 x) Ioc_subset_Ioi_self
        · rw [interior_Ioc]; intro h; exact absurd h.2 (not_lt.mpr hxk)
        · rw [interior_Ioc]; intro y hy; exact hsx y hy.1 hy.2
      · apply antitoneOn_glue hk hkx.le
        · apply hneg _ (convex_Ioc 0 k) Ioc_subset_Ioi_self
          · rw [interior_Ioc]; intro h; exact lt_irrefl _ h.2
          · rw [interior_Ioc]; intro y hy; exact hsx y hy.1 (hy.2.trans hkx)
        · apply hneg _ (convex_Icc k x) (fun y hy => lt_of_lt_of_le hk hy.1)
          · rw [interior_Icc]; intro h; exact lt_irrefl _ h.1
          · rw [interior_Icc]; intro y hy; exact hsx y (hk.trans hy.1) hy.2
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Δ x ≤ Δ ε := by
      filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
      exact hanti ⟨hε.1, hε.2.le⟩ ⟨hx, le_rfl⟩ hε.2.le
    exact ge_of_tendsto h0 hev
  · -- `Δ` is monotone on `[x, ∞)`, hence `Δ x ≤ Δ M` for large `M`, and `Δ M → 0`.
    push Not at hs
    have hmono : MonotoneOn Δ (Ici x) := by
      have hsx : ∀ y, x < y → 0 ≤ σ y := by
        intro y hxy
        by_contra h
        push Not at h
        exact absurd (hσ x y hx hxy h) (not_lt.mpr hs)
      rcases le_or_gt k x with hkx | hxk
      · apply hpos _ (convex_Ici x) (fun y hy => lt_of_lt_of_le hx hy)
        · rw [interior_Ici]; intro h; exact absurd h (not_lt.mpr hkx)
        · rw [interior_Ici]; intro y hy; exact hsx y hy
      · apply monotoneOn_glue hxk.le
        · apply hpos _ (convex_Icc x k) (fun y hy => lt_of_lt_of_le hx hy.1)
          · rw [interior_Icc]; intro h; exact lt_irrefl _ h.2
          · rw [interior_Icc]; intro y hy; exact hsx y hy.1
        · apply hpos _ (convex_Ici k) (fun y hy => lt_of_lt_of_le hk hy)
          · rw [interior_Ici]; intro h; exact lt_irrefl _ (mem_Ioi.mp h)
          · rw [interior_Ici]; intro y hy; exact hsx y (hxk.trans hy)
    have hev : ∀ᶠ M in atTop, Δ x ≤ Δ M := by
      filter_upwards [eventually_ge_atTop x] with M hM
      exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hM) hM
    exact ge_of_tendsto hinf hev

end Ripple.Kurtz.StrongApprox

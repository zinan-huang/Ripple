/-
Ripple.BoundedUniversality.GPAC.ReadoutPreserve
----------------------------
Readout preservation under time reparameterization.

If s : ℝ → ℝ tends to +∞, and traj eventually enters a set S,
then traj ∘ s also eventually enters S (forward direction).

The backward direction needs tail-surjectivity of s.
-/

import Ripple.BoundedUniversality.GPAC.Readout

namespace Ripple.BoundedUniversality.GPAC

open Filter

/-- Forward: eventual membership transfers through a time change s → ∞. -/
theorem eventually_mem_comp_of_tendsto
    {α : Type*} {S : Set α} {f : ℝ → α} {s : ℝ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hf : ∃ T : ℝ, ∀ t ≥ T, f t ∈ S) :
    ∃ T' : ℝ, ∀ τ ≥ T', f (s τ) ∈ S := by
  obtain ⟨T, hT⟩ := hf
  have hev := hs.eventually (eventually_ge_atTop T)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T', hT'⟩ := hev
  exact ⟨T', fun τ hτ => hT (s τ) (hT' τ hτ)⟩

/-- Backward: if tail-surjectivity holds, eventual membership in
compiled time implies eventual membership in original time. -/
theorem eventually_mem_of_comp_tailSurj
    {α : Type*} {S : Set α} {f : ℝ → α} {s : ℝ → ℝ}
    (hsurj_tail : ∀ T' : ℝ, ∃ T : ℝ, ∀ t ≥ T, ∃ τ ≥ T', s τ = t)
    (hfs : ∃ T' : ℝ, ∀ τ ≥ T', f (s τ) ∈ S) :
    ∃ T : ℝ, ∀ t ≥ T, f t ∈ S := by
  obtain ⟨T', hT'⟩ := hfs
  obtain ⟨T, hT⟩ := hsurj_tail T'
  exact ⟨T, fun t ht => by
    obtain ⟨τ, hτ_ge, hτ_eq⟩ := hT t ht
    rw [← hτ_eq]
    exact hT' τ hτ_ge⟩

/-- Full iff: eventual membership is equivalent under time change
with Tendsto + tail-surjectivity. -/
theorem eventually_mem_iff_comp
    {α : Type*} {S : Set α} {f : ℝ → α} {s : ℝ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hsurj_tail : ∀ T' : ℝ, ∃ T : ℝ, ∀ t ≥ T, ∃ τ ≥ T', s τ = t) :
    (∃ T : ℝ, ∀ t ≥ T, f t ∈ S) ↔ (∃ T' : ℝ, ∀ τ ≥ T', f (s τ) ∈ S) :=
  ⟨eventually_mem_comp_of_tendsto hs, eventually_mem_of_comp_tailSurj hsurj_tail⟩

end Ripple.BoundedUniversality.GPAC

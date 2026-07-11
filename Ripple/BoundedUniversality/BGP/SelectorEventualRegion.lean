import Ripple.BoundedUniversality.BGP.SelectorFlagRegion

/-!
Ripple.BoundedUniversality.BGP.SelectorEventualRegion
---------------------------------
Final-assembly tiling for the flag-coordinate route: turn "the flag coordinate is in the correct
region on each cycle's interval `[a_j, a_{j+1}]` (read window + between-window latch), for all
`j ≥ N`" into the eventual-threshold form `∃ T, ∀ t ≥ T, …`, where `a_j = 2πj + 5π/6` is the
read-window start.  The per-interval premise bundles avenue (c)'s read-window region with the
between-window latch (gap E, carried satisfiably).  Pure real-analysis tiling — no dynamics.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set

/-- **Tiling of `[a_N, ∞)` by the cycle intervals.**  For `a_j = 2πj + 5π/6`, any `t ≥ a_N` lies in
some `[a_j, a_{j+1}]` with `j ≥ N`.  (`j := ⌊(t − 5π/6)/(2π)⌋₊`.) -/
theorem readWindow_tiling {N : ℕ} {t : ℝ}
    (ht : 2 * Real.pi * (N : ℝ) + 5 * Real.pi / 6 ≤ t) :
    ∃ j, N ≤ j ∧
      2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 ≤ t ∧
      t ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by linarith
  set x : ℝ := (t - 5 * Real.pi / 6) / (2 * Real.pi) with hx
  have hxN : (N : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ h2π]; nlinarith [ht]
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg N) hxN
  refine ⟨⌊x⌋₊, ?_, ?_, ?_⟩
  · exact Nat.le_floor hxN
  · have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have : 2 * Real.pi * (⌊x⌋₊ : ℝ) ≤ 2 * Real.pi * x := by nlinarith [hfl, h2π]
    have hxe : 2 * Real.pi * x = t - 5 * Real.pi / 6 := by
      rw [hx]; field_simp
    nlinarith [this, hxe]
  · have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have : 2 * Real.pi * x < 2 * Real.pi * ((⌊x⌋₊ : ℝ) + 1) := by nlinarith [hfl, h2π]
    have hxe : 2 * Real.pi * x = t - 5 * Real.pi / 6 := by
      rw [hx]; field_simp
    nlinarith [this, hxe]

/-- **Eventual region from the tiled per-interval region.**  If a predicate `P` holds on every cycle
interval `[a_j, a_{j+1}]` for `j ≥ N`, then it holds for all `t ≥ a_N`.  This is the final assembly:
given avenue (c)'s read-window region + the between-window latch (together giving `P` on each full
`[a_j, a_{j+1}]`), the eventual-threshold conclusion follows. -/
theorem eventual_region_of_tiled {P : ℝ → Prop} {N : ℕ}
    (htile : ∀ j, N ≤ j → ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), P t) :
    ∃ T : ℝ, ∀ t ≥ T, P t := by
  refine ⟨2 * Real.pi * (N : ℝ) + 5 * Real.pi / 6, fun t ht => ?_⟩
  obtain ⟨j, hjN, hlo, hhi⟩ := readWindow_tiling ht
  exact htile j hjN t ⟨hlo, hhi⟩

end Ripple.BoundedUniversality.BGP

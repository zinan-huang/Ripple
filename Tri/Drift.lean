/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Direction
import Tri.Decay
import Tri.Bracket

/-!
# One-step drift of the Tri chain

`Tri.feller_ruin` is a general theorem about any chain conserving a geometric
potential. This file is the bridge that makes it a statement about **this CRN**:
it computes one step of `triStep` explicitly and identifies the base at which the
potential is conserved.

The computation rests on the odds-ratio identity `Tri.odds_cross_mul`:

    upCount · b = downCount · a          (i.e. up/down = (x-1)/(y-1))

so the harmonic base of the Tri chain is `ρ = (x-1)/(y-1) = a/b`, and
conservation of `ρ⁻¹ ^ level` becomes a comparison of *integers*. No probability,
no division, and no real analysis enter the drift argument at all.

## Main results

* `triStep_eq_zero` — the chain moves by at most one, so the step distribution is
  supported on `{a, a+1, a+2}`.
* `expect_triStep` — one step of the chain, as an explicit three-term sum. This
  is the computation `feller_ruin`'s hypothesis needs.
* `expect_triStep_le` — the conservation inequality, reduced to a hypothesis on
  the three atom masses alone.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Section 3.1.
-/

namespace Tri

open scoped ENNReal

/-- The chain changes the `X`-count by at most one, so from `x = a+1` the step
distribution is supported on `{a, a+1, a+2}`. -/
theorem triStep_eq_zero (a y : ℕ) (h : 3 ≤ (a + 1) + y) {z : ℕ}
    (h0 : z ≠ a) (h1 : z ≠ a + 1) (h2 : z ≠ a + 2) :
    triStep (a + 1) y h z = 0 := by
  unfold triStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  simp [nextX, h0, h1, h2]

/-- **One step of the Tri chain, explicitly.** The expectation of any potential
collapses to three terms, because the chain is supported on `{a, a+1, a+2}`.

This is what turns `feller_ruin`'s abstract conservation hypothesis into a finite
arithmetic obligation. -/
theorem expect_triStep (a y : ℕ) (h : 3 ≤ (a + 1) + y) (V : ℕ → ℝ≥0∞) :
    expect (triStep (a + 1) y h) V
      = triStep (a + 1) y h a * V a
      + triStep (a + 1) y h (a + 1) * V (a + 1)
      + triStep (a + 1) y h (a + 2) * V (a + 2) := by
  unfold expect
  rw [tsum_eq_sum (s := ({a, a + 1, a + 2} : Finset ℕ)) ?_]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    ring
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [triStep_eq_zero a y h hz.1 hz.2.1 hz.2.2, zero_mul]

/-- **Conservation, reduced to the three atom masses.**

If the potential's values at the three reachable states satisfy the one-step
inequality, the potential does not increase. Stated with the masses abstract so
that the probabilistic content is fully separated from the arithmetic of which
base makes the inequality hold.

The point of the reduction: the hypothesis mentions only `V` at three points and
the three masses, all of which are explicit — so discharging it is arithmetic,
not analysis. -/
theorem expect_triStep_le (a y : ℕ) (h : 3 ≤ (a + 1) + y) (V : ℕ → ℝ≥0∞)
    (hdrift : triStep (a + 1) y h a * V a
        + triStep (a + 1) y h (a + 1) * V (a + 1)
        + triStep (a + 1) y h (a + 2) * V (a + 2) ≤ V (a + 1)) :
    expect (triStep (a + 1) y h) V ≤ V (a + 1) := by
  rw [expect_triStep]
  exact hdrift

/-- **The one-step drift inequality in `ℝ≥0∞`.**

The scalar core `Tri.three_term_drift` is stated over `ℝ`, because `ℝ≥0∞`'s
truncated subtraction blocks the `(1-u)` factoring its proof needs. Everything
here is finite — each mass is `≤ 1` because the three sum to `1`, and `u ≤ 1` —
so the transfer costs only bookkeeping and no extra hypotheses.

This is the form the kernel-level argument consumes. -/
theorem three_term_drift_ennreal {p0 p1 p2 u : ℝ≥0∞}
    (hsum : p0 + p1 + p2 = 1) (hu1 : u ≤ 1) (hdrift : p0 ≤ p2 * u) :
    p0 + p1 * u + p2 * u ^ 2 ≤ u := by
  -- everything is finite: each mass is ≤ 1 and u ≤ 1
  have h0 : p0 ≤ 1 := by rw [← hsum]; exact le_add_right (le_add_right le_rfl)
  have h1 : p1 ≤ 1 := by rw [← hsum]; calc p1 ≤ p0 + p1 := le_add_left le_rfl
                                          _ ≤ p0 + p1 + p2 := le_add_right le_rfl
  have h2 : p2 ≤ 1 := by rw [← hsum]; exact le_add_left le_rfl
  have f0 : p0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h0
  have f1 : p1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have f2 : p2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h2
  have fu : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have fL : p0 + p1 * u + p2 * u ^ 2 ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨f0, ?_⟩, ?_⟩
    · exact ENNReal.mul_ne_top f1 fu
    · exact ENNReal.mul_ne_top f2 (ENNReal.pow_ne_top fu)
  rw [← ENNReal.toReal_le_toReal fL fu]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f0, ENNReal.mul_ne_top f1 fu⟩)
        (ENNReal.mul_ne_top f2 (ENNReal.pow_ne_top fu)),
      ENNReal.toReal_add f0 (ENNReal.mul_ne_top f1 fu),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
  refine three_term_drift ?_ ENNReal.toReal_nonneg ?_ ?_
  · have := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f0, f1⟩) f2,
        ENNReal.toReal_add f0 f1, ENNReal.toReal_one] at this
  · exact (ENNReal.toReal_le_toReal fu ENNReal.one_ne_top).mpr hu1 |>.trans_eq ENNReal.toReal_one
  · have := (ENNReal.toReal_le_toReal f0 (ENNReal.mul_ne_top f2 fu)).mpr hdrift
    rwa [ENNReal.toReal_mul] at this

/-- The masses sum to one, as they must. Recorded because the conservation
argument uses it to convert "the productive part contracts" into "the whole step
contracts" — the laziness step of `Tri.lazy_conserved`. -/
theorem triStep_masses_sum (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    triStep (a + 1) y h a
      + triStep (a + 1) y h (a + 1)
      + triStep (a + 1) y h (a + 2) = 1 := by
  have := expect_triStep a y h (fun _ => 1)
  simpa [expect, PMF.tsum_coe] using this.symm

/-- Dividing both sides of a drift inequality by the same quantity preserves its
shape. Used to pass from the integer reaction *counts* to the actual step
*masses*, which share the denominator `C(n,3)`. -/
theorem div_le_div_mul_right {d U m c : ℝ≥0∞} (h : d ≤ U * m) :
    d / c ≤ U / c * m := by
  simp only [div_eq_mul_inv]
  calc d * c⁻¹ ≤ (U * m) * c⁻¹ := mul_le_mul_left h _
    _ = U * c⁻¹ * m := by ring

/-- **From integer counts to the drift condition on masses.**

The three atom masses share the denominator `C(n,3)`, so an inequality between
the reaction *counts* transfers verbatim to the probabilities. This is what lets
the entire drift argument be settled by `Tri.odds_cross_mul`, an identity about
natural numbers. -/
theorem triStep_drift_of_counts (a b : ℕ) (h : 3 ≤ (a + 1) + (b + 1)) {u : ℝ≥0∞}
    (hc : (downCount a b : ℝ≥0∞) ≤ (upCount a b : ℝ≥0∞) * u) :
    triStep (a + 1) (b + 1) h a ≤ triStep (a + 1) (b + 1) h (a + 2) * u := by
  rw [triStep_down, triStep_up]
  refine div_le_div_mul_right ?_
  simp only [downCount, upCount] at hc
  push_cast at hc ⊢
  convert hc using 2

/-- **Geometric conservation for the Tri chain.**

If the drift condition holds at a state, the geometric potential `u ^ level` does
not increase in expectation there. This is `feller_ruin`'s hypothesis `hfroz`,
discharged for `triStep` at a single state. -/
theorem triStep_geometric_conserve (a y : ℕ) (h : 3 ≤ (a + 1) + y) {u : ℝ≥0∞}
    (hu1 : u ≤ 1)
    (hdrift : triStep (a + 1) y h a ≤ triStep (a + 1) y h (a + 2) * u) :
    expect (triStep (a + 1) y h) (fun k => u ^ k) ≤ u ^ (a + 1) := by
  rw [expect_triStep]
  have key := three_term_drift_ennreal (triStep_masses_sum a y h) hu1 hdrift
  calc triStep (a + 1) y h a * u ^ a
        + triStep (a + 1) y h (a + 1) * u ^ (a + 1)
        + triStep (a + 1) y h (a + 2) * u ^ (a + 2)
      = u ^ a * (triStep (a + 1) y h a
          + triStep (a + 1) y h (a + 1) * u
          + triStep (a + 1) y h (a + 2) * u ^ 2) := by ring
    _ ≤ u ^ a * u := mul_le_mul_right key _
    _ = u ^ (a + 1) := by ring

/-- **The harmonic base of the Tri chain, realized.**

At `u = b/a` — the reciprocal of the odds ratio `(x-1)/(y-1)` — the drift
condition holds, by `Tri.odds_cross_mul`. Combined with
`triStep_geometric_conserve` this discharges the conservation hypothesis at every
interior state, with no probabilistic input whatsoever: the entire content is the
integer identity `upCount · b = downCount · a`. -/
theorem triStep_drift_at_harmonic (a b : ℕ) (h : 3 ≤ (a + 1) + (b + 1))
    (ha : 0 < a) :
    triStep (a + 1) (b + 1) h a
      ≤ triStep (a + 1) (b + 1) h (a + 2) * ((b : ℝ≥0∞) / (a : ℝ≥0∞)) := by
  refine triStep_drift_of_counts a b h ?_
  have hodds : upCount a b * b = downCount a b * a := odds_cross_mul a b
  have hane : (a : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hatop : (a : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top a
  rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hane) (Or.inl hatop)]
  have hcast : ((downCount a b * a : ℕ) : ℝ≥0∞) = ((upCount a b * b : ℕ) : ℝ≥0∞) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0∞)) hodds.symm
  simp only [downCount, upCount] at hcast ⊢
  push_cast at hcast ⊢
  exact le_of_eq hcast

/-- **The uniform drift condition on a region.**

Combines `Tri.odds_uniform` with the counts-to-masses bridge: throughout the
region `aLo ≤ a`, `b ≤ bHi` the geometric potential with the *single* base
`u = bHi/aLo` satisfies the drift condition. This is the form `feller_ruin`
needs, since it requires one base for the whole live region.

As with the pointwise version, the entire content is an inequality between
natural numbers — no probabilistic estimate is involved anywhere. -/
theorem triStep_drift_uniform (a b aLo bHi : ℕ) (h : 3 ≤ (a + 1) + (b + 1))
    (hLo : aLo ≤ a) (hHi : b ≤ bHi) (haLo : 0 < aLo) :
    triStep (a + 1) (b + 1) h a
      ≤ triStep (a + 1) (b + 1) h (a + 2) * ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) := by
  refine triStep_drift_of_counts a b h ?_
  have hcount : downCount a b * aLo ≤ upCount a b * bHi := odds_uniform hLo hHi haLo
  have hane : (aLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hatop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top aLo
  rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hane) (Or.inl hatop)]
  have hcast : ((downCount a b * aLo : ℕ) : ℝ≥0∞) ≤ ((upCount a b * bHi : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.mpr hcount
  simp only [downCount, upCount] at hcast ⊢
  push_cast at hcast ⊢
  convert hcast using 2

/-- **Conservation on a region, for the Tri chain.**

The geometric potential with the uniform base `bHi/aLo` does not increase
anywhere in the region. Together with `Tri.feller_ruin` this is the safety half
of the paper's Lemma 3, specialized to this CRN.

The hypothesis `bHi ≤ aLo` is the majority-side condition: it makes the base
`≤ 1`, which is what a *decreasing* potential requires. -/
theorem triStep_conserve_on_region (a b aLo bHi : ℕ) (h : 3 ≤ (a + 1) + (b + 1))
    (hLo : aLo ≤ a) (hHi : b ≤ bHi) (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) :
    expect (triStep (a + 1) (b + 1) h) (fun k => ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ (a + 1) := by
  have hane : (aLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hatop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top aLo
  refine triStep_geometric_conserve a (b + 1) h ?_
    (triStep_drift_uniform a b aLo bHi h hLo hHi haLo)
  calc (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)
      ≤ (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) := ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
    _ = 1 := ENNReal.div_self hane hatop

end Tri

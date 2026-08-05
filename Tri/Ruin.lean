/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Decay
import Tri.Bracket

/-!
# The safety (ruin) bound

This is the first of the two engines the analysis needs. Following the paper's
own Lemma 3 — whose proof produces a ruin term and a Chernoff term *separately* —
safety and progress are run with **different** potentials. Sharing one base is
the error recorded in `design/08-cancellation.md`: the Markov threshold factor
then cancels the contraction at leading order and the resulting bound is vacuous.

The safety engine is the cheaper of the two, because at the harmonic base
`ρ_F = p/(1-p)` the one-step bracket is *exactly* `1` (`Tri.bracket_harmonic`),
so the potential is a martingale and no contraction is needed — only
conservation.

Everything is finite-horizon and terminal-state: the bad event is "the level is
low at time `T`", never "the level was ever low". No stopping times, no Doob, no
conditional expectation.

## Main results

* `supermartingale_tail` — if the potential does not increase in expectation,
  it is at least `θ` at time `T` with probability at most `V s₀ / θ`.
* `ruin_le` — Feller's bound in the shape the paper cites as Lemma 1: with the
  geometric potential `ρ⁻¹ ^ level` and `ρ ≥ 1`, dropping `b` levels below the
  start costs at most `ρ⁻¹ ^ b`. At the harmonic base this is `((1-p)/p)^b`.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemma 1 (Feller XIV.2) and Lemma 3.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- **Supermartingale tail bound.** If the potential does not increase in
expectation under one step, then it is unlikely to be large at the horizon.

This is `expect_iter_le` at `c = 1` composed with `markov_div`, and it is the
whole of the safety engine: no contraction is required, only conservation —
which is exactly what the harmonic base provides via `bracket_harmonic`. -/
theorem supermartingale_tail (K : α → PMF α) (V : α → ℝ≥0∞)
    (hK : ∀ s, expect (K s) V ≤ V s) (T : ℕ) (s₀ : α)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (htop : θ ≠ ⊤) :
    ∑' z, (if θ ≤ V z then iter K T s₀ z else 0) ≤ V s₀ / θ := by
  have hstep : ∀ s, expect (K s) V ≤ 1 * V s := by simpa using hK
  have hiter : expect (iter K T s₀) V ≤ 1 ^ T * V s₀ :=
    expect_iter_le K V 1 hstep T s₀
  refine le_trans (markov_div (iter K T s₀) V θ hθ htop) ?_
  exact ENNReal.div_le_div_right (by simpa using hiter) θ

/-- **Feller's ruin bound**, finite-horizon and terminal-state.

`level : α → ℕ` measures progress and `V = ρ⁻¹ ^ level` is the geometric
potential, with `1 ≤ ρ` so that `V` is *antitone* in the level: low levels carry
high potential, which is what makes "ruin" the large-potential event that
Markov's inequality controls.

If `V` is conserved in expectation, then starting from level `m + b` the chance
of sitting at level `≤ m` at time `T` — i.e. of having dropped `b` levels — is
at most `ρ⁻¹ ^ b`. With the harmonic base `ρ = p/(1-p)`, where conservation is
*exact* by `bracket_harmonic`, this is precisely the paper's Lemma 1 bound
`((1-p)/p) ^ b`.

The start level is written `m + b` rather than `level s₀ - b`, keeping the
statement free of truncated subtraction. -/
theorem ruin_le (K : α → PMF α) (level : α → ℕ) (ρ : ℝ≥0∞)
    (hρ1 : 1 ≤ ρ) (hρtop : ρ ≠ ⊤)
    (V : α → ℝ≥0∞) (hV : ∀ s, V s = ρ⁻¹ ^ (level s))
    (hK : ∀ s, expect (K s) V ≤ V s)
    (T m b : ℕ) (s₀ : α) (hs₀ : level s₀ = m + b) :
    ∑' z, (if level z ≤ m then iter K T s₀ z else 0) ≤ ρ⁻¹ ^ b := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hρ1; simp at hρ1
  have hinv : ρ⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hρtop
  have hinvtop : ρ⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hρ0
  have hinv1 : ρ⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hρ1
  set θ : ℝ≥0∞ := ρ⁻¹ ^ m with hθdef
  have hθ : θ ≠ 0 := pow_ne_zero _ hinv
  have htop : θ ≠ ⊤ := ENNReal.pow_ne_top hinvtop
  -- The bad set `level z ≤ m` is contained in the large-potential set `θ ≤ V z`,
  -- because `ρ⁻¹ ≤ 1` makes `ρ⁻¹ ^ ·` antitone.
  have hsub : ∀ z, (if level z ≤ m then iter K T s₀ z else 0)
      ≤ (if θ ≤ V z then iter K T s₀ z else 0) := by
    intro z
    by_cases hz : level z ≤ m
    · have : θ ≤ V z := by
        rw [hV z, hθdef]
        exact pow_le_pow_right_of_le_one' hinv1 hz
      simp [hz, this]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (supermartingale_tail K V hK T s₀ θ hθ htop) ?_
  -- `V s₀ / θ = ρ⁻¹ ^ (m + b) / ρ⁻¹ ^ m = ρ⁻¹ ^ b`
  rw [hV s₀, hs₀, hθdef, pow_add, mul_comm, mul_div_assoc,
    ENNReal.div_self hθ htop, mul_one]

end Tri

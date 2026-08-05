/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma14Leaf

/-!
# Lemma 15, part P2 — the containment leaf for the windowed maximal bound

Paper Lemma 15 asks for a deviation bound that holds at EVERY prefix of a
reveal window, not just at its end.  `ville_frozen` (`Tri/Lemma14Leaf.lean`)
already supplies the maximal inequality in the abstract:

```text
B ⊆ {θ ≤ V}   and   V a supermartingale   ⟹   ⨆ T, hitProb B K T q ≤ V q / θ
```

so all that is missing on the urn side is the CONTAINMENT hypothesis for the
concrete bad set.  That is this file.

## The load-bearing trap: the bad set must carry the clock

The naive bad set — "the centred red fraction has deviated by `δ`" — does NOT
sit inside `{θ ≤ urnG}`.  The potential's variance budget is `urnA (t-1)`,
which SHRINKS as the urn empties, so a state that is deeper in the run than
the window's end can have the same deviation and a strictly smaller potential.
Adding the clock conjunct `u + 1 ≤ z.1 + z.2` — the state has not yet passed
the window's end — restores the containment via `urnA_mono`, and it costs
nothing downstream because the frozen chain is run for exactly the window's
length.

## Subtraction-free clock

The window ends after `s` reveals out of an initial total `ν`.  Rather than
write `ν - s`, the window is parametrised by `u` with

```text
s + (u + 1) = ν
```

so `u + 1` is the total remaining at the window's end and `urnA u` is the
variance budget there.  No statement in this file mentions `ν` or `s`.

## One theorem, both tails

Instead of separate upper/lower containment lemmas, the bad set is stated with
the SIGNED TILT `|λ| · δ ≤ λ · M(z)`.  At `λ ≥ 0` this is the upper tail
`δ ≤ M`; at `λ ≤ 0` it is the lower tail `M ≤ -δ`.  Pairing a negative tilt
with the upper condition would be unsound — multiplying an inequality by a
negative number reverses it — and the signed form makes that impossible to
write by accident.
-/

open scoped ENNReal

namespace Tri

/-- The centred red fraction, as a state function.  This is the `M` of the
Lemma 14 development, read off a state rather than a time. -/
noncomputable def urnM (c₀ : ℝ) (z : ℕ × ℕ) : ℝ :=
  c₀ - (z.1 : ℝ) / ((z.1 : ℝ) + (z.2 : ℝ))

/-- The bad set for the windowed maximal bound: the state is still inside the
window (`u + 1 ≤ total`) AND the signed tilt has reached `|λ| δ`.

Both conjuncts are load-bearing.  Without the clock the containment below is
FALSE, because a deeper state carries a smaller variance budget. -/
def UrnWindowBad (c₀ δ lam : ℝ) (u : ℕ) (z : ℕ × ℕ) : Prop :=
  u + 1 ≤ z.1 + z.2 ∧ |lam| * δ ≤ lam * urnM c₀ z

noncomputable instance (c₀ δ lam : ℝ) (u : ℕ) :
    DecidablePred (UrnWindowBad c₀ δ lam u) :=
  Classical.decPred _

/-- The threshold: the potential value that the bad set is guaranteed to have
reached.  The variance term is evaluated at the window's END budget `urnA u`,
which is the smallest budget any in-window state can have. -/
noncomputable def urnTheta (δ lam : ℝ) (u : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (|lam| * δ + lam ^ 2 / 8 * urnA u))

theorem urnTheta_ne_zero (δ lam : ℝ) (u : ℕ) : urnTheta δ lam u ≠ 0 := by
  unfold urnTheta
  simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]

theorem urnTheta_ne_top (δ lam : ℝ) (u : ℕ) : urnTheta δ lam u ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- **P2, the containment leaf.**  Every in-window state whose signed tilt has
reached `|λ| δ` has potential at least `θ`.

The proof is exactly two monotonicities: `urnA_mono` on the clock conjunct
(this is where the clock is spent), and `Real.exp` monotone.  The linear term
transfers verbatim from the tilt conjunct — no sign analysis is needed,
because the signed form has already absorbed it. -/
theorem urn_window_contain (c₀ δ lam : ℝ) (u : ℕ) (z : ℕ × ℕ)
    (hz : UrnWindowBad c₀ δ lam u z) :
    urnTheta δ lam u ≤ urnG c₀ lam z := by
  obtain ⟨hclock, hdev⟩ := hz
  unfold urnTheta urnG
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  unfold urnExp
  unfold urnM at hdev
  have hA : urnA u ≤ urnA (z.1 + z.2 - 1) := urnA_mono (by omega)
  have hbudget : lam ^ 2 / 8 * urnA u ≤ lam ^ 2 / 8 * urnA (z.1 + z.2 - 1) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

/-- **P2 assembled.**  The maximal windowed deviation bound: over EVERY prefix
length `T`, the mass that has ever entered the bad set is at most `G(q)/θ`.

This is the Lemma 15 shape.  Note that the bound is the same as the
fixed-time Markov bound `urnG_markov` — the maximal strengthening is free,
which is the whole point of routing through `ville_frozen`. -/
theorem urn_window_ville (c₀ δ lam : ℝ) (u : ℕ) (q : ℕ × ℕ) :
    ⨆ T : ℕ, hitProb (UrnWindowBad c₀ δ lam u) urnStopped T q
      ≤ urnG c₀ lam q / urnTheta δ lam u :=
  ville_frozen urnStopped (UrnWindowBad c₀ δ lam u) (urnG c₀ lam)
    (urnTheta δ lam u) (urnTheta_ne_zero δ lam u) (urnTheta_ne_top δ lam u)
    (urn_window_contain c₀ δ lam u) (urnG_step_stopped c₀ lam) q

/-- **P2 at a centred start.**  Starting the window at a state whose red
fraction is exactly `c₀`, the potential collapses to the pure variance term
and the bound becomes an honest exponential tail: the linear part of the
exponent is `-|λ| δ` and the variance part telescopes.

This is the form Lemma 15's assembly consumes: `q = (R, B)`, `c₀ = R/(R+B)`. -/
theorem urn_window_ville_centered (δ lam : ℝ) (u R B : ℕ) :
    ⨆ T : ℕ, hitProb (UrnWindowBad ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ lam u)
        urnStopped T (R, B)
      ≤ ENNReal.ofReal (Real.exp (lam ^ 2 / 8 * urnA (R + B - 1)))
          / urnTheta δ lam u := by
  have h := urn_window_ville ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ lam u (R, B)
  rwa [urnG_centered_start] at h

/-- The bound in closed exponential form: the quotient of the two `ofReal`s is
a single `ofReal` of the exponent difference.  Both budgets are explicit, so
the endgame that optimises `λ` sees a plain real inequality. -/
theorem urn_window_ville_exp (δ lam : ℝ) (u R B : ℕ) :
    ⨆ T : ℕ, hitProb (UrnWindowBad ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ lam u)
        urnStopped T (R, B)
      ≤ ENNReal.ofReal (Real.exp
          (lam ^ 2 / 8 * urnA (R + B - 1)
            - (|lam| * δ + lam ^ 2 / 8 * urnA u))) := by
  refine le_trans (urn_window_ville_centered δ lam u R B) ?_
  unfold urnTheta
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]

end Tri

#print axioms Tri.urn_window_contain
#print axioms Tri.urn_window_ville
#print axioms Tri.urn_window_ville_centered
#print axioms Tri.urn_window_ville_exp

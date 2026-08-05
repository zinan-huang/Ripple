/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Kernel

/-!
# The state-level step distribution

`Tri.interactionPMF` distributes the *composition* of the sampled triple. Pushing
it forward along the resulting change in the `X`-count gives the step
distribution of the CRN on its state space, `Tri.triStep`.

The main results are the three-atom formulas: from an interior state the chain
moves up by one, down by one, or stays, with the masses

    up    : C(x,2)·y  / C(n,3)          (reaction (1), one `Y` becomes an `X`)
    down  : x·C(y,2)  / C(n,3)          (reaction (2), one `X` becomes a `Y`)
    stay  : (C(x,3) + C(y,3)) / C(n,3)  (a homogeneous triple)

Note the "stay" fiber has *two* preimages, `xxx` and `yyy`: this four-to-three
collapse is the only place the composition type and the state space differ, and
it is discharged once here.

## On natural subtraction

Interior states are written `x = a + 1`, so that "down" is `a` rather than
`x - 1`. This keeps every *statement* free of truncated subtraction, which
would silently change meaning exactly at the degenerate populations the paper's
endgame visits. Subtraction appears only inside `nextX`, where it is harmless:
`nextX_zero_xyy_weight_eq_zero` records that the truncating branch carries zero
mass.

## Main results

* `triStep_up`, `triStep_down`, `triStep_stay` — the three atom masses.
* `triStep_consensus_X`, `triStep_consensus_Y` — at consensus the step is `pure`,
  i.e. the consensus states are absorbing. This is what licenses stating the
  final theorem as a marginal rather than as a path property.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Figure 1 and Section 3.
-/

namespace Tri

open scoped ENNReal

/-- The new `X`-count produced by a triple of the given composition.

Reaction (1) (`xxy`) turns a `Y` into an `X`; reaction (2) (`xyy`) turns an `X`
into a `Y`; homogeneous triples change nothing. The truncating branch `x - 1` at
`x = 0` is unreachable in the sense that it carries zero mass — see
`nextX_zero_xyy_weight_eq_zero`. -/
def nextX (x : ℕ) : TripleKind → ℕ
  | .xxx => x
  | .xxy => x + 1
  | .xyy => x - 1
  | .yyy => x

/-- The only branch of `nextX` involving truncated subtraction carries zero
mass, because a triple of composition `xyy` needs an `X` to exist. -/
theorem nextX_zero_xyy_weight_eq_zero (y : ℕ) : TripleKind.weight 0 y .xyy = 0 := by
  simp [TripleKind.weight]

/-- The step distribution of the CRN on its state space, where the state records
the number of `X` molecules. -/
noncomputable def triStep (x y : ℕ) (h : 3 ≤ x + y) : PMF ℕ :=
  (interactionPMF x y h).map (nextX x)

/-- **Up-step mass.** From the interior state `a + 1` the chain moves to `a + 2`
exactly when the sampled triple has composition `xxy`, i.e. reaction (1)
fires. -/
theorem triStep_up (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    triStep (a + 1) y h (a + 2)
      = (Nat.choose (a + 1) 2 * y : ℝ≥0∞) / (Nat.choose ((a + 1) + y) 3 : ℝ≥0∞) := by
  unfold triStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  simp [nextX, TripleKind.weight, interactionPMF]

/-- **Down-step mass.** From the interior state `a + 1` the chain moves to `a`
exactly when the sampled triple has composition `xyy`, i.e. reaction (2)
fires. -/
theorem triStep_down (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    triStep (a + 1) y h a
      = ((a + 1) * Nat.choose y 2 : ℝ≥0∞) / (Nat.choose ((a + 1) + y) 3 : ℝ≥0∞) := by
  unfold triStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  simp [nextX, TripleKind.weight, interactionPMF, show a ≠ a + 1 + 1 by omega]

/-- **Stay mass.** The chain is unchanged exactly when the sampled triple is
homogeneous. This fiber has two preimages, `xxx` and `yyy`, and is the only
place where the four compositions collapse onto three state transitions. -/
theorem triStep_stay (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    triStep (a + 1) y h (a + 1)
      = (Nat.choose (a + 1) 3 + Nat.choose y 3 : ℝ≥0∞)
          / (Nat.choose ((a + 1) + y) 3 : ℝ≥0∞) := by
  unfold triStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  simp [nextX, TripleKind.weight, interactionPMF]
  rw [ENNReal.div_add_div_same]

/-- **`X`-consensus is absorbing.** With no `Y` molecules present every triple is
homogeneous, so the state cannot change. -/
theorem triStep_consensus_X (x : ℕ) (h : 3 ≤ x + 0) : triStep x 0 h = PMF.pure x := by
  have h' : 3 ≤ x := by omega
  have hne : ((Nat.choose x 3 : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_three_pos h').ne'
  have htop : ((Nat.choose x 3 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext b
  unfold triStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  rcases eq_or_ne b x with rfl | hb
  · simp [nextX, TripleKind.weight, interactionPMF, PMF.pure_apply,
      ENNReal.div_self hne htop]
  · simp [nextX, TripleKind.weight, interactionPMF, PMF.pure_apply, hb]

/-- **`Y`-consensus is absorbing.** With no `X` molecules present every triple is
homogeneous, so the state cannot change. -/
theorem triStep_consensus_Y (y : ℕ) (h : 3 ≤ 0 + y) : triStep 0 y h = PMF.pure 0 := by
  have h' : 3 ≤ y := by omega
  have hne : ((Nat.choose y 3 : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_three_pos h').ne'
  have htop : ((Nat.choose y 3 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext b
  unfold triStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind)
        = {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [nextX, TripleKind.weight, interactionPMF, PMF.pure_apply,
      ENNReal.div_self hne htop]
  · simp [nextX, TripleKind.weight, interactionPMF, PMF.pure_apply, hb]

end Tri

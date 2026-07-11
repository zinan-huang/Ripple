/-
Ripple.BoundedUniversality.GPAC.BoundedRobustStep
-----------------------------
Capstone of the bounded rational robust step: combine the concrete
rational coordinatewise rounder (`coordinatewise_rounder_contracts`)
with the abstract robustness mechanism (`step_contracts`).

Result: there is a rational rounder polynomial `R` and a radius `ρ>0`
such that, for ANY transition `T` that is exact on the encoding grid
(`T c = c'`) and `L`-Lipschitz near it, with `k` pre-roundings absorbing
`L` (`L ≤ 2^k`), the bounded rational step
`Step = C ∘ T ∘ C^[k]` (with `C` the coordinatewise rounder) contracts the
`ρ`-neighborhood of `enc c` toward `enc c'` by `½`.

The only thing left to fully de-axiomatize a space-bounded `Step_S` is a
concrete rational transition `T` (the selector/carry/borrow gate algebra)
meeting the exact+Lipschitz hypotheses — everything around it is now
proved, axiom-free.
-/

import Ripple.BoundedUniversality.GPAC.RationalRounding
import Ripple.BoundedUniversality.GPAC.RobustnessAmplification

namespace Ripple.BoundedUniversality.GPAC.BoundedRobustStep

open Polynomial Ripple.BoundedUniversality.GPAC.RationalRounding Ripple.BoundedUniversality.GPAC.RobustnessAmplification

/-- The coordinatewise rational rounder as a self-map of `Fin N → ℝ`. -/
noncomputable def Cmap (R : ℚ[X]) (N : ℕ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun j => (R.map (algebraMap ℚ ℝ)).eval (x j)

/-- A point is on the symbol grid if every coordinate is a symbol in `{0,…,B}`. -/
def OnGrid (B N : ℕ) (g : Fin N → ℝ) : Prop :=
  ∀ j, ∃ i ∈ Finset.Icc 0 B, g j = (i : ℝ)

/-- **Bounded rational robust step.** A single rational rounder `R` and
radius `ρ` work uniformly: for any exact, Lipschitz transition `T`
between grid points, the rational step `C ∘ T ∘ C^[k]` is a `½`-contraction
of the `ρ`-ball of `c` toward `c'`. -/
theorem bounded_rational_robust_step (B N : ℕ) :
    ∃ (R : ℚ[X]) (ρ : ℝ), 0 < ρ ∧
      ∀ (T : (Fin N → ℝ) → (Fin N → ℝ)) (c c' : Fin N → ℝ) (L : ℝ) (k : ℕ),
        OnGrid B N c → OnGrid B N c' → 1 ≤ L → L ≤ 2^k → T c = c' →
        (∀ x, dist x c ≤ ρ → dist (T x) c' ≤ L * dist x c) →
        ∀ x, dist x c ≤ ρ →
          dist ((Cmap R N ∘ T ∘ (Cmap R N)^[k]) x) c' ≤ (1/2) * dist x c := by
  obtain ⟨R, ρ, hρ, hcw⟩ := coordinatewise_rounder_contracts B N
  refine ⟨R, ρ, hρ, fun T c c' L k hc hc' hL1 hLk hTc hTL => ?_⟩
  exact step_contracts (Cmap R N) T c c' ρ L k (le_of_lt hρ) hL1 hLk
    (fun y hy => hcw c hc y hy)
    (fun y hy => hcw c' hc' y hy)
    hTc hTL

/-- **End-to-end instance: the single-digit increment.** A genuine (if
minimal) register-machine step — increment one digit coordinate, no carry —
is exact between grid points and a sup-norm isometry (Lipschitz `L = 1`), so
it instantiates `bounded_rational_robust_step` with `k = 0`. This closes the
bounded-rational robust-step chain end-to-end with a concrete rational
transition: the machinery is not vacuous. -/
theorem robust_step_inc (B N : ℕ) (j0 : Fin N) (c : Fin N → ℝ)
    (hc : OnGrid B N c)
    (hc' : OnGrid B N (Function.update c j0 (c j0 + 1))) :
    ∃ (R : ℚ[X]) (ρ : ℝ), 0 < ρ ∧
      ∀ x, dist x c ≤ ρ →
        dist ((Cmap R N ∘ (fun y => Function.update y j0 (y j0 + 1))
                  ∘ (Cmap R N)^[0]) x)
             (Function.update c j0 (c j0 + 1)) ≤ (1/2) * dist x c := by
  obtain ⟨R, ρ, hρ, hmain⟩ := bounded_rational_robust_step B N
  refine ⟨R, ρ, hρ, ?_⟩
  have hLip : ∀ x, dist x c ≤ ρ →
      dist ((fun y => Function.update y j0 (y j0 + 1)) x)
           (Function.update c j0 (c j0 + 1)) ≤ 1 * dist x c := by
    intro x _
    rw [one_mul]
    rw [dist_pi_le_iff dist_nonneg]
    intro j
    dsimp only
    rcases eq_or_ne j j0 with h | h
    · rw [h, Function.update_self, Function.update_self, Real.dist_eq,
        show x j0 + 1 - (c j0 + 1) = x j0 - c j0 from by ring, ← Real.dist_eq]
      exact dist_le_pi_dist x c j0
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      exact dist_le_pi_dist x c j
  exact hmain (fun y => Function.update y j0 (y j0 + 1)) c
    (Function.update c j0 (c j0 + 1)) 1 0 hc hc' le_rfl (by norm_num) rfl hLip

end Ripple.BoundedUniversality.GPAC.BoundedRobustStep

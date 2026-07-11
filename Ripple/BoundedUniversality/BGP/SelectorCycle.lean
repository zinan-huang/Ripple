import Ripple.BoundedUniversality.BGP.CycleTracking
import Ripple.BoundedUniversality.BGP.LogisticReset
import Ripple.BoundedUniversality.BGP.SelectorPolynomial

/-!
Ripple.BoundedUniversality.BGP.SelectorCycle
------------------------
Per-phase Reach bounds for the clock-driven selector cycle.

Design source: `notes/gpt-clock-driven-selector-r2.md` §6 (sample → reset →
gate → write) and the existing BGP Reach primitive `moving_target_bound`
(`CycleTracking.lean`): `y' = g·(w - y)` with `|w - c| ≤ δ` gives
`|y(b) - c| ≤ exp(-∫g)·|y(a) - c| + δ`.

This file packages the sample / reset / write phases as instances of that
primitive.  The reset phase is the new ingredient: it produces the reset error
`δ_reset = (1/2)·exp(-∫g_reset)` consumed by the reset-error logistic bounds
(`LogisticReset.lean`).  The gate phase itself is the logistic block
(`SelectorBlock.lean`); composing the four phases into one Poincaré-cycle
contract is avenue (f6).
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set

/-- **Reach tracking (sample/write phases, f1/f5).** A coordinate `y` driven by
the Reach field toward a moving target `w` that stays within `δ` of a constant
`c` contracts toward `c`: `|y(b) - c| ≤ exp(-∫g)·|y(a) - c| + δ`.  This is the BGP
Reach primitive specialised to a phase window with gate envelope `g ≥ 0`. -/
theorem reach_track_bound
    (y w g : ℝ → ℝ) (c δ a b : ℝ) (hab : a ≤ b)
    (hg_cont : Continuous g) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hw_cont : Continuous w) (hδ : ∀ t ∈ Icc a b, |w t - c| ≤ δ)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (g t * (w t - y t)) t) :
    |y b - c| ≤ Real.exp (-(∫ t in a..b, g t)) * |y a - c| + δ :=
  moving_target_bound g w y a b hab hg_cont hg0 hw_cont c δ hδ hy

/-- **Reset phase (f2).** A weight `λ` driven by Reach toward `1/2`,
`λ' = g·(1/2 - λ)` with gate envelope `g ≥ 0`, contracts toward `1/2`:
`|λ(b) - 1/2| ≤ exp(-∫g)·|λ(a) - 1/2|`.  No additive term — the target is the
exact constant `1/2`. -/
theorem reset_to_half_bound
    (lam g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hg_cont : Continuous g) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hlam : ∀ t ∈ Icc a b, HasDerivAt lam (g t * (1 / 2 - lam t)) t) :
    |lam b - 1 / 2| ≤ Real.exp (-(∫ t in a..b, g t)) * |lam a - 1 / 2| := by
  have h := moving_target_bound g (fun _ => (1 / 2 : ℝ)) lam a b hab hg_cont hg0
    continuous_const (1 / 2) 0 (fun t _ => by norm_num)
    (fun t ht => by simpa using hlam t ht)
  simpa using h

/-- **Reset error bound (f2).** With the weight constrained to `[0,1]` at the
window start, the reset error is `δ_reset ≤ (1/2)·exp(-∫g_reset)`.  This is the
`δ` consumed by `logistic_true_bound_reset` / `logistic_false_bound_reset`. -/
theorem reset_to_half_bound_unit
    (lam g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hg_cont : Continuous g) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hlam : ∀ t ∈ Icc a b, HasDerivAt lam (g t * (1 / 2 - lam t)) t)
    (hunit : 0 ≤ lam a ∧ lam a ≤ 1) :
    |lam b - 1 / 2| ≤ Real.exp (-(∫ t in a..b, g t)) * (1 / 2) := by
  have h := reset_to_half_bound lam g a b hab hg_cont hg0 hlam
  have hle : |lam a - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [hunit.1, hunit.2]
  exact h.trans (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le)

open scoped BigOperators

/-- **(f6) per-step error composition.** One selector cycle
(hold → reset → gate → write) realises one discrete step: the written
configuration is within `mult·|x_start_i - E(c)_i| + ε_F` of `E(step c)_i`, with

  `ε_F = ε_mix + ε_write + mult·ε_hold`.

Triangle composition of the four phase bounds: `hwrite` (write Reach lands at the
mixture up to `ε_write`); `hmix` (gate block mixture within `ε_mix` of the true
branch — `ε_mix = card·R·C_reset·e^{-αΔG}` from `selector_mix_error_reset`, → 0);
`hdiag` (branch contract diagonal for the true view at `x_hold`); `hhold` (the
held copy drifts from `E(c)` by at most `ε_hold` beyond the live tube).

This is the clock-driven replacement for the static-selector per-step error: the
recurrence shape `mult·e_j + ε_F` is exactly `RobustStepContract.diagonal_bound`,
and `ε_F → 0` is what makes `hspread`/`hdisp` satisfiable. -/
theorem selector_cycle_step_error
    {V : Type} [Fintype V] {d B : ℕ}
    (branch : V → BranchData d B) (xstart xhold xwrite : Fin d → ℝ) (lamout : V → ℝ)
    (encC encStepC : Fin d → ℝ) (vstar : V) (i : Fin d)
    {εmix εwrite εhold mult : ℝ}
    (hmult : 0 ≤ mult)
    (hmix : |selectorF branch xhold lamout i
              - BranchData.evalBranch (branch vstar) xhold i| ≤ εmix)
    (hdiag : |BranchData.evalBranch (branch vstar) xhold i - encStepC i|
              ≤ mult * |xhold i - encC i|)
    (hhold : |xhold i - encC i| ≤ |xstart i - encC i| + εhold)
    (hwrite : |xwrite i - selectorF branch xhold lamout i| ≤ εwrite) :
    |xwrite i - encStepC i|
      ≤ mult * |xstart i - encC i| + (εmix + εwrite + mult * εhold) := by
  set S := selectorF branch xhold lamout i with hS
  set Avs := BranchData.evalBranch (branch vstar) xhold i with hAvs
  have hdiag' : |Avs - encStepC i| ≤ mult * |xstart i - encC i| + mult * εhold := by
    calc |Avs - encStepC i| ≤ mult * |xhold i - encC i| := hdiag
      _ ≤ mult * (|xstart i - encC i| + εhold) :=
          mul_le_mul_of_nonneg_left hhold hmult
      _ = mult * |xstart i - encC i| + mult * εhold := by ring
  calc |xwrite i - encStepC i|
      ≤ |xwrite i - S| + |S - encStepC i| := abs_sub_le _ _ _
    _ ≤ |xwrite i - S| + (|S - Avs| + |Avs - encStepC i|) := by
        gcongr; exact abs_sub_le _ _ _
    _ ≤ εwrite + (εmix + (mult * |xstart i - encC i| + mult * εhold)) :=
        add_le_add hwrite (add_le_add hmix hdiag')
    _ = mult * |xstart i - encC i| + (εmix + εwrite + mult * εhold) := by ring

end Ripple.BoundedUniversality.BGP

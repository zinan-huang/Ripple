/-
Ripple.BoundedUniversality.GPAC.RobustnessAmplification
-----------------------------------
The abstract robustness mechanism behind the bounded rational robust
step `Step_S = C ∘ T ∘ C^[k]` (RB3 design):

* `C` is a coordinatewise rounding contraction toward the encoding grid
  (each application halves the distance to the nearest configuration
  encoding) — provided concretely by `RationalRounding.finite_symbol_rounder`;
* `T` is the exact rational transition (`T (enc c) = enc (Δc)`), Lipschitz
  with constant `L` near the grid;
* pre-rounding `k ≥ log₂ L` times absorbs `T`'s expansion, and one final
  rounding gives a genuine `½`-contraction toward the next configuration.

This file proves that mechanism abstractly in any metric space: it reduces
the robustness of `Step` to (i) the rounder's contraction and (ii) a
Lipschitz bound on `T`.  Combined with the (formalized) rounder, this is
the analytic heart of the space-bounded robust step.
-/

import Mathlib

namespace Ripple.BoundedUniversality.GPAC.RobustnessAmplification

variable {X : Type*} [MetricSpace X]

/-- Iterating a contraction-toward-`c` map `k` times contracts the distance
to `c` by `(1/2)^k`, staying inside the `ρ`-ball throughout. -/
theorem iterate_contraction (R : X → X) (c : X) (ρ : ℝ)
    (hR : ∀ x, dist x c ≤ ρ → dist (R x) c ≤ (1/2) * dist x c) :
    ∀ (k : ℕ) (x : X), dist x c ≤ ρ → dist (R^[k] x) c ≤ (1/2)^k * dist x c := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    have hin : dist (R^[n] x) c ≤ (1/2)^n * dist x c := ih x hx
    have hpow : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hballn : dist (R^[n] x) c ≤ ρ :=
      le_trans hin (le_trans (mul_le_of_le_one_left dist_nonneg hpow) hx)
    calc dist (R (R^[n] x)) c
        ≤ (1/2) * dist (R^[n] x) c := hR _ hballn
      _ ≤ (1/2) * ((1/2)^n * dist x c) := by gcongr
      _ = (1/2)^(n+1) * dist x c := by ring

/-- **Robustness amplification.**  If `R` is a `½`-contraction toward both
`c` and `c'` on their `ρ`-balls, `T` is exact at `c` (`T c = c'`) and
`L`-Lipschitz from `c` to `c'` on the `ρ`-ball, and `k` pre-roundings
satisfy `L ≤ 2^k`, then `Step = R ∘ T ∘ R^[k]` is a genuine `½`-contraction
of the `ρ`-ball of `c` toward `c'`:
`dist (Step x) c' ≤ ½ · dist x c`. -/
theorem step_contracts (R T : X → X) (c c' : X) (ρ : ℝ) (L : ℝ) (k : ℕ)
    (hρ : 0 ≤ ρ) (hL1 : 1 ≤ L) (hLk : L ≤ 2^k)
    (hRc  : ∀ x, dist x c  ≤ ρ → dist (R x) c  ≤ (1/2) * dist x c)
    (hRc' : ∀ x, dist x c' ≤ ρ → dist (R x) c' ≤ (1/2) * dist x c')
    (hTc : T c = c')
    (hTL : ∀ x, dist x c ≤ ρ → dist (T x) c' ≤ L * dist x c) :
    ∀ x, dist x c ≤ ρ →
      dist ((R ∘ T ∘ R^[k]) x) c' ≤ (1/2) * dist x c := by
  intro x hx
  -- after k pre-roundings, still within ρ of c, distance ≤ (1/2)^k · dist x c
  have hpre : dist (R^[k] x) c ≤ (1/2)^k * dist x c :=
    iterate_contraction R c ρ hRc k x hx
  have hpowk : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpre_ρ : dist (R^[k] x) c ≤ ρ :=
    le_trans hpre (le_trans (mul_le_of_le_one_left dist_nonneg hpowk) hx)
  -- T maps it to within ρ of c'
  have hkey : (2 : ℝ)^k * (1/2)^k = 1 := by
    rw [← mul_pow]; norm_num
  have hTbound : dist (T (R^[k] x)) c' ≤ L * ((1/2)^k * dist x c) :=
    le_trans (hTL _ hpre_ρ) (by gcongr)
  have hLpow : L * (1/2)^k ≤ 1 := by
    have : L * (1/2)^k ≤ 2^k * (1/2)^k := by gcongr
    rwa [hkey] at this
  have hTc'_ρ : dist (T (R^[k] x)) c' ≤ ρ := by
    refine le_trans hTbound (le_trans ?_ hx)
    calc L * ((1/2)^k * dist x c)
        = (L * (1/2)^k) * dist x c := by ring
      _ ≤ 1 * dist x c := by gcongr
      _ = dist x c := one_mul _
  -- final rounding toward c' contracts by 1/2
  have hfin : dist (R (T (R^[k] x))) c' ≤ (1/2) * dist (T (R^[k] x)) c' :=
    hRc' _ hTc'_ρ
  -- assemble: (1/2) · dist (T ...) c' ≤ (1/2) · (L (1/2)^k dist x c) ≤ (1/2) dist x c
  have : dist ((R ∘ T ∘ R^[k]) x) c' ≤ (1/2) * (L * ((1/2)^k * dist x c)) := by
    simp only [Function.comp_apply]
    exact le_trans hfin (by gcongr)
  refine le_trans this ?_
  calc (1/2) * (L * ((1/2)^k * dist x c))
      = (1/2) * ((L * (1/2)^k) * dist x c) := by ring
    _ ≤ (1/2) * (1 * dist x c) := by gcongr
    _ = (1/2) * dist x c := by rw [one_mul]

end Ripple.BoundedUniversality.GPAC.RobustnessAmplification

/-
Ripple.BoundedUniversality.BGP.ContractFlagLowFromTrapping
--------------------------------------
Discharges the `hflag_low_below` hypothesis of `contract_flag_only_headline_MU`:

    ∀ w sol j, j < j₀ → ∀ t ∈ sched.zActiveWindow j,
        I.Hval (sol.z t) ≤ I.eta

from the [0, 1/4]-trapping invariant on the flag coordinate.

**Discharge path:**
1. `contract_z_Icc_trapping` with `[lo, hi] = [0, 1/4]` gives
   `sol.z t flagCoord ∈ [0, 1/4]` provided:
   - `z(0) flagCoord ∈ [0, 1/4]` (initial data: flag starts at 0 for non-halt)
   - `w(τ) flagCoord ∈ [0, 1/4]` for all τ in the interval (field at flag
     maps near 0 for non-halting configs)
2. From `z flagCoord ∈ [0, 1/4]`:
   - `z flagCoord ∈ [0, 1]` (subset)
   - `|z flagCoord - 0| = z flagCoord ≤ 1/4`
3. `I.on_flag_zero` gives `I.Hval(sol.z t) ≤ I.eta`.

No sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractFlagTrapping
import Ripple.BoundedUniversality.BGP.ContractMain

namespace Ripple.BoundedUniversality.BGP

open Real Set
open Ripple.BoundedUniversality.Core

noncomputable section

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-! ## From [0, 1/4]-membership to on_flag_zero inputs -/

/-- If `x flagCoord ∈ [0, 1/4]`, then `x flagCoord ∈ [0, 1]`. -/
private theorem flag_in_unit_of_in_quarter {x : Fin d → ℝ} {flagCoord : Fin d}
    (h : x flagCoord ∈ Icc (0 : ℝ) (1 / 4)) :
    x flagCoord ∈ Icc (0 : ℝ) 1 :=
  ⟨h.1, le_trans h.2 (by norm_num)⟩

/-- If `x flagCoord ∈ [0, 1/4]`, then `|x flagCoord - 0| ≤ 1/4`. -/
private theorem abs_sub_zero_le_quarter_of_in_quarter {x : Fin d → ℝ} {flagCoord : Fin d}
    (h : x flagCoord ∈ Icc (0 : ℝ) (1 / 4)) :
    |x flagCoord - 0| ≤ 1 / 4 := by
  simp only [sub_zero]
  rw [abs_of_nonneg h.1]
  exact h.2

/-! ## Generic flag-low-from-trapping theorem -/

/-- **Flag indicator low from [0, 1/4]-trapping.**  If the z-coordinate at
`flagCoord` is trapped in `[0, 1/4]` (by `contract_z_Icc_trapping`), then
`I.Hval(sol.z t) ≤ I.eta` via `I.on_flag_zero`.

This theorem takes the trapping conclusion directly — the caller is responsible
for supplying it via `contract_z_Icc_trapping` with the appropriate initial
data and moving-target bounds.  The purpose of this lemma is to convert the
coordinate-level bound into the indicator-level bound consumed by
`contract_flag_only_headline`. -/
theorem flag_low_of_z_in_quarter
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    {x : Fin d → ℝ}
    (hx : x flagCoord ∈ Icc (0 : ℝ) (1 / 4)) :
    I.Hval x ≤ I.eta :=
  I.on_flag_zero x
    (flag_in_unit_of_in_quarter hx)
    (abs_sub_zero_le_quarter_of_in_quarter hx)

/-- **Flag-low discharge for z-active windows via [0, 1/4]-trapping.**

Given:
* `hz_init`: z(0) flagCoord ∈ [0, 1/4] (initial data)
* `hw_quarter`: w(τ) flagCoord ∈ [0, 1/4] for all τ ∈ [0, t] (field maps near 0)
* The ODE regularity hypotheses needed by `contract_z_Icc_trapping`

Produces `I.Hval(sol.z t) ≤ I.eta` for any `t ≥ 0` in the domain.

The proof applies `contract_z_Icc_trapping` on `[0, t]` with `lo = 0, hi = 1/4`,
then feeds the resulting membership to `flag_low_of_z_in_quarter`. -/
theorem flag_low_below_from_trapping
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    {t : ℝ} (ht : 0 ≤ t)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Icc 0 t, 0 ≤ sol.α τ)
    (hdom : Icc 0 t ⊆ sched.domain)
    (hz_init : sol.z 0 flagCoord ∈ Icc (0 : ℝ) (1 / 4))
    (hw_quarter : ∀ τ ∈ Icc 0 t, sol.w τ flagCoord ∈ Icc (0 : ℝ) (1 / 4)) :
    I.Hval (sol.z t) ≤ I.eta := by
  have htrapped : sol.z t flagCoord ∈ Icc (0 : ℝ) (1 / 4) :=
    contract_z_Icc_trapping sol flagCoord 0 (1 / 4) 0 t ht hk_cont hA hαnn hdom hz_init
      hw_quarter
  exact flag_low_of_z_in_quarter flagCoord I htrapped

/-! ## Full `hflag_low_below` producer

This is the version that matches the shape consumed by `contract_flag_only_headline`:
    ∀ w sol j, j < j₀ → ∀ t ∈ sched.zActiveWindow j, I.Hval(sol.z t) ≤ I.eta

It wraps `flag_low_below_from_trapping` by:
1. Taking the z-active-window membership `t ∈ sched.zActiveWindow j`
2. Deriving `0 ≤ t` from the window-to-domain inclusion
3. Supplying the trapping on `[0, t]`
-/

/-- **Full `hflag_low_below` discharge from [0, 1/4]-trapping.**

Produces the exact hypothesis shape consumed by `contract_flag_only_headline`.
The caller provides:
* `hwindow_nonneg`: every z-active-window time point is ≥ 0
* `hwindow_dom`: every z-active-window interval is in the domain
* `hz_init`: z(0) flagCoord ∈ [0, 1/4]
* `hw_quarter_all`: w(τ) flagCoord ∈ [0, 1/4] for all τ ≥ 0 in the domain
* ODE regularity (continuous zRate, A ≥ 0, α ≥ 0 on nonneg reals) -/
theorem contract_flag_low_below_from_quarter_trapping
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    (j₀ : ℕ)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A)
    (hαnn_all : ∀ τ : ℝ, 0 ≤ τ → 0 ≤ sol.α τ)
    (hdom_all : ∀ τ : ℝ, 0 ≤ τ → τ ∈ sched.domain)
    (hwindow_nonneg : ∀ j t, t ∈ sched.zActiveWindow j → 0 ≤ t)
    (hz_init : sol.z 0 flagCoord ∈ Icc (0 : ℝ) (1 / 4))
    (hw_quarter_all : ∀ τ : ℝ, 0 ≤ τ → τ ∈ sched.domain →
        sol.w τ flagCoord ∈ Icc (0 : ℝ) (1 / 4)) :
    ∀ j, j < j₀ → ∀ t ∈ sched.zActiveWindow j,
      I.Hval (sol.z t) ≤ I.eta := by
  intro j _hj t ht
  have ht_nn : 0 ≤ t := hwindow_nonneg j t ht
  exact flag_low_below_from_trapping sol flagCoord I ht_nn hk_cont hA
    (fun τ hτ => hαnn_all τ hτ.1)
    (fun τ hτ => hdom_all τ hτ.1)
    hz_init
    (fun τ hτ => hw_quarter_all τ hτ.1 (hdom_all τ hτ.1))

/-! ## Variant: the j₀-free form (indicator low for ALL j) -/

/-- **Flag indicator low for ALL cycles.**  This is the stronger version where
the flag is low at every z-active window, not just for `j < j₀`.  Useful when
the upstream assembly chooses `j₀` from the flag-margin-bound theorem and needs
the flag-low bound on the complementary range.

The hypotheses are identical to `contract_flag_low_below_from_quarter_trapping`
except there is no `j₀` parameter and no `j < j₀` guard. -/
theorem contract_flag_low_all_from_quarter_trapping
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A)
    (hαnn_all : ∀ τ : ℝ, 0 ≤ τ → 0 ≤ sol.α τ)
    (hdom_all : ∀ τ : ℝ, 0 ≤ τ → τ ∈ sched.domain)
    (hwindow_nonneg : ∀ j t, t ∈ sched.zActiveWindow j → 0 ≤ t)
    (hz_init : sol.z 0 flagCoord ∈ Icc (0 : ℝ) (1 / 4))
    (hw_quarter_all : ∀ τ : ℝ, 0 ≤ τ → τ ∈ sched.domain →
        sol.w τ flagCoord ∈ Icc (0 : ℝ) (1 / 4)) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      I.Hval (sol.z t) ≤ I.eta := by
  intro j t ht
  have ht_nn : 0 ≤ t := hwindow_nonneg j t ht
  exact flag_low_below_from_trapping sol flagCoord I ht_nn hk_cont hA
    (fun τ hτ => hαnn_all τ hτ.1)
    (fun τ hτ => hdom_all τ hτ.1)
    hz_init
    (fun τ hτ => hw_quarter_all τ hτ.1 (hdom_all τ hτ.1))

#print axioms flag_low_of_z_in_quarter
#print axioms flag_low_below_from_trapping
#print axioms contract_flag_low_below_from_quarter_trapping
#print axioms contract_flag_low_all_from_quarter_trapping

end

end Ripple.BoundedUniversality.BGP

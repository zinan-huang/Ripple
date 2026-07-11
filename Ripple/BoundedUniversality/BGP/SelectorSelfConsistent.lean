import Ripple.BoundedUniversality.BGP.SelectorExposureTube

/-!
Ripple.BoundedUniversality.BGP.SelectorSelfConsistent
---------------------------------
The NON-CIRCULAR self-consistent induction core for the faithful local-view tube (ChatGPT Pro design
de76a096).  The exposure-tube `expTube_uniform` takes the non-expansiveness step UNCONDITIONALLY, but
in the concrete selector the per-cycle error step `E_{j+1} ≤ E_j + Ω_j` is only available WHEN the tube
holds at cycle `j` (the gate selects the correct symbolic op only when the local view is already within
margin, i.e. `E_j ≤ ρ`).  This file provides the CONDITIONAL uniform bound: a step hypothesis gated on
`E_j ≤ ρ` still yields `E_j ≤ ρ` for all `j`, via the self-consistent induction

  `I_j : E_j ≤ ρ  ⟹  gate-correct_j  ⟹  E_{j+1} ≤ E_j + Ω_j  ⟹  I_{j+1}`.

This is non-circular: the step at `j` consumes only `I_j` and produces `I_{j+1}`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Finset

/-- **Self-consistent telescoping** with a CONDITIONAL step.  If `E_{j+1} ≤ E_j + Ω_j` holds whenever
`E_j ≤ ρ`, and the running reserve `E_0 + Σ_{ℓ<j} Ω_ℓ ≤ ρ`, then `E_j ≤ E_0 + Σ_{ℓ<j} Ω_ℓ` for all `j`.
The conditional step is discharged inside the induction (`E_n ≤ E_0 + Σ ≤ ρ`), so no unconditional
non-expansiveness is needed — exactly the concrete selector's situation. -/
theorem expTube_telescope_conditional {E Ω : ℕ → ℝ} {ρ : ℝ}
    (hstep : ∀ j, E j ≤ ρ → E (j + 1) ≤ E j + Ω j)
    (hres : ∀ j, E 0 + ∑ ℓ ∈ range j, Ω ℓ ≤ ρ) :
    ∀ j, E j ≤ E 0 + ∑ ℓ ∈ range j, Ω ℓ := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
      have hEn_rho : E n ≤ ρ := le_trans ih (hres n)
      have hstn : E (n + 1) ≤ E n + Ω n := hstep n hEn_rho
      rw [Finset.sum_range_succ]
      linarith [ih]

/-- **Self-consistent uniform tube.**  A conditional non-expansiveness step (`E_j ≤ ρ → E_{j+1} ≤ E_j +
Ω_j`) plus a finite reserve (`E_0 + Σ Ω ≤ ρ`) gives `E_j ≤ ρ` for every `j`.  This is the non-circular
induction that the concrete M_U instantiation runs: the tube at `j` enables gate-correctness at `j`,
which produces the tube at `j+1`. -/
theorem expTube_uniform_conditional {E Ω : ℕ → ℝ} {ρ : ℝ}
    (hstep : ∀ j, E j ≤ ρ → E (j + 1) ≤ E j + Ω j)
    (hres : ∀ j, E 0 + ∑ ℓ ∈ range j, Ω ℓ ≤ ρ) :
    ∀ j, E j ≤ ρ :=
  fun j => le_trans (expTube_telescope_conditional hstep hres j) (hres j)

/-- **Self-consistent local-view tube, abstract.**  Combines the conditional self-consistent induction
with the geometric reserve and the exposure-weighted read: a CONDITIONAL per-cycle error step (the
exposure-weighted error stays non-expansive WHEN the tube holds, `E_j ≤ ρ`), with a geometrically-
bounded weighted forcing, yields the top+second read accuracy `B^2·e_j ≤ ρ` for EVERY cycle.  This is
the structural backbone of the M_U instantiation: the deep selector facts enter only through the
conditional step `hstep`. -/
theorem selfConsistent_localview_tube
    (B : ℝ) (hB : 1 ≤ B) (H : ℕ → ℤ) (e Ω : ℕ → ℝ) {C r ρ : ℝ}
    (hHnn : ∀ j, 0 ≤ H j) (hej : ∀ j, 0 ≤ e j)
    (hstep : ∀ j, expWeight B H e j ≤ ρ → expWeight B H e (j + 1) ≤ expWeight B H e j + Ω j)
    (hΩgeo : ∀ ℓ, Ω ℓ ≤ C * r ^ ℓ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hρ : expWeight B H e 0 + C / (1 - r) ≤ ρ) :
    ∀ j, B ^ (2 : ℤ) * e j ≤ ρ := by
  have hres : ∀ j, expWeight B H e 0 + ∑ ℓ ∈ range j, Ω ℓ ≤ ρ := by
    intro j
    exact le_trans (expTube_reserve_geometric (E := expWeight B H e) hΩgeo hC hr0 hr1 j) hρ
  have hEtube : ∀ j, expWeight B H e j ≤ ρ := expTube_uniform_conditional hstep hres
  exact fun j => localview_read_of_expTube B hB H e j (hHnn j) (hej j) (hEtube j)

end Ripple.BoundedUniversality.BGP

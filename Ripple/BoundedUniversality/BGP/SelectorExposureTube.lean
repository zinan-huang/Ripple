import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star

/-!
Ripple.BoundedUniversality.BGP.SelectorExposureTube
-------------------------------
The FAITHFUL local-view tube invariant for the clock-driven selector — the EXPOSURE-WEIGHTED norm,
the §3.3-correct replacement for the (non-inductive) naive `lv_j ≤ ρ` and the (false) divergent
depth-budget.

The §3.3 audit (3 engines + source) established: the stack branch maps push `X' = (c+X)/B` (slope 1/B,
height +1), pop `X' = B·X − c` (slope B, height −1), hold (slope 1) are NOT non-expansive in the raw
absolute error (a pop multiplies it by B), but ARE non-expansive in the EXPOSURE-WEIGHTED norm

  `E_j := B^(H_j + 2) · e_j`        (H_j = stack height, e_j = |ũ_j − X_j| the stack-code error).

Push burial (÷B with H+1) and pop exposure (×B with H−1) INVERSE-CANCEL against the height factor:
the exposure cost of an error injected at cycle ℓ is `B^(H_ℓ)` (the symbols above it), NOT `B^(j−ℓ)`
(the future time gap, which the divergent depth-budget wrongly used).  With double-exponentially small
write/gate defects `ξ_ℓ`, the weighted reserve `Σ B^(H+2)·ξ` is finite, so `E_j ≤ ρ` all-cycle ⟹ the
top+second reads stay inside the gate margin all-cycle (`B^2·e_j ≤ E_j ≤ ρ`).  This is the genuine
local-view tube, locally faithful per fixed input.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Finset

/-- Exposure-weighted stack-code error: `E_j = B^(H_j + 2) · e_j`. -/
def expWeight (B : ℝ) (H : ℕ → ℤ) (e : ℕ → ℝ) (j : ℕ) : ℝ :=
  B ^ (H j + 2) * e j

/-- **Exposure-weighted NON-EXPANSIVENESS** (burial/exposure inverse-cancellation).  From the per-cycle
branch recurrence `e(j+1) ≤ B^(H_j − H_{j+1}) · e_j + ξ_j` (the branch slope is `B^(height decrease)`:
pop `+1`, push `−1`, hold `0`), the exposure-weighted error only accumulates the weighted forcing:

  `E_{j+1} ≤ E_j + B^(H_{j+1}+2) · ξ_j`.

The `B`-amplification of a pop is exactly absorbed by the height-factor drop — it is NOT multiplied by
`B` forever after, unlike the divergent depth-budget. -/
theorem expWeight_nonexpansive (B : ℝ) (hB : 0 < B) (H : ℕ → ℤ) (e ξ : ℕ → ℝ) (j : ℕ)
    (hrec : e (j + 1) ≤ B ^ (H j - H (j + 1)) * e j + ξ j) :
    expWeight B H e (j + 1) ≤ expWeight B H e j + B ^ (H (j + 1) + 2) * ξ j := by
  unfold expWeight
  have hBne : B ≠ 0 := ne_of_gt hB
  have hpos : (0 : ℝ) < B ^ (H (j + 1) + 2) := zpow_pos hB _
  calc B ^ (H (j + 1) + 2) * e (j + 1)
      ≤ B ^ (H (j + 1) + 2) * (B ^ (H j - H (j + 1)) * e j + ξ j) :=
        mul_le_mul_of_nonneg_left hrec hpos.le
    _ = B ^ (H (j + 1) + 2) * B ^ (H j - H (j + 1)) * e j + B ^ (H (j + 1) + 2) * ξ j := by ring
    _ = B ^ (H j + 2) * e j + B ^ (H (j + 1) + 2) * ξ j := by
        rw [← zpow_add₀ hBne]; ring_nf

/-- **Telescoping bound** for any non-expansive sequence: `E_j ≤ E_0 + Σ_{ℓ<j} Ω_ℓ`. -/
theorem expTube_telescope {E Ω : ℕ → ℝ} (hstep : ∀ j, E (j + 1) ≤ E j + Ω j) :
    ∀ j, E j ≤ E 0 + ∑ ℓ ∈ range j, Ω ℓ := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc E (n + 1) ≤ E n + Ω n := hstep n
        _ ≤ (E 0 + ∑ ℓ ∈ range n, Ω ℓ) + Ω n := by linarith [ih]
        _ = E 0 + (∑ ℓ ∈ range n, Ω ℓ + Ω n) := by ring

/-- **Uniform exposure-weighted tube.**  Non-expansiveness + a finite reserve
`E_0 + Σ_{ℓ<j} Ω_ℓ ≤ ρ` ⟹ `E_j ≤ ρ` for every `j`.  (The reserve is finite because the weighted
forcing `Ω_ℓ = B^(H_{ℓ+1}+2)·ξ_ℓ` is super-geometrically summable from double-exp defects.) -/
theorem expTube_uniform {E Ω : ℕ → ℝ} {ρ : ℝ}
    (hstep : ∀ j, E (j + 1) ≤ E j + Ω j)
    (hres : ∀ j, E 0 + ∑ ℓ ∈ range j, Ω ℓ ≤ ρ) :
    ∀ j, E j ≤ ρ :=
  fun j => le_trans (expTube_telescope hstep j) (hres j)

/-- **Local-view read stays in margin.**  `E_j ≤ ρ` (with `B ≥ 1`, `H_j ≥ 0`) gives `B^2·e_j ≤ ρ`,
the top+second-symbol read accuracy the gate needs — uniformly in `j`, independent of stack depth. -/
theorem localview_read_of_expTube (B : ℝ) (hB : 1 ≤ B) (H : ℕ → ℤ) (e : ℕ → ℝ) {ρ : ℝ} (j : ℕ)
    (hH : 0 ≤ H j) (hej : 0 ≤ e j) (hE : expWeight B H e j ≤ ρ) :
    B ^ (2 : ℤ) * e j ≤ ρ := by
  unfold expWeight at hE
  have hle : B ^ (2 : ℤ) ≤ B ^ (H j + 2) := by
    apply zpow_le_zpow_right₀ hB; linarith
  calc B ^ (2 : ℤ) * e j ≤ B ^ (H j + 2) * e j := mul_le_mul_of_nonneg_right hle hej
    _ ≤ ρ := hE

/-- **Faithful local-view tube, assembled.**  Given the branch recurrence each cycle, the matching
height changes, nonneg errors, and a finite weighted reserve, the stack-top+second read stays within
`ρ` of the true symbol for EVERY cycle — the §3.3-faithful uniform local-view invariant (per fixed
input). -/
theorem localview_tube_all (B : ℝ) (hB : 1 ≤ B) (H : ℕ → ℤ) (e ξ : ℕ → ℝ) {ρ : ℝ}
    (hHnn : ∀ j, 0 ≤ H j) (hej : ∀ j, 0 ≤ e j)
    (hrec : ∀ j, e (j + 1) ≤ B ^ (H j - H (j + 1)) * e j + ξ j)
    (hres : ∀ j, expWeight B H e 0 + ∑ ℓ ∈ range j, B ^ (H (ℓ + 1) + 2) * ξ ℓ ≤ ρ) :
    ∀ j, B ^ (2 : ℤ) * e j ≤ ρ := by
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  have hstep : ∀ j, expWeight B H e (j + 1) ≤ expWeight B H e j + B ^ (H (j + 1) + 2) * ξ j :=
    fun j => expWeight_nonexpansive B hB0 H e ξ j (hrec j)
  have hEtube : ∀ j, expWeight B H e j ≤ ρ := expTube_uniform hstep hres
  exact fun j => localview_read_of_expTube B hB H e j (hHnn j) (hej j) (hEtube j)

/-- **Finite reserve from a geometrically-bounded weighted forcing.**  If the weighted forcing
`Ω_ℓ ≤ C·r^ℓ` with `0 ≤ r < 1`, then the running reserve `E_0 + Σ_{ℓ<j} Ω_ℓ` is uniformly bounded by
`E_0 + C/(1−r)`.  Double-exponential write/gate defects give a super-geometric `Ω`, a fortiori this
geometric bound — so the reserve is finite for each fixed input. -/
theorem expTube_reserve_geometric {E Ω : ℕ → ℝ} {C r : ℝ}
    (hΩ : ∀ ℓ, Ω ℓ ≤ C * r ^ ℓ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ j, E 0 + ∑ ℓ ∈ range j, Ω ℓ ≤ E 0 + C / (1 - r) := by
  intro j
  have hgeom : ∑ ℓ ∈ range j, r ^ ℓ ≤ (1 - r)⁻¹ := by
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have hne : (1 - r) ≠ 0 := ne_of_gt h1r
    have hrj : (0 : ℝ) ≤ r ^ j := pow_nonneg hr0 j
    have hmul := geom_sum_mul r j  -- (∑ i in range j, r^i) * (r - 1) = r^j - 1
    have hSr : (∑ ℓ ∈ range j, r ^ ℓ) * (1 - r) ≤ 1 := by
      have hrel : (∑ ℓ ∈ range j, r ^ ℓ) * (1 - r)
          = -((∑ ℓ ∈ range j, r ^ ℓ) * (r - 1)) := by ring
      rw [hrel, hmul]; linarith
    calc ∑ ℓ ∈ range j, r ^ ℓ
        = (∑ ℓ ∈ range j, r ^ ℓ) * (1 - r) * (1 - r)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ ≤ 1 * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right hSr (by positivity)
      _ = (1 - r)⁻¹ := one_mul _
  have hsum : ∑ ℓ ∈ range j, Ω ℓ ≤ C / (1 - r) := by
    calc ∑ ℓ ∈ range j, Ω ℓ ≤ ∑ ℓ ∈ range j, C * r ^ ℓ := Finset.sum_le_sum (fun ℓ _ => hΩ ℓ)
      _ = C * ∑ ℓ ∈ range j, r ^ ℓ := by rw [Finset.mul_sum]
      _ ≤ C * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hC
      _ = C / (1 - r) := by rw [div_eq_mul_inv]
  linarith

/-- **Faithful local-view tube, per fixed input, FULLY PROVEN.**  Branch recurrence + height changes +
nonneg errors + a GEOMETRICALLY-bounded weighted forcing `B^(H_{ℓ+1}+2)·ξ_ℓ ≤ C·r^ℓ` (`r < 1`, met by
double-exp defects) ⟹ the top+second stack reads stay within `ρ := E_0 + C/(1−r)` of the true symbol
for EVERY cycle.  No asserted reserve — the reserve is discharged from the geometric decay.  This is
the genuine §3.3-faithful uniform local-view tube for a fixed input (locally faithful). -/
theorem localview_tube_all_of_geometric (B : ℝ) (hB : 1 ≤ B) (H : ℕ → ℤ) (e ξ : ℕ → ℝ)
    {C r : ℝ} (hHnn : ∀ j, 0 ≤ H j) (hej : ∀ j, 0 ≤ e j)
    (hrec : ∀ j, e (j + 1) ≤ B ^ (H j - H (j + 1)) * e j + ξ j)
    (hgeo : ∀ ℓ, B ^ (H (ℓ + 1) + 2) * ξ ℓ ≤ C * r ^ ℓ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ j, B ^ (2 : ℤ) * e j ≤ expWeight B H e 0 + C / (1 - r) := by
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  refine localview_tube_all B hB H e ξ hHnn hej hrec ?_
  exact expTube_reserve_geometric (E := expWeight B H e) hgeo hC hr0 hr1

end Ripple.BoundedUniversality.BGP

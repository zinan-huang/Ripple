/-
Ripple.BoundedUniversality.BGP.DynChiLeak
---------------------
The dynChi leak-rate collapse — the analytic core of the `InactiveLeakage`
`hleak` hypothesis.  Contrary to the worry that this needs an irreducible
integral, the `InactiveLeakage` API asks for a sup-rate × window-length bound
`K · Dgap · Δ ≤ χ_j · D`, which closes from PURE ALGEBRA once the window geometry
is exposed: pointwise off-phase gate suppression `K ≤ A·exp(−λ·a)` + the
window-length budget `gapFactor · Δ ≤ 1/λ`.

Design + proof cross-checked with the repo-connected channel (pbook R-DYNCHI);
verified here by build.
-/

import Ripple.BoundedUniversality.BGP.DynamicGate

namespace Ripple.BoundedUniversality.BGP

open Real

noncomputable section

namespace DynChiLeak

/-- Off-phase leak decay exponent `λ = cμ·2^(−L) − cα`. -/
def leakLambda (cμ cα : ℝ) (L : ℕ) : ℝ := cμ * (1 / 2 : ℝ) ^ L - cα

/-- **Pure-algebra dynChi leak close** for the MVT-style `InactiveLeakage` API:
pointwise gate bound `K ≤ A·exp(−λ·a)` + gap bound `Dgap ≤ gapFactor·D` + window
budget `gapFactor·Δ ≤ 1/λ` ⟹ `K·Dgap·Δ ≤ (A·exp(−λ·a)/λ)·D`. -/
lemma hleak_of_pointwise_dynChi_budget
    {A lam a K Dgap D gapFactor Δ : ℝ}
    (hlam : 0 < lam)
    (hA : 0 ≤ A)
    (hK_nonneg : 0 ≤ K)
    (hK : K ≤ A * Real.exp (-(lam * a)))
    (hD : 0 ≤ D)
    (hDgap0 : 0 ≤ Dgap)
    (hDgap : Dgap ≤ gapFactor * D)
    (hgap : 0 ≤ gapFactor)
    (hΔ : 0 ≤ Δ)
    (hbudget : gapFactor * Δ ≤ 1 / lam) :
    K * Dgap * Δ ≤ (A * Real.exp (-(lam * a)) / lam) * D := by
  have hE : 0 ≤ A * Real.exp (-(lam * a)) := mul_nonneg hA (Real.exp_pos _).le
  set E := A * Real.exp (-(lam * a)) with hEdef
  calc
    K * Dgap * Δ
        ≤ E * Dgap * Δ := by nlinarith [mul_nonneg hDgap0 hΔ, hK, hE]
    _ ≤ E * (gapFactor * D) * Δ := by nlinarith [hDgap, mul_nonneg hE hΔ]
    _ = E * D * (gapFactor * Δ) := by ring
    _ ≤ E * D * (1 / lam) := by nlinarith [hbudget, mul_nonneg hE hD]
    _ = (E / lam) * D := by field_simp

/-- The same close, rewritten against `dynChi` at a `2πn`-cycle start. -/
lemma hleak_of_pointwise_dynChi_cycle
    {A cμ cα K Dgap D gapFactor Δ : ℝ} {L n : ℕ}
    (hlam : 0 < leakLambda cμ cα L)
    (hA : 0 ≤ A)
    (hK_nonneg : 0 ≤ K)
    (hK : K ≤ A * Real.exp (-(leakLambda cμ cα L * (2 * Real.pi * (n : ℝ)))))
    (hD : 0 ≤ D)
    (hDgap0 : 0 ≤ Dgap)
    (hDgap : Dgap ≤ gapFactor * D)
    (hgap : 0 ≤ gapFactor)
    (hΔ : 0 ≤ Δ)
    (hbudget : gapFactor * Δ ≤ 1 / leakLambda cμ cα L) :
    K * Dgap * Δ ≤ dynChi A L cμ cα n * D := by
  have h := hleak_of_pointwise_dynChi_budget
    (A := A) (lam := leakLambda cμ cα L) (a := 2 * Real.pi * (n : ℝ))
    (K := K) (Dgap := Dgap) (D := D) (gapFactor := gapFactor) (Δ := Δ)
    hlam hA hK_nonneg hK hD hDgap0 hDgap hgap hΔ hbudget
  have hdc : dynChi A L cμ cα n =
      A * Real.exp (-(leakLambda cμ cα L * (2 * Real.pi * (n : ℝ)))) / leakLambda cμ cα L := by
    unfold dynChi leakLambda
    ring_nf
  rw [hdc]
  exact h

end DynChiLeak

end

end Ripple.BoundedUniversality.BGP

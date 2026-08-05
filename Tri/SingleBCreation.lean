/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBLevel
import Tri.Lemma14Leaf

/-!
# The Single-B creation imbalance is a fair walk

`Tri/SingleBLevel.lean` reduced Single-B to the corrected coordinates
`LX = x + CY`, `LY = y + CX`, which move only at resolution events. Recovering
the PHYSICAL gap from the corrected one leaves exactly the signed creation
imbalance `CX − CY`, and that is the last genuinely new piece.

This file establishes that it is a **fair** walk, and supplies the compensated
potential that turns fairness into concentration.

## Why it is fair, with no conditioning

`SingleComp.weight` gives `xyToX` and `xyToY` the SAME weight `x*y`. The two
creation masses are therefore equal at every state — not merely equal after
conditioning on a creation, and not merely equal in the interior. At states
with `x*y = 0` both masses are zero and the statement is still true, which is
why it can be stated as an unconditional equality rather than as a `1/2`
conditional law needing a nonzero denominator.

That equality is the whole probabilistic input. Everything below is algebra.

## The compensated potential

```text
G(q) = exp (λ·CX − λ·CY − (λ²/2)·(CX + CY))
```

Inert events (`xx`, `yy`, `bb`) and resolutions (`xb`, `yb`) leave both
creation ledgers fixed, so they leave `G` fixed. The two creations move
`CX − CY` by `±1` and `CX + CY` by `+1`, so they multiply `G` by
`exp(±λ − λ²/2)`. With equal masses `p` on the two, the one-step expectation is

```text
(1 − 2p)·G + p·G·exp(λ − λ²/2) + p·G·exp(−λ − λ²/2) ≤ G
```

which reduces to `(exp λ + exp(−λ))/2 ≤ exp(λ²/2)` — the fair Rademacher MGF,
and an instance of `centered_bernoulli_mgf_le` already proved for Lemma 14.

Note the compensator carries `λ²/2`, not Lemma 14's `λ²/8`. The `1/8` is the
Hoeffding constant for a bounded CENTRED increment of range 1; here the
increment is `±1`, range 2, and `(2)²/8 = 1/2`.
-/

namespace Tri

open scoped ENNReal

/-- **The fair-coin input.**  The two creation orientations carry exactly the
same mass at every state, because `SingleComp.weight` assigns both the weight
`x*y`.  No conditioning and no nonzero-denominator side condition. -/
theorem singleCompPMF_creation_masses_eq
    (x y b : ℕ) (h : 2 ≤ x + y + b) :
    singleCompPMF x y b h SingleComp.xyToX
      = singleCompPMF x y b h SingleComp.xyToY := rfl

/-- The two creation weights agree as naturals, which is the statement the
`ledger` arithmetic uses. -/
theorem singleComp_creation_weight_eq (x y b : ℕ) :
    SingleComp.weight x y b SingleComp.xyToX
      = SingleComp.weight x y b SingleComp.xyToY := rfl

/-- **The fair Rademacher MGF**, as an instance of the centred Bernoulli MGF
already proved for Lemma 14.  Taking `p = p' = 1/2` and `u = 2λ` there gives
exactly this, and the resulting compensator is `λ²/2`. -/
theorem rademacher_mgf_le (lam : ℝ) :
    (1 / 2 : ℝ) * Real.exp lam + (1 / 2 : ℝ) * Real.exp (-lam)
      ≤ Real.exp (lam ^ 2 / 2) := by
  have h := centered_bernoulli_mgf_le (p := (1 / 2 : ℝ)) (p' := (1 / 2 : ℝ))
    (u := 2 * lam) (by norm_num) (by norm_num) (by norm_num)
  have hsq : (2 * lam) ^ 2 / 8 = lam ^ 2 / 2 := by ring
  have harg : 2 * lam * (1 / 2 : ℝ) = lam := by ring
  rw [hsq, harg] at h
  exact h

/-- The signed creation imbalance, as a real-valued state function.  The
subtraction is over `ℝ` after casting, so no `ℕ`-subtraction enters. -/
noncomputable def creationImbalance {n : ℕ} (q : SingleLedger n) : ℝ :=
  (q.cx : ℝ) - (q.cy : ℝ)

/-- The creation count, which is the compensator's clock. -/
def creationCount {n : ℕ} (q : SingleLedger n) : ℕ := q.cx + q.cy

/-- **The compensated exponent.**  Compare `urnExp`: same shape, different
constant — `λ²/2` here versus `λ²/8` there, because the increment is `±1`
(range 2) rather than a centred Bernoulli of range 1. -/
noncomputable def creationExp {n : ℕ} (lam : ℝ) (q : SingleLedger n) : ℝ :=
  lam * creationImbalance q - lam ^ 2 / 2 * (creationCount q : ℝ)

/-- The `ℝ≥0∞` potential. -/
noncomputable def creationG {n : ℕ} (lam : ℝ) (q : SingleLedger n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (creationExp lam q))

/-- Inert and resolution events leave the potential fixed: they touch neither
creation ledger. -/
theorem creationG_of_noncreation {n : ℕ} (lam : ℝ) (q : SingleLedger n)
    (k : SingleComp)
    (hk : k ≠ SingleComp.xyToX) (hk' : k ≠ SingleComp.xyToY) :
    creationG lam (SingleComp.nextSingleLedger q k) = creationG lam q := by
  unfold creationG creationExp creationImbalance creationCount
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · rfl
  · cases k <;> first
      | exact absurd rfl hk
      | exact absurd rfl hk'
      | simp [SingleComp.cxInc, SingleComp.cyInc]

/-- An `X`-oriented creation multiplies the potential by `exp(λ − λ²/2)`. -/
theorem creationExp_xyToX {n : ℕ} (lam : ℝ) (q : SingleLedger n)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b
      SingleComp.xyToX ≠ 0) :
    creationExp lam (SingleComp.nextSingleLedger q SingleComp.xyToX)
      = creationExp lam q + (lam - lam ^ 2 / 2) := by
  unfold creationExp creationImbalance creationCount SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleComp.cxInc, SingleComp.cyInc]
  push_cast
  ring

/-- A `Y`-oriented creation multiplies the potential by `exp(−λ − λ²/2)`. -/
theorem creationExp_xyToY {n : ℕ} (lam : ℝ) (q : SingleLedger n)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b
      SingleComp.xyToY ≠ 0) :
    creationExp lam (SingleComp.nextSingleLedger q SingleComp.xyToY)
      = creationExp lam q + (-lam - lam ^ 2 / 2) := by
  unfold creationExp creationImbalance creationCount SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleComp.cxInc, SingleComp.cyInc]
  push_cast
  ring

/-- **The scalar step.**  With equal masses `p` on the two creations and the
rest inert for the ledger, the one-step expectation contracts.

This is the whole content of the supermartingale, isolated from the `ℝ≥0∞`
bookkeeping: it says the fair Rademacher MGF pays for the compensator. -/
theorem creation_scalar_step (lam p : ℝ) (hp : 0 ≤ p) :
    (1 - 2 * p) + p * Real.exp (lam - lam ^ 2 / 2)
        + p * Real.exp (-lam - lam ^ 2 / 2)
      ≤ 1 := by
  have hrad := rademacher_mgf_le lam
  have hsplit : Real.exp (lam - lam ^ 2 / 2)
      = Real.exp lam * Real.exp (-(lam ^ 2 / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hsplit' : Real.exp (-lam - lam ^ 2 / 2)
      = Real.exp (-lam) * Real.exp (-(lam ^ 2 / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, hsplit']
  have hkey : Real.exp lam * Real.exp (-(lam ^ 2 / 2))
      + Real.exp (-lam) * Real.exp (-(lam ^ 2 / 2)) ≤ 2 := by
    have hinv : Real.exp (-(lam ^ 2 / 2)) = (Real.exp (lam ^ 2 / 2))⁻¹ := by
      rw [Real.exp_neg]
    have hEpos : 0 < Real.exp (lam ^ 2 / 2) := Real.exp_pos _
    rw [hinv, ← add_mul]
    rw [← le_div_iff₀ (by positivity), ]
    have : Real.exp lam + Real.exp (-lam) ≤ 2 * Real.exp (lam ^ 2 / 2) := by
      linarith [hrad]
    calc Real.exp lam + Real.exp (-lam) ≤ 2 * Real.exp (lam ^ 2 / 2) := this
      _ = 2 / (Real.exp (lam ^ 2 / 2))⁻¹ := by
          field_simp
  nlinarith [hkey, hp]

end Tri

#print axioms Tri.singleCompPMF_creation_masses_eq
#print axioms Tri.rademacher_mgf_le
#print axioms Tri.creationG_of_noncreation
#print axioms Tri.creationExp_xyToX
#print axioms Tri.creationExp_xyToY
#print axioms Tri.creation_scalar_step

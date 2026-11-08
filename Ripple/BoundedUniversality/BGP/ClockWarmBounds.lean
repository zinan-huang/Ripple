/-
Ripple.BoundedUniversality.BGP.ClockWarmBounds
--------------------------
Pre-cycle warm-up bounds for the dynamic clock defects.

The exposure-weighted reserve (`Ripple.BoundedUniversality.BGP.SelectorForallW`,
`warmup_defect_bound`) needs each per-cycle defect, evaluated at the
SHIFTED cycle index `m + j` (where `m` cycles of warm-up have already
preloaded the precision `μ`), to carry the suppression factor
`B^{−N} · q^{j}` — `B^{−N}` from the warm-up, and a geometric
per-cycle factor `q^{j}` for the exposure sum.

This file supplies that factor for the two dynamic cascade constants of
`Ripple.BoundedUniversality.BGP.DynamicGate`:

  * `dynChi  A L c₀ c₁ j = A · exp(−r·(2π j)) / r`,  r := c₀·2^{−L} − c₁
        — leak budget (exp-affine off-leak, decay rate `r`).
  * `dynKappa A L c₀ c₁ j = exp(−A·exp(c₁·2π j)·exp(−c₀·2π(j+1)·4^{−L})·(2π/3))
        — active-window contraction factor.

For `χ` the split is exact and elementary: the exponent
`−r·(2π·(m+j))` factors as `−r·(2π m) + −r·(2π j)`, the first term is
dominated by `B^{−N}` (warm-up reserve `exp_warm_cycles_le`), the second
gives the geometric `qχ^j` with `qχ := exp(−r·2π) ∈ (0,1)`.

For `κ` the value is `exp(−P_{m+j})` with `P_{m+j} ≥ 0`, so an UPPER
bound `≤ Cκ·B^{−N}·qκ^j` requires a LOWER bound on the inner exponent
`P_{m+j}` that grows with `j` — exactly the cascade-monotonicity
content of `DynamicGate` (the V2/V3/V4 inequalities).  We therefore
expose that lower bound as an explicit hypothesis
(`writeIntegral`-style: `P_{m+j} ≥ N·log B + j·log(1/qκ)`), keeping the
analytic core elementary and the regime assumption HONEST and named.
-/

import Ripple.BoundedUniversality.BGP.DynamicGate

namespace Ripple.BoundedUniversality.BGP

open Real

/-! ## (a) The warm-cycle exponential reserve (pure real analysis)

After `m` warm-up cycles the off-leak prefactor `exp(−2π r m)` has
fallen below the input-length reserve `B^{−N}`, provided the warm-up
length condition `N·log B ≤ 2π r m` holds.  This is the `B^{−N}`
half of the `B^{−N}·q^j` factor. -/

/-- **Warm-cycle reserve.** Under the warm-up length condition
`N·log B ≤ 2π·r·m` (enough warm-up cycles `m` to pay off the
input-length reserve), the warm-up exponential prefactor is dominated
by `B^{−N}`. -/
theorem exp_warm_cycles_le {B r : ℝ} {N m : ℕ}
    (hB : 1 < B) (hr : 0 < r)
    (hm : (N : ℝ) * Real.log B ≤ 2 * Real.pi * r * (m : ℝ)) :
    Real.exp (-(2 * Real.pi * r * (m : ℝ))) ≤ B ^ (-(N : ℤ)) := by
  have hB0 : 0 < B := lt_trans one_pos hB
  -- exp(-(N·log B)) = B^(-N)
  have hid : Real.exp (-((N : ℝ) * Real.log B)) = B ^ (-(N : ℤ)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hB0, zpow_neg, zpow_natCast]
  calc
    Real.exp (-(2 * Real.pi * r * (m : ℝ)))
        ≤ Real.exp (-((N : ℝ) * Real.log B)) :=
          Real.exp_le_exp.mpr (by linarith)
    _ = B ^ (-(N : ℤ)) := hid

/-! ## (b) The χ warm-bound (algebra on `dynChi`)

At the shifted cycle `m + j`, `dynChi` factors as
`(A/r) · exp(−r·2π m) · exp(−r·2π j)`.  With the warm-up reserve from
(a) and `exp(−r·2π j) = qχ^j` for `qχ := exp(−r·2π)`, we obtain the
target `Cχ · B^{−N} · qχ^j` with `Cχ := A/r ≥ 0`. -/

/-- The geometric per-cycle factor for `χ`: `qχ := exp(−r·2π)`,
where `r := c₀·2^{−L} − c₁` is the leak decay rate.  In the regime
`r > 0` we have `qχ ∈ (0,1)`. -/
noncomputable def qChi (L : ℕ) (c₀ c₁ : ℝ) : ℝ :=
  Real.exp (-((c₀ * (1/2)^L - c₁) * (2*π)))

theorem qChi_pos (L : ℕ) (c₀ c₁ : ℝ) : 0 < qChi L c₀ c₁ := Real.exp_pos _

/-- **χ warm-bound.**  At the shifted cycle index `m + j`, the dynamic
leak budget `dynChi` is dominated by `Cχ · B^{−N} · qχ^j`, with the
explicit constant `Cχ := A / r` (`r := c₀·2^{−L} − c₁` the leak decay
rate) and the geometric factor `qχ := exp(−r·2π)`.

Hypotheses: `1 < B`, the leak-rate positivity `0 < r` (the genuine
parameter-window regime of `DynamicGate`), `0 ≤ A`, and the warm-up
length condition `N·log B ≤ 2π·r·m`. -/
theorem dynChi_warm_bound {A B : ℝ} {L : ℕ} {c₀ c₁ : ℝ} {N m j : ℕ}
    (hB : 1 < B) (hA : 0 ≤ A)
    (hr : 0 < c₀ * (1/2)^L - c₁)
    (hm : (N : ℝ) * Real.log B
            ≤ 2 * Real.pi * (c₀ * (1/2)^L - c₁) * (m : ℝ)) :
    dynChi A L c₀ c₁ (m + j)
      ≤ (A / (c₀ * (1/2)^L - c₁)) * B ^ (-(N : ℤ)) * qChi L c₀ c₁ ^ j := by
  have hB0 : 0 < B := lt_trans one_pos hB
  -- Unfold both defs FIRST so that `set r` below captures every literal
  -- occurrence of the decay rate, including the ones produced by unfolding.
  unfold dynChi qChi
  have hcast : ((m + j : ℕ) : ℝ) = (m : ℝ) + (j : ℝ) := by push_cast; ring
  rw [hcast]
  set r : ℝ := c₀ * (1/2)^L - c₁
  -- Warm-up reserve from (a):  exp(−2π r m) ≤ B^(−N).
  have hwarm : Real.exp (-(2 * Real.pi * r * (m : ℝ))) ≤ B ^ (-(N : ℤ)) :=
    exp_warm_cycles_le (r := r) hB hr hm
  -- Geometric factor:  qχ^j = exp(−r·2π·j).
  have hqpow : Real.exp (-(r * (2*π))) ^ j = Real.exp (-(r * (2*π) * (j : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- The exponent of `dynChi (m+j)` splits.
  have hsplit :
      Real.exp (-(r * (2*π*((m : ℝ) + (j : ℝ)))))
        = Real.exp (-(2 * Real.pi * r * (m : ℝ)))
            * Real.exp (-(r * (2*π) * (j : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- Rewrite the split exponent and the geometric factor directly in the goal.
  rw [hsplit, hqpow]
  -- Goal now:  A · (exp(−2πrm) · exp(−r2πj)) / r  ≤  (A/r) · B^{−N} · exp(−r2πj)
  have hAr_nonneg : 0 ≤ A / r := div_nonneg hA hr.le
  have hgpos : 0 < Real.exp (-(r * (2*π) * (j : ℝ))) := Real.exp_pos _
  have hmono :
      Real.exp (-(2 * Real.pi * r * (m : ℝ)))
          * Real.exp (-(r * (2*π) * (j : ℝ)))
        ≤ B ^ (-(N : ℤ)) * Real.exp (-(r * (2*π) * (j : ℝ))) :=
    mul_le_mul_of_nonneg_right hwarm hgpos.le
  calc
    A * (Real.exp (-(2 * Real.pi * r * (m : ℝ)))
          * Real.exp (-(r * (2*π) * (j : ℝ)))) / r
        = (A / r) * (Real.exp (-(2 * Real.pi * r * (m : ℝ)))
            * Real.exp (-(r * (2*π) * (j : ℝ)))) := by ring
    _ ≤ (A / r) * (B ^ (-(N : ℤ)) * Real.exp (-(r * (2*π) * (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left hmono hAr_nonneg
    _ = (A / r) * B ^ (-(N : ℤ)) * Real.exp (-(r * (2*π) * (j : ℝ))) := by ring

/-! ## (c) The κ warm-bound (active-contraction exponential)

`dynKappa A L c₀ c₁ (m+j) = exp(−P_{m+j})` with `P_{m+j} ≥ 0`, so an
upper bound of the form `Cκ·B^{−N}·qκ^j` (with `qκ < 1`) requires a
LOWER bound on the inner exponent `P_{m+j}` that grows with `j`.  That
growth is precisely the cascade-monotonicity content of `DynamicGate`
(`κ_j` strictly decreasing once `c₁ > c₀·4^{−L}`); we expose it as the
explicit hypothesis `hP`, mirroring the write-integral lower bound used
by `warmup_defect_bound` in `SelectorForallW`.

The analytic core is then identical to `warmup_defect_bound`:
`exp(−Lbd) ≤ B^{−N}·qκ^j` whenever `Lbd ≥ N·log B + j·log(1/qκ)`.
Here `Cκ = 1`. -/

/-- The inner (active-contraction) exponent of `dynKappa` at cycle `j`:
`P_j := A·exp(c₁·2π j)·exp(−c₀·2π(j+1)·4^{−L})·(2π/3)`, so that
`dynKappa A L c₀ c₁ j = exp(−P_j)`. -/
noncomputable def dynKappaExponent (A : ℝ) (L : ℕ) (c₀ c₁ : ℝ) (j : ℕ) : ℝ :=
  A * Real.exp (c₁ * 2*π*j)
    * Real.exp (-(c₀ * 2*π*(j+1) * (1/4)^L)) * (2*π/3)

theorem dynKappa_eq_exp_neg_exponent (A : ℝ) (L : ℕ) (c₀ c₁ : ℝ) (j : ℕ) :
    dynKappa A L c₀ c₁ j = Real.exp (-(dynKappaExponent A L c₀ c₁ j)) := by
  unfold dynKappa dynKappaExponent
  rfl

/-- **κ warm-bound.**  At the shifted cycle index `m + j`, the dynamic
contraction factor `dynKappa` is dominated by `B^{−N} · qκ^j`
(`Cκ = 1`), under the explicit cascade lower bound `hP` on the inner
active-contraction exponent.

The hypothesis `hP` states that the warm-up has driven the inner
exponent `P_{m+j}` above `N·log B + j·log(1/qκ)` — the precise,
satisfiable cascade-monotonicity input (`κ_j` decreasing, leak rate
beating the gain) that `DynamicGate`'s V2/V3/V4 obligations supply.
`hqκ : 0 < qκ` (and `qκ < 1` in the intended regime, though only
positivity is needed for the bound).  No new analytic workhorse: the
core is the `exp(−Lbd) ≤ B^{−N}·qκ^j` identity. -/
theorem dynKappa_warm_bound {A B qκ : ℝ} {L : ℕ} {c₀ c₁ : ℝ} {N m j : ℕ}
    (hB0 : 0 < B) (hqκ : 0 < qκ)
    (hP : (N : ℝ) * Real.log B + (j : ℝ) * Real.log (1 / qκ)
            ≤ dynKappaExponent A L c₀ c₁ (m + j)) :
    dynKappa A L c₀ c₁ (m + j) ≤ B ^ (-(N : ℤ)) * qκ ^ j := by
  rw [dynKappa_eq_exp_neg_exponent]
  -- exp(−P) ≤ exp(−(N·log B + j·log(1/qκ)))  by monotonicity (P ≥ that lower bound)
  have hmono : Real.exp (-(dynKappaExponent A L c₀ c₁ (m + j))) ≤
      Real.exp (-((N : ℝ) * Real.log B + (j : ℝ) * Real.log (1 / qκ))) :=
    Real.exp_le_exp.mpr (by linarith)
  refine le_trans hmono (le_of_eq ?_)
  rw [neg_add, Real.exp_add]
  congr 1
  · -- exp(−(N·log B)) = B^(−N)
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hB0, zpow_neg, zpow_natCast]
  · -- exp(−(j·log(1/qκ))) = qκ^j
    rw [Real.log_div one_ne_zero (ne_of_gt hqκ), Real.log_one, zero_sub,
      mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hqκ]

end Ripple.BoundedUniversality.BGP

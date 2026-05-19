/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Central Region Supermartingale (Lemma 4)

The central region (no count ≥ 7n/8) cannot use the multiplicative drift
of 1/f (counterexample: n=4, x=1, b=0, y=3, where E[1/f'] > 1/f).
Instead, the proof requires an exponential supermartingale on an
augmented state that tracks cumulative interaction counts.

## The supermartingale

M_t = α_vb^{S^vb_t} · α_xy^{S^xy_t} / f(C_t)

where α_vb = (16n+7)/(16n), α_xy = (16n-5)/(16n), and S^vb_t, S^xy_t
count cumulative vb and xy interactions.

## Per-step condition

The key algebraic fact: for each interaction type,
- vb: α_vb · f · E[1/f' | vb] ≤ 1  (from `supermartingale_factor_vb_le`)
- xy: α_xy · f · E[1/f' | xy] ≤ 1  (from `supermartingale_factor_xy_le`)
- other: f' = f, so the contribution is exactly 1

This gives E[M_{t+1}/M_t | F_t] ≤ 1 (supermartingale property).

## Proof roadmap (paper: Lemma 4 → Corollary 2 → Lemma 5 → Theorem 1)

1. ✅ Per-step algebraic bounds (Supermartingale.lean)
2. 🔨 Per-step supermartingale condition on transition kernel (this file)
3. ⬜ Augmented state (Config × ℕ × ℕ) and augmented kernel
4. ⬜ E[M_t] ≤ M_0 by iteration (Corollary 2)
5. ⬜ Counting supermartingale C_t (Lemma 5)
6. ⬜ Combine to bound P[still in central at time t]
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.Supermartingale
import Ripple.PopulationProtocol.Majority.PopProto.Convergence.Expected

namespace PopProto

open State MeasureTheory

namespace Config

variable {n : ℕ}

/-! ### Per-step supermartingale condition (algebraic core)

The per-step condition E[M'/M] ≤ 1 reduces to showing that the weighted
sum of interaction contributions is ≤ totalPairs.

Specifically, for c in the central region with potential f = u²+2n:

  Σ_{vb} count·α_vb·f/f' + Σ_{xy} count·α_xy·f/f' + Σ_{other} count ≤ totalPairs

This splits into two independent bounds:
  (A) Σ_{vb} count·α_vb·f/f' ≤ bv  (from supermartingale_factor_vb_le)
  (B) Σ_{xy} count·α_xy·f/f' ≤ 2xy  (from supermartingale_factor_xy_le)

Since Σ_{other} count = totalPairs - bv - 2xy, the total is ≤ totalPairs. -/

/-- **VB contribution bound**: The weighted sum of α_vb · f/f' over vb interactions
    (xb and yb) is ≤ bv.

    In cross-multiplied form: for all u, v, n with n ≥ 1 and v ≤ n,
    (16n+7) · f · (v(f+1)-2u²) ≤ 16n · v · ((f+1)²-4u²)
    which is exactly `supermartingale_factor_vb_le`.

    Multiplying both sides by b/((f+1)²-4u²) gives:
    b · α_vb · f · (v(f+1)-2u²)/((f+1)²-4u²) ≤ bv

    The LHS is exactly Σ_{vb} count · α_vb · f / f'. -/
theorem vb_weighted_sum_le (u : ℤ) (v n : ℕ) (hn : n ≥ 1) (hv : v ≤ n) :
    (16 * (n : ℤ) + 7) * (u ^ 2 + 2 * n) *
    ((v : ℤ) * (u ^ 2 + 2 * n + 1) - 2 * u ^ 2) ≤
    16 * (n : ℤ) * (v : ℤ) * ((u ^ 2 + 2 * n + 1) ^ 2 - 4 * u ^ 2) :=
  supermartingale_factor_vb_le u v n hn hv

/-- **XY contribution bound**: The weighted sum of α_xy · f/f' over xy interactions
    (xy and yx) is ≤ 2xy.

    In cross-multiplied form:
    (16n-5) · f · (f+1) ≤ 16n · ((f+1)²-4u²)
    which is exactly `supermartingale_factor_xy_le`.

    Multiplying both sides by 2xy/((f+1)²-4u²) gives:
    2xy · α_xy · f · (f+1)/((f+1)²-4u²) ≤ 2xy

    The LHS is exactly Σ_{xy} count · α_xy · f / f'. -/
theorem xy_weighted_sum_le (u : ℤ) (n : ℕ) (hn : n ≥ 1) :
    (16 * (n : ℤ) - 5) * (u ^ 2 + 2 * n) * (u ^ 2 + 2 * n + 1) ≤
    16 * (n : ℤ) * ((u ^ 2 + 2 * n + 1) ^ 2 - 4 * u ^ 2) :=
  supermartingale_factor_xy_le u n hn

/-! ### Positivity of the denominator (f+1)² - 4u²

The product a·b = ((u+1)²+2n)·((u-1)²+2n) = (f+1)²-4u² is always positive.
This is needed to divide by it safely. -/

/-- The denominator `(f+1)² - 4u² = ((u+1)²+2n)·((u-1)²+2n) > 0` for n ≥ 1. -/
theorem ab_pos (u : ℤ) (n : ℕ) (hn : n ≥ 1) :
    0 < (u ^ 2 + 2 * (n : ℤ) + 1) ^ 2 - 4 * u ^ 2 := by
  have : (u ^ 2 + 2 * (n : ℤ) + 1) ^ 2 - 4 * u ^ 2 =
    ((u + 1) ^ 2 + 2 * (n : ℤ)) * ((u - 1) ^ 2 + 2 * (n : ℤ)) := by ring
  rw [this]
  have hn' : (0 : ℤ) < 2 * n := by omega
  apply mul_pos <;> nlinarith [sq_nonneg (u + 1), sq_nonneg (u - 1)]

/-- The numerator `v(f+1) - 2u²` is non-negative when `v ≥ 1`,
    `f = u²+2n`, and `|u| ≤ v` (which holds since u = x-y, v = x+y).
    Proof: (v-2)·u² + v·(2n+1) ≥ 0. Split on v ≥ 2 vs v = 1. -/
theorem vb_numerator_nonneg (u : ℤ) (v n : ℕ) (hv : v ≥ 1)
    (huv : u.natAbs ≤ v) :
    0 ≤ (v : ℤ) * (u ^ 2 + 2 * (n : ℤ) + 1) - 2 * u ^ 2 := by
  have hv' : (1 : ℤ) ≤ v := by exact_mod_cast hv
  by_cases hv2 : (v : ℕ) ≥ 2
  · -- v ≥ 2: (v-2)·u² ≥ 0 and v·(2n+1) ≥ 0
    have : (2 : ℤ) ≤ v := by exact_mod_cast hv2
    nlinarith [sq_nonneg u]
  · -- v = 1: expression = 2n+1-u², and u² ≤ v² = 1
    have hv1 : v = 1 := by omega
    have hu1 : u.natAbs ≤ 1 := by omega
    have huv_sq : u ^ 2 ≤ 1 := by
      have h := Nat.pow_le_pow_left hu1 2
      simp only [Nat.one_pow] at h
      exact_mod_cast (Int.natAbs_sq u ▸ (show (u.natAbs : ℤ) ^ 2 ≤ 1 from by exact_mod_cast h))
    subst hv1; simp; nlinarith

/-! ### Per-step supermartingale condition in ℝ

The key bridge lemma: the expected weighted-α/f ratio under the
transition kernel is ≤ 1. This is the per-step supermartingale condition
expressed as a property of the stepDist PMF. -/

/-- **Per-step supermartingale condition (ℝ form)**:

    The α-weighted expected value of f/f' is ≤ 1:

    Σ (count/T) · α(type) · f(c)/f(step) ≤ 1

    Equivalently (clearing T):

    Σ count · α(type) · f(c) / f(step) ≤ totalPairs

    This is the fundamental property that makes M_t a supermartingale.

    Proof: split into vb, xy, and other contributions.
    - vb: ≤ bv (from `supermartingale_factor_vb_le`)
    - xy: ≤ 2xy (from `supermartingale_factor_xy_le`)
    - other: = T - bv - 2xy (f unchanged)
    - Total: ≤ T ✓ -/
theorem supermartingale_per_step (c : Config n) (hn : n ≥ 1)
    (hv : 0 < c.v) :
    -- Cross-multiplied integer form of E[M'/M] ≤ 1:
    -- VB: b · (16n+7) · f · (v(f+1) - 2u²) ≤ b · 16n · v · ab
    -- XY: 2xy · (16n-5) · f · (f+1) ≤ 2xy · 16n · ab
    -- Combined: LHS_vb + LHS_xy ≤ (bv + 2xy) · 16n · ab
    -- where f = u²+2n, ab = (f+1)²-4u²
    (c.b_count : ℤ) *
      ((16 * n + 7) * ((c.u : ℤ) ^ 2 + 2 * n) *
       ((c.v : ℤ) * ((c.u : ℤ) ^ 2 + 2 * n + 1) - 2 * c.u ^ 2)) +
    2 * (c.x_count : ℤ) * c.y_count *
      ((16 * n - 5) * ((c.u : ℤ) ^ 2 + 2 * n) *
       ((c.u : ℤ) ^ 2 + 2 * n + 1)) ≤
    ((c.b_count : ℤ) * c.v + 2 * c.x_count * c.y_count) *
      (16 * n * (((c.u : ℤ) ^ 2 + 2 * n + 1) ^ 2 - 4 * c.u ^ 2)) := by
  -- Abbreviate for readability
  set f : ℤ := (c.u : ℤ) ^ 2 + 2 * (n : ℤ) with hf_def
  set ab : ℤ := (f + 1) ^ 2 - 4 * c.u ^ 2 with hab_def
  -- Both individual bounds hold:
  have hvb := supermartingale_factor_vb_le c.u c.v n hn c.v_le_n
  have hxy := supermartingale_factor_xy_le c.u n hn
  -- Multiply vb bound by b (non-negative)
  have hb : (0 : ℤ) ≤ c.b_count := by exact_mod_cast Nat.zero_le _
  have hvb' : (c.b_count : ℤ) * ((16 * ↑n + 7) * f * (↑c.v * (f + 1) - 2 * c.u ^ 2)) ≤
      (c.b_count : ℤ) * (16 * ↑n * ↑c.v * ab) := by
    exact mul_le_mul_of_nonneg_left hvb hb
  -- Multiply xy bound by 2xy (non-negative)
  have hxy_nn : (0 : ℤ) ≤ 2 * c.x_count * c.y_count := by positivity
  have hxy' : 2 * (c.x_count : ℤ) * c.y_count * ((16 * ↑n - 5) * f * (f + 1)) ≤
      2 * (c.x_count : ℤ) * c.y_count * (16 * ↑n * ab) := by
    exact mul_le_mul_of_nonneg_left hxy hxy_nn
  -- Combine: LHS = vb_part + xy_part ≤ bv · 16n·ab + 2xy · 16n·ab = (bv+2xy) · 16n·ab
  calc (c.b_count : ℤ) * ((16 * ↑n + 7) * f * (↑c.v * (f + 1) - 2 * c.u ^ 2)) +
      2 * ↑c.x_count * ↑c.y_count * ((16 * ↑n - 5) * f * (f + 1))
      ≤ ↑c.b_count * (16 * ↑n * ↑c.v * ab) +
        2 * ↑c.x_count * ↑c.y_count * (16 * ↑n * ab) := add_le_add hvb' hxy'
    _ = (↑c.b_count * ↑c.v + 2 * ↑c.x_count * ↑c.y_count) * (16 * ↑n * ab) := by ring

/-! ### Roadmap for the central-region probability theorem

The per-step supermartingale condition above is the algebraic foundation.
The remaining steps for the full theorem packaging are:

**Step 3: Augmented state and kernel**
- Define `AugConfig n := Config n × ℕ × ℕ` (tracks S^vb, S^xy)
- Define `augmentedKernelCentral` that transitions the config via
  `transitionKernel` and increments the appropriate counter
- Show it projects to `absorbedKernelCentral` via `Prod.fst`

**Step 4: Supermartingale M on augmented state**
- Define `M (a : AugConfig n) := α_vb^a.2.1 · α_xy^a.2.2 / f(a.1)` as ℝ≥0∞
- Prove `∫⁻ M d(augKernel a) ≤ M(a)` using `supermartingale_per_step`
- Conclude `E[M_t] ≤ M_0 = 1/f₀` by iteration

**Step 5: Counting supermartingale (Lemma 5)**
- Define `C_t = exp(n⁻¹(S^c - 130·S^vb - 258·S^xy))` on augmented state
- Show the per-step condition: E[C_{t+1}|F_t, in central] ≤ C_t
  (requires analyzing the probability of each interaction type in central)
- Conclude `E[C_{τ∧t}] ≤ 1`

**Step 6: Combine for geometric tail**
From M supermartingale (Corollary 2):
  Pr[S^vb ≥ 8n·log(n+2) + 8cn·log n + 5n/2] ≤ n⁻ᶜ
From Lemma 5:
  Pr[S^c ≥ 130·S^vb + 258·S^xy + cn·log n] ≤ n⁻ᶜ
Combine to bound total central interactions, yielding geometric tail.
-/

end Config
end PopProto

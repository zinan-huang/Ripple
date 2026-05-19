/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Supermartingale Construction (Lemma 4)

The central supermartingale from Section 4.4 of Angluin-Aspnes-Eisenstat 2008.

## The process

Define `Mₜ = exp((7/16·S^vb - 5/16·S^xy)/n) / (u²+2n)`

## Key intermediate results

- E[Δf | I^vb] = (2u²+v)/v  (Δf = change in f = u²+2n)
- E[Δf | I^xy] = 1
- E[Δ(1/f)/(1/f) | I^vb] ≤ -15/32·n⁻¹ + O(n⁻³/²)  (Lemma 2)
- E[Δ(1/f)/(1/f) | I^xy] ≤ 9/32·n⁻¹ + O(n⁻³/²)  (Lemma 3)
- Mₜ is a supermartingale (Lemma 4)

The first two are proven. Lemmas 2-4 are stated with proof structure.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.DeltaF
import Ripple.PopulationProtocol.Majority.PopProto.Convergence.RelativeChange

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ### E[Δf | I^vb] = (2u² + v) / v

From weighted_delta_f_vb: the probability-weighted Δf over vb interactions
has numerator `b·(2u²+v)` and denominator `b·v` (total vb interaction count).
Canceling b gives `(2u²+v)/v`. -/

/-- The conditional expected value of Δf given a vb interaction is `(2u²+v)/v`.
    Here we express it as: the weighted sum of Δf equals `b·(2u²+v)`,
    and the total weight of vb interactions is `b·v`. -/
theorem expected_delta_f_vb_num (c : Config n) :
    (c.x_count : ℤ) * c.b_count * (2 * c.u + 1) +
    (c.y_count : ℤ) * c.b_count * (-2 * c.u + 1) =
    (c.b_count : ℤ) * (2 * c.u ^ 2 + c.v) :=
  weighted_delta_f_vb c

/-- The total weight of vb interactions is `b·v` (in ℤ). -/
theorem vb_total_weight (c : Config n) :
    (c.x_count : ℤ) * c.b_count + (c.y_count : ℤ) * c.b_count =
    (c.b_count : ℤ) * c.v := by
  unfold v; push_cast; ring

/-! ### E[Δf | I^xy] = 1

From weighted_delta_f_xy: the probability-weighted Δf over xy interactions
has numerator `2xy` and denominator `2xy` (total xy interaction count).
So E[Δf | I^xy] = 1. -/

/-- The conditional expected value of Δf given an xy interaction is 1.
    The weighted sum of Δf is `2xy` and the total weight is `2xy`. -/
theorem expected_delta_f_xy_eq (c : Config n) :
    (c.x_count : ℤ) * c.y_count * (2 * c.u + 1) +
    (c.y_count : ℤ) * c.x_count * (-2 * c.u + 1) =
    2 * (c.x_count : ℤ) * c.y_count :=
  weighted_delta_f_xy c

/-- The total weight of xy interactions is `2xy`. -/
theorem xy_total_weight (c : Config n) :
    (c.x_count : ℤ) * c.y_count + (c.y_count : ℤ) * c.x_count =
    2 * (c.x_count : ℤ) * c.y_count := by
  ring

/-! ### Lemma 2: Bound on E[Δ(1/f)/(1/f) | I^vb]

The paper proves: E[Δ(1/f)/(1/f) | I^vb] ≤ -15/32·n⁻¹ + O(n⁻³/²)

Key steps:
1. E[-Δf/f | I^vb] = -(2u²/v + 1) / (u² + 2n) = -(2u²+v) / (v·f)
2. This is ≤ -1/(2n) (from (2u²+v)/(v·f) ≥ v/(v·2n) = 1/(2n))
3. The quadratic correction E[(Δf)²/f² | I^vb] is O(n⁻¹) but with
   coefficient ≤ 15/32 - 1/2 = -1/32, yielding the overall -15/32.
-/

/-- Lower bound: (2u²+v)/(v·f) ≥ 1/(2n).
    Since 2u²+v ≥ v and f = u²+2n ≤ v·(u²+2n), we get
    (2u²+v)/(v·f) ≥ v/(v·f) = 1/f ≥ 1/(n²+2n) ... that's too weak.
    Better: (2u²+v)/(v·f) ≥ v/(v·2n) = 1/(2n) since f ≤ ... hmm.
    Actually: (2u²+v)·(2n) ≥ v·f = v·(u²+2n) iff 4nu²+2nv ≥ vu²+2nv
    iff 4nu² ≥ vu², which holds since v ≤ n ≤ 4n. ✓
    (When u = 0: both sides equal 2nv.) -/
theorem linear_term_vb_lower_bound (c : Config n) (hn : n ≥ 1)
    (hv : 0 < c.v) :
    (2 * c.u ^ 2 + (c.v : ℤ)) * (2 * (n : ℤ)) ≥
    (c.v : ℤ) * ((c.u ^ 2 : ℤ) + 2 * n) := by
  have hvn : (c.v : ℤ) ≤ n := by exact_mod_cast c.v_le_n
  nlinarith [sq_nonneg c.u]

/-! ### E[(Δf)² | I^vb] and E[(Δf)² | I^xy]

From weighted_delta_f_sq_vb:
  Weighted (Δf)² sum = b·(4u²v + 4u² + v)
  Total weight = b·v
  So E[(Δf)² | I^vb] = (4u²v + 4u² + v)/v = 4u² + 4u²/v + 1

From weighted_delta_f_sq_xy:
  Weighted (Δf)² sum = 2xy·(4u²+1)
  Total weight = 2xy
  So E[(Δf)² | I^xy] = 4u² + 1 -/

/-- E[(Δf)² | I^vb]: numerator is `b·(4u²v + 4u² + v)`, denominator is `b·v`. -/
theorem expected_delta_f_sq_vb_num (c : Config n) :
    (c.x_count : ℤ) * c.b_count * (2 * c.u + 1) ^ 2 +
    (c.y_count : ℤ) * c.b_count * (-2 * c.u + 1) ^ 2 =
    (c.b_count : ℤ) * (4 * c.u ^ 2 * c.v + 4 * c.u ^ 2 + c.v) :=
  weighted_delta_f_sq_vb c

/-- E[(Δf)² | I^xy] = 4u² + 1. The numerator is `2xy·(4u²+1)` and
    the denominator is `2xy`, so they cancel. -/
theorem expected_delta_f_sq_xy_num (c : Config n) :
    (c.x_count : ℤ) * c.y_count * (2 * c.u + 1) ^ 2 +
    (c.y_count : ℤ) * c.x_count * (-2 * c.u + 1) ^ 2 =
    2 * (c.x_count : ℤ) * c.y_count * (4 * c.u ^ 2 + 1) :=
  weighted_delta_f_sq_xy c

/-! ### Key bound for Lemma 2

The paper needs: E[(Δf)²/f² | I^vb] ≤ (some bound).
We express this as: (4u²v + 4u² + v) / (v · f²) ≤ ...

Setting r = u²/n, f = u² + 2n = n(r+2):
  E[(Δf)²/f² | I^vb] = (4u²v + 4u² + v) / (v · (u²+2n)²)

When v ≤ n:
  = (4u² + 4u²/v + 1) / (u² + 2n)²
  ≤ (4u² + 4u² + 1) / (u² + 2n)²   [since 1/v ≤ 1]
  hmm, this doesn't help directly...

The paper's approach is different: it uses Lemma 1 to bound the
relative change of 1/f, then combines linear and quadratic terms
to get the -15/32 coefficient.

Specifically, from p. 92:
  E[Δ(1/(u²+2n))] / (1/(u²+2n))
  = E[-Δf/f + (Δf/f)² / (1 + Δf/f)]

Conditioned on I^vb:
  Linear term:  -(2u²/v + 1) / f
  Quadratic term (from Lemma 1 remainder): bounded above

The paper shows the combined coefficient is ≤ -15/32 · n⁻¹. -/

/-- The product `E[Δf | I^vb] · E[Δf | I^vb]` divided by `f²` gives
    the square of the linear term. We need a bound on
    `(Δf)² / f²` in expectation, which we express as a cross-multiply. -/
theorem delta_f_sq_over_f_sq_vb_bound (c : Config n) (hn : n ≥ 1)
    (hv : 0 < c.v) :
    -- (4u²v + 4u² + v) · (2n)² ≤ ... [bound for Lemma 2 coefficient]
    -- For now, we prove a weaker but useful bound:
    -- (4u²v + 4u² + v) ≤ (4n + 1) · v + 4u²
    -- Actually, let's prove: 4u²v + 4u² + v ≤ 4u²·n + 4u² + n
    -- i.e., 4u²v + v ≤ 4u²n + n, i.e., (4u²+1)·v ≤ (4u²+1)·n
    -- which holds since v ≤ n. ✓
    4 * c.u ^ 2 * (c.v : ℤ) + 4 * c.u ^ 2 + (c.v : ℤ) ≤
    4 * c.u ^ 2 * (n : ℤ) + 4 * c.u ^ 2 + n := by
  have hvn : (c.v : ℤ) ≤ n := by exact_mod_cast c.v_le_n
  nlinarith [sq_nonneg c.u]

/-! ### Lemma 2 coefficient bound (α = 7/16)

The supermartingale construction uses `α = 7/(16n)` as the vb coefficient.
This requires: `E[Δf/f | I^vb] = (2u²+v)/(vf) ≥ 7/(16n)`.

Cross-multiplying by `16n·v·f > 0`:
  `(2u²+v)·16n ≥ 7·v·(u²+2n)`

This holds because `(2u²+v)·16n - 7·v·(u²+2n) = u²(32n-7v) + 2nv ≥ 0`
since `v ≤ n` implies `32n-7v ≥ 25n ≥ 0`. -/

/-- **Lemma 2 core**: `(2u²+v)·16n ≥ 7·v·f`, i.e., `(2u²+v)/(vf) ≥ 7/(16n)`.
    This is the coefficient needed for the supermartingale (α = 7/(16n)). -/
theorem lemma2_coefficient (c : Config n) (hn : n ≥ 1) :
    (2 * c.u ^ 2 + (c.v : ℤ)) * (16 * (n : ℤ)) ≥
    7 * (c.v : ℤ) * (c.u ^ 2 + 2 * n) := by
  have hvn : (c.v : ℤ) ≤ n := by exact_mod_cast c.v_le_n
  nlinarith [sq_nonneg c.u]

/-! ### Lemma 3: E[f/f' | I^xy] as exact rational expression

E[f/f' | I^xy] = (f/a + f/b) / 2 = f(f+1) / (ab)

where a = (u+1)²+2n = f+2u+1 and b = (u-1)²+2n = f-2u+1.
And ab = (f+1)²-4u² = f² + 2f + 1 - 4u².

Since f = u²+2n ≥ 2n and |Δf| ≤ 2|u|+1 ≤ 2√(f)+1 (since |u| ≤ √(f-2n)),
the ratio f/f' is close to 1, and E[f/f' | I^xy] ≈ 1 + O(1/n). -/

/-- For xy interactions, `a·b = (f+1)²-4u²` where `a = (u+1)²+2n`, `b = (u-1)²+2n`.
    This is used to compute E[f/f' | I^xy] = f(f+1)/(ab). -/
theorem xy_denominator_product (c : Config n) :
    ((c.u + 1) ^ 2 + 2 * (n : ℤ)) * ((c.u - 1) ^ 2 + 2 * (n : ℤ)) =
    ((c.potential : ℤ) + 1) ^ 2 - 4 * c.u ^ 2 := by
  simp [potential, Int.natAbs_sq]; ring

/-- For xy interactions, `a + b = 2(f+1)` where `a = (u+1)²+2n`, `b = (u-1)²+2n`.
    This gives `f/a + f/b = f(a+b)/(ab) = 2f(f+1)/(ab)`. -/
theorem xy_sum_denominators (c : Config n) :
    ((c.u + 1) ^ 2 + 2 * (n : ℤ)) + ((c.u - 1) ^ 2 + 2 * (n : ℤ)) =
    2 * ((c.potential : ℤ) + 1) := by
  simp [potential, Int.natAbs_sq]; ring

/-! ### Per-step supermartingale bounds (Corollary 1 algebraic core)

These bounds are the algebraic core of the exponential supermartingale
construction (Lemma 4). They express the per-type bounds:

- **XY bound**: `(1 - 5/(16n)) · f · E[1/f' | xy] ≤ 1`
  Cross-multiplied: `(16n-5) · f · (f+1) ≤ 16n · ((f+1)² - 4u²)`

- **VB bound**: `(1 + 7/(16n)) · f · E[1/f' | vb] ≤ 1`
  Cross-multiplied: `(16n+7) · f · (v(f+1) - 2u²) ≤ 16n · v · ((f+1)² - 4u²)`

where `f = u² + 2n`, `E[1/f' | xy] = (f+1) / ((f+1)² - 4u²)` (average of
`1/((u±1)²+2n)`), and `E[1/f' | vb]` is the x,y-weighted average.

The rational factors `(16n+7)/(16n)` and `(16n-5)/(16n)` play the role of
`exp(7/(16n))` and `exp(-5/(16n))` in the paper's construction. Since
`1 + x ≤ exp(x)` for all `x`, our rational bounds are strictly stronger
than the paper's exponential bounds, and hold for ALL `n ≥ 1`
(not just "sufficiently large n"). -/

/-- **XY per-step supermartingale bound** (Corollary 1, algebraic core):
    `(16n-5) · f · (f+1) ≤ 16n · ((f+1)² - 4u²)` where `f = u²+2n`.

    Proof: RHS - LHS = 5u⁴ + (5-28n)u² + 52n²+26n ≥ 0.
    Via: `5·(RHS-LHS) = (5u²-14n)² + 25u² + 64n² + 130n`. -/
theorem supermartingale_factor_xy_le (u : ℤ) (n : ℕ) (hn : n ≥ 1) :
    (16 * (n : ℤ) - 5) * (u ^ 2 + 2 * n) * (u ^ 2 + 2 * n + 1) ≤
    16 * (n : ℤ) * ((u ^ 2 + 2 * n + 1) ^ 2 - 4 * u ^ 2) := by
  have hn' : (n : ℤ) ≥ 1 := by exact_mod_cast hn
  nlinarith [sq_nonneg (5 * u ^ 2 - 14 * (n : ℤ)), sq_nonneg u, sq_nonneg (n : ℤ)]

/-- Auxiliary: at `v = n`, the VB expression is non-negative.
    `(25n+14)u⁴ + n(-12n+21)u² + n²(4n+2) ≥ 0`.
    Via: `4(25n+14)·LHS = ((50n+28)u²-n(12n-21))² + n²(256n²+928n-329)`. -/
private theorem vb_bound_at_v_eq_n (u : ℤ) (n : ℕ) (hn : n ≥ 1) :
    (25 * (n : ℤ) + 14) * u ^ 4 + (n : ℤ) * (-12 * (n : ℤ) + 21) * u ^ 2 +
    (n : ℤ) ^ 2 * (4 * (n : ℤ) + 2) ≥ 0 := by
  have hn' : (n : ℤ) ≥ 1 := by exact_mod_cast hn
  nlinarith [sq_nonneg ((50 * (n : ℤ) + 28) * u ^ 2 - (n : ℤ) * (12 * (n : ℤ) - 21)),
             sq_nonneg (n : ℤ), sq_nonneg u]

/-- **VB per-step supermartingale bound** (Corollary 1, algebraic core):
    `(16n+7) · f · (v(f+1)-2u²) ≤ 16n · v · ((f+1)²-4u²)`
    where `f = u²+2n` and `0 ≤ v ≤ n`.

    The expression is linear in `v` with non-negative constant term
    `B = 2u²(16n+7)f` and slope `A`. When `A < 0`, the minimum over
    `[0, n]` is at `v = n`, which is non-negative by `vb_bound_at_v_eq_n`. -/
theorem supermartingale_factor_vb_le (u : ℤ) (v n : ℕ) (hn : n ≥ 1) (hv : v ≤ n) :
    (16 * (n : ℤ) + 7) * (u ^ 2 + 2 * n) *
    ((v : ℤ) * (u ^ 2 + 2 * n + 1) - 2 * u ^ 2) ≤
    16 * (n : ℤ) * (v : ℤ) * ((u ^ 2 + 2 * n + 1) ^ 2 - 4 * u ^ 2) := by
  have hn' : (n : ℤ) ≥ 1 := by exact_mod_cast hn
  have hvn : (v : ℤ) ≤ n := by exact_mod_cast hv
  -- The expression RHS - LHS is linear in v: A·v + B.
  -- B = 2u²(16n+7)(u²+2n) ≥ 0 (at v=0).
  -- At v=n: value = (25n+14)u⁴ + n(-12n+21)u² + n²(4n+2) ≥ 0.
  -- Since it's linear in v and non-neg at both endpoints [0,n], it's non-neg on [0,n].
  -- Strategy: show value at v=n is non-neg, and (n-v)·B_coeff ≥ 0.
  have hv0 : (0 : ℤ) ≤ v := by exact_mod_cast Nat.zero_le v
  have hatN := vb_bound_at_v_eq_n u n hn
  -- B ≥ 0: the value at v = 0
  have hB : (0 : ℤ) ≤ (32 * (n : ℤ) + 14) * u ^ 4 +
      (64 * (n : ℤ) ^ 2 + 28 * (n : ℤ)) * u ^ 2 := by
    have : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
    positivity
  -- (n-v) · B ≥ 0
  have h1 : (0 : ℤ) ≤ ((n : ℤ) - v) *
      ((32 * (n : ℤ) + 14) * u ^ 4 +
       (64 * (n : ℤ) ^ 2 + 28 * (n : ℤ)) * u ^ 2) :=
    mul_nonneg (by linarith) hB
  -- v · nAB ≥ 0
  have h2 : (0 : ℤ) ≤ (v : ℤ) *
      ((25 * (n : ℤ) + 14) * u ^ 4 +
       (n : ℤ) * (-12 * (n : ℤ) + 21) * u ^ 2 +
       (n : ℤ) ^ 2 * (4 * (n : ℤ) + 2)) :=
    mul_nonneg hv0 hatN.le
  -- Identity: n·(RHS-LHS) = h1_val + h2_val ≥ 0, and n ≥ 1.
  nlinarith

/-! ### Convergence Theorem

The main convergence result: O(n log n) interactions with high probability.
The algebraic bounds above provide the coefficients. The probabilistic
argument (supermartingale + Markov's inequality + region analysis) requires
measure-theoretic infrastructure that is work in progress.

**Formalized (zero sorry):**
1. Configuration space, transition rules, invariants
2. Potential function f = u²+2n and all Δf computations
3. Lemma 1: relative change decomposition of 1/f
4. Key coefficients: E[Δf | I^vb], E[Δf | I^xy], E[(Δf)²]
5. Lemma 2 core: (2u²+v)/(vf) ≥ 7/(16n) — supermartingale coefficient
6. Corollary 1 per-step bounds: xy and vb factors (rational, all n ≥ 1)
7. Region predicates and potential functions for each region
8. Drift bounds: negative expected drift in all non-consensus regions
9. Scheduler PMF construction and Markov chain kernel
10. Expected value bridge: PMF integral = ℤ drift / totalPairs
11. Multiplicative drift in ℝ for all three corner regions:
    - Large-x: E[Φ'] ≤ (1 - 13/(64(n-1)))·Φ
    - Large-y: E[Φ'] ≤ (1 - 13/(64(n-1)))·Φ  (symmetric)
    - Large-b: E[v'] ≥ (1 + 13/(16(n-1)))·v

**Remaining theorem assembly:**
The central region cannot use multiplicative drift of 1/f (proven FALSE,
see ConvergenceTime.lean). The augmented-state supermartingale needed for
that region is formalized separately, but the final high-probability
Theorem 1 still needs the global stopping-time/union-bound packaging:
- Augmented state tracking cumulative vb/xy interaction counts
- Supermartingale M_t = α_vb^{S^vb} · α_xy^{S^xy} / f_t
  with α_vb = (16n+7)/(16n), α_xy = (16n-5)/(16n)
- Per-step bound E[M_{t+1}|F_t] ≤ M_t (from the bounds above)
- Iterative E[M_t] ≤ M_0 and Markov's inequality
- Combine region bounds via union bound (Theorem 1)
The three corner regions are fully proven with 0 sorry. -/

end Config
end PopProto

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Hoeffding
import Tri.PaperLemma3

/-!
# Lemma 14 leaf 1 — the two-sided centered Bernoulli MGF

Paper Lemma 14 is sampling-WITHOUT-replacement concentration.  Two routes are
deliberately NOT taken: Hoeffding-1963 with-replacement convex-order
domination (the coupling is painful in Lean), and closed-form hypergeometric
tails.  Instead the remaining-urn reveal chain is a finite explicit Markov
kernel on the state `(r, t)` = (remaining red, remaining total), and the
concentration is driven by the SCALED centered count

```text
M(r, t) = R/ν - r/t     ( = (S_k - k·R/ν)/(ν - k) )
```

Two facts make this the right object, and both were checked numerically before
any Lean was written:

* the naive compensated sum `S_k - Σ μ_i` is NOT a state function — at `ν = 4`,
  `R = 2` the paths red-then-blue and blue-then-red both land at `(r,t) = (1,2)`
  with compensators `5/6` and `7/6` — so it would force a trace layer;
* `r/t` IS an exact martingale: `E[r'/t'] = (r/t)(r-1)/(t-1) +
  ((t-r)/t)(r/(t-1)) = r(t-1)/(t(t-1)) = r/t`, for every `t ≥ 2`.

The one-step increment of `M` is a shifted Bernoulli `(X - p)/(t-1)` with
`p = r/t`, so every later step — both tails — factors through the lemma below
with `u = λ/(t-1)`.

Also deliberately NOT taken: the `count_tail` reflex of using a uniform
worst-case lower bound on `p`.  That is quantitatively insufficient here, not
merely awkward: the worst reachable `p` at step `k` is `(R-k)/(ν-k)`, and the
accumulated deterministic gap `Σ_k (R/ν - (R-k)/(ν-k))` exceeds the allowed
deviation `√(γ s lg ν)` for large `s` (at `ν = 10⁶`, `s = 0.9ν`: gap `701290`
against an allowed `4235`).  The mean-reversion that `M` captures is exactly
what makes without-replacement at least as concentrated as with-replacement,
and throwing it away loses the lemma.
-/

namespace Tri

open scoped ENNReal

/-- The regrouping used in both signs: the centered Bernoulli MGF is
`exp (-(v q)) * (q' + q * exp v)`. -/
private theorem centered_bernoulli_regroup (q q' v : ℝ) (hqq : q + q' = 1) :
    q * Real.exp (v * q') + q' * Real.exp (-(v * q))
      = Real.exp (-(v * q)) * (q' + q * Real.exp v) := by
  have hkey : Real.exp (-(v * q)) * (q * Real.exp v) = q * Real.exp (v * q') := by
    rw [mul_comm (Real.exp (-(v * q))), mul_assoc, ← Real.exp_add]
    congr 2
    have : q' = 1 - q := by linarith
    rw [this]; ring
  rw [mul_add, hkey]
  ring

/-- **Two-sided Hoeffding for a centered Bernoulli increment.**

For a Bernoulli `X` with `P[X = 1] = p`, this is `E[exp (u (X - p))] ≤ exp (u²/8)`
for EVERY real `u`, both signs in one statement.

First leaf of the Lemma 14 urn chain: without-replacement concentration is
driven by the scaled centered count `M(r,t) = R/ν - r/t`, whose one-step
increment is a shifted Bernoulli `(X - p)/(t-1)`, so every later step — both
tails — factors through this with `u = λ/(t-1)`.  Settling the sign
bookkeeping here is what keeps the two-sided bound free of any negation of an
`ℝ≥0∞` potential. -/
theorem centered_bernoulli_mgf_le {p p' u : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hsum : p + p' = 1) :
    p * Real.exp (u * p') + p' * Real.exp (-(u * p))
      ≤ Real.exp (u ^ 2 / 8) := by
  have hp'₀ : 0 ≤ p' := by linarith
  have hp'₁ : p' ≤ 1 := by linarith
  have hsum' : p' + p = 1 := by linarith
  by_cases hu : u ≤ 0
  · -- `u ≤ 0`: Hoeffding at `t = -u ≥ 0`
    have ht : (0 : ℝ) ≤ -u := by linarith
    have hH := bernoulli_hoeffding hp₀ hp₁ hsum ht
    rw [centered_bernoulli_regroup p p' u hsum,
      show Real.exp u = Real.exp (-(-u)) by ring_nf]
    calc Real.exp (-(u * p)) * (p' + p * Real.exp (-(-u)))
        ≤ Real.exp (-(u * p)) * Real.exp (-p * (-u) + (-u) ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hH (Real.exp_nonneg _)
      _ = Real.exp (u ^ 2 / 8) := by rw [← Real.exp_add]; congr 1; ring
  · -- `u > 0`: the same bound with the two colours swapped, `t = u ≥ 0`
    push Not at hu
    have ht : (0 : ℝ) ≤ u := le_of_lt hu
    have hH := bernoulli_hoeffding hp'₀ hp'₁ hsum' ht
    have hswap := centered_bernoulli_regroup p' p (-u) hsum'
    have hL : p * Real.exp (u * p') + p' * Real.exp (-(u * p))
        = Real.exp (-(-u * p')) * (p + p' * Real.exp (-u)) := by
      rw [← hswap]
      rw [show -(-u * p') = u * p' by ring, show -u * p = -(u * p) by ring]
      ring
    rw [hL]
    calc Real.exp (-(-u * p')) * (p + p' * Real.exp (-u))
        ≤ Real.exp (-(-u * p')) * Real.exp (-p' * u + u ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hH (Real.exp_nonneg _)
      _ = Real.exp (u ^ 2 / 8) := by rw [← Real.exp_add]; congr 1; ring

/-- **The urn martingale identity, scalar form.**  With `a+1` red and `b+1`
blue remaining (total `a+b+2`), one reveal sends the red fraction to
`a/(a+b+1)` with mass `(a+1)/(a+b+2)` and to `(a+1)/(a+b+1)` with mass
`(b+1)/(a+b+2)`, and the expectation is exactly the current red fraction.

This is the whole reason Lemma 14 needs no trace layer: the red fraction is an
EXACT martingale and a function of the state alone.  Both branches land at the
same total `a+b+1`, so the identity is a single cancellation. -/
theorem urn_red_fraction_drift (a b : ℕ) :
    ((a + 1 : ℕ) : ℝ≥0∞) / ((a + b + 2 : ℕ) : ℝ≥0∞)
        * (((a : ℕ) : ℝ≥0∞) / ((a + b + 1 : ℕ) : ℝ≥0∞))
      + ((b + 1 : ℕ) : ℝ≥0∞) / ((a + b + 2 : ℕ) : ℝ≥0∞)
        * (((a + 1 : ℕ) : ℝ≥0∞) / ((a + b + 1 : ℕ) : ℝ≥0∞))
      = ((a + 1 : ℕ) : ℝ≥0∞) / ((a + b + 2 : ℕ) : ℝ≥0∞) := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hA : ((a : ℕ) : ℝ) + (b : ℕ) + 1 > 0 := by positivity
  have hB : ((a : ℕ) : ℝ) + (b : ℕ) + 2 > 0 := by positivity
  push_cast
  field_simp
  ring

/-- One reveal from an urn holding `a+1` red and `b+1` blue balls, on the
state `(red remaining, blue remaining)`.  Both successors have total
`a + b + 1`, so the total is a deterministic clock and no step index is
needed in the state. -/
noncomputable def urnInterior (a b : ℕ) : PMF (ℕ × ℕ) :=
  (productiveDirectionPMF (a + 1) (b + 1) (by omega)).map
    fun red => if red then (a, b + 1) else (a + 1, b)

/-- Exact two-atom expectation for one urn reveal. -/
theorem expect_urnInterior (a b : ℕ) (V : ℕ × ℕ → ℝ≥0∞) :
    expect (urnInterior a b) V =
      ((b + 1 : ℕ) : ℝ≥0∞) / (((a + 1 : ℕ) : ℝ≥0∞) + ((b + 1 : ℕ) : ℝ≥0∞))
          * V (a + 1, b)
        + ((a + 1 : ℕ) : ℝ≥0∞) / (((a + 1 : ℕ) : ℝ≥0∞) + ((b + 1 : ℕ) : ℝ≥0∞))
          * V (a, b + 1) := by
  rw [urnInterior, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up; cases up <;> simp]
  simp

/-- **The urn red-fraction martingale, kernel form.**  The red fraction
`r / (r + b)` is an exact martingale for the reveal kernel. -/
theorem urnInterior_redFraction_drift (a b : ℕ) :
    expect (urnInterior a b)
        (fun q => ((q.1 : ℕ) : ℝ≥0∞) / (((q.1 + q.2 : ℕ) : ℝ≥0∞)))
      = ((a + 1 : ℕ) : ℝ≥0∞) / ((a + b + 2 : ℕ) : ℝ≥0∞) := by
  rw [expect_urnInterior]
  have hden : (((a + 1 : ℕ) : ℝ≥0∞) + ((b + 1 : ℕ) : ℝ≥0∞))
      = ((a + b + 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
  rw [hden]
  have h1 : ((a + 1 + b : ℕ) : ℝ≥0∞) = ((a + b + 1 : ℕ) : ℝ≥0∞) := by
    push_cast; ring
  have h2 : ((a + (b + 1) : ℕ) : ℝ≥0∞) = ((a + b + 1 : ℕ) : ℝ≥0∞) := by
    push_cast; ring
  simp only [h1, h2]
  rw [add_comm]
  exact urn_red_fraction_drift a b

/-- The urn reveal chain on the state `(red remaining, blue remaining)`,
totalized by a self-loop on the empty urn.

Note this single definition covers the one-colour edges too: at `(r, 0)` the
direction law has red-mass `r/(r+0) = 1`, so the blue branch carries mass `0`
and its `ℕ`-truncated target is harmless. -/
noncomputable def urnChain : ℕ × ℕ → PMF (ℕ × ℕ) := fun q =>
  if h : 0 < q.1 + q.2 then
    (productiveDirectionPMF q.1 q.2 h).map
      fun red => if red then (q.1 - 1, q.2) else (q.1, q.2 - 1)
  else PMF.pure q

/-- On a live urn the chain is the two-atom interior kernel. -/
theorem urnChain_interior (a b : ℕ) :
    urnChain (a + 1, b + 1) = urnInterior a b := by
  unfold urnChain urnInterior
  rw [dif_pos (by omega : 0 < (a + 1) + (b + 1))]
  simp only [Nat.add_sub_cancel]

/-- **The urn clock.**  Every reveal from a nonempty urn drops the total by
exactly one.  This is what makes the total a deterministic clock, so the state
needs no step index and the tail argument needs no trace layer. -/
theorem urnChain_support_total (q : ℕ × ℕ) (hq : 0 < q.1 + q.2) :
    ∀ z, urnChain q z ≠ 0 → z.1 + z.2 + 1 = q.1 + q.2 := by
  intro z hz
  by_contra hzn
  apply hz
  unfold urnChain
  rw [dif_pos hq, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro red
  by_cases hmass : productiveDirectionPMF q.1 q.2 hq red = 0
  · simp [hmass]
  · have hne : z ≠ (if red then (q.1 - 1, q.2) else (q.1, q.2 - 1)) := by
      intro hEq
      apply hzn
      cases red with
      | true =>
          have h1 : q.1 ≠ 0 := by
            intro h0
            apply hmass
            rw [productiveDirectionPMF_true, h0]
            simp
          subst hEq; simp; omega
      | false =>
          have h2 : q.2 ≠ 0 := by
            intro h0
            apply hmass
            rw [productiveDirectionPMF_false, h0]
            simp
          subst hEq; simp; omega
    simp [hne]

/-- The variance accumulator of the urn martingale: `urnA n = ∑_{u<n} 1/(u+1)²`.

Indexed by the NUMBER of terms, so that the successor identity below is a bare
`Finset.sum_range_succ` and no ℕ-subtraction ever appears in a statement.  A
state with total `t` carries `urnA (t-1)`; its successors have total `t-1` and
carry `urnA (t-2)`, and the difference is exactly `1/(t-1)²` — which is exactly
the one-step Hoeffding cost `λ²/(8(t-1)²)` divided by `λ²/8`. -/
noncomputable def urnA (n : ℕ) : ℝ :=
  ∑ u ∈ Finset.range n, 1 / ((u : ℝ) + 1) ^ 2

@[simp] theorem urnA_zero : urnA 0 = 0 := by simp [urnA]

/-- Successor form — the ONLY way the accumulator is ever used. -/
theorem urnA_succ (n : ℕ) :
    urnA (n + 1) = urnA n + 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold urnA
  rw [Finset.sum_range_succ]

theorem urnA_nonneg (n : ℕ) : 0 ≤ urnA n := by
  unfold urnA
  exact Finset.sum_nonneg fun u _ => by positivity

theorem urnA_mono : Monotone urnA := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [urnA_succ]
  have : 0 ≤ 1 / ((n : ℝ) + 1) ^ 2 := by positivity
  linarith

/-- **The telescope.**  `urnA n + 2/(n+1)` is antitone, which is the
subtraction-free form of `urnA n - urnA m ≤ 2/(m+1) - 2/(n+1)`.

At `m = ν-s-1`, `n = ν-1` this is exactly the bound `ΔA ≤ 2s/(ν(ν-s))` the
scalar endgame needs.  The one-line reason is `1/(u+1)² ≤ 2/((u+1)(u+2))`,
i.e. `u+2 ≤ 2(u+1)`. -/
theorem urnA_add_tail_antitone {m n : ℕ} (hmn : m ≤ n) :
    urnA n + 2 / ((n : ℝ) + 1) ≤ urnA m + 2 / ((m : ℝ) + 1) := by
  induction n with
  | zero =>
      have : m = 0 := by omega
      subst this
      norm_num
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · have hmn' : m ≤ n := by omega
        refine le_trans ?_ (ih hmn')
        rw [urnA_succ]
        have hkey : 1 / ((n : ℝ) + 1) ^ 2 + 2 / ((n : ℝ) + 1 + 1)
            ≤ 2 / ((n : ℝ) + 1) := by
          rw [div_add_div _ _ (by positivity) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg ((n : ℝ) + 1), Nat.cast_nonneg (α := ℝ) n]
        push_cast
        linarith
      · have : m = n + 1 := by omega
        subst this
        exact le_rfl

/-- The urn potential exponent at the state `(r, b)` = (red remaining, blue
remaining):  `λ·(c₀ − r/(r+b)) + (λ²/8)·urnA (r+b−1)`.

`c₀` is abstract: the global centering `R/ν` cancels out of every one-step
increment, so the step lemma below never sees it and the assembly instantiates
it once.  The `r+b-1` is inside a definition, never inside a statement. -/
noncomputable def urnExp (c₀ lam : ℝ) (r b : ℕ) : ℝ :=
  lam * (c₀ - (r : ℝ) / ((r : ℝ) + (b : ℝ)))
    + lam ^ 2 / 8 * urnA (r + b - 1)

/-- **The one-step exponent inequality.**  At a live state with `a+1` red and
`b+1` blue, the two successor exponents weighted by the two reveal masses do
not exceed the current exponent.

This is leaf 1 at `u = λ/(t−1)` composed with the exact `urnA` telescoping, so
the contraction factor is `1` with no slack on either side. -/
theorem urn_exp_step (c₀ lam : ℝ) (a b : ℕ) :
    ((a : ℝ) + 1) / ((a : ℝ) + (b : ℝ) + 2)
        * Real.exp (urnExp c₀ lam a (b + 1))
      + ((b : ℝ) + 1) / ((a : ℝ) + (b : ℝ) + 2)
        * Real.exp (urnExp c₀ lam (a + 1) b)
      ≤ Real.exp (urnExp c₀ lam (a + 1) (b + 1)) := by
  have h1 : (0 : ℝ) < (a : ℝ) + (b : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (a : ℝ) + (b : ℝ) + 2 := by positivity
  set p : ℝ := ((a : ℝ) + 1) / ((a : ℝ) + (b : ℝ) + 2) with hp
  set p' : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + (b : ℝ) + 2) with hp'
  set u : ℝ := lam / ((a : ℝ) + (b : ℝ) + 1) with hu
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp'0 : 0 ≤ p' := by rw [hp']; positivity
  have hpp : p + p' = 1 := by
    rw [hp, hp']; field_simp; ring
  have hp1 : p ≤ 1 := by linarith
  -- the three `urnA` indices
  have hAr : (a + (b + 1) - 1 : ℕ) = a + b := by omega
  have hAb : (a + 1 + b - 1 : ℕ) = a + b := by omega
  have hAc : (a + 1 + (b + 1) - 1 : ℕ) = a + b + 1 := by omega
  have hAsucc : urnA (a + b + 1) = urnA (a + b) + 1 / ((a : ℝ) + (b : ℝ) + 1) ^ 2 := by
    rw [urnA_succ]
    congr 2
    push_cast
    ring
  -- each successor exponent, written against the current one
  have hred : urnExp c₀ lam a (b + 1)
      = urnExp c₀ lam (a + 1) (b + 1) + (u * p' - u ^ 2 / 8) := by
    unfold urnExp
    rw [hAr, hAc, hAsucc, hu, hp']
    push_cast
    field_simp
    ring
  have hblue : urnExp c₀ lam (a + 1) b
      = urnExp c₀ lam (a + 1) (b + 1) + (-(u * p) - u ^ 2 / 8) := by
    unfold urnExp
    rw [hAb, hAc, hAsucc, hu, hp]
    push_cast
    field_simp
    ring
  rw [hred, hblue]
  have hleaf := centered_bernoulli_mgf_le (p := p) (p' := p') (u := u) hp0 hp1 hpp
  calc p * Real.exp (urnExp c₀ lam (a + 1) (b + 1) + (u * p' - u ^ 2 / 8))
        + p' * Real.exp (urnExp c₀ lam (a + 1) (b + 1) + (-(u * p) - u ^ 2 / 8))
      = Real.exp (urnExp c₀ lam (a + 1) (b + 1)) * Real.exp (-(u ^ 2 / 8))
          * (p * Real.exp (u * p') + p' * Real.exp (-(u * p))) := by
        rw [Real.exp_add, Real.exp_add]
        have e1 : Real.exp (u * p' - u ^ 2 / 8)
            = Real.exp (-(u ^ 2 / 8)) * Real.exp (u * p') := by
          rw [← Real.exp_add]; congr 1; ring
        have e2 : Real.exp (-(u * p) - u ^ 2 / 8)
            = Real.exp (-(u ^ 2 / 8)) * Real.exp (-(u * p)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e1, e2]; ring
    _ ≤ Real.exp (urnExp c₀ lam (a + 1) (b + 1)) * Real.exp (-(u ^ 2 / 8))
          * Real.exp (u ^ 2 / 8) := by
        refine mul_le_mul_of_nonneg_left hleaf (by positivity)
    _ = Real.exp (urnExp c₀ lam (a + 1) (b + 1)) := by
        rw [mul_assoc, ← Real.exp_add]
        norm_num

/-- The `ℝ≥0∞` urn potential. -/
noncomputable def urnG (c₀ lam : ℝ) (q : ℕ × ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (urnExp c₀ lam q.1 q.2))

/-- Uniform two-atom expectation for the totalized chain, valid at every
nonempty urn including the one-colour edges (there the vanishing mass makes
the truncated successor harmless). -/
theorem expect_urnChain (r b : ℕ) (h : 0 < r + b) (V : ℕ × ℕ → ℝ≥0∞) :
    expect (urnChain (r, b)) V =
      (b : ℝ≥0∞) / ((r : ℝ≥0∞) + (b : ℝ≥0∞)) * V (r, b - 1)
        + (r : ℝ≥0∞) / ((r : ℝ≥0∞) + (b : ℝ≥0∞)) * V (r - 1, b) := by
  unfold urnChain
  rw [dif_pos h, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up; cases up <;> simp]
  simp

private theorem urn_mass_ofReal (k a b : ℕ) :
    ((k : ℕ) : ℝ≥0∞) / ((a + b + 2 : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((k : ℝ) / ((a : ℝ) + (b : ℝ) + 2)) := by
  have hcast : (a : ℝ) + (b : ℝ) + 2 = ((a + b + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- **The urn potential is a supermartingale** at every urn of total at least
two.

The `total ≤ 1` corner is genuinely excluded, not merely inconvenient: the last
reveal sends `(1,0)` to `(0,0)`, where the red fraction jumps from `1` to
`0/0 = 0`, so that step is not a supermartingale step for any `λ > 0`.  The
assembly avoids it by taking `s ≤ ν - 1`. -/
theorem urnG_step (c₀ lam : ℝ) (r b : ℕ) (hq : 2 ≤ r + b) :
    expect (urnChain (r, b)) (urnG c₀ lam) ≤ urnG c₀ lam (r, b) := by
  rw [expect_urnChain r b (by omega)]
  match r, b with
  | (a + 1), (c + 1) =>
      simp only [urnG, Nat.add_sub_cancel]
      have hden : ((a + 1 : ℕ) : ℝ≥0∞) + ((c + 1 : ℕ) : ℝ≥0∞)
          = ((a + c + 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
      rw [hden, urn_mass_ofReal (c + 1) a c, urn_mass_ofReal (a + 1) a c]
      have hp : (0 : ℝ) ≤ ((a : ℝ) + 1) / ((a : ℝ) + (c : ℝ) + 2) := by positivity
      have hp' : (0 : ℝ) ≤ ((c : ℝ) + 1) / ((a : ℝ) + (c : ℝ) + 2) := by positivity
      rw [show (((c + 1 : ℕ) : ℝ)) = (c : ℝ) + 1 by push_cast; ring,
        show (((a + 1 : ℕ) : ℝ)) = (a : ℝ) + 1 by push_cast; ring,
        ← ENNReal.ofReal_mul hp', ← ENNReal.ofReal_mul hp,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith [urn_exp_step c₀ lam a c])
  | (a + 1), 0 =>
      -- all red: the blue mass is zero, the red reveal is deterministic
      have hne : ((a + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
      simp only [urnG, Nat.cast_zero, ENNReal.zero_div, zero_mul, zero_add,
        add_zero, Nat.add_sub_cancel, ENNReal.div_self hne (ENNReal.natCast_ne_top _),
        one_mul]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      unfold urnExp
      have hA : urnA (a + 0 - 1) ≤ urnA a := urnA_mono (by omega)
      -- with no blue left the red fraction is 1 both before and after, so the
      -- linear term cancels EXACTLY and only `urnA` monotonicity is needed.
      -- (At `a = 0` it would not cancel — but then the total is 1, excluded.)
      have hapos : 0 < a := by omega
      have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
      have hfrac : (a : ℝ) / ((a : ℝ) + 0) = ((a : ℝ) + 1) / (((a : ℝ) + 1) + 0) := by
        rw [add_zero, add_zero, div_self (ne_of_gt ha),
          div_self (by positivity : ((a : ℝ) + 1) ≠ 0)]
      push_cast
      rw [hfrac]
      nlinarith [sq_nonneg lam, hA]
  | 0, (c + 1) =>
      have hne : ((c + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
      simp only [urnG, Nat.cast_zero, ENNReal.zero_div, zero_mul, add_zero,
        zero_add, Nat.add_sub_cancel, ENNReal.div_self hne (ENNReal.natCast_ne_top _),
        one_mul]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      unfold urnExp
      have hA : urnA (0 + c - 1) ≤ urnA (0 + (c + 1) - 1) := urnA_mono (by omega)
      push_cast
      simp only [zero_div]
      nlinarith [sq_nonneg lam, hA]
  | 0, 0 => omega

/-- The urn chain stopped once at most one ball remains.  Freezing there is
what makes the supermartingale step UNIFORM in the state, which is what
`expect_iter_le` requires; the assembly never actually reaches the frozen set,
because it runs only `s ≤ ν - 1` reveals. -/
noncomputable def urnStopped : ℕ × ℕ → PMF (ℕ × ℕ) :=
  freeze (fun z => z.1 + z.2 ≤ 1) urnChain

/-- The supermartingale step, now at EVERY state. -/
theorem urnG_step_stopped (c₀ lam : ℝ) (q : ℕ × ℕ) :
    expect (urnStopped q) (urnG c₀ lam) ≤ urnG c₀ lam q := by
  unfold urnStopped freeze
  by_cases h : q.1 + q.2 ≤ 1
  · rw [if_pos h, expect_pure]
  · rw [if_neg h]
    obtain ⟨r, b⟩ := q
    exact urnG_step c₀ lam r b (by simp at h; omega)

/-- **The iterated bound**, with contraction factor exactly `1`. -/
theorem urnG_iter_le (c₀ lam : ℝ) (T : ℕ) (q : ℕ × ℕ) :
    expect (iter urnStopped T q) (urnG c₀ lam) ≤ urnG c₀ lam q := by
  have h := expect_iter_le urnStopped (urnG c₀ lam) 1
    (fun s => by simpa using urnG_step_stopped c₀ lam s) T q
  simpa using h

/-- **The Markov tail.**  The mass of states whose potential has reached the
threshold `θ` after `T` reveals is at most `G(start)/θ`.  With
`θ = ofReal (exp (λ·θ₀ + κ))` this is the one-sided urn tail; the second tail
comes from the colour swap, i.e. from running the same bound at `-λ`. -/
theorem urnG_markov (c₀ lam : ℝ) (T : ℕ) (q : ℕ × ℕ)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (htop : θ ≠ ⊤) :
    ∑' z, (if θ ≤ urnG c₀ lam z then iter urnStopped T q z else 0)
      ≤ urnG c₀ lam q / θ := by
  refine le_trans (markov_div (iter urnStopped T q) (urnG c₀ lam) θ hθ htop) ?_
  exact ENNReal.div_le_div_right (urnG_iter_le c₀ lam T q) θ

/-- **The lambda optimisation.**  With variance budget `K > 0`, the exponent
`λ²/8·K − λ·θ₀` at `λ = 4θ₀/K` is exactly `−2θ₀²/K`.  An identity, not an
estimate: the optimum is attained. -/
theorem urn_lambda_opt (K θ₀ : ℝ) (hK : 0 < K) :
    (4 * θ₀ / K) ^ 2 / 8 * K - (4 * θ₀ / K) * θ₀ = -(2 * θ₀ ^ 2 / K) := by
  field_simp
  ring

/-- A SMALLER variance budget gives a better (more negative) exponent, so
bounding `ΔA` from above bounds the exponent from above — the direction the
telescope is used in. -/
theorem urn_exponent_mono (K K' θ₀ : ℝ) (hK : 0 < K) (hKK : K ≤ K') :
    -(2 * θ₀ ^ 2 / K) ≤ -(2 * θ₀ ^ 2 / K') := by
  have hK' : 0 < K' := lt_of_lt_of_le hK hKK
  have : 2 * θ₀ ^ 2 / K' ≤ 2 * θ₀ ^ 2 / K :=
    div_le_div_of_nonneg_left (by positivity) hK hKK
  linarith

/-- **The urn tail exponent reaches the paper's bound.**

With `θ₀ = D/(ν−s)` and the telescoped budget `ΔA ≤ 2s/(ν(ν−s))`, the optimised
exponent `2θ₀²/ΔA` equals `D²·ν/((ν−s)·s)`, which is at least `L/s = γ·lg ν`
whenever `L ≤ D²` — the slack being exactly the finite-population factor
`ν/(ν−s) ≥ 1`, which is why the without-replacement bound comes out STRONGER
than the paper's statement.

No `Real.sqrt` appears: `D` stands for `√(γ s lg ν)` and is constrained only by
`L ≤ D²`. -/
theorem urn_tail_exponent_ge (nu s L D : ℝ)
    (hs : 0 < s) (hgap : 0 < nu - s) (hL : 0 ≤ L) (hD : L ≤ D ^ 2) :
    L / s ≤ 2 * (D / (nu - s)) ^ 2 / (2 * s / (nu * (nu - s))) := by
  have hnu : 0 < nu := by linarith
  have hrhs : 2 * (D / (nu - s)) ^ 2 / (2 * s / (nu * (nu - s)))
      = D ^ 2 * nu / ((nu - s) * s) := by
    field_simp
  rw [hrhs, div_le_div_iff₀ hs (by positivity)]
  have hD0 : (0 : ℝ) ≤ D ^ 2 := le_trans hL hD
  have hpos : (0 : ℝ) < (nu - s) * s := mul_pos hgap hs
  calc L * ((nu - s) * s) ≤ D ^ 2 * ((nu - s) * s) :=
        mul_le_mul_of_nonneg_right hD hpos.le
    _ ≤ D ^ 2 * (nu * s) := by
        refine mul_le_mul_of_nonneg_left ?_ hD0
        have : (nu - s) ≤ nu := by linarith
        exact mul_le_mul_of_nonneg_right this hs.le
    _ = D ^ 2 * nu * s := by ring

section
variable {α : Type*}

/-- **Ville's maximal inequality, in the repo's frozen-chain idiom.**

For a nonnegative supermartingale `V` and any decidable `B` contained in the
superlevel set `{θ ≤ V}`, the probability of EVER entering `B` — over every
horizon at once — is at most `V(start)/θ`.

There is no circularity in letting `B` be defined by `V` itself: `freeze` takes
an arbitrary decidable predicate, and frozen states are `pure`, so `B` is
absorbing *syntactically*, regardless of what defines it.

The bound is IDENTICAL to the fixed-time Markov bound — the maximal version is
free.  `feller_ruin_u` is the special case `B = {level ≤ m}`, `V = u^level`,
`θ = u^m`. -/
theorem ville_frozen (K : α → PMF α) (B : α → Prop) [DecidablePred B]
    (V : α → ℝ≥0∞) (θ : ℝ≥0∞) (hθ : θ ≠ 0) (htop : θ ≠ ⊤)
    (hcontain : ∀ z, B z → θ ≤ V z)
    (hsuper : ∀ s, expect (K s) V ≤ V s)
    (q : α) :
    ⨆ T : ℕ, hitProb B K T q ≤ V q / θ := by
  refine iSup_le fun T => ?_
  have hrewrite : hitProb B K T q
      = ∑' z, (if B z then iter (freeze B K) T q z else 0) := by
    unfold hitProb expect ind
    congr 1; ext z
    by_cases hz : B z <;> simp [hz]
  rw [hrewrite]
  -- the frozen chain is still a supermartingale for `V`
  have hstep : ∀ s, expect (freeze B K s) V ≤ V s := by
    intro s
    unfold freeze
    by_cases hs : B s
    · rw [if_pos hs, expect_pure]
    · rw [if_neg hs]; exact hsuper s
  calc ∑' z, (if B z then iter (freeze B K) T q z else 0)
      ≤ ∑' z, (if θ ≤ V z then iter (freeze B K) T q z else 0) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : B z
        · rw [if_pos hz, if_pos (hcontain z hz)]
        · rw [if_neg hz]; simp
    _ ≤ expect (iter (freeze B K) T q) V / θ :=
        markov_div (iter (freeze B K) T q) V θ hθ htop
    _ ≤ V q / θ := by
        refine ENNReal.div_le_div_right ?_ θ
        have := expect_iter_le (freeze B K) V 1 (fun s => by simpa using hstep s) T q
        simpa using this

end

/-- **The two-tail union, from the SAME initial state.**

The lower tail needs no colour swap, no `PMF.map Prod.swap` equivariance layer,
and no swapped initial state — starting the chain at `(B, R)` would be a
DIFFERENT law from the one the event lives under, so a swapped-start theorem
could not be inserted into the union at all.

Instead: every lemma in the chain — `centered_bernoulli_mgf_le`,
`urn_exp_step`, `urnG_step_stopped`, `urnG_iter_le`, `urnG_markov` — is valid
for EVERY real `lam`, because leaf 1 was proved for every real `u`.  So the two
tails are the same theorem instantiated at `lam` and at `-lam`, from the same
start.  That is why leaf 1 was stated two-sided in the first place. -/
theorem urnG_two_tail (c₀ lam : ℝ) (T : ℕ) (q : ℕ × ℕ)
    (thP thM : ℝ≥0∞) (hthP : thP ≠ 0) (htP : thP ≠ ⊤)
    (hthM : thM ≠ 0) (htM : thM ≠ ⊤) :
    (∑' z, (if thP ≤ urnG c₀ lam z then iter urnStopped T q z else 0))
      + (∑' z, (if thM ≤ urnG c₀ (-lam) z then iter urnStopped T q z else 0))
      ≤ urnG c₀ lam q / thP + urnG c₀ (-lam) q / thM :=
  add_le_add (urnG_markov c₀ lam T q thP hthP htP)
    (urnG_markov c₀ (-lam) T q thM hthM htM)

/-- Both tails at a common bound: if each Markov ratio is at most `ε`, the two
tails together are at most `2ε`. -/
theorem urnG_two_tail_le (c₀ lam : ℝ) (T : ℕ) (q : ℕ × ℕ)
    (thP thM ε : ℝ≥0∞) (hthP : thP ≠ 0) (htP : thP ≠ ⊤)
    (hthM : thM ≠ 0) (htM : thM ≠ ⊤)
    (hgP : urnG c₀ lam q / thP ≤ ε) (hgM : urnG c₀ (-lam) q / thM ≤ ε) :
    (∑' z, (if thP ≤ urnG c₀ lam z then iter urnStopped T q z else 0))
      + (∑' z, (if thM ≤ urnG c₀ (-lam) z then iter urnStopped T q z else 0))
      ≤ 2 * ε := by
  refine le_trans (urnG_two_tail c₀ lam T q thP thM hthP htP hthM htM) ?_
  rw [two_mul]
  exact add_le_add hgP hgM

/-- At the centred start the potential collapses: `urnG c₀ lam (R, B) =
ofReal (exp (λ²/8 · urnA (R+B−1)))` whenever `c₀` is exactly the initial red
fraction.  This is what removes the `w^{count s₀}` residue that a `count_tail`
route would have carried. -/
theorem urnG_centered_start (lam : ℝ) (R B : ℕ) :
    urnG ((R : ℝ) / ((R : ℝ) + (B : ℝ))) lam (R, B)
      = ENNReal.ofReal (Real.exp (lam ^ 2 / 8 * urnA (R + B - 1))) := by
  unfold urnG urnExp
  norm_num

end Tri

#print axioms Tri.centered_bernoulli_mgf_le
#print axioms Tri.urn_red_fraction_drift
#print axioms Tri.expect_urnInterior
#print axioms Tri.urnInterior_redFraction_drift
#print axioms Tri.urnChain_interior
#print axioms Tri.urnChain_support_total
#print axioms Tri.urnA_succ
#print axioms Tri.urnA_mono
#print axioms Tri.urnA_add_tail_antitone
#print axioms Tri.urn_exp_step
#print axioms Tri.expect_urnChain
#print axioms Tri.urnG_step
#print axioms Tri.urnG_step_stopped
#print axioms Tri.urnG_iter_le
#print axioms Tri.urnG_markov
#print axioms Tri.urn_lambda_opt
#print axioms Tri.urn_exponent_mono
#print axioms Tri.urn_tail_exponent_ge
#print axioms Tri.ville_frozen
#print axioms Tri.urnG_two_tail
#print axioms Tri.urnG_two_tail_le
#print axioms Tri.urnG_centered_start

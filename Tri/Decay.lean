/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Geometric decay of a potential along a finite-horizon chain

This is the generic engine the whole analysis runs on, and it is deliberately
free of any Markov-chain, martingale or measure-theoretic machinery.

The design invariant for this development is:

> every probabilistic statement is about a terminal state of an explicitly
> constructed finite kernel, proved by induction on the horizon over sums, with
> Markov's inequality as the only measure-theoretic tool. No stopping times, no
> Doob, no conditional expectation.

`expect_iter_le` is that invariant made precise: a pointwise one-step
contraction `E_{K s}[V] ≤ c · V s` iterates to `E_{K^T s}[V] ≤ c^T · V s`. Since
`c` and `V` are arbitrary, this single lemma serves both engines of the
analysis — the safety (ruin) potential and the progress potential — which the
design requires to be run with *different* bases; see `design/08-cancellation.md`
for why sharing one base makes the resulting bound vacuous.

`markov` is the only other tool needed: it converts a bound on the expected
potential into a bound on the probability that the potential is large, which is
how every phase lemma reaches a probability statement.

Everything lives in `ℝ≥0∞`, and every statement is an upper bound on a bad
event, so no truncated subtraction is ever needed.

## Main results

* `expect_pure`, `expect_bind'`/`expect_bind` — the structural identities.
* `expect_map` — pushing a potential through `PMF.map`.
* `expect_iter_le` — geometric decay over a deterministic horizon.
* `markov` — Markov's inequality for a `PMF`, in tsum form.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- The expectation of a nonnegative potential under a `PMF`. Kept in `ℝ≥0∞` so
that no integrability side condition is ever required. -/
noncomputable def expect (p : PMF α) (V : α → ℝ≥0∞) : ℝ≥0∞ := ∑' z, p z * V z

@[simp] theorem expect_pure (s : α) (V : α → ℝ≥0∞) : expect (PMF.pure s) V = V s := by
  unfold expect
  rw [tsum_eq_single s (by intro b hb; simp [PMF.pure_apply, if_neg hb])]
  simp

/-- **The tower identity for `bind`.** This is the definitional Markov property,
and it is the only "probability theory" the composition of stages needs.

Stated heterogeneously (the kernel may land in a different type) because the
success-counting chain is built by `PMF.map`, which needs exactly that. -/
theorem expect_bind' {β : Type*} (p : PMF α) (f : α → PMF β) (V : β → ℝ≥0∞) :
    expect (p.bind f) V = ∑' a, p a * expect (f a) V := by
  unfold expect
  have h1 : ∀ z, (p.bind f) z * V z = ∑' a, p a * (f a z * V z) := by
    intro z
    rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
    congr 1; ext a; ring
  simp only [h1]
  rw [ENNReal.tsum_comm]
  congr 1; ext a
  rw [ENNReal.tsum_mul_left]

/-- The endomorphic case, which is what the iteration lemma uses. -/
theorem expect_bind (p : PMF α) (f : α → PMF α) (V : α → ℝ≥0∞) :
    expect (p.bind f) V = ∑' a, p a * expect (f a) V :=
  expect_bind' p f V

/-- Pushing a potential through `PMF.map`: the expectation of `V` under the
image is the expectation of `V ∘ f`. -/
theorem expect_map {β : Type*} (p : PMF α) (f : α → β) (V : β → ℝ≥0∞) :
    expect (p.map f) V = expect p (fun a => V (f a)) := by
  rw [PMF.map, expect_bind']
  simp only [Function.comp_apply, expect_pure]
  rfl

/-- The `T`-fold iterate of a one-step kernel. Horizons are deterministic
throughout this development, which is what keeps composition to the trivial
`K^(a+b) = K^a ∘ K^b` and avoids stopping times entirely. -/
noncomputable def iter (K : α → PMF α) : ℕ → α → PMF α
  | 0 => PMF.pure
  | n + 1 => fun s => (K s).bind (iter K n)

@[simp] theorem iter_zero (K : α → PMF α) : iter K 0 = PMF.pure := rfl

theorem iter_succ (K : α → PMF α) (n : ℕ) (s : α) :
    iter K (n + 1) s = (K s).bind (iter K n) := rfl

/-- **Geometric decay.** A pointwise one-step contraction of the potential
iterates to a contraction over the whole horizon.

This is the workhorse: instantiated with the harmonic base it gives the safety
(ruin) bound, and with a progress tilt it gives the deadline bound. Note the
hypothesis is required at *every* state, which in use is arranged by freezing
the chain outside the live region so that frozen states satisfy it trivially. -/
theorem expect_iter_le (K : α → PMF α) (V : α → ℝ≥0∞) (c : ℝ≥0∞)
    (hK : ∀ s, expect (K s) V ≤ c * V s) :
    ∀ T s, expect (iter K T s) V ≤ c ^ T * V s := by
  intro T
  induction T with
  | zero => intro s; simp
  | succ t ih =>
    intro s
    rw [iter_succ, expect_bind]
    calc ∑' a, (K s) a * expect (iter K t a) V
        ≤ ∑' a, (K s) a * (c ^ t * V a) :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_right (ih a) _
      _ = c ^ t * ∑' a, (K s) a * V a := by
          rw [← ENNReal.tsum_mul_left]; congr 1; ext a; ring
      _ ≤ c ^ t * (c * V s) := mul_le_mul_right (hK s) _
      _ = c ^ (t + 1) * V s := by ring

/-- **Markov's inequality**, in the tsum form this development uses. The only
measure-theoretic tool the design permits: it is what turns a bound on the
expected potential into a bound on a probability. -/
theorem markov (p : PMF α) (V : α → ℝ≥0∞) (θ : ℝ≥0∞) :
    θ * ∑' z, (if θ ≤ V z then p z else 0) ≤ expect p V := by
  unfold expect
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : θ ≤ V z
  · simp only [if_pos hz]
    rw [mul_comm θ (p z)]
    exact mul_le_mul_right hz _
  · simp [if_neg hz]

/-- The form used at call sites: if the potential is at least `θ` on the bad
set, the bad set has probability at most `E[V]/θ`. -/
theorem markov_div (p : PMF α) (V : α → ℝ≥0∞) (θ : ℝ≥0∞) (hθ : θ ≠ 0) (htop : θ ≠ ⊤) :
    ∑' z, (if θ ≤ V z then p z else 0) ≤ expect p V / θ := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hθ) (Or.inl htop), mul_comm]
  exact markov p V θ

end Tri

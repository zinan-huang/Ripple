# Experiment 04 — Brusselator

## System

Two-species autocatalytic chemical oscillator (Prigogine & Lefever,
1968):

    x₁' = A + x₁² x₂ − (B + 1) x₁,
    x₂' = B x₁ − x₁² x₂,
    x₁(0) = x₂(0) = 0.

Parameters `A, B > 0`. Fixed point `(x₁*, x₂*) = (A, B/A)`.
Stability: Hopf bifurcation at `B = 1 + A²`. For `B > 1 + A²`,
stable limit cycle around `(A, B/A)`.

Zero init is not a fixed point (because of constant source `A`), so
we don't need a bias term here — Brusselator is a *natural*
zero-init bounded GPAC.

## Properties

- **Native CRN structure.** Species stay non-negative by construction
  (at `x₁ = 0`: `x₁' = A > 0`; at `x₂ = 0`: `x₂' = B x₁ ≥ 0`).
- **Degree 3** (the autocatalytic term `x₁² x₂`).
- **All coefficients non-negative monomial-wise** except the
  degradation `−(B+1) x₁` and `−x₁² x₂`.
- **Sign-definite species.** Since `x_i ≥ 0`, the minimal dual-rail
  representation has `v_i = 0, u_i = x_i`. This is a **qualitatively
  different** test from experiments 02, 03 where `x_i` changes sign.

## GPAC / dual-rail

Positive monomials go to `u'`; negative (the degradations) go to the
annihilation. Let me write `x_i = u_i − v_i` but expect `v_i ≈ 0`.

Expand `x₁² x₂ = (u₁ − v₁)²(u₂ − v₂)`:

    x₁² x₂ = u₁² u₂ − u₁² v₂ − 2u₁ v₁ u₂ + 2u₁ v₁ v₂
           + v₁² u₂ − v₁² v₂.

Monomial sign split per species:

    p₁ = A + x₁² x₂ − (B+1) x₁
       → p̂₁⁺ = A + (+terms of x₁² x₂) + (B+1) v₁
       → p̂₁⁻ = (−terms of x₁² x₂, taken positive) + (B+1) u₁
    where
       +terms of x₁² x₂: u₁² u₂, 2u₁ v₁ v₂, v₁² u₂
       −terms (abs val): u₁² v₂, 2u₁ v₁ u₂, v₁² v₂

    p₂ = B x₁ − x₁² x₂
       → p̂₂⁺ = B u₁ + (−terms of x₁² x₂, taken positive)
             = B u₁ + u₁² v₂ + 2u₁ v₁ u₂ + v₁² v₂
       → p̂₂⁻ = B v₁ + (+terms of x₁² x₂)
             = B v₁ + u₁² u₂ + 2u₁ v₁ v₂ + v₁² u₂

## Hypothesis

Because `x_i` never changes sign, we expect `v_i → 0` quickly — the
negative rail has only small seed mass. The annihilation `k·u_i·v_i`
has small `v_i` factor, so it provides weak drain. On the other hand
production into `v_i` also has only small factors. **Prediction:** the
system stays on the slow manifold `v_i ≈ 0` easily, and constant-k
is bounded at small k.

Different from 02, 03: no rail-swapping needed. Should be the easiest
oscillator test.

## Why this system

Completes the "native CRN" side of the test matrix: where experiments
02, 03 tested sign-changing oscillation, this tests non-negative
oscillation. If constant-k *fails* even here, we'd have a strong
counterexample. If it works easily, confirms intuition about why the
hard case is sign-changing species.

# Experiment 04 Notes — Brusselator

Date: 2026-04-18

## Setup

Original:  `x₁' = A + x₁² x₂ − (B+1) x₁,  x₂' = B x₁ − x₁² x₂`,
zero init. Classic limit-cycle regime `B > 1 + A²`.

Zero init is *not* a fixed point (source term `A`), so no bias needed.
Native CRN, non-negative species.

Configs tested: (A, B) ∈ {(1, 3), (1, 5), (2, 6)}, k ∈ {0.01, 0.1, 1,
10, 100, 1000}.

## Results

Peak u₁, v₁ over T = 40. Original max x₁, x₂ for reference.

| (A, B) | Orig (max x₁, x₂) | k | max u₁ | max v₁ | max u₂ | max v₂ | status |
|--------|-------------------|---|--------|--------|--------|--------|--------|
| (1, 3) | (3.77, 4.74) | 0.01 | 12.2 | 12.0 | 11.6 | 11.3 | ✗ blowup |
| (1, 3) |              | 0.1  | 6.0  | 5.8  | 5.4  | 5.1  | ✗ blowup |
| (1, 3) |              | 1    | 13.9 | 13.7 | 13.5 | 13.2 | ✗ blowup |
| (1, 3) |              | 10   | 6.2  | 5.9  | 7.6  | 4.8  | ✗ blowup |
| (1, 3) |              | 100  | 3.82 | **0.047** | 4.74 | **0.147** | ✓ |
| (1, 3) |              | 1000 | 3.77 | 0.004 | 4.74 | 0.014 | ✓ tightest |
| (1, 5) | (9.5, 10.1)  | ≤10  | 5–6 | 5–6 | 5–7 | 5–6 | ✗ blowup |
| (1, 5) |              | 100  | 9.66 | 0.157 | 10.1 | 0.95 | ✓ |
| (1, 5) |              | 1000 | 9.51 | 0.007 | 10.1 | 0.09 | ✓ tighter |
| (2, 6) | (7.0, 7.39)  | ≤10  | 7–10 | 6–10 | 6–10 | 6–10 | ✗ blowup |
| (2, 6) |              | 100  | 7.11 | 0.110 | 7.40 | 0.515 | ✓ |
| (2, 6) |              | 1000 | 7.01 | 0.007 | 7.39 | 0.049 | ✓ tighter |

All blow-ups show LSODA step-collapse warnings.

## Observations

1. **Non-negativity of original species doesn't automatically help the
   dual-rail.** Constant-k threshold around k* ≈ 100, same ballpark as
   Hopf (experiment 03). I had hypothesized it would work at smaller k
   because no rail-swapping is needed — that was wrong.

2. **Steady-state negative rail `v₁* ≈ (B+1)/k`.** At k = 100, B = 3:
   predicted v₁* ≈ 4/100 = 0.04. Measured max v₁ = 0.047. Very close.
   This is the *spurious* mass on the negative rail, driven by the
   degradation term. At k = 10, predicted v₁* ≈ 0.4, but positive
   feedback (big v₁ feeds u₁ back via `(B+1)·v₁` term in `p̂₁⁺`)
   amplifies it — blow-up.

3. **At large k, dual-rail is nearly minimal.**
   - u₁ → x₁, v₁ → (B+1)/k → 0.
   - u₂ → x₂, v₂ → pos_x₁²x₂/k → 0 at slow rate.
   Tracking quality scales as 1/k.

4. **The k-threshold is coefficient-dominated, not frequency-dominated.**
   - Brusselator `B + 1`, `B` coefficients ≈ 4–6.
   - Hopf unit coefficients × ω ∈ [1, 100].
   - Van der Pol μ coefficient ∈ [1, 20].
   Yet all three have k* ≈ 10–100. The coefficient magnitude in the
   polynomial matters more than ω, and there's a floor around 10 that
   even small-coefficient systems have.

## Conclusion

**Not a counterexample.** For each (A, B) in the limit-cycle regime,
k ≥ 100 bounds the dual-rail and tracks the original up to 1/k error.
Small k blows up.

The "native CRN non-negative" intuition that this would be *easier*
than sign-changing oscillators (02, 03) did not pan out. The dual-rail
transformation introduces a spurious negative rail from the degradation
term `−(B+1)·x₁` becoming `+(B+1)·u₁` in `p̂₁⁻`, and this creates an
annihilation-dependent pathology that looks a lot like the sign-changing
case.

## k → ∞ behaviour

On the slow manifold `v_i · k = p̂_i⁻(u, 0)` (quasi-steady-state for v):
- `v₁* = ((B+1) u₁) / (k u₁) = (B+1) / k` (when u₁ > 0 dominates)
- `v₂* = pos_x₁²x₂ / (k u₂)` ≈ (u₁² u₂) / (k u₂) = u₁²/k

Substituting into u_i' gives the original p_i(x) dynamics to leading
order. Standard Tikhonov picture.

## Caveats

- Blow-up vs "huge bounded" not distinguished rigorously — LSODA
  step-collapse is the signal.
- Tested only limit-cycle regime. Sub-critical B might test the
  fixed-point approach.

## Files

- `system.md` — system + dual-rail derivation
- `run.py` — simulation
- `original_A=*_B=*.png`, `dualrail_A=*_B=*_k=*.png`, `k_sweep.png`
- `summary.txt`

## Next

Experiment 05: multi-species with one exponentially-growing internal
variable but bounded output — try to construct a case where the
*internal* dual-rail species is large even though the output is small.
This is the Bournez-Pouly motivation.

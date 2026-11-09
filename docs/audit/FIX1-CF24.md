# CF'24 readout from the canonical initial condition

Paper: the PP-to-NAP note (PP to NAP via the cubing construction, CF'24 worked example) and
its errata.

## 1. The paper's claim and the Lean statements

Paper, §1–§2 and §4 (eq. 1–3) and §10: the CF'24 PP on the simplex
`z00 + z01 + z11 = 1`,

    ż00 = −2 z00² + 7 z00 z01 − 2 z00 z11
    ż01 =  2 z00² − 8 z00 z01 + 16 z00 z11 − z01 z11
    ż11 =  z00 z01 − 14 z00 z11 + z01 z11

started at the canonical initial condition `(z00, z01, z11) = (1, 0, 0)` (§1: "at the initial
condition (1, 0, 0) there is simply no room"; §2.2; §5 uses `r(0) = u(0) = 1/2`,
`z01(0) = z11(0) = 0`; §9 the NAP initial condition `v1 = 1/8, v2 = 3/8, v5 = 3/8, v11 = 1/8`),
has readout `z11 + z01/2 → (3 − √5)/6`. The λ-trick (Prop. 11.4), the r²-trick (Prop. 11.5)
and the cubing (Thm 11.2) keep the limit. The paper supports the limit by simulation (§12),
not by a proof.

Lean before (r2026.11):
- `cf24_step5_readout_of_basinEntry` and `cf24_{lambda,r2,nap20}_lifted_readout_of_basinEntry`:
  hypothesis `Cf24BasinEntry` (every interior initial point enters `V < 1/512`), refuted in the
  same file (`cf24_basinEntry_false`, the saddle point). **V.**
- `cf24_step5_readout_of_saddleExcludedBasinEntry` and the three lifts: hypothesis
  `Cf24SaddleExcludedBasinEntry` (every interior point off the saddle's stable manifold enters
  the sharp basin), never proved. **C.** Also: these are about interior initial points, while
  the paper's initial point `(1, 0, 0)` is on the boundary.

Lean after (`Ripple/LPP/CF24Canonical.lean`), no hypotheses:
- `cf24_readout_canonical`: along the global trajectory from `canonicalInit = (1, 0, 0)`,
  `z11 + z01/2 → readoutLimit = (3 − √5)/6`.
- `cf24_lambda_readout_canonical` (λ-trick embedding), `cf24_r2_readout_canonical` (time change
  `τ` with `τ 0 = 0`, `τ ≥ 0`, `τ → ∞`, the reparametrized orbit solves the r²-trick field,
  readout limit kept), `cf24_nap20_readout_canonical` (the cubed lift `w` of the
  reparametrized orbit starts at the cubed lift of `(1/2, 1/2, 0, 0)`
  (`cf24LambdaEmbed_canonicalInit`), solves the NAP system `ẇ = napField w` for `s > 0`, and
  `Σ readoutCoeff i · w i` tends to the same limit). The derivative at `s = 0` (one-sided) is
  not stated: the cubed-lift chain rule exists only in `HasDerivAt` form.
- `cf24_canonical_basin_entry`, `lyapunovDeriv_le_of_annulus`: the analytic step (§2 below).

The `…_of_basinEntry` theorems are deleted (false hypothesis). The `…_of_saddleExcludedBasinEntry`
theorems stay as conditional lemmas, removed from the roots; the global statement (every
interior point off the stable manifold) is not a claim of the paper and is recorded in
`OPEN_PROBLEMS.md` §6.3.

## 2. Proof of basin entry from (1, 0, 0)

Notation: `b = z01`, `c = z11`, `a = z00 = 1 − b − c`; fixed point `b* = 2/9`,
`c* = (7 − 3√5)/18`; `u = b − b*`, `v = c − c*`; `V = u² + v²` (`lyapunov`);
`V̇ = lyapunovDeriv = 2u ḃ + 2v ċ`. On the simplex (`lyapunovDeriv_on_simplex`, already proved)

    V̇ = Q(u, v) + 20u³ − 12u²v + 28v³,
    Q(u, v) = ((−57 + 5√5)/3) u² + (2(18 + 7√5)/3) uv − (28√5/3) v².

`V0 := V(1, 0, 0) = b*² + c*² ≈ 0.049646`. The sharp basin of the existing bridge
`cf24_readout_tendsto_from_sharp_lyapunov_init` is `0 < V < θ`, `θ = (13 − 4√5)²/784 ≈ 0.020981`.

**Lemma A (annulus bound).** If `a, b, c ≥ 0`, `a + b + c = 1` and `1/48 ≤ V ≤ V0`, then
`V̇ ≤ −1/20`.

Proof. Bounds `2.23606 ≤ √5 ≤ 2.23607`. Then:
1. `Q(u, v) ≤ −15.27u² + 22.435uv − 20.86v² + 0.0002(u² + v²)` (`lyapunovQuad_le_rat`): the
   difference is `(5/3)(2.23607 − √5)u² + (28/3)(√5 − 2.23606)v² + c·uv` plus the constant
   slack `≈ 0.003417u² + 0.010093v²` (which already includes the `+0.0002(u² + v²)`), with
   `c = 10.435 − (14/3)√5 ∈ [6.7·10⁻⁶, 5.4·10⁻⁵]` and
   `c·uv = (c/4)((u+v)² − (u−v)²) ≥ −1.4·10⁻⁵ (u−v)²`; all terms are products of the `√5`
   bounds with squares, so the inequality is linear in them. (Exact certificate from the
   `nlinarith` hints, found by the reviewer: `11·b v² + 2·a(u+v)² + (1/3)·b(u−v)² +
   (333/50000)v² + (171/100000)(u+v)² + (511/300000)(u−v)²`, `a = 2.23607 − √5`,
   `b = √5 − 2.23606`.)
2. Constraints in `(u, v)`: `u ≥ −2/9` (b ≥ 0); `v ≥ −c* ≥ −0.01623` (c ≥ 0);
   `u + v = 1 − a − b* − c* ≤ 0.7617` (a ≥ 0); `1/48 ≤ u² + v² ≤ V0 ≤ 0.04965`.
3. On this region the rational cubic `P(u, v) = −15.27u² + 22.435uv − 20.86v² +
   0.0002(u²+v²) + 20u³ − 12u²v + 28v³` satisfies `P ≤ −1/20` (`annulus_poly`). Certificate
   (found by linear programming over products of the constraints; Lean's `linarith` recomputes
   exact coefficients from the listed products): with `l0 = u + 2/9`, `l1 = v + 0.01623`,
   `l2 = 0.7617 − u − v`, `q0 = u² + v² − 1/48`, `q1 = 0.04965 − u² − v²`,

       −1/20 − P = 1.155 l0 q1 + 0.707 l1 q1 + 7.373 l2 q0 + 0.038 l1 l2² + 0.121 l2³ + 0.972 u²
                   + 0.975 l1 (u − v/4)² + 0.702 l1 (u − v/2)² + 7.950 l2 (u − 5v/4)²
                   + 3.401 l2 (u − 3v/2)²

   (coefficients rounded; each term is nonnegative on the region). Numerically the maximum of
   the exact `V̇` on the annulus is about −0.100 (grid search, 1500² points).
∎

**Lemma B (entry).** The trajectory `x(t)` from `(1, 0, 0)` satisfies `V(x(t)) ≤ V0 − t/40`
for `t ∈ [0, T]`, `T = 40(V0 − 1/48)`; hence `V(x(T)) ≤ 1/48 < θ`, and some `t₀ ∈ [0, T]` has
`0 < V(x(t₀)) < θ`.

Proof. `x(t)` stays in the closed simplex (`pivp_solution_nonneg`,
`conservative_trajectory_simplex`). Barrier comparison
(`image_le_of_deriv_right_lt_deriv_boundary'`) with `B(t) = V0 − t/40`: at a time
`t ∈ [0, T)` where `V(x(t)) = B(t)`, `V(x(t)) ∈ [1/48, V0]`, so Lemma A gives
`V̇ ≤ −1/20 < −1/40 = B'`. At `T`: `V ≤ 1/48`, and `1/48 < θ` (from `√5 ≤ 2.23607`). If
`V(x(T)) > 0` take `t₀ = T`; otherwise the intermediate value theorem gives `t₀` with
`V(x(t₀)) = 1/96`. ∎

Then `cf24_readout_of_sharp_entry` (the body of the existing
`cf24_step5_readout_of_saddleExcludedBasinEntry`, with the entry time as an argument) gives
the readout limit. Numerically the trajectory enters the sharp basin at `t ≈ 0.052`; the
bound `T ≈ 1.15` is crude but sufficient.

## 3. Lifts

λ-trick: `cf24Lambda_readout_tendsto` (existing). r²-trick: the existing time change
`cf24_tau` and its lemmas need only `z00(0) > 0` (true at `(1, 0, 0)`); the old wrapper
`Cf24R2Reparam` additionally asked for interior initial points, which is why the canonical
statement uses the lemmas directly. NAP-20: `readout_eq_z11_plus_half_z01` on the 4-simplex.

## 4. Independent review

One reviewer (2026-11-08), against the paper and the code. Verdicts: §1 OK
(the paper names only `(1, 0, 0)`; nothing is claimed for interior points; the transfer
results 11.4/11.5 are conditional and already general in Lean); Lemma A OK (identity checked
to 1e-15; exact `V̇` maximum on the annulus −0.1003 on a 3000² grid; rational cubic ≤ −0.1002;
an exact rational LP vertex certificate exists); Lemma B OK (simulation: entry at t ≈ 0.0515,
barrier never crossed, readout at t = 60 equal to `(3 − √5)/6` to 1e-14); deletions OK
(no other users; nothing faithful lost). Adopted: the step-1 slack text (corrected above);
the NAP-20 statement strengthened (it previously kept only `τ → ∞`, which `τ = id`
satisfies; it now states the NAP dynamics and the initial value). The three beta-redex `rw`
failures the reviewer predicted were found by the first compile and fixed. Not adopted:
stating the theorems for every solution rather than the chosen `cf24_global_solution` (the
solution is unique by local Lipschitz continuity; the chosen one is the object of the paper).

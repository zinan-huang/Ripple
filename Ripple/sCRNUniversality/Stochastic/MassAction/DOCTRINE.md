# Automode Doctrine — rawLaw_coord_complement (last sorry)

## Goal

Prove `rawLaw_coord_complement`: the Ionescu-Tulcea marginal at coordinate (t+1) bounds the mass-action PMF complement. This is the LAST sorry in the entire MassActionRaceLaw construction.

## Avenues

### (a) Direct Ionescu-Tulcea marginal extraction via map_traj_succ_self

Use `Kernel.map_traj_succ_self` to show the pushforward of `traj κ t` along coordinate `t+1` equals `stepKernel t`. Then:
- `rawLaw = trajFun κ 0 initial`
- Decompose via `traj_comp_partialTraj`: `traj 0 = partialTraj 0 t ⊗ₖ traj t`
- Push forward `traj t` along coord `t+1` → `stepKernel t`
- Under `hstate`, all prefixes give the same state z → `stepKernel t p = massActionPMF(z).toMeasure`
- Bound: `rawLaw {ω | ω(t+1) ≠ some i} ≤ massActionPMF(z).toMeasure {o ≠ some i}`

Terminal: compiles with 0 sorry, or concrete Lean error showing the Mathlib API shape doesn't match.

### (b) Outer measure upper bound via cylinder covering

Instead of extracting the exact marginal, use the outer measure property:
- `rawLaw E ≤ ∑' (covering cylinders)`
- The relevant cylinder at depth t+1 projects to `massActionPMF(z).toMeasure {o ≠ some i}`
- This avoids needing the full marginal decomposition

Terminal: compiles, or shows cylinder API doesn't exist in Mathlib v4.30.

### (c) Direct probability bound via IsProbabilityMeasure + complement

Since `rawLaw` is a probability measure:
- `rawLaw {ω | ω(t+1) = some i} + rawLaw {ω | ω(t+1) ≠ some i} ≤ 1`
- If we can lower-bound `rawLaw {ω | ω(t+1) = some i} ≥ jumpProbAt(z, i)`, we get the complement bound
- This might be easier than extracting the exact marginal

Terminal: compiles, or shows the lower bound path is equally hard.

### (d) Factor through finite-prefix PMF + monotone convergence

Define the bound at finite prefix level using `prefixPMF` (product of step PMFs), then lift to `rawLaw` via the projective limit property `isProjectiveLimit_trajFun`.

Terminal: compiles, or shows projective limit API is too opaque.

## Fallback

If all avenues fail: leave this one sorry with full documentation of what was tried and why each failed. The sorry is well-scoped (pure measure-theory, no mathematical content gap) and can be attacked with a dedicated Mathlib PR or manual Carathéodory argument later.

## Notes

- The subagent for this sorry is currently running. Wait for its result before starting.
- Key Mathlib files: `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`
- Key project files: `Traj.lean` (rawLaw, stepKernel), `Weights.lean` (massActionPMF)

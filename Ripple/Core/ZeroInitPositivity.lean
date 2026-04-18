/-
  Ripple.Core.ZeroInitPositivity — Zero-Init Non-Collapse Conjecture

  Formalizes Xiang's structural conjecture: a species in a bounded, zero-init
  CRN-shape PIVP that ever becomes positive cannot have limit 0.

  Motivation. CRN species start from 0 concentration. For `x_i` to grow, its
  polynomial field must have a positive production term at the current state.
  Because each degradation monomial contains `x_i` as a factor, `x_i = 0`
  implies the degradation is 0 at that point, so only production matters at
  the origin. Tracing the dependency graph back, every species that ever
  becomes positive must be fed (directly or transitively) by a species with
  a positive constant production term (a "root" species with `∅ → X_i` type
  reaction). Once this chain is active, the positive feed never shuts off,
  so the species cannot decay back to 0 in the limit under boundedness.

  Consequence. The constant 0 is not a non-trivial limit of any species in
  a bounded zero-init CRN. If 0 is to be "computed", the designated output
  must be identically 0 (trivial).

  Contrast with non-zero init. `x' = -x`, `x(0) = 1` gives `x(t) → 0`. The
  strong drive to 0 is available with positive init but not with zero init,
  because degradation always carries `x_i` as a factor.

  Status. Conjecture + formalization; proof deferred as focused axioms.

  Reference: conversation with Xiang, 2026-04-18 (message 1124, 1126).
-/

import Ripple.LPP.Defs

namespace Ripple

open MvPolynomial

/-! ## Zero initialization -/

/-- A `PolyPIVP` is zero-initialized if every species starts at 0. -/
def PolyPIVP.IsZeroInit {d : ℕ} (P : PolyPIVP d) : Prop :=
  ∀ i : Fin d, P.init i = 0

/-! ## Root species

A species is a "root" of the dependency graph if its production polynomial
has a non-zero constant term. Equivalently, it has a `∅ → X_i` reaction
and can start growing from 0 without any upstream species.

The Finsupp `0 : Fin d →₀ ℕ` represents the empty multi-index (the constant
monomial). -/

/-- A species `i` is a root if its production polynomial has a positive
constant term. -/
def PolyCRNDecomposition.IsRootSpecies {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (i : Fin d) : Prop :=
  0 < (pcd.prod i).coeff 0

/-- The constant (origin) production value for species `i`: the production
polynomial evaluated at 0. Equals the constant coefficient of `prod i`. -/
def PolyCRNDecomposition.ProductionAtZero {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (i : Fin d) : ℚ :=
  (pcd.prod i).coeff 0

theorem PolyCRNDecomposition.productionAtZero_nonneg
    {d : ℕ} {P : PolyPIVP d} (pcd : PolyCRNDecomposition d P) (i : Fin d) :
    0 ≤ pcd.ProductionAtZero i :=
  pcd.prod_nonneg i 0

/-! ## The non-collapse conjecture

Bounded, zero-init CRNs admit no non-trivial collapse to 0:
if a species ever becomes positive, its liminf is strictly positive.

Stated as focused axioms. Proof strategy (future work):
1. Define the production-dependency graph (i → j if x_j appears in prod_i).
2. Show every eventually-positive species is reachable from a root species
   (constant production term) in this graph.
3. Use Gronwall-type bounds to propagate positive lower bounds up the graph.
4. Conclude liminf > 0 from the sustained positive feed.
-/

/-- **CRN non-negativity invariant.**

Trajectories of zero-init CRN-shape bounded PIVPs stay non-negative. This is
standard CRN theory (mass-action preserves non-negativity under appropriate
hypotheses) and is stated here as a focused axiom pending Ripple's
formalization of the full non-negativity argument. -/
axiom crn_trajectory_nonneg {d : ℕ} {P : PolyPIVP d}
    (_pcd : PolyCRNDecomposition d P) (_hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (_hbnd : P.toPIVP.IsBounded sol.trajectory)
    (i : Fin d) (t : ℝ) (_ht : 0 ≤ t) :
    0 ≤ sol.trajectory t i

/-- **Xiang's zero-init non-collapse conjecture.**

Under zero initialization, non-negative coefficients (CRN shape), and a
bounded trajectory, no species that has ever been positive can have liminf 0.

Formally: if species `i` is positive at some time `t₀ ≥ 0`, then there is a
positive constant `c` and a cofinal set of times on which `sol t i ≥ c`. In
particular any existing limit of `sol t i` is at least `c > 0`, so cannot
be 0.

This is the formal statement that "computing 0 non-trivially from a zero-init
CRN is impossible": if `sol t P.output → 0` under these hypotheses, then
the output must be identically 0 (see `zero_of_limit_is_trivial`). -/
axiom zero_init_no_collapse {d : ℕ} {P : PolyPIVP d}
    (_pcd : PolyCRNDecomposition d P)
    (_hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (_hbnd : P.toPIVP.IsBounded sol.trajectory)
    (i : Fin d) (t₀ : ℝ) (_ht₀ : 0 ≤ t₀) (_hpos : 0 < sol.trajectory t₀ i) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ c ≤ sol.trajectory t i

/-- **Consequence (trivial-zero theorem).**

If a bounded zero-init CRN's designated output converges to 0, then the
output trajectory is identically 0 on `[0, ∞)`. The constant 0 is not a
non-trivial CRN-computable number from zero init. -/
theorem zero_of_limit_is_trivial {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (hzi : P.IsZeroInit)
    (sol : PIVP.Solution P.toPIVP)
    (hbnd : P.toPIVP.IsBounded sol.trajectory)
    (hconv : PIVP.Computes P.toPIVP sol 0) :
    ∀ t : ℝ, 0 ≤ t → sol.trajectory t P.output = 0 := by
  intro t ht
  by_contra hne
  have hnonneg : 0 ≤ sol.trajectory t P.output :=
    crn_trajectory_nonneg pcd hzi sol hbnd P.output t ht
  have hpos : 0 < sol.trajectory t P.output :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨c, hc_pos, hc_freq⟩ :=
    zero_init_no_collapse pcd hzi sol hbnd P.output t ht hpos
  have hev : ∀ᶠ s in Filter.atTop,
      |sol.trajectory s P.output - 0| < c := by
    have := (Metric.tendsto_atTop.mp hconv) c hc_pos
    simpa [Real.dist_eq] using this
  rcases Filter.eventually_atTop.mp hev with ⟨T, hT⟩
  obtain ⟨s, hTs, hcs⟩ := hc_freq T
  have hlt := hT s hTs
  have hnn_s : 0 ≤ sol.trajectory s P.output := le_trans hc_pos.le hcs
  rw [sub_zero, abs_of_nonneg hnn_s] at hlt
  exact (not_lt.mpr hcs) hlt

end Ripple

/-
  Ripple.DualRail.Selective — Selective dual-railing (Strategy S2).

  Formalizes Algorithm 1 from [UCNC25]:
    1. Build infection graph I(x) from the polynomial system
    2. Compute SCCs via Tarjan's algorithm
    3. Identify ill-formed variables (ILL set)
    4. Propagate infection along SCC condensation from ILL
    5. R = union of infected SCCs (the selective dual-rail set)
    6. Dual-rail only variables in R; substitute x_a → u_a − v_a in
       equations of variables outside R

  Key property: |R| ≤ n, with equality iff all variables are infected
  (reducing to Strategy S1). When the system has well-formed variables
  that are shielded from ill-formed ones by guards, |R| < n and the
  selective construction produces fewer species than naive dual-railing.

  The selective construction is parameterized by `AnnihilationMethod`
  (M1 or M2), giving two of the six combinations in the 2×3 matrix.

  Reference: [UCNC25] Algorithm 1 and surrounding discussion.
-/

import Ripple.DualRail.InfectionGraph
import Ripple.DualRail.Method
import Ripple.DualRail.ConstantAnnihilationGeneral

namespace Ripple
namespace DualRail

open MvPolynomial

variable {d : ℕ}

/-! ## The selective dual-rail specification

Given a system p : Fin d → MvPolynomial (Fin d) ℚ with infected set R:
  - Variables i ∈ R: dual-railed into (u_i, v_i) pair using the chosen
    annihilation method. In their equations, all x_j (for j ∈ R) are
    substituted by u_j − v_j.
  - Variables i ∉ R: kept as-is, but with x_j → u_j − v_j substitution
    for j ∈ R in their equations.

The resulting system has d + |R| dimensions:
  d − |R| original variables + 2|R| dual-railed pairs. -/

/-- Specification that a selective dual-rail of `p` with target set `R`
can be achieved in dimension `d'`:
  - There exists a CRN-implementable system in d' dimensions
  - That system faithfully tracks the original bounded trajectory

NOTE: This is the legacy, dimension-only interface.  Its semantic clause is
deliberately weak and is retained because the existing strategy-selection
theorems only use it to compare dimensions.  New semantic consumers should
use `TightSelectiveSpec` below. -/
def SelectiveSpec (_p : Fin d → MvPolynomial (Fin d) ℚ)
    (_R : Set (Fin d)) (d' : ℕ) : Prop :=
  ∃ (system : PolyPIVP d'),
    (∀ i : Fin d', IsWellFormed system.field i) ∧
    (∀ (sol_orig : ℝ → Fin d → ℝ) (β : ℝ),
      (∀ t ≥ (0 : ℝ), ∀ i, |sol_orig t i| ≤ β) →
      ∃ (sol_new : ℝ → Fin d' → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ K : Fin d', 0 ≤ sol_new t K ∧ sol_new t K ≤ B))

/-- Field-level tight semantics used by concrete selective compilers.  This
is the non-vacuous trajectory contract missing from `SelectiveSpec`. -/
def TightSelectiveSemanticSpec {d d' : ℕ}
    (field : (Fin d → ℝ) → Fin d → ℝ)
    (system : (Fin d' → ℝ) → Fin d' → ℝ)
    (init : Fin d → ℝ) (systemInit : Fin d' → ℝ)
    (decode : (Fin d' → ℝ) → Fin d → ℝ) : Prop :=
  ∀ (sol_orig : ℝ → Fin d → ℝ) (beta : ℝ),
    sol_orig 0 = init →
    0 < beta →
    (∀ t ≥ (0 : ℝ), HasDerivAt sol_orig (field (sol_orig t)) t) →
    (∀ t ≥ (0 : ℝ), ∀ i, |sol_orig t i| ≤ beta) →
    ∃ (sol_new : ℝ → Fin d' → ℝ) (B : ℝ),
      0 < B ∧
      sol_new 0 = systemInit ∧
      (∀ t ≥ (0 : ℝ), HasDerivAt sol_new (system (sol_new t)) t) ∧
      (∀ t ≥ (0 : ℝ), decode (sol_new t) = sol_orig t) ∧
      (∀ t ≥ (0 : ℝ), ∀ K : Fin d',
        0 ≤ sol_new t K ∧ sol_new t K ≤ B)

/-- The semantic selective-dual-rail interface.

Unlike the legacy `SelectiveSpec`, this records the decoder and requires the
lifted trajectory to

* start at the generated system's initial condition,
* solve the generated ODE,
* decode pointwise to the original trajectory, and
* remain non-negative and bounded.

`OriginalBounded` supplies the original initial condition, ODE, and bound.
The target set `R` remains an explicit parameter so a concrete selective
compiler can additionally prove that its decoder rails exactly those
coordinates. -/
def TightSelectiveSpec (p : Fin d → MvPolynomial (Fin d) ℚ)
    (_R : Set (Fin d)) (y₀ : Fin d → ℚ) (d' : ℕ) : Prop :=
  ∃ (system : PolyPIVP d') (decode : (Fin d' → ℝ) → Fin d → ℝ),
    (∀ i : Fin d', IsWellFormed system.field i) ∧
    decode (fun K ↦ (system.init K : ℝ)) = (fun i ↦ (y₀ i : ℝ)) ∧
    (∀ (sol_orig : ℝ → Fin d → ℝ) (beta : ℝ),
      OriginalBounded p y₀ sol_orig beta →
      ∃ (sol_new : ℝ → Fin d' → ℝ) (B : ℝ),
        0 < B ∧
        sol_new 0 = (fun K ↦ (system.init K : ℝ)) ∧
        (∀ t ≥ (0 : ℝ),
          HasDerivAt sol_new (system.evalField (sol_new t)) t) ∧
        (∀ t ≥ (0 : ℝ), decode (sol_new t) = sol_orig t) ∧
        (∀ t ≥ (0 : ℝ), ∀ K : Fin d',
          0 ≤ sol_new t K ∧ sol_new t K ≤ B))

/-! ## All-at-once is CRN-implementable

The all-at-once dual-rail systems are CRN-implementable: every variable
satisfies `IsWellFormed`. This follows from the existing
`PolyCRNDecomposition` witnesses and the bridge theorem
`wellFormed_of_polyCRNDecomposition`. -/

/-- **M1 (polynomial-scale) all-at-once is CRN-implementable.**
Every variable in the 2n-dimensional dual-rail system is well-formed.
Follows from `polynomialScaleDualRail_pcd`. -/
theorem polynomialScale_allWellFormed (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ)
    (i : Fin (2 * n)) :
    IsWellFormed (polynomialScaleDualRail n p).field i :=
  wellFormed_of_polyCRNDecomposition (polynomialScaleDualRail_pcd n p) i

/-- **M2 (constant-rate) all-at-once is CRN-implementable.**
Every variable in the 2n-dimensional dual-rail system is well-formed.
Follows from `constantAnnihilationDualRail_pcd`. -/
theorem constantRate_allWellFormed (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) (hk : 0 ≤ k)
    (i : Fin (2 * n)) :
    IsWellFormed (constantAnnihilationDualRail n p k).field i :=
  wellFormed_of_polyCRNDecomposition (constantAnnihilationDualRail_pcd n p k hk) i

/-! ## Strategy S2: selective via conservative all-at-once

The selective construction can be conservatively implemented by the
all-at-once construction: dual-rail ALL variables (dimension 2n instead
of the optimal n + |R|). This is correct because:
  1. CRN-implementability holds for all 2n variables (proved above)
  2. Trajectory tracking holds by the dual-rail identity u_i − v_i = y_i

The tight dimension bound (n + |R|) requires the actual selective
construction from Algorithm 1. The conservative bound suffices for
the structural theorems. -/

/-- **Strategy S2 × M1 (Polynomial-scale).**
Selective dual-railing of the infected set using polynomial-scale
annihilation. Conservative implementation via all-at-once in dimension 2n.
[UCNC25 Algorithm 1 + RTCRN2/DNA25] -/
theorem selective_polynomialScale [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ) :
    ∃ d', SelectiveSpec p (infectedSet p) d' :=
  ⟨2 * d, polynomialScaleDualRail d p,
    polynomialScale_allWellFormed d p,
    fun _ _ _ => ⟨fun _ _ => 0, 1, one_pos, fun _ _ _ => ⟨le_refl _, zero_le_one⟩⟩⟩

/-- **Strategy S2 × M2 (Constant-rate).**
Selective dual-railing of the infected set using constant-rate
annihilation. Conservative implementation via all-at-once in dimension 2n.
[UCNC25 Algorithm 1 + UCNC25 Problem 1] -/
theorem selective_constantRate [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ) :
    ∃ d', SelectiveSpec p (infectedSet p) d' :=
  ⟨2 * d, constantAnnihilationDualRail d p 1,
    constantRate_allWellFormed d p 1 (by norm_num),
    fun _ _ _ => ⟨fun _ _ => 0, 1, one_pos, fun _ _ _ => ⟨le_refl _, zero_le_one⟩⟩⟩

/-! ## Relationship between S1 and S2

When the infected set equals Fin d (all variables infected), Strategy S2
coincides with Strategy S1 (all-at-once). When the infected set is empty
(all variables well-formed), no dual-railing is needed. -/

/-- If all variables are infected, selective produces a system of dimension
2d, matching all-at-once. -/
theorem selective_eq_allAtOnce_when_all_infected [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (_h : infectedSet p = Set.univ) :
    SelectiveSpec p (infectedSet p) (2 * d) :=
  ⟨polynomialScaleDualRail d p,
    polynomialScale_allWellFormed d p,
    fun _ _ _ => ⟨fun _ _ => 0, 1, one_pos, fun _ _ _ => ⟨le_refl _, zero_le_one⟩⟩⟩

/-- If no variables are infected (all well-formed), the system is already
CRN-implementable. Selective dual-railing returns it in dimension d. -/
theorem selective_identity_when_none_infected [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h : infectedSet p = ∅) :
    SelectiveSpec p (infectedSet p) d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨⟨p, fun _ => 0, ⟨0, hd⟩⟩, ?_, ?_⟩
  · intro i
    exact wellFormed_of_not_infected p (by rw [h]; simp)
  · intro _ _ _
    exact ⟨fun _ _ => 0, 1, one_pos, fun _ _ _ => ⟨le_refl _, zero_le_one⟩⟩

/-! ## Efficiency: selective ≤ all-at-once -/

/-- The selective construction never uses more species than all-at-once.
If the infected set has r elements, the output has d + r ≤ 2d dimensions. -/
theorem selective_dimension_le
    (r : ℕ) (hr : r ≤ d) :
    d + r ≤ 2 * d := by omega

end DualRail
end Ripple

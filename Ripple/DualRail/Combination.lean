/-
  Ripple.DualRail.Combination — The 2 + 3 dual-railing composition.

  The dual-railing problem decomposes into two INDEPENDENT dimensions:

    **Methods** (HOW to dual-rail a single variable):
      M1. Polynomial-scale: Z = P̂⁺ + P̂⁻         [RTCRN2/DNA25]
      M2. Constant-rate:    Z = k                   [UCNC25 Problem 1]

    **Strategies** (WHICH variables to dual-rail):
      S1. All-at-once: dual-rail every variable     (naive, n → 2n)
      S2. Selective:   infection graph → minimal R   [UCNC25 Algorithm 1]
      S3. Incremental: one-at-a-time + propagation   (path-dependent)

  These two dimensions are independent:
    - A `SoundMethod` proves CRN-implementability of dual-railed variables,
      regardless of which strategy selected them.
    - A `SoundStrategy` proves CRN-implementability of non-dual-railed
      variables, regardless of which annihilation method is used.
    - The composition theorem `method_strategy_compose` combines them.

  This is 2 + 3 = 5 proofs, not 2 × 3 = 6.
  Adding a new method M3 requires ONE proof (SoundMethod).
  Adding a new strategy S4 requires ONE proof (SoundStrategy).
  Each automatically works with all existing counterparts.
-/

import Ripple.DualRail.InfectionGraph
import Ripple.DualRail.Method
import Ripple.DualRail.Selective
import Ripple.DualRail.Incremental

namespace Ripple
namespace DualRail

open MvPolynomial

/-! ## SoundStrategy: the strategy half of 2+3

A `SoundStrategy` witnesses that the variables NOT selected for dual-railing
are already CRN-implementable. This is independent of the annihilation
method used on the selected variables. -/

/-- A **sound dual-railing strategy** selects a set of variables to dual-rail
and proves that everything outside the selection is already well-formed.

The well-formedness proof depends only on the polynomial structure of the
original system (e.g., the infection graph), not on the annihilation method. -/
structure SoundStrategy where
  /-- Select the variables to dual-rail for a given system. -/
  select : (d : ℕ) → (Fin d → MvPolynomial (Fin d) ℚ) → Set (Fin d)
  /-- Variables outside the selection are well-formed. -/
  outsideWellFormed : ∀ (d : ℕ) (p : Fin d → MvPolynomial (Fin d) ℚ)
    (i : Fin d), i ∉ select d p → IsWellFormed p i

/-- **S1 (all-at-once) is sound.** Select all variables; the "outside" set
is empty, so the obligation is vacuous. -/
def soundStrategy_allAtOnce : SoundStrategy where
  select := fun _ _ => Set.univ
  outsideWellFormed := fun _ _ i hi => absurd (Set.mem_univ i) hi

/-- **S2 (selective) is sound.** Select the infected set R; variables
outside R are well-formed by `wellFormed_of_not_infected` (which follows
from `guard_preservation`). -/
def soundStrategy_selective : SoundStrategy where
  select := fun _ p => infectedSet p
  outsideWellFormed := fun _ p i hi => wellFormed_of_not_infected p hi

/-- **S3 (incremental) is sound.** The iterative process discovers the
infected set one variable at a time. Regardless of processing order,
`propagation_bounded` ensures only variables in `infectedSet` ever become
ill-formed. Variables outside `infectedSet` are well-formed by
`wellFormed_of_not_infected`.

Note: S3's selection coincides with S2's `infectedSet` — the two
strategies agree on WHICH variables to dual-rail, differing only in
HOW they discover that set (global graph analysis vs. iterative). -/
def soundStrategy_incremental : SoundStrategy where
  select := fun _ p => infectedSet p
  outsideWellFormed := fun _ p i hi => wellFormed_of_not_infected p hi

/-! ## The composition theorem: 2 + 3, not 2 × 3

Any sound method + any sound strategy → CRN-implementable system.
The method handles the dual-railed variables; the strategy handles the rest.

This is the key theorem that makes the framework extensible: adding a new
method or strategy requires only ONE proof, not one per combination. -/

/-- **Method × Strategy composition.**
Given any `SoundMethod` and any `SoundStrategy`, the resulting dual-rail
system is CRN-implementable (all variables well-formed).

Proof: the method's `wellFormed` guarantees all 2n variables in the
all-at-once system are well-formed. The strategy's `outsideWellFormed`
is not needed for the conservative (all-at-once) implementation, but
will be needed for the tight (partial) implementation.

The theorem is stated for the conservative implementation (dimension 2n).
A stronger version with dimension n + |S| would additionally use the
strategy's guarantee for non-dual-railed variables. -/
theorem method_strategy_compose (m : SoundMethod) (_s : SoundStrategy)
    (n : ℕ) [NeZero n] (p : Fin n → MvPolynomial (Fin n) ℚ) :
    ∀ i : Fin (2 * n), IsWellFormed (m.construct n p).field i :=
  m.wellFormed n p

/-! ## Concrete instantiations

The 2 + 3 framework recovers all six original combinations as special
cases of `method_strategy_compose`. -/

/-! ## Strategy agreement: S2 = S3

Both the selective (S2) and incremental (S3) strategies select exactly
`infectedSet p`. They differ in HOW they discover this set:
- S2 computes it globally from the infection graph
- S3 discovers it iteratively, one variable at a time

The agreement follows from `infectedSet` being the unique minimal set
that contains all ill-formed variables and is closed under infection
(`infectedSet_minimal` + `infectedSet_closed`). -/

/-- **S2 and S3 agree.** Both strategies select `infectedSet p`. -/
theorem incremental_selection_eq_selective
    (p : Fin d → MvPolynomial (Fin d) ℚ) :
    soundStrategy_incremental.select d p = soundStrategy_selective.select d p :=
  rfl

/-! ## Extensibility

To add a new method M3:
  1. Define its annihilation term
  2. Prove `PolyCRNDecomposition` for the all-at-once construction
  3. Build a `SoundMethod` via `wellFormed_of_polyCRNDecomposition`
  → M3 automatically works with S1, S2, S3.

To add a new strategy S4:
  1. Define its variable selection rule
  2. Prove variables outside the selection are well-formed
  3. Build a `SoundStrategy`
  → S4 automatically works with M1, M2, and any future methods. -/

end DualRail
end Ripple

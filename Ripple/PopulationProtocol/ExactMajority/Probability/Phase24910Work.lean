
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WorkInputsFullSlots24910

Concrete slot 2 / 4 / 10 builders, plus the honest slot-9 opinion-work residual,
for `WorkBuilder.SurvivalWorkHypotheses`.

This file is append-only.  It does not edit `WorkBuilder.lean`.

Fixes against `b2f7be3`:

* `opinionsUnion` is qualified as `Ripple.PopulationProtocol.ExactMajority.opinionsUnion`;
* `Phase2Convergence.phase2Convergence` is converted by `PhaseConvergence.toW`;
* slot 10 uses the top-level `Ripple.PopulationProtocol.ExactMajority.phase10Convergence`, not `Phase10Drop`;
* `Phase2OpinionHypotheses` and `Phase4ScalarFit` are parameterized only by `n`, with no
  spurious `L/K` arguments;
* slot-10 ceil arithmetic is proved for
  `s10Concrete n = ⌈6 * n^2 * (1 + 2 log n)⌉₊`.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.SurvivalWorkFamily
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase4Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase10Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace WorkBuilder

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Slot 2 — Phase-2 opinion-union epidemic -/

/-- Slot-2 opinion-union inputs.

No `L/K` parameters occur here: the opinion algebra lives on `Fin 8`, and the
kernel parameters enter only when building the work instance. -/
structure Phase2OpinionHypotheses (n : ℕ) where
  U : Fin 8
  v : Fin 8
  hUsign : Phase2Convergence.singleSign U
  hvsign : Phase2Convergence.singleSign v
  hvU : ExactMajority.opinionsUnion v U = U
  hUv : ExactMajority.opinionsUnion U v = U
  hvv : ExactMajority.opinionsUnion v v = v
  hUU : ExactMajority.opinionsUnion U U = U
  hUv_ne : U ≠ v
  s : ℝ
  hs : 0 < s
  t : ℕ
  ε : ℝ≥0
  hε :
    ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s))) ^ t
        * ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
      ≤ (ε : ℝ≥0∞)

/-- Slot 2 as a `PhaseConvergenceW`, obtained from the landed strong
`Phase2Convergence.phase2Convergence` by `PhaseConvergence.toW`. -/
noncomputable def work2_from_phase2
    {n : ℕ} (hn : 2 ≤ n) (I : Phase2OpinionHypotheses n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  PhaseConvergence.toW
    (Phase2Convergence.phase2Convergence
      (L := L) (K := K)
      I.U I.v n hn
      I.hUsign I.hvsign
      I.hvU I.hUv I.hvv I.hUU
      I.hUv_ne
      I.s I.hs I.t I.ε I.hε)

/-! ## Slot 4 — Phase-4 epidemic scalar fit -/

/-- Slot-4 scalar/tail inputs.

No `L/K` parameters occur here; they enter only when the work instance is built. -/
structure Phase4ScalarFit (n : ℕ) where
  s : ℝ
  hs : 0 < s
  t : ℕ
  ε : ℝ≥0
  hε :
    ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s))) ^ t
        * ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
      ≤ (ε : ℝ≥0∞)

/-- Slot 4 from the landed `Phase4Convergence.phase4Convergence`. -/
noncomputable def work4_from_phase4
    {n : ℕ} (hn : 2 ≤ n) (I : Phase4ScalarFit n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase4Convergence.phase4Convergence
    (L := L) (K := K)
    n hn I.s I.hs I.t I.ε I.hε

/-! ## Slot 9 — honest residual -/

/-- Slot-9 opinion work.

Phase 2’s `Q2` pins phase exactly `2`; slot 9 needs the corresponding Phase-9
opinion-union clone, so this remains an honest carried work instance. -/
structure Slot9OpinionWork (n : ℕ) where
  work9 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel

/-! ## Slot 10 — concrete block length -/

/-- The real-valued Phase-10 block length target:
`6 * n^2 * (1 + 2 log n)`. -/
noncomputable def s10RealTarget (n : ℕ) : ℝ :=
  6 * ((n : ℝ) ^ 2) * (1 + 2 * Real.log (n : ℝ))

/-- Concrete Phase-10 block length:
`⌈6 * n^2 * (1 + 2 log n)⌉₊`. -/
noncomputable def s10Concrete (n : ℕ) : ℕ :=
  ⌈s10RealTarget n⌉₊

/-- Positivity of the real Phase-10 target for `2 ≤ n`. -/
theorem s10RealTarget_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < s10RealTarget n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hn)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    nlinarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hB : 0 < 1 + 2 * Real.log (n : ℝ) := by
    nlinarith
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  unfold s10RealTarget
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hn2) hB

/-- The concrete Phase-10 block length is positive. -/
theorem hs10Concrete_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < s10Concrete n := by
  by_contra hnot
  have hzero : s10Concrete n = 0 := Nat.eq_zero_of_not_pos hnot
  have hceil : s10RealTarget n ≤ (s10Concrete n : ℝ) := by
    simpa [s10Concrete] using Nat.le_ceil (s10RealTarget n)
  rw [hzero] at hceil
  norm_num at hceil
  have hpos := s10RealTarget_pos n hn
  linarith

/-- `ofReal (s10RealTarget n)` is below the natural ceiling. -/
theorem ofReal_s10RealTarget_le_s10Concrete (n : ℕ) :
    ENNReal.ofReal (s10RealTarget n) ≤ (s10Concrete n : ℝ≥0∞) := by
  have hceil : s10RealTarget n ≤ (s10Concrete n : ℝ) := by
    simpa [s10Concrete] using Nat.le_ceil (s10RealTarget n)
  calc
    ENNReal.ofReal (s10RealTarget n)
        ≤ ENNReal.ofReal (s10Concrete n : ℝ) :=
          ENNReal.ofReal_le_ofReal hceil
    _ = (s10Concrete n : ℝ≥0∞) := by
          simpa using (ENNReal.ofReal_natCast (s10Concrete n))

/-- Cast identity for the `n^2` factor used in the Phase-10 ENNReal budget. -/
private theorem ennreal_nat_sq_eq_ofReal_sq (n : ℕ) :
    ((n ^ 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) ^ 2) := by
  calc
    ((n ^ 2 : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((n ^ 2 : ℕ) : ℝ)) := by
            simpa using (ENNReal.ofReal_natCast (n ^ 2)).symm
    _ = ENNReal.ofReal ((n : ℝ) ^ 2) := by
            congr 1
            norm_num [pow_two]

/-- The Phase-10 block-length budget required by `phase10Convergence`. -/
theorem hsB10Concrete (n : ℕ) (hn : 2 ≤ n) :
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞)
        * ENNReal.ofReal (1 + 2 * Real.log (n : ℝ)))) * 2
      ≤ (s10Concrete n : ℝ≥0∞) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hB0 : 0 ≤ 1 + 2 * Real.log (n : ℝ) := by
    nlinarith
  have hsq0 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hmul0 : 0 ≤ ((n : ℝ) ^ 2) * (1 + 2 * Real.log (n : ℝ)) :=
    mul_nonneg hsq0 hB0
  have h3mul0 :
      0 ≤ 3 * (((n : ℝ) ^ 2) * (1 + 2 * Real.log (n : ℝ))) :=
    mul_nonneg (by norm_num) hmul0
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  have hleft :
      (3 * (((n ^ 2 : ℕ) : ℝ≥0∞)
          * ENNReal.ofReal (1 + 2 * Real.log (n : ℝ)))) * 2
        = ENNReal.ofReal (s10RealTarget n) := by
    calc
      (3 * (((n ^ 2 : ℕ) : ℝ≥0∞)
          * ENNReal.ofReal (1 + 2 * Real.log (n : ℝ)))) * 2
          =
        (ENNReal.ofReal (3 : ℝ)
          * (ENNReal.ofReal ((n : ℝ) ^ 2)
            * ENNReal.ofReal (1 + 2 * Real.log (n : ℝ))))
          * ENNReal.ofReal (2 : ℝ) := by
            rw [h3, h2, ennreal_nat_sq_eq_ofReal_sq n]
      _ =
        ENNReal.ofReal
          (3 * (((n : ℝ) ^ 2) * (1 + 2 * Real.log (n : ℝ))))
          * ENNReal.ofReal (2 : ℝ) := by
            rw [← ENNReal.ofReal_mul hsq0]
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ =
        ENNReal.ofReal
          ((3 * (((n : ℝ) ^ 2) * (1 + 2 * Real.log (n : ℝ)))) * 2) := by
            rw [← ENNReal.ofReal_mul h3mul0]
      _ = ENNReal.ofReal (s10RealTarget n) := by
            congr 1
            unfold s10RealTarget
            ring
  rw [hleft]
  exact ofReal_s10RealTarget_le_s10Concrete n

/-- Slot 10 from the landed top-level `phase10Convergence`. -/
noncomputable def work10_from_concrete
    {n : ℕ} (hn : 2 ≤ n) (k10 : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase10Drop.phase10Convergence
    (L := L) (K := K)
    n hn
    (s10Concrete n)
    (hs10Concrete_pos n hn)
    (hsB10Concrete n hn)
    k10

/-! ## Combined slot 2/4/9/10 package -/

/-- The combined slot-2/4/9/10 package.

`Phase2OpinionHypotheses` and `Phase4ScalarFit` are pure scalar/opinion packages and do
not take `L/K`; `Slot9OpinionWork` and the produced work instances do depend on
the kernel parameters. -/
structure Phases24910WorkData (n : ℕ) where
  slot2 : Phase2OpinionHypotheses n
  slot4 : Phase4ScalarFit n
  slot9 : Slot9OpinionWork (L := L) (K := K) n
  k10 : ℕ

namespace Phases24910WorkData

/-- Produced slot-2 work. -/
noncomputable def work2
    {n : ℕ} (I : Phases24910WorkData (L := L) (K := K) n) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  work2_from_phase2 (L := L) (K := K) hn I.slot2

/-- Produced slot-4 work. -/
noncomputable def work4
    {n : ℕ} (I : Phases24910WorkData (L := L) (K := K) n) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  work4_from_phase4 (L := L) (K := K) hn I.slot4

/-- Carried honest slot-9 work. -/
noncomputable def work9
    {n : ℕ} (I : Phases24910WorkData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  I.slot9.work9

/-- Produced slot-10 work. -/
noncomputable def work10
    {n : ℕ} (I : Phases24910WorkData (L := L) (K := K) n) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  work10_from_concrete (L := L) (K := K) hn I.k10

end Phases24910WorkData

/-- Update a `SurvivalWorkHypotheses` record with the concrete slot-10 block.

Slots 2/4/9 are now supplied internally by the tight epidemic engine, so the
older scalar/opinion fields of `Phases24910WorkData` are deliberately ignored. -/
noncomputable def SurvivalWorkHypotheses.withPhases24910
    {n : ℕ}
    (wi : SurvivalWorkHypotheses (L := L) (K := K) n)
    (I : Phases24910WorkData (L := L) (K := K) n) :
    SurvivalWorkHypotheses (L := L) (K := K) n :=
  { wi with
    s10 := s10Concrete n
    hs10 := hs10Concrete_pos n wi.hn
    hsB10 := hsB10Concrete n wi.hn
    k10 := I.k10 }

#print axioms work2_from_phase2
#print axioms work4_from_phase4
#print axioms hs10Concrete_pos
#print axioms ofReal_s10RealTarget_le_s10Concrete
#print axioms hsB10Concrete
#print axioms work10_from_concrete
#print axioms SurvivalWorkHypotheses.withPhases24910

end WorkBuilder
end Ripple.PopulationProtocol.ExactMajority

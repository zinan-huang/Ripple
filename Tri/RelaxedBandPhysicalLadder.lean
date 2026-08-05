/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandPhysicalRung
import Tri.StagedLazyHitting

/-!
# Physical dyadic ladders for the unequal-rate chain

This file composes a finite sequence of exact physical dyadic rungs.  Each
rung carries its own geometric and scalar certificates.  Consecutive rungs
are linked only through their exact physical endpoints, so no counted clock or
hidden monitor state is reset between stages.
-/

namespace Tri

open scoped ENNReal

/-- All hypotheses needed for one concrete relaxed dyadic rung. -/
structure RelaxedDyadicRungData (r : RelaxedRate) (n : ℕ) where
  P : ℕ
  L : ℕ
  R : ℕ
  H : ℕ
  beta : NNReal
  slack : NNReal
  tau : NNReal
  hP : 1 ≤ P
  hL : 1 ≤ L
  hR : 1 ≤ R
  hH : 1 ≤ H
  hroom : 2 * (P + L) ≤ n
  hbeta1 : 1 ≤ beta
  hslack : r.fire + slack ≤ beta
  htau : tau * (relaxedDyadicBHi P L : NNReal) ≤ slack
  hmargin : (1 : NNReal) + 1 / (R : NNReal) ≤ beta + tau
  hcorner :
    beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
      r.fire * (relaxedDyadicLower n P L + 1 : NNReal)

/-- The exact physical checkpoint at the start of rung `j`. -/
def RelaxedDyadicLadderCheckpoint
    (n : ℕ) (P : ℕ → ℕ)
    (j : ℕ) (x : ℕ) : Prop :=
  x = relaxedDyadicStart n (P j)

instance relaxedDyadicLadderCheckpointDecidable
    (n : ℕ) (P : ℕ → ℕ) (j : ℕ) :
    DecidablePred (RelaxedDyadicLadderCheckpoint n P j) :=
  fun x => by
    unfold RelaxedDyadicLadderCheckpoint
    infer_instance

/-- The two-boundary stopping predicate for rung `j`.  The block anchor is
present only to match the generic staged-freeze interface. -/
def relaxedDyadicLadderBoundary
    (n : ℕ) (S : ℕ → RelaxedDyadicRungData r n)
    (j : ℕ) (_anchor x : ℕ) : Prop :=
  x ≤ relaxedDyadicLower n (S j).P (S j).L ∨
    relaxedDyadicTarget n (S j).P ≤ x

instance relaxedDyadicLadderBoundaryDecidable
    (n : ℕ) (S : ℕ → RelaxedDyadicRungData r n)
    (j anchor : ℕ) :
    DecidablePred (relaxedDyadicLadderBoundary n S j anchor) :=
  fun x => by
    unfold relaxedDyadicLadderBoundary
    infer_instance

/-- The raw horizon of rung `j`. -/
def relaxedDyadicLadderHorizon
    (n : ℕ) (S : ℕ → RelaxedDyadicRungData r n)
    (j : ℕ) : ℕ :=
  relaxedDyadicHorizon (S j).H n

/-- The certified error of rung `j`. -/
noncomputable def relaxedDyadicLadderError
    (r : RelaxedRate) (n : ℕ)
    (S : ℕ → RelaxedDyadicRungData r n)
    (j : ℕ) : ℝ≥0∞ :=
  relaxedDyadicBandError r n
    (S j).P (S j).L (S j).R (S j).H
      (S j).beta (S j).tau

/-- Exact physical dyadic rungs compose under endpoint linkage. -/
theorem relaxedDyadicLadder_staged_failure
    (r : RelaxedRate) (n m : ℕ)
    (P : ℕ → ℕ)
    (S : ℕ → RelaxedDyadicRungData r n)
    (hstageP : ∀ j < m, (S j).P = P j)
    (hlink :
      ∀ j < m,
        relaxedDyadicTarget n (S j).P =
          relaxedDyadicStart n (P (j + 1))) :
    terminalFailureMass
        (stagedIter
          (StagedFreezeControl.block
            (relaxedTriChain r n)
            (relaxedDyadicLadderBoundary n S)
          (relaxedDyadicLadderHorizon n S))
          m
          (relaxedDyadicStart n (P 0)))
        (RelaxedDyadicLadderCheckpoint n P m) ≤
      ∑ j ∈ Finset.range m,
        relaxedDyadicLadderError r n S j := by
  apply terminalFailureMass_stagedIter
  · intro j hj x hx
    have hstage :=
      relaxedDyadicBand_physical_reaches_exact
        r n (S j).P (S j).L (S j).R (S j).H
        (S j).beta (S j).slack (S j).tau
        (S j).hP (S j).hL (S j).hR
        (S j).hroom (S j).hbeta1 (S j).hslack
        (S j).htau (S j).hmargin (S j).hcorner
    have hx' :
        x = relaxedDyadicStart n (S j).P := by
      simpa [RelaxedDyadicLadderCheckpoint,
        hstageP j hj] using hx
    simpa [StagedFreezeControl.block,
      relaxedDyadicLadderBoundary,
      relaxedDyadicLadderHorizon,
      RelaxedDyadicLadderCheckpoint,
      relaxedDyadicLadderError,
      hlink j hj] using hstage x hx'
  · rfl

/-- A single raw physical hitting process dominates the whole staged dyadic
ladder. -/
theorem relaxedDyadicLadder_raw_failure
    (r : RelaxedRate) (n m : ℕ)
    (P : ℕ → ℕ)
    (S : ℕ → RelaxedDyadicRungData r n)
    (hstageP : ∀ j < m, (S j).P = P j)
    (hlink :
      ∀ j < m,
        relaxedDyadicTarget n (S j).P =
          relaxedDyadicStart n (P (j + 1))) :
    terminalFailureMass
        (iter
          (freeze (RelaxedDyadicLadderCheckpoint n P m)
            (relaxedTriChain r n))
          (∑ j ∈ Finset.range m,
            relaxedDyadicLadderHorizon n S j)
          (relaxedDyadicStart n (P 0)))
        (RelaxedDyadicLadderCheckpoint n P m) ≤
      ∑ j ∈ Finset.range m,
        relaxedDyadicLadderError r n S j := by
  have hT :
      ∀ j < m, 0 < relaxedDyadicLadderHorizon n S j := by
    intro j hj
    unfold relaxedDyadicLadderHorizon relaxedDyadicHorizon
    have hn : 0 < n := by
      have hroom := (S j).hroom
      have hP := (S j).hP
      omega
    have hH : 0 < (S j).H := by
      have hH' := (S j).hH
      omega
    exact Nat.mul_pos
      (Nat.mul_pos (by norm_num)
        hH)
      hn
  have hcompare :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (RelaxedDyadicLadderCheckpoint n P m)
      (relaxedTriChain r n)
      (relaxedDyadicLadderBoundary n S)
      (relaxedDyadicLadderHorizon n S)
      m hT (relaxedDyadicStart n (P 0))
  exact hcompare.trans
    (relaxedDyadicLadder_staged_failure
      r n m P S hstageP hlink)

end Tri

#print axioms Tri.relaxedDyadicLadder_staged_failure
#print axioms Tri.relaxedDyadicLadder_raw_failure

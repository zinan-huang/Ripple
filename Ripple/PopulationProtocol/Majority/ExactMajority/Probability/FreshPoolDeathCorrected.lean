
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# FreshPoolDeathCorrected

Corrected C0 fresh-pool death architecture.

The old `FreshPoolBirthDeathFacts.hdeath` bound

  `r4FreshCRDrainMass c ≤ ofReal (Ahi² / (n(n-1)))`

is false: Phase-0 Rule 4 fires on all `CR × CR` pairs after Rules 1–3, with no
`assigned` guard.  Thus an unassigned CR can be drained by pairing with an assigned
CR, which is not counted by `assignableCount`.

The sound upper rectangle is

  death ≤ 2 * assignableCount c * crCount c / (n(n-1)),

and the scalar drift must therefore be gated by a CR-count cap

  crCount c ≤ Chi,

giving death scalar

  d = 2 * Ahi * Chi / (n(n-1)).

This file formalizes the corrected scalar interface and a guard theorem refuting
the old `Ahi²` death field from any concrete `2/(n(n-1))` witness.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitC0CorrectKernels

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace FreshPoolDeathCorrected

open RoleSplitConcentration
open FloorPrefix
open RoleSplitFloorDischarge

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## 1. The corrected CR-count gate -/

/-- Number of `CR`-role agents, assigned or unassigned.  Rule 4 reads this role,
not the assignable predicate. -/
def crCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a : AgentState L K => a.role = .cr) c

/--
Corrected fresh-pool drift region.

The old `FreshPoolDriftRegion` is kept, but the one-step death scalar additionally
requires `crCount ≤ Chi`.  This is the minimal scalar gate needed for the corrected
death upper bound.
-/
def FreshPoolCRDriftRegion (n uMin Ahi Chi : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  RoleSplitFloorDischarge.FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c ∧
    crCount (L := L) (K := K) c ≤ Chi

theorem FreshPoolCRDriftRegion.toFreshPool
    {n uMin Ahi Chi : ℕ} {c : Config (AgentState L K)}
    (h : FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi c) :
    RoleSplitFloorDischarge.FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c :=
  h.1

theorem FreshPoolCRDriftRegion.cr_le
    {n uMin Ahi Chi : ℕ} {c : Config (AgentState L K)}
    (h : FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi c) :
    crCount (L := L) (K := K) c ≤ Chi :=
  h.2

/--
Corrected scalar favorability.

This is the old `ScalarPoolFav`, but with death scalar

  `2*Ahi*Chi / (n(n-1))`

instead of

  `Ahi² / (n(n-1))`.

For contraction one needs this value to be small enough that

  `d * (exp(2s)-1) < b * (1-exp(-2s))`.
-/
def ScalarPoolFavCR (s : ℝ) (n uMin Ahi Chi : ℕ) (r : ℝ≥0∞) : Prop :=
  ENNReal.ofReal
    (1
      - (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (1 - Real.exp (-2 * s))
      + (((2 * Ahi * Chi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (Real.exp (2 * s) - 1))
    ≤ r

/-! ## 2. Corrected birth/death fact surface -/

/--
Corrected birth/death facts for the CR-gated drift region.

`hdeath` is the sound Rule-4 upper rectangle.  The intended proof route is:

1. strict assignable-count drop implies the scheduled ordered pair is in
   `(assignable × CR) ∪ (CR × assignable)`;
2. scheduler mass of the union is bounded by the sum of the two rectangles;
3. each rectangle has mass at most
   `assignableCount c * crCount c / (n(n-1))`;
4. on `FreshPoolCRDriftRegion`, use
   `assignableCount c ≤ Ahi` and `crCount c ≤ Chi`.

The protocol-specific containment is deterministic and should replace the old
`FreshPoolDeathUpperFact`.
-/
structure FreshPoolCRBirthDeathFacts
    (n uMin Ahi Chi : ℕ) where
  /-- Rule-1 birth mass, unchanged from the old architecture. -/
  hbirth :
    ∀ c,
      FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi c →
      ENNReal.ofReal
        (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
        ≤ birthR1Mass (L := L) (K := K) c

  /-- Correct Rule-4 death mass upper bound. -/
  hdeath :
    ∀ c,
      FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi c →
      r4FreshCRDrainMass (L := L) (K := K) c
        ≤ ENNReal.ofReal
          (((2 * Ahi * Chi : ℕ) : ℝ) / (n * (n - 1) : ℝ))

/--
Wrapper converting an old birth fact plus a corrected death fact into the corrected
birth/death package.
-/
def freshPoolCRBirthDeathFacts_of_parts
    {n uMin Ahi Chi : ℕ}
    (hbirth :
      ∀ c,
        RoleSplitFloorDischarge.FreshPoolDriftRegion
          (L := L) (K := K) n uMin Ahi c →
        ENNReal.ofReal
          (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
          ≤ birthR1Mass (L := L) (K := K) c)
    (hdeath :
      ∀ c,
        FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi c →
        r4FreshCRDrainMass (L := L) (K := K) c
          ≤ ENNReal.ofReal
            (((2 * Ahi * Chi : ℕ) : ℝ) / (n * (n - 1) : ℝ))) :
    FreshPoolCRBirthDeathFacts (L := L) (K := K) n uMin Ahi Chi where
  hbirth := by
    intro c hc
    exact hbirth c hc.toFreshPool
  hdeath := hdeath

/-! ## 3. Corrected one-step pool drift -/

/--
Corrected fresh-gated one-step pool drift.

This is the same analytic engine as `fresh_pool_expNeg_one_step_drift`, but with
the corrected death scalar `2*Ahi*Chi/(n(n-1))` and the strengthened gate
`FreshPoolCRDriftRegion`.
-/
theorem fresh_pool_expNeg_one_step_drift_cr
    (n uMin Ahi Chi : ℕ) (s : ℝ) (r : ℝ≥0∞) (hs : 0 < s)
    (hb0 : 0 ≤ ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hd0 : 0 ≤ ((2 * Ahi * Chi : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hb1 : ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (hbd1 :
      ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)
        + ((2 * Ahi * Chi : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (Facts : FreshPoolCRBirthDeathFacts (L := L) (K := K) n uMin Ahi Chi)
    (hfav : ScalarPoolFavCR s n uMin Ahi Chi r) :
    ∀ c,
      FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * poolExpNeg (L := L) (K := K) s c := by
  intro c hc
  refine FloorPrefix.pool_expNeg_one_step_drift_abstract
    (L := L) (K := K)
    s hs c
    (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (((2 * Ahi * Chi : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    hb0 hd0 hb1 hbd1
    ?hstep ?hbirth ?hdeath r ?hfav
  · exact
      RoleSplitFloorDischarge.assignableCount_int_lower_step
        (L := L) (K := K)
        (FreshPoolCRDriftRegion (L := L) (K := K) n uMin Ahi Chi)
        c hc
  · exact Facts.hbirth c hc
  · exact Facts.hdeath c hc
  · exact hfav

/-! ## 4. Guard: the old `Ahi²` death field is refuted by a `2/(n(n-1))` witness -/

/--
A concrete counterexample certificate for the old `Ahi = 1` death field.

To instantiate this, use the four-agent shape described in the design note:
one unassigned phase-0 CR, one assigned phase-0 CR, and enough other phase-0
agents to meet the chosen `FreshPoolDriftRegion` side conditions.  The key lower
bound is the scheduler mass of the two ordered pairs between the unassigned CR
and the assigned CR.
-/
structure OldAhiSqDeathCounterexample
    (n uMin : ℕ) where
  hn2 : 2 ≤ n
  c : Config (AgentState L K)

  hregion :
    RoleSplitFloorDischarge.FreshPoolDriftRegion
      (L := L) (K := K) n uMin 1 c

  /-- The real one-step drain mass is at least `2/(n(n-1))`. -/
  hlower :
    ENNReal.ofReal ((2 : ℝ) / (n * (n - 1) : ℝ))
      ≤ r4FreshCRDrainMass (L := L) (K := K) c

/--
Any instantiated `OldAhiSqDeathCounterexample` refutes the old too-tight
`Ahi²/(n(n-1))` death bound at `Ahi = 1`.
-/
theorem not_old_Ahi_sq_hdeath_of_counterexample
    {n uMin : ℕ}
    (X : OldAhiSqDeathCounterexample (L := L) (K := K) n uMin) :
    ¬
      (∀ c,
        RoleSplitFloorDischarge.FreshPoolDriftRegion
          (L := L) (K := K) n uMin 1 c →
        r4FreshCRDrainMass (L := L) (K := K) c
          ≤ ENNReal.ofReal
            (((1 * 1 : ℕ) : ℝ) / (n * (n - 1) : ℝ))) := by
  intro hold
  have hupper := hold X.c X.hregion
  have hle :
      ENNReal.ofReal ((2 : ℝ) / (n * (n - 1) : ℝ))
        ≤ ENNReal.ofReal (((1 * 1 : ℕ) : ℝ) / (n * (n - 1) : ℝ)) :=
    le_trans X.hlower hupper

  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast X.hn2
  have hden_pos : (0 : ℝ) < (n * (n - 1) : ℝ) := by nlinarith

  have hreal :
      (((1 * 1 : ℕ) : ℝ) / (n * (n - 1) : ℝ))
        < (2 : ℝ) / (n * (n - 1) : ℝ) := by
    have h1 : ((1 * 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1, div_lt_div_iff_of_pos_right hden_pos]
    norm_num

  have hlt :
      ENNReal.ofReal (((1 * 1 : ℕ) : ℝ) / (n * (n - 1) : ℝ))
        < ENNReal.ofReal ((2 : ℝ) / (n * (n - 1) : ℝ)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ?_).mpr hreal
    positivity

  exact (not_lt_of_ge hle) hlt

#print axioms crCount
#print axioms FreshPoolCRDriftRegion.toFreshPool
#print axioms ScalarPoolFavCR
#print axioms freshPoolCRBirthDeathFacts_of_parts
#print axioms fresh_pool_expNeg_one_step_drift_cr
#print axioms not_old_Ahi_sq_hdeath_of_counterexample

end FreshPoolDeathCorrected

end ExactMajority

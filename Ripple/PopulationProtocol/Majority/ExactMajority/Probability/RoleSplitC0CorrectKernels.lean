
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# RoleSplitC0CorrectKernels — fresh-gated floor drift and martingale windows

This file corrects the C0 kernel shape:

* Floor: use `pool_expNeg_one_step_drift_abstract` / scalar favorability, but
  strengthen `PoolDriftRegion` with `NoAssignedMcrConfig`, because Rule-1 birth
  needs unassigned MCRs.
* Windows: use a direct martingale-window atom, not a rare strict-rise fact.

No sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitC0MicroFacts
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitC0RiseObstruction

namespace ExactMajority
namespace RoleSplitFloorDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open RoleSplitConcentration
open FloorPrefix

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## 1. Correct floor drift gate: `PoolDriftRegion ∧ NoAssignedMcrConfig` -/

/--
The honest pool-drift region for the Rule-1 birth lower bound.

The landed `FloorPrefix.PoolDriftRegion` has the analytic band conditions, but
not the freshness invariant required by `assignable_rule1_both_fresh`.  We add
`NoAssignedMcrConfig` here.
-/
def FreshPoolDriftRegion (n uMin Ahi : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  PoolDriftRegion (L := L) (K := K) n uMin Ahi c ∧
  NoAssignedMcrConfig (L := L) (K := K) c

theorem FreshPoolDriftRegion.toPoolDriftRegion
    {n uMin Ahi : ℕ} {c : Config (AgentState L K)}
    (h : FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c) :
    PoolDriftRegion (L := L) (K := K) n uMin Ahi c :=
  h.1

theorem FreshPoolDriftRegion.noAssignedMcr
    {n uMin Ahi : ℕ} {c : Config (AgentState L K)}
    (h : FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c) :
    NoAssignedMcrConfig (L := L) (K := K) c :=
  h.2

/--
The `±2` lower step bound needed by `pool_expNeg_one_step_drift_abstract`.

This is just the reverse `+2` countP fact for `assignableCount`, transported to `ℤ`.
-/
theorem assignableCount_int_lower_step
    (Gate : Config (AgentState L K) → Prop) :
    ∀ c, Gate c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        (assignableCount (L := L) (K := K) c : ℤ) - 2
          ≤ (assignableCount (L := L) (K := K) c' : ℤ) := by
  intro c hc
  have h :=
    assignableCount_hstep_reverse_add_two (L := L) (K := K) Gate c hc
  filter_upwards [h] with c' hc'
  have hz : (assignableCount (L := L) (K := K) c : ℤ)
      ≤ (assignableCount (L := L) (K := K) c' : ℤ) + 2 := by
    exact_mod_cast hc'
  omega

/--
The two protocol-side mass facts for the fresh-gated pool drift.

These are the true irreducible interaction-PMF facts:

* `hbirth`: Rule-1 MCR-MCR mass gives the birth band;
* `hdeath`: Rule-4 fresh-CR/fresh-CR mass bounds the drain band.

They are gated by `FreshPoolDriftRegion`, not by arbitrary configurations.
-/
structure FreshPoolBirthDeathFacts
    (n uMin Ahi : ℕ) where
  /-- Rule-1 birth mass, using unassigned phase-0 MCR pairs. -/
  hbirth :
    ∀ c,
      FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      ENNReal.ofReal
        (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
        ≤ birthR1Mass (L := L) (K := K) c

  /-- Rule-4 fresh-CR drain mass. -/
  hdeath :
    ∀ c,
      FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      r4FreshCRDrainMass (L := L) (K := K) c
        ≤ ENNReal.ofReal
          (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ))

/--
Fresh-gated one-step pool drift.

This is the corrected wrapper over the landed analytic engine.  It avoids the
false bare-`PoolDriftRegion` quantification.
-/
theorem fresh_pool_expNeg_one_step_drift
    (n uMin Ahi : ℕ) (s : ℝ) (r : ℝ≥0∞) (hs : 0 < s)
    (hb0 : 0 ≤ ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hd0 : 0 ≤ ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hb1 : ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (hbd1 :
      ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)
        + ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (Facts : FreshPoolBirthDeathFacts (L := L) (K := K) n uMin Ahi)
    (hfav : ScalarPoolFav s n uMin Ahi r) :
    ∀ c,
      FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * poolExpNeg (L := L) (K := K) s c := by
  intro c hc
  refine pool_expNeg_one_step_drift_abstract
    (L := L) (K := K)
    s hs c
    (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    hb0 hd0 hb1 hbd1
    ?hstep ?hbirth ?hdeath r ?hfav
  · exact
      (assignableCount_int_lower_step
        (L := L) (K := K)
        (FreshPoolDriftRegion (L := L) (K := K) n uMin Ahi)) c hc
  · exact Facts.hbirth c hc
  · exact Facts.hdeath c hc
  · exact hfav

/-! ## 2. Concrete deterministic start bridge for the fresh region -/

/--
A `Phase0InitialFresh` start satisfies `NoAssignedMcrConfig`.

This is just re-exported in the current namespace so the floor-region facts can
consume it without reopening the Phase0InitialFresh file.
-/
theorem noAssignedMcr_of_fresh
    {n : ℕ} {c₀ : Config (AgentState L K)}
    (h : Phase0InitialFresh (L := L) (K := K) n c₀) :
    NoAssignedMcrConfig (L := L) (K := K) c₀ :=
  noAssignedMcrConfig_of_phase0InitialFresh (L := L) (K := K) h

/-! ## 3. Correct window interface: direct martingale atom -/

/--
The correct role-window concentration interface.

`RoleSplitWindows` is not a rare strict-rise event.  Main creation is expected,
and at a fresh all-MCR start its strict-rise probability is `1`.  Therefore the
window proof must be a centered martingale/Azuma/Bernstein statement about the
classification mix.

This atom directly supplies the tail of `RoleSplitWindows` from a fresh Phase-0
start.  All genuine martingale content is in `htail`, and the gate is explicit.
-/
structure RoleSplitWindowMartingaleAtom
    (η : ℝ) (n t : ℕ) (εwin : ℝ≥0∞) where
  Gate : Config (AgentState L K) → Prop

  hGate_of_fresh :
    ∀ c₀,
      Phase0InitialFresh (L := L) (K := K) n c₀ →
      Gate c₀

  /-- The centered role-allocation martingale/Azuma tail. -/
  htail :
    ∀ c₀,
      Phase0InitialFresh (L := L) (K := K) n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ RoleSplitWindows (L := L) (K := K) η n c} ≤ εwin

/-- Consumer theorem for the martingale role-window atom. -/
theorem roleSplitWindows_tail_of_martingale
    {η : ℝ} {n t : ℕ} {εwin : ℝ≥0∞}
    (A : RoleSplitWindowMartingaleAtom (L := L) (K := K) η n t εwin)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0InitialFresh (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
      {c | ¬ RoleSplitWindows (L := L) (K := K) η n c} ≤ εwin :=
  A.htail c₀ hinit

/-! ## 4. Corrected final C0 probabilistic package -/

/--
The corrected C0 probabilistic package.

It separates:
* floor concentration: fresh-gated pool birth/death facts;
* window concentration: a centered martingale atom;
* postwarm Stage 1: the already existing gated core.

No strict-rise role-window facts appear here.
-/
structure C0CorrectKernelFacts
    (η : ℝ) (n a₀ uMin Ahi Tstage Twin : ℕ) (hn2 : 2 ≤ n)
    (εwin εcore εshell εfloorFail : ℝ≥0∞) where
  floorFacts :
    FreshPoolBirthDeathFacts (L := L) (K := K) n uMin Ahi

  windowAtom :
    RoleSplitWindowMartingaleAtom (L := L) (K := K) η n Twin εwin

  postwarmCore :
    PostwarmStage1Core (L := L) (K := K)
      n a₀ uMin Tstage hn2 εcore εshell εfloorFail

end RoleSplitFloorDischarge
end ExactMajority

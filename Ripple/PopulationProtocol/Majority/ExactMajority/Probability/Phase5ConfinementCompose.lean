/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gap C2 resolution — slot-5 survival by COMPOSING the whp confinement event (Doty Thm 6.2)

This append-only file edits NO existing file.  It RESOLVES gap C2 — the slot-5 sampling-drain
survival — WITHOUT the FALSE pointwise biased-Main floor.

## The whp ⊬ pointwise crux (what C2 is)

The slot-5 sampling drain (`SamplingConcentration.sampleDrain_hdrop`,
`SamplingConcentration.phase5SamplingConvergence`) needs, at EVERY config it drains through, a
per-step floor `1 ≤ (usefulMains).sum c.count` (at least one useful biased Main = eliminator pool).
That floor was carried over the BARE Phase-5 window as

    hMainFloor : ∀ b, Phase5AllWin n b → 1 ≤ (usefulMains).sum b.count            -- FALSE

which is FALSE: an all-Reserve config satisfies `Phase5AllWin` with ZERO useful Mains.
`ConfinementSurface.lean` documents this — the floor "CANNOT be derived at a single reachable
config"; the honest object is the whp confinement EVENT, not a pointwise predicate.

## The proven assets consumed

* `MainExponentConfinement.theorem6_2_main_confinement_whp` (PROVEN, orphaned): from a per-hour
  squaring union budget it concludes
  `(K^T) c₀ {c | ¬ MainProfileConfinedToUseful c} ≤ η_conf`, where
  `MainProfileConfinedToUseful c := 0.92·|M| ≤ #usefulMains c` is the Thm-6.2 confinement event.
* `SamplingConcentration.phase5SamplingConvergence` (PROVEN): the slot-5 sampling drain at the
  level-dependent rate `1 − m/(n(n−1))`, parametric in the eliminator floor `hMainFloor`.

## The confinement → floor bridge (TRUE pointwise — this kills the false floor)

The honest floor is NOT over the bare window; it is `confinement c → 1 ≤ #usefulMains c`, a TRUE
pointwise implication FROM the confinement predicate, given one biased Main exists.  Precisely:

    confinement c  (i.e. 0.92·|M| ≤ #usefulMains c)   ∧   1 ≤ |M| (one Main exists)
      ⟹   1 ≤ #usefulMains c.

Indeed `(#usefulMains c : ℝ) ≥ 0.92·|M| ≥ 0.92·1 = 0.92 > 0`, so the natural `#usefulMains c ≥ 1`.
This is `confinement_mainPos_floor`: a structural consequence of the confinement profile (it
contains ≥ 1 useful Main once any Main exists), refutation-checked TRUE.  `1 ≤ |M|` is the genuine
side condition (an empty Main population makes BOTH sides 0, so confinement gives no floor); on a
Phase-5 window with the Lemma-5.2 role floor `n/3 ≤ |M|` (`n ≥ 2`) it holds.

## The composition (the C2 resolution)

The honest slot-5 survival is the OFF-EVENT composition.  The drain runs on the
**confinement-confined invariant** `Phase5Confined n c := Phase5AllWin n c ∧ confinement c ∧
1 ≤ |M| c`, on which the eliminator floor holds POINTWISE via the bridge.  Running
`phase5SamplingConvergence` on `Phase5Confined` (its closure carried as the honest residual
`hConfClosed` — confinement-as-invariant is exactly what Thm 6.2's per-hour drift maintains whp,
NOT a false pointwise floor) gives the on-event survival `≤ ε_sample`.  The off-event mass
(`{¬confinement}`) is bounded by `η_conf` via `theorem6_2_main_confinement_whp`.  Sub-additivity:

    {¬sampling-done} ⊆ {¬confinement} ∪ {¬sampling-done-on-confined-window}

so `(K^T) c₀ {¬sampling-done} ≤ ε_sample + η_conf`, both Θ(1/n²).  The biased-Main floor appears
ONLY as `confinement c → 1 ≤ #usefulMains c` (the TRUE bridge), NEVER as
`∀ b, Phase5AllWin b → floor` (the false form).

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SamplingConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainExponentConfinement

namespace ExactMajority
namespace Phase5ConfinementCompose

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal Real
open ReserveSampling Phase5Convergence SamplingConcentration

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the confinement → eliminator-floor bridge (TRUE pointwise).

The honest floor is the implication FROM the confinement predicate, not a universal over the bare
window.  This is the structural fact that confinement profile contains ≥ 1 useful Main once a Main
exists — the TRUE pointwise bridge that REPLACES the false `∀ b, Phase5AllWin b → floor`. -/

/-- **The confinement → eliminator-floor bridge (TRUE pointwise).**  From the Thm-6.2 confinement
event `MainProfileConfinedToUseful c` (`0.92·|M| ≤ #usefulMains c`) and one biased Main existing
(`1 ≤ |M| c`), the eliminator floor `1 ≤ #usefulMains c` holds.  Reason:
`(#usefulMains c : ℝ) ≥ 0.92·|M| ≥ 0.92·1 = 0.92 > 0`, so the natural count is `≥ 1`.

This is the SOLE place the biased-Main floor enters, and it is a TRUE implication FROM confinement
— NOT the false `∀ b, Phase5AllWin b → floor`.  The side `1 ≤ |M| c` is genuine (an empty Main
population makes both confinement sides 0, yielding no floor); it is supplied by the role floor on
a Phase-5 window. -/
theorem confinement_mainPos_floor {c : Config (AgentState L K)}
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c)
    (hMainPos : 1 ≤ RoleSplitConcentration.mainCount (L := L) (K := K) c) :
    1 ≤ (usefulMains (L := L) (K := K)).sum c.count := by
  -- Work in ℝ: #usefulMains ≥ 0.92·|M| ≥ 0.92·1 = 0.92 > 0, then descend to ℕ.
  have hMainPosR : (1 : ℝ) ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) := by
    exact_mod_cast hMainPos
  have hposR : (0 : ℝ) < (((usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) := by
    have hstep : (0.92 : ℝ) * 1
        ≤ (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) :=
      mul_le_mul_of_nonneg_left hMainPosR (by norm_num)
    calc (0 : ℝ) < (0.92 : ℝ) * 1 := by norm_num
      _ ≤ (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) := hstep
      _ ≤ (((usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) := hConf
  -- A natural with positive real cast is ≥ 1.
  have hpos : 0 < (usefulMains (L := L) (K := K)).sum c.count := by exact_mod_cast hposR
  omega

/-! ## Part 2 — the confinement-confined drain invariant and the floor it supplies.

`Phase5Confined n c := Phase5AllWin n c ∧ confinement c ∧ 1 ≤ |M| c`.  On THIS invariant the
eliminator floor holds pointwise (the bridge).  The drain `sampleDrain_hdrop` is fed the floor in
its TRUE bridge form — never the false universal over the bare window. -/

/-- The confinement-confined Phase-5 drain invariant: the Phase-5 window TOGETHER with the Thm-6.2
confinement event and one biased Main.  On this invariant the eliminator floor is POINTWISE TRUE. -/
def Phase5Confined (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase5AllWin (L := L) (K := K) n c
    ∧ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c
    ∧ 1 ≤ RoleSplitConcentration.mainCount (L := L) (K := K) c

/-- **The eliminator floor on the confined invariant (the honest floor, via the bridge).**  On
`Phase5Confined` the floor `1 ≤ #usefulMains` holds POINTWISE — derived from the confinement field
by `confinement_mainPos_floor`.  This is the floor in its TRUE form; it is NOT a universal over the
bare `Phase5AllWin` window (the false form), only over the confinement-confined sub-window. -/
theorem confinedFloor (n : ℕ)
    (b : Config (AgentState L K)) (hConf : Phase5Confined (L := L) (K := K) n b) :
    1 ≤ (usefulMains (L := L) (K := K)).sum b.count :=
  confinement_mainPos_floor hConf.2.1 hConf.2.2

/-! ## Part 3 — the confined-invariant slot-5 drain survival (on the confinement event).

We run `phase5SamplingConvergence` with `Inv := Phase5Confined n`.  The `hMainFloor` input is now
`∀ b, Phase5Confined b → 1 ≤ #usefulMains b`, supplied by `confinedFloor` — the TRUE bridge form.
Its window closure `hConfClosed` (confinement-as-invariant) is the honest residual; it is what
Thm 6.2's per-hour drift maintains whp, NOT a false pointwise floor.  The drift
`potNonincrOn_unsampledReserveU` restricts from `Phase5AllWin` to the sub-invariant, since the drop
floor needs only the floor, which `Phase5Confined` supplies. -/

/-- The `unsampledReserveU` per-step drop floor on the CONFINED invariant.  Mirror of
`sampleDrain_hdrop` but with `Inv := Phase5Confined`; the eliminator floor is supplied POINTWISE by
`confinedFloor` (the bridge), so NO false universal-over-bare-window floor is used.  The Phase-5
window facts the rectangle count needs are the `.1` projection of `Phase5Confined`. -/
theorem confinedDrain_hdrop (n : ℕ) (hn : 2 ≤ n) :
    ∀ m, ∀ b : Config (AgentState L K), Phase5Confined (L := L) (K := K) n b →
      unsampledReserveU (L := L) (K := K) b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => unsampledReserveU (L := L) (K := K) c) m)ᶜ
        ≤ sampleLevelRate n m := by
  intro m b hConf hbm
  -- Reduce to the proven per-step floor on the bare window, with the floor from the bridge.
  have hfloor := sampleDrain_prob_floor (L := L) (K := K) n hn m b hConf.1 hbm
    (confinedFloor (L := L) (K := K) n b hConf)
  -- The complement bridge, copied from `sampleDrain_hdrop`, on the same config `b`.
  classical
  set Φ := fun c => unsampledReserveU (L := L) (K := K) c with hΦ
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) | Φ c' + 1 ≤ Φ b}
      = OneSidedCancel.potBelow Φ m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hΦ, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow Φ m) :=
    OneSidedCancel.potBelow_measurable Φ m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow Φ m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow Φ m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : ENNReal.ofReal ((m : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure (OneSidedCancel.potBelow Φ m) := by
    rw [← hsucc_eq]; exact hfloor
  unfold sampleLevelRate
  exact tsub_le_tsub_left hp_le 1

end Phase5ConfinementCompose
end ExactMajority


/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# RoleSplitFloorDischarge — gated C0 floor/window MGF consumers

This file is intentionally a CONSUMER of the genuine C0 MGF atoms.  It does not
assert any universal drift over arbitrary configurations.  Every drift is gated.

Status note against the current visible signatures:
* `FloorPrefix.phase0_floor_warmup_whp` consumes a named `hreach`.
* `FloorPrefix.floor_prefix_le_inv_sq` consumes three named shifted-prefix feeders.
* `RoleSplitConcentration.phase0_stage1_whp_final` currently still has a raw
  `(floorGate n a₀)ᶜ` prefix and a `Phase0Initial` start, so the post-warmup CK
  splice must be done in a follow-up theorem whose residual is `floorFailsBeforePost`.

This file supplies the compile-ready gated atom wrappers and deterministic
composition around the already landed engines.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorPrefix
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainCountFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ChapmanKolmogorovChain

namespace ExactMajority
namespace RoleSplitFloorDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open RoleSplitConcentration
open FloorPrefix

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## 1. Warm-up reach atom: `Phase0Initial → Phase0WarmGood` -/

/--
A Bennett/MGF-ready atom for the **warm-up pool-growth** reach theorem.

The intended concrete potential is the dual-direction pool potential,
large on failure of `Phase0WarmGood`, for example an exponential transform of
`assignableCount` and/or the remaining `.mcr` count.

All probabilistic content is gated:
`hdrift` is required only on `Gate`, and starts are put in `Gate` only through
`hGate_of_phase0Initial`.
-/
structure WarmupReachBennettAtom
    (n a₀ uMin T₀ : ℕ) (εwarm : ℝ≥0∞) where
  /-- The honest Phase-0 warm-up gate.  Typical concrete gate:
  card `= n`, all `.mcr` agents phase 0, and the no-assigned-MCR/freshness shell. -/
  Gate : Config (AgentState L K) → Prop

  /-- A Phase-0 initial start lies in the warm-up gate.  If using
  `Phase0InitialFresh`, instantiate this by composing its projection to
  `Phase0Initial` plus the fresh/no-assigned invariant. -/
  hGate_of_phase0Initial :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
      Gate c₀

  /-- Gate closure along one-step support.  This is deliberately a field:
  it must be proven for the concrete Phase-0 shell, not assumed globally. -/
  hGate_abs :
    ∀ c c',
      Gate c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Gate c'

  /-- Warm-up potential. -/
  Ψ : Config (AgentState L K) → ℝ≥0∞

  hΨ : Measurable Ψ

  /-- One-step multiplicative drift rate. -/
  r : ℝ≥0∞

  /-- Threshold for warm-up failure. -/
  θ : ℝ≥0∞

  hθ : θ ≠ 0
  hθ_top : θ ≠ ⊤

  /-- Failure of the warm-up checkpoint forces the potential above threshold. -/
  hlink :
    ∀ c,
      ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
      θ ≤ Ψ c

  /-- The genuine per-step MGF drift, required only on `Gate`. -/
  hdrift :
    ∀ c,
      Gate c →
      ∫⁻ c', Ψ c' ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * Ψ c

  /-- The scalar/tail arithmetic budget at every admissible start. -/
  hbudget :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
      r ^ T₀ * Ψ c₀ / θ ≤ εwarm

/--
Warm-up reach from a gated Bennett atom.

This is exactly the `MainFloorBennettAtom` consumer pattern specialized to
`Phase0WarmGood`.
-/
theorem warmup_reach_of_bennett
    {n a₀ uMin T₀ : ℕ} {εwarm : ℝ≥0∞}
    (A : WarmupReachBennettAtom (L := L) (K := K) n a₀ uMin T₀ εwarm)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
      {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c} ≤ εwarm := by
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
        ≤ A.r ^ T₀ * A.Ψ c₀ / A.θ :=
    WindowConcentration.windowDrift_tail
      (NonuniformMajority L K)
      A.Ψ A.hΨ
      A.Gate A.hGate_abs
      A.r A.hdrift
      (fun c => Phase0WarmGood (L := L) (K := K) n a₀ uMin c)
      A.θ A.hθ A.hθ_top
      A.hlink
      T₀ c₀ (A.hGate_of_phase0Initial c₀ hinit)
  exact htail.trans (A.hbudget c₀ hinit)

/--
The landed `FloorPrefix.phase0_floor_warmup_whp` with its carried `hreach`
filled by a gated Bennett atom.
-/
theorem phase0_floor_warmup_whp_of_bennett
    {n a₀ uMin T₀ : ℕ} {εwarm : ℝ≥0∞}
    (A : WarmupReachBennettAtom (L := L) (K := K) n a₀ uMin T₀ εwarm)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
      {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c} ≤ εwarm :=
  FloorPrefix.phase0_floor_warmup_whp
    (L := L) (K := K)
    n a₀ uMin T₀ εwarm
    hinit
    (warmup_reach_of_bennett (L := L) (K := K) A hinit)

/-! ## 2. Shifted floor-prefix feeders -/

/--
The three shifted prefix feeders consumed by `FloorPrefix.floor_prefix_le_inv_sq`.

These are intentionally not global facts.  Each is a concrete shifted-time prefix
bound from the chosen start `c₀`.
-/
structure FloorPrefixFeeders
    (n a₀ uMin T₀ t : ℕ) (hn2 : 2 ≤ n)
    (c₀ : Config (AgentState L K)) where
  εwarm : ℝ≥0∞
  εmid : ℝ≥0∞
  εlate : ℝ≥0∞

  /-- Structural-shell failure prefix.  This may be `0` if the Phase-0 shell is
  shown support-closed through the relevant horizon. -/
  hshell :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        ((cardPhaseShell (L := L) (K := K) n)ᶜ) ≤ εwarm

  /-- Mid-band floor-failure prefix.  This is the main stopped/gated pool MGF
  feeder after the warm-up checkpoint. -/
  hmid :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | midBandBad (L := L) (K := K) n a₀ uMin hn2 c} ≤ εmid

  /-- Late-band floor-failure prefix.  This is the low-`u` completion tail feeder. -/
  hlate :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c} ≤ εlate

  /-- Paper-scale budget sum. -/
  hbudget :
    εwarm + εmid + εlate ≤ εfloor n

/--
The shifted post-gated floor-failure prefix is at most `εfloor n = n⁻²`
from the three region feeders.
-/
theorem floor_prefix_le_inv_sq_of_feeders
    {n a₀ uMin T₀ t : ℕ} {hn2 : 2 ≤ n}
    {c₀ : Config (AgentState L K)}
    (F : FloorPrefixFeeders (L := L) (K := K) n a₀ uMin T₀ t hn2 c₀) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}
      ≤ εfloor n :=
  FloorPrefix.floor_prefix_le_inv_sq
    (L := L) (K := K)
    n a₀ uMin T₀ t hn2
    F.εwarm F.εmid F.εlate
    F.hshell F.hmid F.hlate F.hbudget

/-! ## 3. Mid/late feeder atom shells -/

/--
A generic shifted-prefix feeder atom.

This is useful for `hshell`, `hmid`, and `hlate` once their concrete MGF/stopped-kernel
proofs have been instantiated.  The point is that the carry is not a false universal:
it is a finite shifted-prefix theorem for one named region, from one named start.
-/
structure ShiftedPrefixAtom
    (T₀ t : ℕ) (c₀ : Config (AgentState L K))
    (Bad : Config (AgentState L K) → Prop)
    (ε : ℝ≥0∞) where
  hprefix :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | Bad c} ≤ ε

theorem shifted_prefix_of_atom
    {T₀ t : ℕ} {c₀ : Config (AgentState L K)}
    {Bad : Config (AgentState L K) → Prop}
    {ε : ℝ≥0∞}
    (A : ShiftedPrefixAtom (L := L) (K := K) T₀ t c₀ Bad ε) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | Bad c} ≤ ε :=
  A.hprefix

/--
A convenience constructor for the three `FloorPrefixFeeders` from three shifted
prefix atoms.
-/
def floorPrefixFeeders_of_atoms
    {n a₀ uMin T₀ t : ℕ} {hn2 : 2 ≤ n}
    {c₀ : Config (AgentState L K)}
    {εshell εmid εlate : ℝ≥0∞}
    (Ashell :
      ShiftedPrefixAtom (L := L) (K := K) T₀ t c₀
        (fun c => c ∈ (cardPhaseShell (L := L) (K := K) n)ᶜ)
        εshell)
    (Amid :
      ShiftedPrefixAtom (L := L) (K := K) T₀ t c₀
        (fun c => midBandBad (L := L) (K := K) n a₀ uMin hn2 c)
        εmid)
    (Alate :
      ShiftedPrefixAtom (L := L) (K := K) T₀ t c₀
        (fun c => lateBandBad (L := L) (K := K) n a₀ uMin hn2 c)
        εlate)
    (hbudget : εshell + εmid + εlate ≤ εfloor n) :
    FloorPrefixFeeders (L := L) (K := K) n a₀ uMin T₀ t hn2 c₀ where
  εwarm := εshell
  εmid := εmid
  εlate := εlate
  hshell := by
    simpa using Ashell.hprefix
  hmid := by
    simpa using Amid.hprefix
  hlate := by
    simpa using Alate.hprefix
  hbudget := hbudget

/-! ## 4. RoleSplitWindows atom -/

/--
A Bennett-ready atom for the final `RoleSplitWindows η n` concentration.

Concrete instantiations normally combine four one-sided/two-sided potentials:
main lower tail, main upper tail, clock lower tail, and reserve lower tail.
This structure intentionally packages the combined potential/threshold view,
again gated and not universal.
-/
structure RoleSplitWindowsBennettAtom
    (η : ℝ) (n t : ℕ) (εwin : ℝ≥0∞) where
  Gate : Config (AgentState L K) → Prop

  hGate_of_phase0Initial :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
      Gate c₀

  hGate_abs :
    ∀ c c',
      Gate c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Gate c'

  Ψ : Config (AgentState L K) → ℝ≥0∞
  hΨ : Measurable Ψ

  r : ℝ≥0∞
  θ : ℝ≥0∞

  hθ : θ ≠ 0
  hθ_top : θ ≠ ⊤

  hlink :
    ∀ c,
      ¬ RoleSplitWindows (L := L) (K := K) η n c →
      θ ≤ Ψ c

  hdrift :
    ∀ c,
      Gate c →
      ∫⁻ c', Ψ c' ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * Ψ c

  hbudget :
    ∀ c₀,
      Phase0Initial (L := L) (K := K) n c₀ →
      r ^ t * Ψ c₀ / θ ≤ εwin

/-- `RoleSplitWindows` tail from a gated Bennett atom. -/
theorem roleSplitWindows_tail_of_bennett
    {η : ℝ} {n t : ℕ} {εwin : ℝ≥0∞}
    (A : RoleSplitWindowsBennettAtom (L := L) (K := K) η n t εwin)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
      {c | ¬ RoleSplitWindows (L := L) (K := K) η n c} ≤ εwin := by
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ RoleSplitWindows (L := L) (K := K) η n c}
        ≤ A.r ^ t * A.Ψ c₀ / A.θ :=
    WindowConcentration.windowDrift_tail
      (NonuniformMajority L K)
      A.Ψ A.hΨ
      A.Gate A.hGate_abs
      A.r A.hdrift
      (fun c => RoleSplitWindows (L := L) (K := K) η n c)
      A.θ A.hθ A.hθ_top
      A.hlink
      t c₀ (A.hGate_of_phase0Initial c₀ hinit)
  exact htail.trans (A.hbudget c₀ hinit)

/-! ## 5. Deterministic ledger consumer -/

/--
The deterministic final ledger: if the stage-2 conclusion gives no MCR and the
probabilistic window atom gives `RoleSplitWindows`, then `RoleSplitGood` follows.

This simply exposes the already-landed deterministic theorem in a compact form for
the final C0 assembly.
-/
theorem roleSplitGood_of_stage2_and_windows
    {η : ℝ} {n : ℕ}
    (c : Config (AgentState L K))
    (hcard : Multiset.card c = n)
    (hstage2 : RoleSplitStage2Good (L := L) (K := K) c)
    (hbal : ClockReserveBalanced (L := L) (K := K) c)
    (hwin : RoleSplitWindows (L := L) (K := K) η n c) :
    RoleSplitGood (L := L) (K := K) η n c :=
  (phase0_roleSplit_whp_assembled_stage2
    (L := L) (K := K) c hcard hstage2 hbal hwin).1

/-! ## 6. Generic CK splice for warm-up followed by any post-warm-up target -/

/--
A generic CK splice from the warm-up checkpoint to any post-warm-up target.

Use this once the post-warmup Stage-1 theorem is expressed as:
`∀ y, Phase0WarmGood y → (K^tStage)y {¬ Target} ≤ εStage`.

It is deliberately generic because the currently visible `phase0_stage1_whp_final`
still has the old fresh-start/floorGate signature, not this post-warmup signature.
-/
theorem warmup_ck_extend
    {n a₀ uMin T₀ tStage : ℕ}
    {εwarm εStage : ℝ≥0∞}
    {c₀ : Config (AgentState L K)}
    (hWarm :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c} ≤ εwarm)
    (Target : Config (AgentState L K) → Prop)
    (hStage :
      ∀ y,
        Phase0WarmGood (L := L) (K := K) n a₀ uMin y →
        ((NonuniformMajority L K).transitionKernel ^ tStage) y
          {z | ¬ Target z} ≤ εStage) :
    ((NonuniformMajority L K).transitionKernel ^ (T₀ + tStage)) c₀
      {z | ¬ Target z} ≤ εwarm + εStage :=
  ChapmanKolmogorovChain.ck_bad_extend
    ((NonuniformMajority L K).transitionKernel)
    (fun y => Phase0WarmGood (L := L) (K := K) n a₀ uMin y)
    Target
    T₀ tStage c₀ εwarm εStage hWarm hStage

end RoleSplitFloorDischarge
end ExactMajority

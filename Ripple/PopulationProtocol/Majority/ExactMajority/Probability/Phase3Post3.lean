/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 3 final Post₃ snapshot and deterministic closure

This file is the slot-3 Piece 8 surface.

It deliberately separates Doty's final Lemma 6.18 step into:

* a probabilistic snapshot at `end_(ell+2)`, carrying the remaining Core/6.17 tail;
* a deterministic reachability closure while the population is still in Phase 3.

No probability appears in the closure.  The deterministic readout is exposed as
explicit fields so the later discharge can prove it from the Phase-3 transition
algebra (`g`, `μ`, and `μAbove`) plus quantization.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Engines
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ChapmanKolmogorovChain
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Post3

open P3DeterministicAlgebra

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Phase-3 observables and Post₃ -/

/-- Exact Phase-3 support at population size `n`. -/
def AllPhase3 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c

/-- Real-valued positive dyadic mass. -/
noncomputable def betaPlus (c : Config (AgentState L K)) : ℝ :=
  (betaPlusQ (L := L) (K := K) c : ℝ)

/-- Real-valued negative dyadic mass. -/
noncomputable def betaMinus (c : Config (AgentState L K)) : ℝ :=
  (betaMinusQ (L := L) (K := K) c : ℝ)

/-- Real-valued signed weighted bias `g = β₊ - β₋`. -/
noncomputable def signedGap (c : Config (AgentState L K)) : ℝ :=
  Phase3Pre3.signedGap (L := L) (K := K) c

/-- Slot-3 entry pins the exact Phase-3 window together with the preserved
initial signed gap. -/
def Slot3Entry (n : ℕ) (g₀ : ℝ) (c : Config (AgentState L K)) : Prop :=
  AllPhase3 (L := L) (K := K) n c ∧
    signedGap (L := L) (K := K) c = g₀

theorem Slot3Entry.phase3 {n : ℕ} {g₀ : ℝ}
    {c : Config (AgentState L K)}
    (h : Slot3Entry (L := L) (K := K) n g₀ c) :
    AllPhase3 (L := L) (K := K) n c :=
  h.1

theorem Slot3Entry.gap_eq {n : ℕ} {g₀ : ℝ}
    {c : Config (AgentState L K)}
    (h : Slot3Entry (L := L) (K := K) n g₀ c) :
    signedGap (L := L) (K := K) c = g₀ :=
  h.2

/-- Real-valued total weighted mass `μ = β₊ + β₋`. -/
noncomputable def weightedMass (c : Config (AgentState L K)) : ℝ :=
  Phase3Pre3.weightedMass (L := L) (K := K) c

/-- Real-valued deterministic-algebra strict upper-tail mass. -/
noncomputable def massAboveQReal (h : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (massAboveQ (L := L) (K := K) h c : ℝ)

/-- The minority mass determined by the preserved majority sign. -/
noncomputable def minorityMass (σ : Sign) (c : Config (AgentState L K)) : ℝ :=
  match σ with
  | .pos => betaMinus (L := L) (K := K) c
  | .neg => betaPlus (L := L) (K := K) c

/-- The majority mass determined by the preserved majority sign. -/
noncomputable def majorityMass (σ : Sign) (c : Config (AgentState L K)) : ℝ :=
  match σ with
  | .pos => betaPlus (L := L) (K := K) c
  | .neg => betaMinus (L := L) (K := K) c

/-- The opinion sign opposite to the preserved majority sign. -/
def minoritySignOfMajority : Sign → Sign
  | .pos => .neg
  | .neg => .pos

/-- All biased agents carrying the minority sign, irrespective of role.  This is
the count-level conclusion needed for exact readout; a mass upper bound is not
strong enough in the large-population regime. -/
noncomputable def minorityBiasedAgents (σ : Sign) :
    Finset (AgentState L K) :=
  Finset.univ.filter fun a =>
    ∃ i : Fin (L + 1), a.bias = Bias.dyadic (minoritySignOfMajority σ) i

/-- Count of minority-opinion biased agents. -/
noncomputable def minorityBiasedCount (σ : Sign)
    (c : Config (AgentState L K)) : ℕ :=
  (minorityBiasedAgents (L := L) (K := K) σ).sum c.count

/-- Real signed gap decomposes as `β₊ - β₋`. -/
theorem signedGap_eq_betaPlus_sub_betaMinus
    (c : Config (AgentState L K)) :
    signedGap (L := L) (K := K) c =
      betaPlus (L := L) (K := K) c -
        betaMinus (L := L) (K := K) c := by
  unfold signedGap Phase3Pre3.signedGap betaPlus betaMinus
  exact_mod_cast
    (biasSumQ_eq_betaPlus_sub_betaMinus (L := L) (K := K) c)

/-- Sign condition for the preserved signed gap. -/
def WinningGap (σ : Sign) (g₀ : ℝ) : Prop :=
  match σ with
  | .pos => 0 < g₀
  | .neg => g₀ < 0

/-- Majority mass equals the preserved signed gap, with sign orientation. -/
def MajorityMassMatches (σ : Sign) (g₀ : ℝ)
    (c : Config (AgentState L K)) : Prop :=
  match σ with
  | .pos => majorityMass (L := L) (K := K) σ c = g₀
  | .neg => majorityMass (L := L) (K := K) σ c = -g₀

/-- The Phase-3 mass readout expected by the phase-4 adapter. -/
def ReadyForPhase4 (ell : ℕ) (M : ℝ) (σ : Sign) (g₀ : ℝ)
    (c : Config (AgentState L K)) : Prop :=
  signedGap (L := L) (K := K) c = g₀ ∧
    minorityMass (L := L) (K := K) σ c ≤
      (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))

/-- Final slot-3 postcondition.

This remains an exact Phase-3 endpoint.  It is not a global postcondition over
the later Phase-4/cleanup phases.
-/
structure Post3 (n ell : ℕ) (M : ℝ) (σ : Sign) (g₀ : ℝ)
    (c : Config (AgentState L K)) : Prop where
  phase3 : AllPhase3 (L := L) (K := K) n c
  gap_eq : signedGap (L := L) (K := K) c = g₀
  minority_small :
    minorityMass (L := L) (K := K) σ c ≤
      (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  main_confined :
    MainExponentConfinement.MainProfileConfinedToUseful
      (L := L) (K := K) c

theorem Post3.ready {n ell : ℕ} {M : ℝ} {σ : Sign} {g₀ : ℝ}
    {c : Config (AgentState L K)}
    (h : Post3 (L := L) (K := K) n ell M σ g₀ c) :
    ReadyForPhase4 (L := L) (K := K) ell M σ g₀ c :=
  ⟨h.gap_eq, h.minority_small⟩

theorem Post3.phase3_shape {n ell : ℕ} {M : ℝ} {σ : Sign} {g₀ : ℝ}
    {c : Config (AgentState L K)}
    (h : Post3 (L := L) (K := K) n ell M σ g₀ c) :
    SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c :=
  h.phase3

theorem Post3.to_confinement {n ell : ℕ} {M : ℝ} {σ : Sign} {g₀ : ℝ}
    {c : Config (AgentState L K)}
    (h : Post3 (L := L) (K := K) n ell M σ g₀ c) :
    SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
      MainExponentConfinement.MainProfileConfinedToUseful
        (L := L) (K := K) c :=
  ⟨h.phase3, h.main_confined⟩

/-! ## The probabilistic snapshot at `end_(ell+2)` -/

/-- The `end_(ell+2)` snapshot produced by Core(h) at `h = ell+2` plus Lemma 6.17.

The domain fact `ell+2≤L` is intentionally not hidden inside this predicate; it is
carried by the tail object below.
-/
structure Snapshot617 (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (c : Config (AgentState L K)) : Prop where
  phase3 : AllPhase3 (L := L) (K := K) n c
  gap_eq : signedGap (L := L) (K := K) c = g₀
  total_mass_bound :
    weightedMass (L := L) (K := K) c ≤
      Lemma616TotalMass.Constants.rho_l * M * (2 : ℝ) ^ (-(ell : ℤ))
  muAbove_bound :
    Lemma615MassAbove.muAbove (L := L) (K := K) ell c ≤
      (1 / 500 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  minority_bound :
    minorityMass (L := L) (K := K) σ c ≤
      (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  main_confined :
    MainExponentConfinement.MainProfileConfinedToUseful
      (L := L) (K := K) c

/-- Constructor wiring the 6.17 minority-mass cap into the `Snapshot617`
readout. -/
def Snapshot617.ofCapBound
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign} {c : Config (AgentState L K)}
    (hphase : AllPhase3 (L := L) (K := K) n c)
    (hgap : signedGap (L := L) (K := K) c = g₀)
    (htotal :
      weightedMass (L := L) (K := K) c ≤
        Lemma616TotalMass.Constants.rho_l * M * (2 : ℝ) ^ (-(ell : ℤ)))
    (hmuAbove :
      Lemma615MassAbove.muAbove (L := L) (K := K) ell c ≤
        (1 / 500 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)))
    (hminority :
      minorityMass (L := L) (K := K) σ c ≤
        (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)))
    (hmain :
      MainExponentConfinement.MainProfileConfinedToUseful
        (L := L) (K := K) c) :
    Snapshot617 (L := L) (K := K) n ell M g₀ σ c where
  phase3 := hphase
  gap_eq := hgap
  total_mass_bound := htotal
  muAbove_bound := hmuAbove
  minority_bound := hminority
  main_confined := hmain

/-- The strengthened snapshot is already the Post₃ readout at the same
`end_(ell+2)` endpoint. -/
theorem Snapshot617.toPost3
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign} {c : Config (AgentState L K)}
    (hs : Snapshot617 (L := L) (K := K) n ell M g₀ σ c) :
    Post3 (L := L) (K := K) n ell M σ g₀ c where
  phase3 := hs.phase3
  gap_eq := hs.gap_eq
  minority_small := hs.minority_bound
  main_confined := hs.main_confined

/-! ## Concrete `end_(ell+2)` horizon surface -/

/-- Per-hour synchronous-window budget: the `2/c + 47/m` work window plus a
caller-supplied slack term for the clock-front gap around that hour. -/
def phase3HourBudget (θ : Phase3GoodClock.ClockTimingParams)
    (slack : ℕ → ℕ) (h : ℕ) : ℕ :=
  θ.twoOverC + θ.fortySevenOverM + slack h

/-- The concrete hour-sum horizon through `end_(ell+2)`.  There are `ell+3`
hours, indexed `0, …, ell+2`. -/
def phase3EndHourSum (θ : Phase3GoodClock.ClockTimingParams)
    (slack : ℕ → ℕ) (ell : ℕ) : ℕ :=
  Finset.sum (Finset.range (ell + 3)) (fun h => phase3HourBudget θ slack h)

/-- A concrete horizon certificate for the `end_(ell+2)` snapshot.

The actual tail horizon is tied to `GoodClock.finish (ell+2)`, i.e. the
`end_h` first-hit interface.  The numerical proof is separated into the honest
hour-sum upper bound and a per-hour `≤ 17*n` budget. -/
structure Snapshot617Horizon (n ell : ℕ) where
  T_end_l2 : ℕ
  h_l2 : ell + 2 ≤ L
  M : ℕ
  θ : Phase3GoodClock.ClockTimingParams
  tr : Phase3GoodClock.Trace L K
  good : Phase3GoodClock.GoodClock (L := L) (K := K) M θ tr
  slack : ℕ → ℕ
  T_end_l2_eq_end_h :
    T_end_l2 =
      Phase3GoodClock.GoodClock.finish (L := L) (K := K) good (ell + 2)
  end_le_hourSum :
    T_end_l2 ≤ phase3EndHourSum θ slack ell
  per_hour_le :
    ∀ h, h < ell + 3 → phase3HourBudget θ slack h ≤ 17 * n

namespace Snapshot617Horizon

/-- The hour-count times per-hour-budget arithmetic for the concrete
`end_(ell+2)` horizon. -/
theorem T_end_l2_le {n ell : ℕ}
    (H : Snapshot617Horizon (L := L) (K := K) n ell) :
    H.T_end_l2 ≤ 17 * n * (L + 1) := by
  have hsum :
      phase3EndHourSum H.θ H.slack ell ≤ (ell + 3) * (17 * n) := by
    unfold phase3EndHourSum
    calc
      Finset.sum (Finset.range (ell + 3))
          (fun h => phase3HourBudget H.θ H.slack h)
          ≤ Finset.sum (Finset.range (ell + 3)) (fun _ => 17 * n) := by
            refine Finset.sum_le_sum ?_
            intro h hh
            exact H.per_hour_le h (Finset.mem_range.mp hh)
      _ = (ell + 3) * (17 * n) := by
            simp
  have hcount : ell + 3 ≤ L + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right H.h_l2 1
  have hmul : (ell + 3) * (17 * n) ≤ (L + 1) * (17 * n) :=
    Nat.mul_le_mul_right (17 * n) hcount
  calc
    H.T_end_l2 ≤ phase3EndHourSum H.θ H.slack ell := H.end_le_hourSum
    _ ≤ (ell + 3) * (17 * n) := hsum
    _ ≤ (L + 1) * (17 * n) := hmul
    _ = 17 * n * (L + 1) := by
      ac_rfl

end Snapshot617Horizon

/-- The probabilistic half of Lemma 6.18: the endpoint at `end_(ell+2)` satisfies
the 6.17 snapshot except with failure probability `ε`.
-/
structure Snapshot617Tail (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  horizon : Snapshot617Horizon (L := L) (K := K) n ell
  ε : ℝ≥0
  tail :
    ∀ c₀,
      Slot3Entry (L := L) (K := K) n g₀ c₀ →
      ((NonuniformMajority L K).transitionKernel ^ horizon.T_end_l2) c₀
        {c | ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c}
        ≤ (ε : ℝ≥0∞)

/-- The killed-chain state space is discrete.  The immediate-kill kernel already
uses this convention in `GatedKillNow`; the local instances make `ChapmanKolmogorovChain`
available for the lifted state space. -/
local instance instOptionMSPhase3Post3 :
    MeasurableSpace (Option (Config (AgentState L K))) := ⊤

local instance instOptionDMSPhase3Post3 :
    DiscreteMeasurableSpace (Option (Config (AgentState L K))) :=
  ⟨fun _ => trivial⟩

/-- A finite killed-kernel hour chain whose final alive good gate reads out the
full `Snapshot617` endpoint.  The per-hour probabilistic content is isolated in
`tail`; `toSnapshot617Tail` below is only the killed CK/union composition plus
the final `real_le_killed_now` transfer back to the full kernel. -/
structure Snapshot617HourChain (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  horizon : Snapshot617Horizon (L := L) (K := K) n ell
  gate : Set (Config (AgentState L K))
  H : ℕ
  hourLen : ℕ → ℕ
  Good : ℕ → Option (Config (AgentState L K)) → Prop
  ηhour : ℕ → ℝ≥0∞
  good0 :
    ∀ c₀,
      Slot3Entry (L := L) (K := K) n g₀ c₀ →
        Good 0 (some c₀)
  none_bad :
    ¬ Good H none
  tail :
    ∀ i, i < H → ∀ o,
      Good i o →
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel gate ^ hourLen i) o
          {x | ¬ Good (i + 1) x} ≤ ηhour i
  readout :
    ∀ c, Good H (some c) →
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c
  horizon_eq :
    horizon.T_end_l2 = ChapmanKolmogorovChain.hourPrefix hourLen H
  ε : ℝ≥0
  budget :
    (∑ i ∈ Finset.range H, ηhour i) ≤ (ε : ℝ≥0∞)

namespace Snapshot617HourChain

/-- Compose a killed-kernel hour chain into the `Snapshot617Tail` endpoint tail.

The CK iteration is performed entirely on `killK_now`; only after the killed
endpoint bad mass is bounded do we transfer the full-kernel endpoint event by
`GatedDrift.real_le_killed_now`. -/
noncomputable def toSnapshot617Tail
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Snapshot617HourChain (L := L) (K := K) n ell M g₀ σ) :
    Snapshot617Tail (L := L) (K := K) n ell M g₀ σ where
  horizon := A.horizon
  ε := A.ε
  tail := by
    intro c₀ hpre
    have hchain :
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
            ChapmanKolmogorovChain.hourPrefix A.hourLen A.H) (some c₀)
          {x | ¬ A.Good A.H x}
          ≤ ∑ i ∈ Finset.range A.H, A.ηhour i :=
      ChapmanKolmogorovChain.ck_chain_bad_bound_lt
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate)
        A.Good A.hourLen A.ηhour (some c₀) (A.good0 c₀ hpre) A.H A.tail
    have hchainT :
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
            A.horizon.T_end_l2) (some c₀)
          {x | ¬ A.Good A.H x}
          ≤ ∑ i ∈ Finset.range A.H, A.ηhour i := by
      rw [A.horizon_eq]
      exact hchain
    have hsub :
        {o : Option (Config (AgentState L K)) |
          o = none ∨
            (∃ c, o = some c ∧
              ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c)}
          ⊆ {o | ¬ A.Good A.H o} := by
      intro o hbad hgood
      rcases hbad with hnone | ⟨c, hsome, hbadSnap⟩
      · subst o
        exact A.none_bad hgood
      · subst o
        exact hbadSnap (A.readout c hgood)
    calc
      ((NonuniformMajority L K).transitionKernel ^ A.horizon.T_end_l2) c₀
          {c | ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c}
        ≤ (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
              A.horizon.T_end_l2) (some c₀)
            {o | o = none ∨
              (∃ c, o = some c ∧
                ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c)} :=
          GatedDrift.real_le_killed_now
            (K := (NonuniformMajority L K).transitionKernel) (G := A.gate)
            (bad := fun c => ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c)
            A.horizon.T_end_l2 c₀
      _ ≤ (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
              A.horizon.T_end_l2) (some c₀)
            {o | ¬ A.Good A.H o} :=
          measure_mono hsub
      _ ≤ ∑ i ∈ Finset.range A.H, A.ηhour i := hchainT
      _ ≤ (A.ε : ℝ≥0∞) := A.budget

end Snapshot617HourChain

/-- Entry-specialized snapshot tail.  This is the protocol-entry shape used by
`Phase3Assembly.slot3_of_entry`: the tail is only required from the concrete
entry configuration already supplied by the phase-2→3 handoff. -/
structure Snapshot617EntryTail (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) where
  horizon : Snapshot617Horizon (L := L) (K := K) n ell
  ε : ℝ≥0
  tail :
    ((NonuniformMajority L K).transitionKernel ^ horizon.T_end_l2) entry
      {c | ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c}
      ≤ (ε : ℝ≥0∞)

/-- Entry-specialized killed-kernel hour chain.  Unlike `Snapshot617HourChain`,
the initial-good obligation is not universal over all `Slot3Entry` states; it is
only the concrete entry state threaded by the assembly layer. -/
structure Snapshot617EntryHourChain (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) where
  horizon : Snapshot617Horizon (L := L) (K := K) n ell
  gate : Set (Config (AgentState L K))
  H : ℕ
  hourLen : ℕ → ℕ
  Good : ℕ → Option (Config (AgentState L K)) → Prop
  ηhour : ℕ → ℝ≥0∞
  good0 : Good 0 (some entry)
  none_bad :
    ¬ Good H none
  tail :
    ∀ i, i < H → ∀ o,
      Good i o →
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel gate ^ hourLen i) o
          {x | ¬ Good (i + 1) x} ≤ ηhour i
  readout :
    ∀ c, Good H (some c) →
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c
  horizon_eq :
    horizon.T_end_l2 = ChapmanKolmogorovChain.hourPrefix hourLen H
  ε : ℝ≥0
  budget :
    (∑ i ∈ Finset.range H, ηhour i) ≤ (ε : ℝ≥0∞)

namespace Snapshot617EntryHourChain

/-- Compose an entry-specialized killed-kernel hour chain into the endpoint
snapshot tail. -/
noncomputable def toSnapshot617EntryTail
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : Snapshot617EntryHourChain (L := L) (K := K) n ell M g₀ σ entry) :
    Snapshot617EntryTail (L := L) (K := K) n ell M g₀ σ entry where
  horizon := A.horizon
  ε := A.ε
  tail := by
    have hchain :
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
            ChapmanKolmogorovChain.hourPrefix A.hourLen A.H) (some entry)
          {x | ¬ A.Good A.H x}
          ≤ ∑ i ∈ Finset.range A.H, A.ηhour i :=
      ChapmanKolmogorovChain.ck_chain_bad_bound_lt
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate)
        A.Good A.hourLen A.ηhour (some entry) A.good0 A.H A.tail
    have hchainT :
        (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
            A.horizon.T_end_l2) (some entry)
          {x | ¬ A.Good A.H x}
          ≤ ∑ i ∈ Finset.range A.H, A.ηhour i := by
      rw [A.horizon_eq]
      exact hchain
    have hsub :
        {o : Option (Config (AgentState L K)) |
          o = none ∨
            (∃ c, o = some c ∧
              ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c)}
          ⊆ {o | ¬ A.Good A.H o} := by
      intro o hbad hgood
      rcases hbad with hnone | ⟨c, hsome, hbadSnap⟩
      · subst o
        exact A.none_bad hgood
      · subst o
        exact hbadSnap (A.readout c hgood)
    calc
      ((NonuniformMajority L K).transitionKernel ^ A.horizon.T_end_l2) entry
          {c | ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c}
        ≤ (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
              A.horizon.T_end_l2) (some entry)
            {o | o = none ∨
              (∃ c, o = some c ∧
                ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c)} :=
          GatedDrift.real_le_killed_now
            (K := (NonuniformMajority L K).transitionKernel) (G := A.gate)
            (bad := fun c => ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c)
            A.horizon.T_end_l2 entry
      _ ≤ (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel A.gate ^
              A.horizon.T_end_l2) (some entry)
            {o | ¬ A.Good A.H o} :=
          measure_mono hsub
      _ ≤ ∑ i ∈ Finset.range A.H, A.ηhour i := hchainT
      _ ≤ (A.ε : ℝ≥0∞) := A.budget

end Snapshot617EntryHourChain

/-! ## Reachability while all agents are still in Phase 3 -/

/-- A single full-protocol step whose source and target are both exact Phase 3. -/
def Phase3ScopedStep (n : ℕ)
    (c c' : Config (AgentState L K)) : Prop :=
  AllPhase3 (L := L) (K := K) n c ∧
    (NonuniformMajority L K).StepRel c c' ∧
      AllPhase3 (L := L) (K := K) n c'

/-- Reflexive-transitive reachability restricted to the exact Phase-3 region. -/
def ReachableWhilePhase3 (n : ℕ)
    (c c' : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen (Phase3ScopedStep (L := L) (K := K) n) c c'

theorem ReachableWhilePhase3.refl {n : ℕ} {c : Config (AgentState L K)}
    (_hc : AllPhase3 (L := L) (K := K) n c) :
    ReachableWhilePhase3 (L := L) (K := K) n c c :=
  Relation.ReflTransGen.refl

theorem ReachableWhilePhase3.endpoint_phase3 {n : ℕ}
    {c c' : Config (AgentState L K)}
    (hc : AllPhase3 (L := L) (K := K) n c)
    (hr : ReachableWhilePhase3 (L := L) (K := K) n c c') :
    AllPhase3 (L := L) (K := K) n c' := by
  induction hr with
  | refl =>
      exact hc
  | tail _ hstep _ =>
      exact hstep.2.2

/-- A full-protocol scoped Phase-3 step is exactly a step of the concrete
Phase-3 protocol used by the deterministic algebra.  The target `AllPhase3`
field rules out the Phase-10 entry wrapper. -/
theorem Phase3ScopedStep.to_p3ProtocolStep {n : ℕ}
    {c c' : Config (AgentState L K)}
    (h : Phase3ScopedStep (L := L) (K := K) n c c') :
    (P3Protocol L K).StepRel c c' := by
  rcases h with ⟨hc, hstep, hc'⟩
  rcases hstep with ⟨r₁, r₂, happ, hc'_def⟩
  dsimp at hc'_def
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₁_phase : r₁.phase.val = 3 := hc.2 r₁ hr₁_mem
  have hr₂_phase : r₂.phase.val = 3 := hc.2 r₂ hr₂_mem
  have hmem₁ : (Transition L K r₁ r₂).1 ∈ c' := by
    rw [hc'_def]
    simp [NonuniformMajority]
  have hmem₂ : (Transition L K r₁ r₂).2 ∈ c' := by
    rw [hc'_def]
    simp [NonuniformMajority]
  have htrans_phase₁ : (Transition L K r₁ r₂).1.phase.val = 3 :=
    hc'.2 (Transition L K r₁ r₂).1 hmem₁
  have htrans_phase₂ : (Transition L K r₁ r₂).2.phase.val = 3 :=
    hc'.2 (Transition L K r₁ r₂).2 hmem₂
  have hepi :=
    ClockRealKernel.phaseEpidemicUpdate_eq_self_p3
      (L := L) (K := K) r₁ r₂ hr₁_phase hr₂_phase
  have hr₁_phase_eq : r₁.phase = (⟨3, by decide⟩ : Fin 11) := Fin.ext hr₁_phase
  have hphase₁ :
      (Transition L K r₁ r₂).1.phase.val =
        (Phase3Transition L K r₁ r₂).1.phase.val := by
    unfold Transition
    rw [hepi]
    simp [hr₁_phase_eq]
  have hphase₂ :
      (Transition L K r₁ r₂).2.phase.val =
        (Phase3Transition L K r₁ r₂).2.phase.val := by
    unfold Transition
    rw [hepi]
    simp [hr₁_phase_eq]
  have hp₁_ne : (Phase3Transition L K r₁ r₂).1.phase.val ≠ 10 := by
    rw [← hphase₁]
    omega
  have hp₂_ne : (Phase3Transition L K r₁ r₂).2.phase.val ≠ 10 := by
    rw [← hphase₂]
    omega
  have htransition :
      Transition L K r₁ r₂ = Phase3Transition L K r₁ r₂ :=
    HourCoupling.transition_eq_phase3
      (L := L) (K := K) r₁ r₂ hr₁_phase hr₂_phase hp₁_ne hp₂_ne
  refine ⟨r₁, r₂, happ, ?_⟩
  simpa [P3Protocol, NonuniformMajority, htransition] using hc'_def

/-- Signed weighted bias is preserved along Phase-3-scoped reachability. -/
theorem ReachableWhilePhase3.signedGap_eq {n : ℕ}
    {c c' : Config (AgentState L K)}
    (hr : ReachableWhilePhase3 (L := L) (K := K) n c c') :
    signedGap (L := L) (K := K) c' =
      signedGap (L := L) (K := K) c := by
  induction hr with
  | refl =>
      rfl
  | tail _ hstep ih =>
      have hp3 := Phase3ScopedStep.to_p3ProtocolStep
        (L := L) (K := K) hstep
      have hq :=
        p3_biasSum_step_eq (L := L) (K := K) hstep.1.2 hp3
      exact Eq.trans (by
        simpa [signedGap, Phase3Pre3.signedGap] using
          congrArg (fun q : ℚ => (q : ℝ)) hq) ih

/-- Entry pinned signed gap propagates to every Phase-3-scoped reachable
endpoint. -/
theorem Slot3Entry.signedGap_eq_of_reachable {n : ℕ} {g₀ : ℝ}
    {c₀ c : Config (AgentState L K)}
    (hentry : Slot3Entry (L := L) (K := K) n g₀ c₀)
    (hreach : ReachableWhilePhase3 (L := L) (K := K) n c₀ c) :
    signedGap (L := L) (K := K) c = g₀ := by
  rw [ReachableWhilePhase3.signedGap_eq (L := L) (K := K) hreach,
    hentry.gap_eq]

/-- Total weighted mass is nonincreasing along Phase-3-scoped reachability. -/
theorem ReachableWhilePhase3.weightedMass_le {n : ℕ}
    {c c' : Config (AgentState L K)}
    (hr : ReachableWhilePhase3 (L := L) (K := K) n c c') :
    weightedMass (L := L) (K := K) c' ≤
      weightedMass (L := L) (K := K) c := by
  induction hr with
  | refl =>
      exact le_rfl
  | tail _ hstep ih =>
      have hp3 := Phase3ScopedStep.to_p3ProtocolStep
        (L := L) (K := K) hstep
      have hq :=
        p3_totalMass_step_le (L := L) (K := K) hstep.1.2 hp3
      exact le_trans (by
        dsimp [weightedMass, Phase3Pre3.weightedMass]
        exact_mod_cast hq) ih

/-- Strict upper-tail weighted mass is nonincreasing along Phase-3-scoped
reachability. -/
theorem ReachableWhilePhase3.massAboveQReal_le {n h : ℕ}
    {c c' : Config (AgentState L K)}
    (hr : ReachableWhilePhase3 (L := L) (K := K) n c c') :
    massAboveQReal (L := L) (K := K) h c' ≤
      massAboveQReal (L := L) (K := K) h c := by
  induction hr with
  | refl =>
      exact le_rfl
  | tail _ hstep ih =>
      have hp3 := Phase3ScopedStep.to_p3ProtocolStep
        (L := L) (K := K) hstep
      have hq :=
        p3_massAbove_step_le (L := L) (K := K) h hstep.1.2 hp3
      exact le_trans (by
        dsimp [massAboveQReal]
        exact_mod_cast hq) ih

/-! ## Core checkpoint handoff, deterministic monotone slice -/

/-- The monotone part of the Core checkpoint invariant.

This is the part that is actually preserved by the Phase-3 transition algebra:
the pinned signed gap, total weighted mass upper bound, and strict upper-tail
mass upper bound.  The hour-local floors (`O_h`, `PhiZero`, etc.) are row
outputs and are re-established at the next hour by the corresponding Doty row,
not claimed as gap-monotone here. -/
structure CoreMonotoneInvariant
    (n level : ℕ) (g₀ Bmass Babove : ℝ)
    (c : Config (AgentState L K)) : Prop where
  phase3 : AllPhase3 (L := L) (K := K) n c
  gap_eq : signedGap (L := L) (K := K) c = g₀
  weightedMass_le : weightedMass (L := L) (K := K) c ≤ Bmass
  massAbove_le : massAboveQReal (L := L) (K := K) level c ≤ Babove

/-- Cut/checkpoint handoff for the Core monotone invariant along a Phase-3
scoped gap.  It is exactly the iteration of the piece-1 algebra facts:
`g` is invariant, while total mass and above-level mass are nonincreasing. -/
theorem core_invariant_handoff {n level : ℕ} {g₀ Bmass Babove : ℝ}
    {c c' : Config (AgentState L K)}
    (hr : ReachableWhilePhase3 (L := L) (K := K) n c c')
    (hgood : CoreMonotoneInvariant
      (L := L) (K := K) n level g₀ Bmass Babove c) :
    CoreMonotoneInvariant
      (L := L) (K := K) n level g₀ Bmass Babove c' where
  phase3 :=
    ReachableWhilePhase3.endpoint_phase3 (L := L) (K := K)
      hgood.phase3 hr
  gap_eq := by
    rw [ReachableWhilePhase3.signedGap_eq (L := L) (K := K) hr,
      hgood.gap_eq]
  weightedMass_le :=
    (ReachableWhilePhase3.weightedMass_le (L := L) (K := K) hr).trans
      hgood.weightedMass_le
  massAbove_le :=
    (ReachableWhilePhase3.massAboveQReal_le (L := L) (K := K)
      (h := level) hr).trans hgood.massAbove_le

/-! ## The deterministic closure half of Lemma 6.18 -/

/-- Deterministic inputs for closing Lemma 6.18 from the snapshot.

These fields are pure reachability/invariant/readout obligations.  They are the
future discharge target for the Phase-3 transition algebra and contain no
probability.
-/
structure Lemma618DeterministicInputs
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) : Prop where
  h_l2 : ell + 2 ≤ L
  hgap_sign : WinningGap σ g₀
  gap_preserved :
    ∀ c_snap c_final,
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c_snap →
      ReachableWhilePhase3 (L := L) (K := K) n c_snap c_final →
      signedGap (L := L) (K := K) c_final =
        signedGap (L := L) (K := K) c_snap
  total_mass_nonincreasing :
    ∀ c_snap c_final,
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c_snap →
      ReachableWhilePhase3 (L := L) (K := K) n c_snap c_final →
      weightedMass (L := L) (K := K) c_final ≤
        weightedMass (L := L) (K := K) c_snap
  massAbove_nonincreasing :
    ∀ c_snap c_final,
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c_snap →
      ReachableWhilePhase3 (L := L) (K := K) n c_snap c_final →
      massAboveQReal (L := L) (K := K) ell c_final ≤
        massAboveQReal (L := L) (K := K) ell c_snap
  readout :
    ∀ c_snap c_final,
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c_snap →
      ReachableWhilePhase3 (L := L) (K := K) n c_snap c_final →
      signedGap (L := L) (K := K) c_final = g₀ →
      weightedMass (L := L) (K := K) c_final ≤
        weightedMass (L := L) (K := K) c_snap →
      massAboveQReal (L := L) (K := K) ell c_final ≤
        massAboveQReal (L := L) (K := K) ell c_snap →
      Post3 (L := L) (K := K) n ell M σ g₀ c_final

/-- The remaining non-reachability part of deterministic Lemma 6.18.

The three clean reachability fields of `Lemma618DeterministicInputs` are now
proved below from `Phase3TransitionAlgebra`; this bundle keeps only the
readout/spec obligation. -/
structure Lemma618ReadoutInputs
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) : Prop where
  h_l2 : ell + 2 ≤ L
  hgap_sign : WinningGap σ g₀
  readout :
    ∀ c_snap c_final,
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c_snap →
      ReachableWhilePhase3 (L := L) (K := K) n c_snap c_final →
      signedGap (L := L) (K := K) c_final = g₀ →
      weightedMass (L := L) (K := K) c_final ≤
        weightedMass (L := L) (K := K) c_snap →
      massAboveQReal (L := L) (K := K) ell c_final ≤
        massAboveQReal (L := L) (K := K) ell c_snap →
      Post3 (L := L) (K := K) n ell M σ g₀ c_final

/-- Discharge the three clean reachability fields from the Phase-3 transition
algebra, leaving only the honest readout obligation. -/
def Lemma618DeterministicInputs.ofReadout
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (R : Lemma618ReadoutInputs (L := L) (K := K) n ell M g₀ σ) :
    Lemma618DeterministicInputs (L := L) (K := K) n ell M g₀ σ where
  h_l2 := R.h_l2
  hgap_sign := R.hgap_sign
  gap_preserved := by
    intro c_snap c_final _hsnap hreach
    exact ReachableWhilePhase3.signedGap_eq (L := L) (K := K) hreach
  total_mass_nonincreasing := by
    intro c_snap c_final _hsnap hreach
    exact ReachableWhilePhase3.weightedMass_le (L := L) (K := K) hreach
  massAbove_nonincreasing := by
    intro c_snap c_final _hsnap hreach
    exact ReachableWhilePhase3.massAboveQReal_le (L := L) (K := K) (h := ell) hreach
  readout := R.readout

/-- The deterministic half of Lemma 6.18, packaged as a closure theorem. -/
structure Lemma618DeterministicClosure
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) : Prop where
  h_l2 : ell + 2 ≤ L
  hgap_sign : WinningGap σ g₀
  closure :
    ∀ c_snap c_final,
      Snapshot617 (L := L) (K := K) n ell M g₀ σ c_snap →
      ReachableWhilePhase3 (L := L) (K := K) n c_snap c_final →
      Post3 (L := L) (K := K) n ell M σ g₀ c_final

/-- Build the deterministic closure from the invariant/readout fields. -/
theorem lemma618_deterministic_closure
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (I : Lemma618DeterministicInputs (L := L) (K := K) n ell M g₀ σ) :
    Lemma618DeterministicClosure (L := L) (K := K) n ell M g₀ σ where
  h_l2 := I.h_l2
  hgap_sign := I.hgap_sign
  closure := by
    intro c_snap c_final hsnap hreach
    have hgap : signedGap (L := L) (K := K) c_final = g₀ := by
      rw [I.gap_preserved c_snap c_final hsnap hreach, hsnap.gap_eq]
    exact I.readout c_snap c_final hsnap hreach hgap
      (I.total_mass_nonincreasing c_snap c_final hsnap hreach)
      (I.massAbove_nonincreasing c_snap c_final hsnap hreach)

/-- Snapshot implies Post₃ at the same endpoint by the 6.17 minority-mass bound. -/
theorem post3_of_snapshot
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hs : Snapshot617 (L := L) (K := K) n ell M g₀ σ c) :
    Post3 (L := L) (K := K) n ell M σ g₀ c :=
  hs.toPost3

/-- The bad-Post₃ event is contained in the bad-snapshot event. -/
theorem not_post3_subset_not_snapshot
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign} :
    {c : Config (AgentState L K) |
      ¬ Post3 (L := L) (K := K) n ell M σ g₀ c}
      ⊆
    {c : Config (AgentState L K) |
      ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c} := by
  intro c hnotPost hsnap
  exact hnotPost (post3_of_snapshot (L := L) (K := K) hsnap)

/-! ## Composition into the slot-3 weak atom -/

/-- The final slot-3 tail: the snapshot tail supplies the same-endpoint Post₃
mass-bound closure. -/
structure Slot3PostTail (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  snap : Snapshot617Tail (L := L) (K := K) n ell M g₀ σ

namespace Slot3PostTail

/-- The slot-3 horizon bound is no longer a caller-supplied arithmetic fact:
it is read from the concrete `GoodClock.finish (ell+2)` hour-sum certificate. -/
theorem ht_le {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3PostTail (L := L) (K := K) n ell M g₀ σ) :
    A.snap.horizon.T_end_l2 ≤ 17 * n * (L + 1) :=
  Snapshot617Horizon.T_end_l2_le (L := L) (K := K) A.snap.horizon

/-- Monotone rebudgeting of the final slot-3 Post₃ tail. -/
noncomputable def withBudget {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3PostTail (L := L) (K := K) n ell M g₀ σ)
    (ε' : ℝ≥0)
    (hε : (A.snap.ε : ℝ≥0∞) ≤ (ε' : ℝ≥0∞)) :
    Slot3PostTail (L := L) (K := K) n ell M g₀ σ where
  snap :=
    { A.snap with
      ε := ε'
      tail := fun c₀ hpre => (A.snap.tail c₀ hpre).trans hε }

end Slot3PostTail

/-- Constructor from the more granular deterministic input bundle. -/
def Slot3PostTail.ofInputs
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (snap : Snapshot617Tail (L := L) (K := K) n ell M g₀ σ)
    (_det : Lemma618DeterministicInputs (L := L) (K := K) n ell M g₀ σ) :
    Slot3PostTail (L := L) (K := K) n ell M g₀ σ where
  snap := snap

/-- Constructor after the reachability fields have been discharged: only the
readout/spec obligation remains. -/
def Slot3PostTail.ofReadout
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (snap : Snapshot617Tail (L := L) (K := K) n ell M g₀ σ)
    (readout : Lemma618ReadoutInputs (L := L) (K := K) n ell M g₀ σ) :
    Slot3PostTail (L := L) (K := K) n ell M g₀ σ :=
  Slot3PostTail.ofInputs (L := L) (K := K) snap
    (Lemma618DeterministicInputs.ofReadout (L := L) (K := K) readout)

/-- Final slot-3 `PhaseConvergenceW`: exact Phase-3 entry reaches Post₃. -/
noncomputable def slot3PostWork
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3PostTail (L := L) (K := K) n ell M g₀ σ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := Slot3Entry (L := L) (K := K) n g₀ c
  Post c := Post3 (L := L) (K := K) n ell M σ g₀ c
  t := A.snap.horizon.T_end_l2
  ε := A.snap.ε
  convergence := by
    intro c₀ hpre
    calc
      ((NonuniformMajority L K).transitionKernel ^ A.snap.horizon.T_end_l2) c₀
          {c | ¬ Post3 (L := L) (K := K) n ell M σ g₀ c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ A.snap.horizon.T_end_l2) c₀
            {c | ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c} :=
          measure_mono (not_post3_subset_not_snapshot (L := L) (K := K))
      _ ≤ (A.snap.ε : ℝ≥0∞) := A.snap.tail c₀ hpre

/-- Entry-specialized slot-3 tail used by the protocol-entry assembly surface. -/
structure Slot3PostEntryTail (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) where
  snap : Snapshot617EntryTail (L := L) (K := K) n ell M g₀ σ entry

namespace Slot3PostEntryTail

/-- The entry-specialized slot-3 horizon bound is read from the same concrete
GoodClock hour-sum certificate. -/
theorem ht_le {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : Slot3PostEntryTail (L := L) (K := K) n ell M g₀ σ entry) :
    A.snap.horizon.T_end_l2 ≤ 17 * n * (L + 1) :=
  Snapshot617Horizon.T_end_l2_le (L := L) (K := K) A.snap.horizon

end Slot3PostEntryTail

/-- Protocol-entry slot-3 `PhaseConvergenceW`: only the concrete entry state
threads into the full-kernel hour chain, together with its `Slot3Entry`
certificate. -/
noncomputable def slot3PostWorkAtEntry
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (_hentry : Slot3Entry (L := L) (K := K) n g₀ entry)
    (A : Slot3PostEntryTail (L := L) (K := K) n ell M g₀ σ entry) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := c = entry ∧ Slot3Entry (L := L) (K := K) n g₀ c
  Post c := Post3 (L := L) (K := K) n ell M σ g₀ c
  t := A.snap.horizon.T_end_l2
  ε := A.snap.ε
  convergence := by
    intro c₀ hpre
    calc
      ((NonuniformMajority L K).transitionKernel ^ A.snap.horizon.T_end_l2) c₀
          {c | ¬ Post3 (L := L) (K := K) n ell M σ g₀ c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ A.snap.horizon.T_end_l2) c₀
            {c | ¬ Snapshot617 (L := L) (K := K) n ell M g₀ σ c} :=
          measure_mono (not_post3_subset_not_snapshot (L := L) (K := K))
      _ ≤ (A.snap.ε : ℝ≥0∞) := by
        rcases hpre with ⟨hentry, _hentry'⟩
        subst c₀
        exact A.snap.tail

#print axioms Post3.ready
#print axioms signedGap_eq_betaPlus_sub_betaMinus
#print axioms Snapshot617.ofCapBound
#print axioms Snapshot617.toPost3
#print axioms Snapshot617HourChain.toSnapshot617Tail
#print axioms Snapshot617EntryHourChain.toSnapshot617EntryTail
#print axioms not_post3_subset_not_snapshot
#print axioms Snapshot617Horizon.T_end_l2_le
#print axioms Phase3ScopedStep.to_p3ProtocolStep
#print axioms ReachableWhilePhase3.signedGap_eq
#print axioms Slot3Entry.signedGap_eq_of_reachable
#print axioms ReachableWhilePhase3.weightedMass_le
#print axioms ReachableWhilePhase3.massAboveQReal_le
#print axioms core_invariant_handoff
#print axioms Lemma618DeterministicInputs.ofReadout
#print axioms lemma618_deterministic_closure
#print axioms Slot3PostTail.ht_le
#print axioms Slot3PostTail.withBudget
#print axioms slot3PostWork
#print axioms Slot3PostEntryTail.ht_le
#print axioms slot3PostWorkAtEntry

end Phase3Post3

end ExactMajority

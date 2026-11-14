
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WorkFromSlots

Construct the faithful `work : Fin 11 → PhaseConvergenceW` family from landed
slot constructors wherever the public constructor surface is currently exposed.

Directly built here:

* slot 1: `Phase1ReadySurvival.phase1ReadySurvival`;
* slots 2/4/9: the tight epidemic work instances from
  `WorkSlotsTightEpidemic`;
* slot 6: the base-4 multiplicative-drift survival instance from
  `Slot6PhiSurvival`;
* slot 7: the naturally truncated three-band multiplicative-drift instance
  from `Slot7BandSurvival`;
* slot 8: `Phase678ReadySurvival.phase8ReadySurvival`;
* slot 10: `WorkBuilder.work10_from_concrete`.

Narrow per-slot work atoms kept explicit:

* slot 0: role-split/C0 work;
* slot 3: main-confinement work;
* slot 5: corrected slot-5 survival work.

These are not hidden as a carried full work family.  They are isolated as three
named slot atoms with their seam-shape obligations exposed.  This is the genuine
current boundary: the older `SurvivalWorkHypotheses` route is not used because its slot-5
surface still carries the false `InvClosed Phase5AllWin` field.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1ReadySurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase678ReadySurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiSurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6HorizonBound
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandSurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7HorizonBound
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase24910Work
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase9Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.TightEpidemicWork

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace PhaseWorkFamily

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A narrow slot-0 work atom.

This is the role-split/C0 work slot.  The atom includes the exact public work instance
and its two structural ties needed by the faithful seam glue and start bridge. -/
structure Phase0WorkData (n : ℕ) where
  work : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  hPre :
    ∀ c, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c →
      work.Pre c
  hPostEq :
    ∀ c, work.Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 0 n c

/-- A narrow slot-3 work atom.

This is the landed main-confinement / Theorem-6.2 slot.  Its public constructor is
kept outside this file; the atom records only the resulting work instance and the
seam-shape ties. -/
structure Phase3WorkData (n : ℕ) where
  work : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  hPostEq :
    ∀ c, work.Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c
  hPreEq :
    ∀ c, AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c →
      work.Pre c

/-- A narrow slot-5 work atom.

This is the corrected slot-5 survival work, whose construction consumes the C5a and
slot-5 confinement/sampling atoms outside this file.  It is intentionally not routed
through `SurvivalWorkHypotheses`, whose slot-5 surface still requires `InvClosed Phase5AllWin`. -/
structure Phase5WorkData (n : ℕ) where
  /-- The sampled reserve hour produced by slot 5 and consumed by slot 6. -/
  i5 : Fin (L + 1)
  /-- The sampled reserve floor produced by slot 5 and consumed by slot 6. -/
  K₀ : ℕ
  /-- The sampled floor cannot exceed the population. -/
  hK₀n : K₀ ≤ n
  /-- Genuine C5a residual: slot 5 produces a paper-scale `0.04 n` floor. -/
  hK₀linear : n ≤ 25 * K₀
  work : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  hPostEq :
    ∀ c, work.Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c
  hPreEq :
    ∀ c, AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c →
      work.Pre c
  /-- The slot-5 post really carries the same sampled floor used by slot 6. -/
  hPostSampled :
    ∀ c, work.Post c →
      Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c

/-- The explicit slot input bundle for constructing the faithful work family.

The largest old atom, `work : Fin 11 → PhaseConvergenceW`, is replaced by explicit
per-slot construction data.  Slots 1/2/4/6/7/8/9/10 are built from committed
constructors; slots 0/3/5 remain narrow per-slot atoms pending their exact public
constructor surfaces. -/
structure WorkFamilyData (n : ℕ) where
  /-- Common sign used by slots 6/7/8. -/
  σ : Sign

  hn : 2 ≤ n
  /-- Common allocated error cap for the survival slots. -/
  δ : ℝ≥0
  /-- The allocated cap fits the headline inverse-square slot budget. -/
  hδ : (δ : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2

  /-- Slot 0 role-split/C0 work. -/
  slot0 : Phase0WorkData (L := L) (K := K) n

  /-- Slot 3 confinement work. -/
  slot3 : Phase3WorkData (L := L) (K := K) n

  /-- Slot 5 corrected survival work. -/
  slot5 : Phase5WorkData (L := L) (K := K) n

  /-- Slot 1 partner-pool floor. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  η1 : ℝ≥0∞
  hesc1 : Phase1ReadySurvival.Phase1ReadyEscapeBound
    (L := L) (K := K) n P1 η1
  drainε1 : ℝ≥0
  hDrain1 :
    (∑ m ∈ Finset.Icc 1 n,
      (DrainEngine.qHat P1 n m) ^ (tWin1 m) : ℝ≥0∞)
        ≤ (drainε1 : ℝ≥0∞)
  escapeε1 : ℝ≥0
  hescε1 :
    (((∑ m ∈ Finset.Icc 1 n, tWin1 m) : ℕ) : ℝ≥0∞) * η1
      ≤ (escapeε1 : ℝ≥0∞)
  hTotal1 :
    (drainε1 : ℝ≥0∞) + (escapeε1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞)

  /-- Slot 6 band level.  Its sampled hour and reserve floor are exactly the
  values exported by `slot5`; they are not independently selectable. -/
  l : ℕ
  hl1 : 1 ≤ l
  hlL : l ≤ L
  hhgt6 : l - 1 < slot5.i5.val
  hhne6 : slot5.i5.val ≠ L
  η6 : ℝ≥0∞
  hesc6 : Phase678ReadySurvival.Phase6ReadyEscapeBound
    (L := L) (K := K) n σ l hl1 hlL slot5.i5 slot5.K₀ η6
  escapeε6 : ℝ≥0
  hescε6 :
    ((DriftSurvival.driftHorizon (slot5.K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2 : ℕ) : ℝ≥0∞) * η6
      ≤ (escapeε6 : ℝ≥0∞)
  hTotal6 :
    (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) + (escapeε6 : ℝ≥0∞)
      ≤ (δ : ℝ≥0∞)

  /-- Slot 7 exact-band eliminator data.  The same three-band block is used
  by every naturally available stage among `l,l+1,l+2`. -/
  E7 : ℕ
  hE7pos : 1 ≤ E7
  /-- The ordered-pair drift rate is at most one. -/
  hE7top : 2 * E7 ≤ n * (n - 1)
  /-- Paper-scale eliminator floor, used for the explicit linear horizon. -/
  hE7linear : n ≤ 4 * E7
  η7 : ℝ≥0∞
  hesc7 : Phase7BandSurvival.Phase7BandEscapeBound
    (L := L) (K := K) n σ l E7 η7
  escapeε7 : ℝ≥0
  hescε7 :
    ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η7
      ≤ (escapeε7 : ℝ≥0∞)
  /-- Each stage's escape share fits its one-sixth drift share. -/
  hescape7 : escapeε7 ≤ DriftSurvival.driftBudgetNN 6 n

  /-- Slot 8 eliminator margin data. -/
  E8 : ℕ
  tWin8 : ℕ → ℕ
  η8 : ℝ≥0∞
  hesc8 : Phase678ReadySurvival.Phase8ReadyEscapeBound
    (L := L) (K := K) n σ E8 η8
  drainε8 : ℝ≥0
  hDrain8 :
    (∑ m ∈ Finset.Icc 1 n,
      (DrainEngine.qHat E8 n m) ^ (tWin8 m) : ℝ≥0∞)
        ≤ (drainε8 : ℝ≥0∞)
  escapeε8 : ℝ≥0
  hescε8 :
    (((∑ m ∈ Finset.Icc 1 n, tWin8 m) : ℕ) : ℝ≥0∞) * η8
      ≤ (escapeε8 : ℝ≥0∞)
  hTotal8 :
    (drainε8 : ℝ≥0∞) + (escapeε8 : ℝ≥0∞) ≤ (δ : ℝ≥0∞)

  /-- Slot 10 block-geometric repetition count. -/
  k10 : ℕ

/-- Slot 1 built from the landed Ready-gate survival constructor. -/
noncomputable def phase1Work_of_familyData
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase1ReadySurvival.phase1ReadySurvivalBudgeted
    (L := L) (K := K)
    A.P1 n A.hn
    A.η1 A.hesc1
    A.tWin1 A.drainε1 A.hDrain1 A.escapeε1 A.hescε1

/-- Slot 6 built from the scheduler-weighted base-4 multiplicative drift. -/
noncomputable def phase6Work_of_familyData
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  have hK₀pos : 1 ≤ A.slot5.K₀ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    have hlinear := A.slot5.hK₀linear
    have hn := A.hn
    rw [hzero, mul_zero] at hlinear
    omega
  exact Phase6PhiSurvival.phase6PhiSurvival
    (L := L) (K := K)
    A.hn 2 (by norm_num)
    A.σ A.l A.hl1 A.hlL A.slot5.i5 A.slot5.K₀ hK₀pos A.slot5.hK₀n
    A.hhgt6 A.hhne6 A.η6 A.hesc6 A.escapeε6 A.hescε6

/-- Slot 7 built from the paper-faithful naturally truncated exact-band drain. -/
noncomputable def phase7Work_of_familyData
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase7BandSurvival.phase7BandsSurvival
    (L := L) (K := K)
    A.hn A.σ A.l A.E7 A.hlL A.hE7pos A.hE7top
    A.η7 A.hesc7 A.escapeε7 A.hescε7

/-- With the paper's linear sampled-reserve floor, the new slot-6 drift work
has a genuine `O(n(L+1))` sequential-interaction horizon. -/
theorem phase6Work_of_familyData_t_le_87
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n)
    (hnL : n ≤ 2 ^ L) :
    (phase6Work_of_familyData (L := L) (K := K) A).t ≤
      87 * n * (L + 1) := by
  change DriftSurvival.driftHorizon (A.slot5.K₀ : ℝ) n
      (Phase6PhiPotential.phase6PhiMax n A.l) 2 ≤ 87 * n * (L + 1)
  exact phase6_driftHorizon_le_87
    A.hn hnL A.hlL A.slot5.hK₀linear

/-- The paper-scale three-band eliminator floor gives slot 7 a genuine
`O(n(L+1))` sequential-interaction horizon. -/
theorem phase7Work_of_familyData_t_le_15
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n)
    (hnL : n ≤ 2 ^ L) :
    (phase7Work_of_familyData (L := L) (K := K) A).t ≤
      15 * n * (L + 1) := by
  simpa only [phase7Work_of_familyData,
      Phase7BandSurvival.phase7BandsSurvival_t] using
    (phase7_allStages_driftHorizon_le_15
      A.l A.hn hnL A.hE7linear)

/-- Slot 8 built from the landed Ready-gate survival constructor. -/
noncomputable def phase8Work_of_familyData
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase678ReadySurvival.phase8ReadySurvivalBudgeted
    (L := L) (K := K)
    A.σ A.E8 n A.hn
    A.η8 A.hesc8
    A.tWin8 A.drainε8 A.hDrain8 A.escapeε8 A.hescε8

@[simp] theorem phase1Work_of_familyData_epsilon
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    (phase1Work_of_familyData (L := L) (K := K) A).ε =
      A.drainε1 + A.escapeε1 := rfl

theorem phase1Work_of_familyData_epsilon_le_delta
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase1Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      (A.δ : ℝ≥0∞) := by
  rw [phase1Work_of_familyData_epsilon, ENNReal.coe_add]
  exact A.hTotal1

theorem phase1Work_of_familyData_epsilon_le_inv_sq
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase1Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2 :=
  (phase1Work_of_familyData_epsilon_le_delta (L := L) (K := K) A).trans A.hδ

@[simp] theorem phase6Work_of_familyData_epsilon
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    (phase6Work_of_familyData (L := L) (K := K) A).ε =
      DriftSurvival.driftBudgetNN 2 n + A.escapeε6 := rfl

theorem phase6Work_of_familyData_epsilon_le_delta
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase6Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      (A.δ : ℝ≥0∞) := by
  rw [phase6Work_of_familyData_epsilon, ENNReal.coe_add]
  exact A.hTotal6

theorem phase6Work_of_familyData_epsilon_le_inv_sq
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase6Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2 :=
  (phase6Work_of_familyData_epsilon_le_delta (L := L) (K := K) A).trans A.hδ

@[simp] theorem phase7Work_of_familyData_epsilon
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    (phase7Work_of_familyData (L := L) (K := K) A).ε =
      (Phase7BandStages.phase7StageCount L A.l : ℝ≥0) *
        (DriftSurvival.driftBudgetNN 6 n + A.escapeε7) := by
  exact Phase7BandSurvival.phase7BandsSurvival_epsilon
    A.hn A.σ A.l A.E7 A.hlL A.hE7pos A.hE7top
      A.η7 A.hesc7 A.escapeε7 A.hescε7

theorem phase7Work_of_familyData_epsilon_le_inv_sq
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase7Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2 :=
  Phase7BandSurvival.phase7BandsSurvival_epsilon_le_inv_sq
    A.hn A.σ A.l A.E7 A.hlL A.hE7pos A.hE7top
      A.η7 A.hesc7 A.escapeε7 A.hescε7 A.hescape7

@[simp] theorem phase8Work_of_familyData_epsilon
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    (phase8Work_of_familyData (L := L) (K := K) A).ε =
      A.drainε8 + A.escapeε8 := rfl

theorem phase8Work_of_familyData_epsilon_le_delta
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase8Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      (A.δ : ℝ≥0∞) := by
  rw [phase8Work_of_familyData_epsilon, ENNReal.coe_add]
  exact A.hTotal8

theorem phase8Work_of_familyData_epsilon_le_inv_sq
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ((phase8Work_of_familyData (L := L) (K := K) A).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2 :=
  (phase8Work_of_familyData_epsilon_le_delta (L := L) (K := K) A).trans A.hδ

/-- The constructed 11-slot faithful work family. -/
noncomputable def workFamily
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => A.slot0.work
    | ⟨1, _⟩ => phase1Work_of_familyData (L := L) (K := K) A
    | ⟨2, _⟩ => TightEpidemicWork.work2Tight (L := L) (K := K) A.hn
    | ⟨3, _⟩ => A.slot3.work
    | ⟨4, _⟩ => TightEpidemicWork.work4Tight (L := L) (K := K) A.hn
    | ⟨5, _⟩ => A.slot5.work
    | ⟨6, _⟩ => phase6Work_of_familyData (L := L) (K := K) A
    | ⟨7, _⟩ => phase7Work_of_familyData (L := L) (K := K) A
    | ⟨8, _⟩ => phase8Work_of_familyData (L := L) (K := K) A
    | ⟨9, _⟩ => TightEpidemicWork.work9Tight (L := L) (K := K) A.hn
    | ⟨10, _⟩ => WorkBuilder.work10_from_concrete
        (L := L) (K := K) A.hn A.k10
    | ⟨m + 11, h⟩ => absurd h (by omega)

/-! ## Seam-shape ties for the constructed work family. -/

/-- Explicit seam shape data for `workFamily`.

These are deterministic once each slot’s public constructor exposes the exact
Pre/Post shape.  Until all slots expose those simplification lemmas uniformly, they
are kept as a small, gated shape package instead of hidden in the full work family. -/
structure WorkShapeTies
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ) where
  hPostEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      ((workFamily (L := L) (K := K) A) ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c
  hPreEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      ((workFamily (L := L) (K := K) A) ⟨k.val + 1, by omega⟩).Pre c
  hSlot10Post :
    ∀ c,
      ((workFamily (L := L) (K := K) A) ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c

/-- Slot-0 start bridge for the constructed work family. -/
theorem workFamily_phase0_pre
    {n : ℕ} (A : WorkFamilyData (L := L) (K := K) n) :
    ∀ c, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c →
      ((workFamily (L := L) (K := K) A) ⟨0, by omega⟩).Pre c := by
  intro c hc
  exact A.slot0.hPre c hc

#print axioms phase1Work_of_familyData
#print axioms phase6Work_of_familyData
#print axioms phase6Work_of_familyData_t_le_87
#print axioms phase7Work_of_familyData
#print axioms phase7Work_of_familyData_t_le_15
#print axioms phase8Work_of_familyData
#print axioms phase1Work_of_familyData_epsilon_le_inv_sq
#print axioms phase6Work_of_familyData_epsilon_le_inv_sq
#print axioms phase7Work_of_familyData_epsilon_le_inv_sq
#print axioms phase8Work_of_familyData_epsilon_le_inv_sq
#print axioms workFamily
#print axioms workFamily_phase0_pre

end PhaseWorkFamily

end Ripple.PopulationProtocol.ExactMajority

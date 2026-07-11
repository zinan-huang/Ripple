
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WorkFromSlots

Construct the faithful `work : Fin 11 → PhaseConvergenceW` family from landed
slot constructors wherever the public constructor surface is currently exposed.

Directly built here:

* slot 1: `Slot1SurvivalInputs.slot1SurvivalReady`;
* slot 2: `WorkBuilder.work2_from_phase2`;
* slot 4: `WorkBuilder.work4_from_phase4`;
* slot 6: `Slot678SurvivalInputs.slot6SurvivalReady`;
* slot 7: `Slot678SurvivalInputs.slot7SurvivalReady`;
* slot 8: `Slot678SurvivalInputs.slot8SurvivalReady`;
* slot 9: `Phase9Convergence.phase9ConvergenceW`;
* slot 10: `WorkBuilder.work10_from_concrete`.

Narrow per-slot work atoms kept explicit:

* slot 0: role-split/C0 work;
* slot 3: main-confinement work;
* slot 5: corrected slot-5 survival work.

These are not hidden as a carried full work family.  They are isolated as three
named slot atoms with their seam-shape obligations exposed.  This is the honest
current boundary: the older `WorkInputsFull` route is not used because its slot-5
surface still carries the false `InvClosed Phase5AllWin` field.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulWitness
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot1SurvivalInputs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot678SurvivalInputs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WorkInputsSlots24910
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase9Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace WorkFromSlots

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A narrow slot-0 work atom.

This is the role-split/C0 work slot.  The atom includes the exact public work instance
and its two structural ties needed by the faithful seam glue and start bridge. -/
structure Slot0WorkAtom (n : ℕ) where
  work : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  hPre :
    ∀ c, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c →
      work.Pre c
  hPostEq :
    ∀ c, work.Post c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c

/-- A narrow slot-3 work atom.

This is the landed main-confinement / Theorem-6.2 slot.  Its public constructor is
kept outside this file; the atom records only the resulting work instance and the
seam-shape ties. -/
structure Slot3WorkAtom (n : ℕ) where
  work : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  hPostEq :
    ∀ c, work.Post c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c
  hPreEq :
    ∀ c, SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c →
      work.Pre c

/-- A narrow slot-5 work atom.

This is the corrected slot-5 survival work, whose construction consumes the C5a and
slot-5 confinement/sampling atoms outside this file.  It is intentionally not routed
through `WorkInputsFull`, whose slot-5 surface still requires `InvClosed Phase5AllWin`. -/
structure Slot5WorkAtom (n : ℕ) where
  work : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  hPostEq :
    ∀ c, work.Post c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c
  hPreEq :
    ∀ c, SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c →
      work.Pre c

/-- Slot-9 opinion-union inputs.

This reuses the exact scalar/opinion surface of slot 2; the constructor below calls
the phase-9 clone `Phase9Convergence.phase9ConvergenceW`. -/
abbrev Slot9OpinionInputs (n : ℕ) :=
  WorkBuilder.Slot2OpinionInputs n

/-- The explicit slot input bundle for constructing the faithful work family.

The largest old atom, `work : Fin 11 → PhaseConvergenceW`, is replaced by explicit
per-slot construction data.  Slots 1/2/4/6/7/8/9/10 are built from committed
constructors; slots 0/3/5 remain narrow per-slot atoms pending their exact public
constructor surfaces. -/
structure SlotInputs (n : ℕ) where
  /-- Common sign used by slots 6/7/8. -/
  σ : Sign

  /-- Common drain budget cap. -/
  M₀ : ℕ

  hn : 2 ≤ n
  hM1 : 1 ≤ M₀

  /-- Slot 0 role-split/C0 work. -/
  slot0 : Slot0WorkAtom (L := L) (K := K) n

  /-- Slot 2 opinion epidemic inputs. -/
  slot2 : WorkBuilder.Slot2OpinionInputs n

  /-- Slot 3 confinement work. -/
  slot3 : Slot3WorkAtom (L := L) (K := K) n

  /-- Slot 4 scalar fit. -/
  slot4 : WorkBuilder.Slot4ScalarFit n

  /-- Slot 5 corrected survival work. -/
  slot5 : Slot5WorkAtom (L := L) (K := K) n

  /-- Slot 1 partner-pool floor. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  η1 : ℝ≥0∞
  hesc1 : Slot1SurvivalInputs.Slot1ReadyEscapeAtom
    (L := L) (K := K) n P1 η1
  hpt1 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat P1 n m) ^ (tWin1 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε1 : ℝ≥0
  hescε1 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η1
      ≤ (escapeε1 : ℝ≥0∞)

  /-- Slot 6 band level and sampled-class data. -/
  l : ℕ
  hl1 : 1 ≤ l
  hlL : l ≤ L
  i6 : Fin (L + 1)
  K₀6 : ℕ
  hhgt6 : l - 1 < i6.val
  hhne6 : i6.val ≠ L
  tWin6 : ℕ → ℕ
  η6 : ℝ≥0∞
  hesc6 : Slot678SurvivalInputs.Slot6ReadyEscapeAtom
    (L := L) (K := K) n σ l hl1 hlL i6 K₀6 η6
  hpt6 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀6 n m) ^ (tWin6 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε6 : ℝ≥0
  hescε6 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η6
      ≤ (escapeε6 : ℝ≥0∞)

  /-- Slot 7 eliminator margin data. -/
  E7 : ℕ
  tWin7 : ℕ → ℕ
  η7 : ℝ≥0∞
  hesc7 : Slot678SurvivalInputs.Slot7ReadyEscapeAtom
    (L := L) (K := K) n σ E7 η7
  hpt7 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin7 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε7 : ℝ≥0
  hescε7 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η7
      ≤ (escapeε7 : ℝ≥0∞)

  /-- Slot 8 eliminator margin data. -/
  E8 : ℕ
  tWin8 : ℕ → ℕ
  η8 : ℝ≥0∞
  hesc8 : Slot678SurvivalInputs.Slot8ReadyEscapeAtom
    (L := L) (K := K) n σ E8 η8
  hpt8 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin8 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε8 : ℝ≥0
  hescε8 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η8
      ≤ (escapeε8 : ℝ≥0∞)

  /-- Slot 9 opinion epidemic inputs. -/
  slot9 : Slot9OpinionInputs n

  /-- Slot 10 block-geometric repetition count. -/
  k10 : ℕ

/-- Slot 1 built from the landed Ready-gate survival constructor. -/
noncomputable def slot1Work_of_inputs
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot1SurvivalInputs.slot1SurvivalReady
    (L := L) (K := K)
    A.P1 A.M₀ A.hn A.hM1
    A.η1 A.hesc1
    A.tWin1 A.hpt1 A.escapeε1 A.hescε1

/-- Slot 6 built from the landed Ready-gate survival constructor. -/
noncomputable def slot6Work_of_inputs
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot678SurvivalInputs.slot6SurvivalReady
    (L := L) (K := K)
    A.σ A.l A.M₀ A.hn A.hM1
    A.hl1 A.hlL A.i6 A.K₀6 A.hhgt6 A.hhne6
    A.η6 A.hesc6
    A.tWin6 A.hpt6 A.escapeε6 A.hescε6

/-- Slot 7 built from the landed Ready-gate survival constructor. -/
noncomputable def slot7Work_of_inputs
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot678SurvivalInputs.slot7SurvivalReady
    (L := L) (K := K)
    A.σ A.E7 A.M₀ A.hn A.hM1
    A.η7 A.hesc7
    A.tWin7 A.hpt7 A.escapeε7 A.hescε7

/-- Slot 8 built from the landed Ready-gate survival constructor. -/
noncomputable def slot8Work_of_inputs
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot678SurvivalInputs.slot8SurvivalReady
    (L := L) (K := K)
    A.σ A.E8 A.M₀ A.hn A.hM1
    A.η8 A.hesc8
    A.tWin8 A.hpt8 A.escapeε8 A.hescε8

/-- Slot 9 built from the landed phase-9 opinion-union clone. -/
noncomputable def slot9Work_of_inputs
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase9Convergence.phase9ConvergenceW
    (L := L) (K := K)
    A.slot9.U A.slot9.v n A.hn
    A.slot9.hUsign A.slot9.hvsign
    A.slot9.hvU A.slot9.hUv A.slot9.hvv A.slot9.hUU
    A.slot9.hUv_ne
    A.slot9.s A.slot9.hs A.slot9.t A.slot9.ε A.slot9.hε

/-- The constructed 11-slot faithful work family. -/
noncomputable def work_of_slots
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => A.slot0.work
    | ⟨1, _⟩ => slot1Work_of_inputs (L := L) (K := K) A
    | ⟨2, _⟩ => WorkBuilder.work2_from_phase2 (L := L) (K := K) A.hn A.slot2
    | ⟨3, _⟩ => A.slot3.work
    | ⟨4, _⟩ => WorkBuilder.work4_from_phase4 (L := L) (K := K) A.hn A.slot4
    | ⟨5, _⟩ => A.slot5.work
    | ⟨6, _⟩ => slot6Work_of_inputs (L := L) (K := K) A
    | ⟨7, _⟩ => slot7Work_of_inputs (L := L) (K := K) A
    | ⟨8, _⟩ => slot8Work_of_inputs (L := L) (K := K) A
    | ⟨9, _⟩ => slot9Work_of_inputs (L := L) (K := K) A
    | ⟨10, _⟩ => WorkBuilder.work10_from_concrete
        (L := L) (K := K) A.hn A.k10
    | ⟨m + 11, h⟩ => absurd h (by omega)

/-! ## Seam-shape ties for the constructed work family. -/

/-- Explicit seam shape data for `work_of_slots`.

These are deterministic once each slot’s public constructor exposes the exact
Pre/Post shape.  Until all slots expose those simplification lemmas uniformly, they
are kept as a small, gated shape package instead of hidden in the full work family. -/
structure WorkShapeTies
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ) where
  hPostEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      ((work_of_slots (L := L) (K := K) A) ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c
  hPreEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      ((work_of_slots (L := L) (K := K) A) ⟨k.val + 1, by omega⟩).Pre c
  hSlot10Post :
    ∀ c,
      ((work_of_slots (L := L) (K := K) A) ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c

/-- Slot-0 start bridge for the constructed work family. -/
theorem hSlot0Pre_of_slots
    {n : ℕ} (A : SlotInputs (L := L) (K := K) n) :
    ∀ c, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c →
      ((work_of_slots (L := L) (K := K) A) ⟨0, by omega⟩).Pre c := by
  intro c hc
  exact A.slot0.hPre c hc

/-! ## FaithfulCore construction from slot inputs. -/

/-- Seam/concentration atoms not belonging to an individual work slot. -/
structure SeamAtoms
    {n : ℕ} (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (c₀ : Config (AgentState L K)) where
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  s : Fin 10 → ℝ
  εovershoot : Fin 10 → ℝ≥0
  hs : ∀ k, 0 < s k
  hTdrift :
    ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (s k))
        * (s k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ)
  hdet :
    ∀ k, SeamNoOvershoot.DetSeamOvershootBridge
      (L := L) (K := K) (seamP k)
  hεNO :
    ∀ k, (seamT k : ℝ≥0∞)
        * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
      ≤ (εovershoot k : ℝ≥0∞)
  hPreToNoOvershoot :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c
  hτ :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | SeamNoOvershoot.AtRiskClockZero
              (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
  hEvent :
    ∀ k : Fin 10,
      CascadeSeamAdvance.SeedStepResidual
        (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post
  hReach10 :
    ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable c₀ c

/-- Build `FaithfulCore` from constructed slots plus seam atoms and shape ties. -/
noncomputable def faithfulCore_of_slotAtoms
    {n : ℕ} {c₀ : Config (AgentState L K)}
    (A : SlotInputs (L := L) (K := K) n)
    (S : SeamAtoms
      (L := L) (K := K)
      (n := n) (work_of_slots (L := L) (K := K) A) c₀)
    (Ties : WorkShapeTies (L := L) (K := K) A S.seamP) :
    FaithfulWitness.FaithfulCore (L := L) (K := K) n c₀ where
  work := work_of_slots (L := L) (K := K) A
  seamP := S.seamP
  hPostEq := Ties.hPostEq
  hPreEq := Ties.hPreEq
  hSlot0Pre := hSlot0Pre_of_slots (L := L) (K := K) A
  hSlot10Post := Ties.hSlot10Post
  seamT := S.seamT
  s := S.s
  εovershoot := S.εovershoot
  hs := S.hs
  hTdrift := S.hTdrift
  hdet := S.hdet
  hεNO := S.hεNO
  hPreToNoOvershoot := S.hPreToNoOvershoot
  hτ := S.hτ
  hEvent := S.hEvent
  hReach10 := S.hReach10

/-- The faithful residual bundle from slot-built work. -/
noncomputable def faithfulResidual_of_slotAtoms
    {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n)
    (A : SlotInputs (L := L) (K := K) n)
    (S : SeamAtoms
      (L := L) (K := K)
      (n := n) (work_of_slots (L := L) (K := K) A) c₀)
    (Ties : WorkShapeTies (L := L) (K := K) A S.seamP) :
    Capstone.ResidualAtomsFaithful
      (L := L) (K := K) n Atoms.C0_numeral :=
  FaithfulWitness.faithfulResidual_of_valid
    (L := L) (K := K) hReg c₀ hv hcard
    (faithfulCore_of_slotAtoms (L := L) (K := K) A S Ties)

/-- Doty headline modulo the explicit slot atoms and seam atoms. -/
theorem theorem_3_1_from_slotAtoms
    {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (hv : validInitial c₀)
    (hcard : Multiset.card c₀ = n)
    (A : SlotInputs (L := L) (K := K) n)
    (S : SeamAtoms
      (L := L) (K := K)
      (n := n) (work_of_slots (L := L) (K := K) A) c₀)
    (Ties : WorkShapeTies (L := L) (K := K) A S.seamP)
    (T : ℕ)
    (hT : T = ∑ i,
      (Capstone.phases
        (faithfulResidual_of_slotAtoms
          (L := L) (K := K) hReg c₀ hv hcard A S Ties) i).t)
    (ht : ∀ i,
      (Capstone.phases
        (faithfulResidual_of_slotAtoms
          (L := L) (K := K) hReg c₀ hv hcard A S Ties) i).t
        ≤ (faithfulResidual_of_slotAtoms
            (L := L) (K := K) hReg c₀ hv hcard A S Ties).Cphase i
          * n * (L + 1))
    (hε : ∀ i,
      ((Capstone.phases
        (faithfulResidual_of_slotAtoms
          (L := L) (K := K) hReg c₀ hv hcard A S Ties) i).ε : ℝ≥0∞)
        ≤ ((faithfulResidual_of_slotAtoms
            (L := L) (K := K) hReg c₀ hv hcard A S Ties).δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (Nat.clog 2 n + 1) := by
  exact
    FaithfulWitness.theorem_3_1_unconditional
      (L := L) (K := K)
      hReg c₀ hv hcard
      (faithfulCore_of_slotAtoms (L := L) (K := K) A S Ties)
      T hT ht hε

#print axioms slot1Work_of_inputs
#print axioms slot6Work_of_inputs
#print axioms slot7Work_of_inputs
#print axioms slot8Work_of_inputs
#print axioms slot9Work_of_inputs
#print axioms work_of_slots
#print axioms hSlot0Pre_of_slots
#print axioms faithfulCore_of_slotAtoms
#print axioms faithfulResidual_of_slotAtoms
#print axioms theorem_3_1_from_slotAtoms

end WorkFromSlots

end ExactMajority

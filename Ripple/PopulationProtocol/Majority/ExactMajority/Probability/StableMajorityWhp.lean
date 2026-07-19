import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulCoreDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulDischargeTierA
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot035Expose
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3RaFieldFromAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CascadeSeamAdvance
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReachablePhaseConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamBudgetSlack
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PreToNoOvershootDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamPreToNoOvershootProvenance
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.DeterministicChain

namespace ExactMajority
namespace Theorem31

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Generic Post₃ tail extracted from the slot-3 post-tail shape.

The adapter stored in `Slot3PostTailShapeInputs` has the universal `good0`
field `∀ c, Slot3Entry c → Good 0 (some c)`, so this is the reachable-preserved
phase-3 shape consumed by the work slot.  It deliberately does not pin the start
configuration to the concrete seam entry. -/
def slot3GenericPostTailFromShape
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry) :
    Phase3Post3.Slot3PostTail (L := L) (K := K) n ell M g₀ σ where
  snap :=
    Phase3Assembly.snapshot617Tail_of_dischargedCore
      (L := L) (K := K) post.producers post.adapter

/-- Slot 3, built from the atomic residual bundle through the generic
`Slot3Entry` work constructor. -/
def slot3WorkFromAtoms
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (atoms : Phase3Assembly.Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (_hstatic_entry :
      Phase3Assembly.Slot3LeafTailDischarge.StaticInv
        (L := L) (K := K) D atoms.leakageC entry)
    (_hstatic_stepClosed :
      Phase3Assembly.Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (_hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase3Post3.slot3PostWork
    (L := L) (K := K)
    ((slot3GenericPostTailFromShape (L := L) (K := K) post).withBudget ε3 (by
      calc
        (((slot3GenericPostTailFromShape (L := L) (K := K) post).snap.ε : ℝ≥0) : ℝ≥0∞)
            = ((post.entryTail).ε : ℝ≥0∞) := rfl
        _ ≤ atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) := by
          rw [add_comm atoms.εcore ((post.entryTail).ε : ℝ≥0∞)]
          exact le_self_add
        _ ≤ (ε3 : ℝ≥0∞) := htotal))

/-- The terminal 11-slot work family.  Slot 3 uses the reachable-preserved
`Slot3Entry` precondition, not equality with one canonical entry config. -/
def terminalWork
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : WorkConcreteSlots.SlotInputsConcrete (L := L) (K := K) n)
    (atoms : Phase3Assembly.Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (hstatic_entry : Phase3Assembly.Slot3LeafTailDischarge.StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Phase3Assembly.Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        WorkConcreteSlots.slot0RoleSplitWork (L := L) (K := K) A.slot0
    | ⟨1, _⟩ =>
        WorkFromSlots.slot1Work_of_inputs
          (L := L) (K := K)
          (WorkConcreteSlots.toSlotInputs (L := L) (K := K) A)
    | ⟨2, _⟩ =>
        WorkBuilder.work2_from_phase2 (L := L) (K := K) A.hn A.slot2
    | ⟨3, _⟩ =>
        slot3WorkFromAtoms
          (L := L) (K := K)
          atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
    | ⟨4, _⟩ =>
        WorkBuilder.work4_from_phase4 (L := L) (K := K) A.hn A.slot4
    | ⟨5, _⟩ =>
        WorkConcreteSlots.slot5C5aWork (L := L) (K := K) A.slot5
    | ⟨6, _⟩ =>
        WorkFromSlots.slot6Work_of_inputs
          (L := L) (K := K)
          (WorkConcreteSlots.toSlotInputs (L := L) (K := K) A)
    | ⟨7, _⟩ =>
        WorkFromSlots.slot7Work_of_inputs
          (L := L) (K := K)
          (WorkConcreteSlots.toSlotInputs (L := L) (K := K) A)
    | ⟨8, _⟩ =>
        WorkFromSlots.slot8Work_of_inputs
          (L := L) (K := K)
          (WorkConcreteSlots.toSlotInputs (L := L) (K := K) A)
    | ⟨9, _⟩ =>
        WorkFromSlots.slot9Work_of_inputs
          (L := L) (K := K)
          (WorkConcreteSlots.toSlotInputs (L := L) (K := K) A)
    | ⟨10, _⟩ =>
        WorkBuilder.work10_from_concrete (L := L) (K := K) A.hn A.k10

/--
The single terminal seam-tie residual.

It carries only the seam-interface facts needed by `Assembly'`: work-post to exact seam
window, exact seam output to next work-pre, and the per-seam seed event.
-/
structure TerminalSeamTieResidual
    (c₀ : Config (AgentState L K))
    (n : ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) where
  hPostEqOnReset :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      (5 ≤ seamP k ∧ seamP k ≤ 7) →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c
  hPostGe :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hPreEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c
  hEvent :
    ∀ k : Fin 10,
      CascadeSeamAdvance.SeedStepResidual
        (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post

/-- The half budget used by the de-vacuumed seam assembly. -/
noncomputable def seamHalfBudget (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / (2 * (n : ℝ) ^ 2))

/--
Reachable, measure-level replacement for the old false blanket no-overshoot carries.

This is the honest shape: the tail is required only from genuine seam-entry
configurations reachable from the actual initial configuration.  The `SeamEntry`
premise includes `NoOvershoot` and counter freshness at the start, so this domain does
not include the already-overshot configurations that refute the weak `SeamPre` version.
The residual also carries the scalar half-budget fit for `εovershoot`; the concentration
proof producing this field is the remaining Chernoff over-selection tail, not a
deterministic zero claim.
-/
structure TerminalReachableOvershootResidual
    (c₀ : Config (AgentState L K)) (n : ℕ)
    (seamP seamT : Fin 10 → ℕ) (εovershoot : Fin 10 → ℝ≥0) where
  hNoOvershoot :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) (seamP k) n c →
      SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  hBudget : ∀ k, εovershoot k ≤ seamHalfBudget n

/-- Acid-test projection: the repaired residual domain cannot already violate
`NoOvershoot`, because `SeamEntry` carries it as an entry fact. -/
theorem seamEntry_domain_noOvershoot {n p : ℕ} {c : Config (AgentState L K)}
    (h : PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c) :
    SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c :=
  PreToNoOvershootDischarge.SeamEntry.noOvershoot h

/-- Scalar witness for the repaired seam budget: the overshoot side can be assigned
`1/(2n²)` at every seam.  The concentration proof that this scalar bounds the reachable
tail is exactly the named residual `TerminalReachableOvershootResidual.hNoOvershoot`. -/
theorem terminal_overshoot_half_budget_witness (n : ℕ) :
    ∃ εovershoot : Fin 10 → ℝ≥0, ∀ k, εovershoot k ≤ seamHalfBudget n :=
  ⟨fun _ => seamHalfBudget n, fun _ => le_rfl⟩

/-- The split seam budget is arithmetically satisfiable:
`1/(2n²) + 1/(2n²) ≤ 1/n²`, including the harmless `n = 0` Lean convention case. -/
theorem seamHalfBudget_double_le_invSq (n : ℕ) :
    (((seamHalfBudget n + seamHalfBudget n : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) := by
  by_cases hn : n = 0
  · subst hn
    norm_num [seamHalfBudget]
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hhalf : (seamHalfBudget n : ℝ) = 1 / (2 * (n : ℝ)^2) := by
      rw [seamHalfBudget]
      rw [Real.coe_toNNReal]
      positivity
    have hnn :
        (seamHalfBudget n + seamHalfBudget n : ℝ≥0) =
          Real.toNNReal (1 / (n : ℝ)^2) := by
      apply Subtype.ext
      change ((seamHalfBudget n : ℝ) + (seamHalfBudget n : ℝ)) =
        ((1 / (n : ℝ)^2).toNNReal : ℝ)
      rw [hhalf, Real.coe_toNNReal]
      · field_simp [hnpos.ne']
        ring
      · positivity
    have hrhs : ENNReal.ofReal (1 / (n : ℝ)^2) = 1 / (n : ℝ≥0∞)^2 := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1)]
      rw [ENNReal.ofReal_inv_of_pos]
      · rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (n : ℝ))]
        norm_num
      · positivity
    rw [hnn, ENNReal.coe_nnreal_eq]
    have hto : ((1 / (n : ℝ)^2).toNNReal : ℝ) = 1 / (n : ℝ)^2 := by
      rw [Real.coe_toNNReal]
      positivity
    change ENNReal.ofReal ((1 / (n : ℝ)^2).toNNReal : ℝ) ≤ 1 / (n : ℝ≥0∞)^2
    rw [hto, hrhs]

/-- Any overshoot budget below the half budget fits with the repaired epidemic half budget. -/
theorem seamHalfBudget_add_overshoot_le_invSq (n : ℕ) {εovershoot : ℝ≥0}
    (hε : εovershoot ≤ seamHalfBudget n) :
    (((seamHalfBudget n + εovershoot : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) := by
  have hnn : seamHalfBudget n + εovershoot ≤ seamHalfBudget n + seamHalfBudget n :=
    add_le_add le_rfl hε
  exact le_trans (by exact_mod_cast hnn) (seamHalfBudget_double_le_invSq n)

/-- Concrete non-vacuity witness for the repaired per-seam scalar budget. -/
theorem terminal_seam_half_budget_sum_witness (n : ℕ) :
    ∃ (εepidemic : Fin 10 → ℝ≥0) (εovershoot : Fin 10 → ℝ≥0),
      (∀ k, εepidemic k = seamHalfBudget n) ∧
      (∀ k, εovershoot k ≤ seamHalfBudget n) ∧
      (∀ k, ((εepidemic k + εovershoot k : ℝ≥0) : ℝ≥0∞) ≤
        (1 / (n : ℝ≥0∞) ^ 2)) := by
  refine ⟨fun _ => seamHalfBudget n, fun _ => seamHalfBudget n, ?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k
    exact le_rfl
  · intro k
    exact seamHalfBudget_double_le_invSq n

/-- The reachable overshoot residual's scalar half-budget closes the repaired seam ε budget. -/
theorem terminalReachableOvershoot_seamBudget
    (c₀ : Config (AgentState L K)) (n : ℕ)
    (seamP seamT : Fin 10 → ℕ) (εovershoot : Fin 10 → ℝ≥0)
    (hOvershoot :
      TerminalReachableOvershootResidual (L := L) (K := K) c₀ n seamP seamT εovershoot) :
    ∀ k, (((seamHalfBudget n + εovershoot k : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) := by
  intro k
  exact seamHalfBudget_add_overshoot_le_invSq n (hOvershoot.hBudget k)

/-- The reachable-scoped exact seam epidemic: drift is global, no-overshoot is only reachable. -/
noncomputable def seamEpidemicExactWR
    (c₀ : Config (AgentState L K)) (p n tseam : ℕ)
    (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c →
        PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c →
        SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞)) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ where
  Pre := fun c =>
    PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c ∧
      SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c
  Post := fun c =>
    SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c
  t := tseam
  ε := εepidemic + εovershoot
  convergence := by
    intro c hreach hPreFull
    obtain ⟨hPre, hExact⟩ := hPreFull
    have hPreWeak : PreToNoOvershootDischarge.SeamPre (L := L) (K := K) p n c :=
      PreToNoOvershootDischarge.SeamEntry.seamPre hPre
    have hA := hDrift c hPreWeak
    have hB := hNoOvershoot c hreach hPre hExact
    have hcover :
        {c' : Config (AgentState L K) |
          ¬ (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
              SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c')}
          ⊆
        {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ∪ {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
              SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c')}
        ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            ({c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
              ∪ {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          + ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'} :=
          measure_union_le _ _
      _ ≤ (εepidemic : ℝ≥0∞) + (εovershoot : ℝ≥0∞) := add_le_add hA hB
      _ = ((εepidemic + εovershoot : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl

/-- The one-step handoff from work `Post` to genuine seam-entry.  This is the
named residual left when the work-post interface has not yet exposed
no-overshoot-at-entry and counter freshness directly. -/
noncomputable def seamEntryStepWR
    (c₀ : Config (AgentState L K)) (p n : ℕ)
    (workPre : Config (AgentState L K) → Prop)
    (hEntryFromWorkPost :
      PreToNoOvershootDischarge.SeamEntryFromWorkPost
        (L := L) (K := K) p n workPre)
    (hExactFromWorkPost :
      ∀ c : Config (AgentState L K), workPre c →
        ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c'} = 0) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ where
  Pre := workPre
  Post := fun c =>
    PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c ∧
      SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c
  t := 1
  ε := 0
  convergence := by
    intro c _hreach hPre
    have hA : ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c'} = 0 := by
      simpa [PreToNoOvershootDischarge.SeamEntryFromWorkPost] using hEntryFromWorkPost c hPre
    have hB := hExactFromWorkPost c hPre
    have hsub :
        {c' : Config (AgentState L K) |
          ¬ (PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c' ∧
              SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c')}
          ⊆
        {c' | ¬ PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c'}
          ∪ {c' | ¬ SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ (PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c' ∧
                SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c')}
          ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
              ({c' | ¬ PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c'}
                ∪ {c' | ¬ SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c'}) :=
            measure_mono hsub
        _ ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
              {c' | ¬ PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c'}
            + ((NonuniformMajority L K).transitionKernel ^ 1) c
              {c' | ¬ SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c'} :=
            measure_union_le _ _
        _ = 0 := by rw [hA, hB]; simp
        _ ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by simp

/-- The shifted reachable seam `seed step ⊕ reachable exact seam`. -/
noncomputable def seamWithSeedWR
    (c₀ : Config (AgentState L K)) (p n tseam : ℕ)
    (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c →
        PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) p n c →
        SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞))
    (workPre : Config (AgentState L K) → Prop)
    (hEntryFromWorkPost :
      PreToNoOvershootDischarge.SeamEntryFromWorkPost
        (L := L) (K := K) p n workPre)
    (hExactFromWorkPost :
      ∀ c : Config (AgentState L K), workPre c →
        ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) p n c'} = 0) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ where
  Pre := workPre
  Post := (seamEpidemicExactWR (L := L) (K := K) c₀ p n tseam
    εepidemic εovershoot hDrift hNoOvershoot).Post
  t := 1 + tseam
  ε := 0 + (εepidemic + εovershoot)
  convergence := by
    intro c hreach hPre
    let seed := seamEntryStepWR (L := L) (K := K) c₀ p n workPre hEntryFromWorkPost
      hExactFromWorkPost
    let seam := seamEpidemicExactWR (L := L) (K := K) c₀ p n tseam
      εepidemic εovershoot hDrift hNoOvershoot
    have hcompose := composeWR_two_phases (NonuniformMajority L K) seed seam
      (fun x _hreach hx => by
        exact hx)
      c hreach hPre
    have hts : seed.t + seam.t = 1 + tseam := rfl
    have hes : (seed.ε + seam.ε : ℝ≥0∞) =
        ((0 + (εepidemic + εovershoot) : ℝ≥0) : ℝ≥0∞) := by
      push_cast
      rfl
    simpa [seed, seam, hts, hes] using hcompose

@[simp] theorem seamWithSeedWR_Post
    (c₀ : Config (AgentState L K)) (p n tseam : ℕ)
    (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hEntryFromWorkPost hExactFromWorkPost)
    (c : Config (AgentState L K)) :
    (seamWithSeedWR (L := L) (K := K) c₀ p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hEntryFromWorkPost hExactFromWorkPost).Post c
      = (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
          SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c) := rfl

/-- Reachable-scoped terminal assembly. -/
structure TerminalAssemblyR
    (n : ℕ) (c₀ : Config (AgentState L K)) where
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  εepidemic : Fin 10 → ℝ≥0
  εovershoot : Fin 10 → ℝ≥0
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      PreToNoOvershootDischarge.SeamPre (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      PreToNoOvershootDischarge.SeamEntry (L := L) (K := K) (seamP k) n c →
      SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  hSeamEntryFromWorkPost : ∀ k : Fin 10,
      PreToNoOvershootDischarge.SeamEntryFromWorkPost
        (L := L) (K := K) (seamP k) n (work ⟨k.val, by omega⟩).Post
  hSeamExactFromWorkPost : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEntryPhaseCeiling.SeamEntryExactIfReset (L := L) (K := K) (seamP k) n c'} = 0
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c

/-- The `k`-th reachable shifted seam instance. -/
noncomputable def seamInstanceR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) (k : Fin 10) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ :=
  seamWithSeedWR (L := L) (K := K) c₀ (asm.seamP k) n (asm.seamT k)
    (asm.εepidemic k) (asm.εovershoot k) (asm.hDrift k) (asm.hNoOvershoot k)
    (fun c => (asm.work ⟨k.val, by omega⟩).Post c)
    (asm.hSeamEntryFromWorkPost k)
    (asm.hSeamExactFromWorkPost k)

/-- The reachable 21-instance family. -/
noncomputable def phasesR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    Fin 21 → PhaseConvergenceWR (NonuniformMajority L K) c₀ :=
  fun i =>
    if h : i.val % 2 = 0 then
      PhaseConvergenceWR.ofW (NonuniformMajority L K) c₀
        (asm.work (ConcreteAssembly.workIdx i))
    else seamInstanceR asm (ConcreteAssembly.seamIdx i (by omega))

@[simp] theorem phasesR_even {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (i : Fin 21) (h : i.val % 2 = 0) :
    phasesR asm i =
      PhaseConvergenceWR.ofW (NonuniformMajority L K) c₀
        (asm.work (ConcreteAssembly.workIdx i)) := by
  simp only [phasesR, dif_pos h]

@[simp] theorem phasesR_odd {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (i : Fin 21) (h : i.val % 2 = 1) :
    phasesR asm i = seamInstanceR asm (ConcreteAssembly.seamIdx i h) := by
  simp only [phasesR, dif_neg (by omega : ¬ i.val % 2 = 0)]

/-- Build the reachable terminal assembly from the terminal work family, half seam drift, and seam glue. -/
def terminalAssembly
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (c₀ : Config (AgentState L K))
    (A : WorkConcreteSlots.SlotInputsConcrete (L := L) (K := K) n)
    (atoms : Phase3Assembly.Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (hstatic_entry : Phase3Assembly.Slot3LeafTailDischarge.StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Phase3Assembly.Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry)
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      SeamBudgetSlack.seamJansonT2 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      PreToNoOvershootDischarge.SeamEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot :
      TerminalReachableOvershootResidual (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (tie :
      TerminalSeamTieResidual (L := L) (K := K) c₀ n
        (terminalWork
          (L := L) (K := K)
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
        seamP) :
    TerminalAssemblyR (L := L) (K := K) n c₀ := by
  let work :=
    terminalWork
      (L := L) (K := K)
      A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
  exact
    { work := work
      seamP := seamP
      seamT := seamT
      εepidemic := fun _ => seamHalfBudget n
      εovershoot := εovershoot
      hDrift := SeamBudgetSlack.seamDischarge_hDrift_janson_half
        (L := L) (K := K) n A.hn seamP seamT hTjanson
      hNoOvershoot := hOvershoot.hNoOvershoot
      hSeamEntryFromWorkPost := by
        intro k
        simpa [work] using hSeamEntryFromWorkPost k
      hSeamExactFromWorkPost := by
        intro k c hpost
        exact SeamEntryPhaseCeiling.exactIfReset_measure_zero_of_allPhaseEqOnReset
          (L := L) (K := K) (seamP k) n c (fun hband => tie.hPostEqOnReset k c hpost hband)
      hWorkPostToWindow := by
        intro k c hpost
        exact tie.hPostGe k c hpost
      hSeedStep := by
        intro k c hpost
        have h :=
          CascadeSeamAdvance.hSeedStep_generic
            (L := L) (K := K) work seamP tie.hEvent k c hpost
        simpa using h
      hWindowToWorkPre := by
        intro k c hreach hwin
        have h := tie.hPreEq k c hreach hwin
        simpa using h }

theorem terminalWork_slot10_post
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : WorkConcreteSlots.SlotInputsConcrete (L := L) (K := K) n)
    (atoms : Phase3Assembly.Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (hstatic_entry : Phase3Assembly.Slot3LeafTailDischarge.StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Phase3Assembly.Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    ∀ c,
      ((terminalWork
        (L := L) (K := K)
        A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
        ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c := by
  intro c hc
  simpa [terminalWork, WorkBuilder.work10_from_concrete] using hc

/-- Work-to-reachable-seam bridge. -/
theorem bridge_work_to_seamR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (asm.work ⟨k.val, by omega⟩).Post c) :
    (seamInstanceR asm k).Pre c := hpost

/-- Reachable seam-to-work bridge. -/
theorem bridge_seam_to_workR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (k : Fin 10) (c : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable c₀ c)
    (hpost : (seamInstanceR asm k).Post c) :
    (asm.work ⟨k.val + 1, by omega⟩).Pre c := by
  have hP : SeamEpidemics.allPhaseGe (L := L) (K := K) (asm.seamP k + 1) n c ∧
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (asm.seamP k) c := by
    simpa [seamInstanceR] using hpost
  have hwin : SeamEpidemics.allPhaseEq (L := L) (K := K) (asm.seamP k + 1) n c :=
    SeamNoOvershoot.seamExact_into_exact_work c hP
  exact asm.hWindowToWorkPre k c hreach hwin

/-- Chain bridge for the reachable 21-phase family. -/
theorem phasesR_h_chain {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x, (NonuniformMajority L K).Reachable c₀ x →
        (phasesR asm i).Post x → (phasesR asm ⟨i.val + 1, hi⟩).Pre x := by
  intro i hi x hreach hpost
  have hjval : (⟨i.val + 1, hi⟩ : Fin 21).val = i.val + 1 := rfl
  rcases Nat.even_or_odd i.val with hev | hod
  · have hi0 : i.val % 2 = 0 := Nat.even_iff.mp hev
    have hsucc1 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 1 := by rw [hjval]; omega
    rw [phasesR_even asm i hi0] at hpost
    rw [phasesR_odd asm ⟨i.val + 1, hi⟩ hsucc1]
    set k : Fin 10 := ConcreteAssembly.seamIdx ⟨i.val + 1, hi⟩ hsucc1 with hkdef
    have hkw : (⟨k.val, by omega⟩ : Fin 11) = ConcreteAssembly.workIdx i := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by
        rw [hkdef, ConcreteAssembly.seamIdx_val, hjval]; omega
      rw [Fin.val_mk, hkval, ConcreteAssembly.workIdx_val]
    have hbridge := bridge_work_to_seamR asm k x
    rw [hkw] at hbridge
    exact hbridge hpost
  · have hi1 : i.val % 2 = 1 := Nat.odd_iff.mp hod
    have hsucc0 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 0 := by rw [hjval]; omega
    rw [phasesR_odd asm i hi1] at hpost
    rw [phasesR_even asm ⟨i.val + 1, hi⟩ hsucc0]
    set k : Fin 10 := ConcreteAssembly.seamIdx i hi1 with hkdef
    have hkw : (⟨k.val + 1, by omega⟩ : Fin 11) = ConcreteAssembly.workIdx ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, ConcreteAssembly.seamIdx_val]
      rw [Fin.val_mk, hkval, ConcreteAssembly.workIdx_val, hjval]
      omega
    have hbridge := bridge_seam_to_workR asm k x hreach
    rw [hkw] at hbridge
    exact hbridge hpost

/-- Reachable-scoped terminal core used by the de-vacuumed final theorem. -/
structure TerminalReachableWorkSeamCore
    (n : ℕ) (c₀ : Config (AgentState L K)) where
  asm : TerminalAssemblyR (L := L) (K := K) n c₀
  hStart : (asm.work ⟨0, by omega⟩).Pre c₀
  hSlot10Post : ∀ c, (asm.work ⟨10, by omega⟩).Post c →
    Phase10Drop.Phase10Post (L := L) (K := K) c
  hValid : validInitial c₀

/-- Wrap the terminal reachable assembly as `TerminalReachableWorkSeamCore`. -/
def terminalFaithfulWorkSeamCore
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    (hValid : validInitial c₀)
    (A : WorkConcreteSlots.SlotInputsConcrete (L := L) (K := K) n)
    (atoms : Phase3Assembly.Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (hstatic_entry : Phase3Assembly.Slot3LeafTailDischarge.StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Phase3Assembly.Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry)
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      SeamBudgetSlack.seamJansonT2 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      PreToNoOvershootDischarge.SeamEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot :
      TerminalReachableOvershootResidual (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (tie :
      TerminalSeamTieResidual (L := L) (K := K) c₀ n
        (terminalWork
          (L := L) (K := K)
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
        seamP) :
    TerminalReachableWorkSeamCore (L := L) (K := K) n c₀ := by
  let asm :=
    terminalAssembly
      (L := L) (K := K)
      c₀ A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
      seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot tie
  exact
    { asm := asm
      hStart := by
        change RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
        exact FaithfulDischargeTierA.phase0Initial_of_validInitial
          (L := L) (K := K) n c₀ hValid hcard
      hSlot10Post := by
        intro c hc
        exact
          terminalWork_slot10_post
            (L := L) (K := K)
            A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry c hc
      hValid := hValid }

set_option maxHeartbeats 2000000 in
/-- Chain-restricted final bad-set bound for reachable terminal assemblies. -/
theorem chainRestricted_bad_boundR {n : ℕ} {c₀ : Config (AgentState L K)}
    (core : TerminalReachableWorkSeamCore (L := L) (K := K) n c₀)
    (T : ℕ) (hT : T = ∑ i, (phasesR core.asm i).t)
    (Esum : ℝ≥0∞) (hEsum : Esum = ∑ i, ((phasesR core.asm i).ε : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ Esum := by
  have hx₀ : (phasesR core.asm ⟨0, by omega⟩).Pre c₀ := by
    rw [phasesR_even _ _ (by rfl)]
    show (core.asm.work (ConcreteAssembly.workIdx ⟨0, by omega⟩)).Pre c₀
    rw [show ConcreteAssembly.workIdx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin 11) from by
      apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
    exact core.hStart
  have hreach₀ : (NonuniformMajority L K).Reachable c₀ c₀ := Relation.ReflTransGen.refl
  have h_compose :=
    composeWR_n_phases (NonuniformMajority L K)
      (m := 21) (by omega) (phasesR core.asm)
      (phasesR_h_chain core.asm) c₀ hreach₀ hx₀
  rw [← hT, ← hEsum] at h_compose
  have hpost :
      ∀ c, (NonuniformMajority L K).Reachable c₀ c →
        (phasesR core.asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) c₀ c := by
    intro c hreach hPost
    have hP10 : Phase10Drop.Phase10Post (L := L) (K := K) c := by
      have heq : (phasesR core.asm ⟨21 - 1, by omega⟩).Post c
          = (core.asm.work ⟨10, by omega⟩).Post c := by
        rw [phasesR_even _ _ (by norm_num)]
        show (core.asm.work (ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩)).Post c
            = (core.asm.work ⟨10, by omega⟩).Post c
        rw [show ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩ = (⟨10, by omega⟩ : Fin 11) from by
          apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
      exact core.hSlot10Post c (heq ▸ hPost)
    exact Or.inr (Or.inr (Or.inr
      (FaithfulCoreDischarge.majorityWitness_of_reachable_post core.hValid hreach hP10)))
  have h_subset :
      {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
        ⊆ {c | ¬ (phasesR core.asm ⟨21 - 1, by omega⟩).Post c}
          ∪ {c | ¬ (NonuniformMajority L K).Reachable c₀ c} := by
    intro c hc
    by_cases hreach : (NonuniformMajority L K).Reachable c₀ c
    · refine Or.inl ?_
      simp only [Set.mem_setOf_eq] at hc ⊢
      intro hPost
      exact hc (hpost c hreach hPost)
    · exact Or.inr hreach
  have h_unreach :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (NonuniformMajority L K).Reachable c₀ c} = 0 :=
    nonuniformTransitionKernel_pow_not_reachable_eq_zero L K c₀ T
  calc ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ ((NonuniformMajority L K).transitionKernel ^ T) c₀
          ({c | ¬ (phasesR core.asm ⟨21 - 1, by omega⟩).Post c}
            ∪ {c | ¬ (NonuniformMajority L K).Reachable c₀ c}) := measure_mono h_subset
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (phasesR core.asm ⟨21 - 1, by omega⟩).Post c}
        + ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (NonuniformMajority L K).Reachable c₀ c} := measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (phasesR core.asm ⟨21 - 1, by omega⟩).Post c} := by
        rw [h_unreach, add_zero]
    _ ≤ Esum := h_compose

set_option maxHeartbeats 4000000 in
/-- Theorem 3.1 of [Doty–Eftekhari–Severson 2021]: the exact majority
population protocol stabilizes within O(n log n) interactions except with
probability ≤ 21/n². -/
theorem stable_majority_whp
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    (hValid : validInitial c₀)
    (A : WorkConcreteSlots.SlotInputsConcrete (L := L) (K := K) n)
    (atoms : Phase3Assembly.Slot3AtomicResiduals (L := L) (K := K) D θ entry)
    (hstatic_entry : Phase3Assembly.Slot3LeafTailDischarge.StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Phase3Assembly.Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Phase3Assembly.Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry)
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      SeamBudgetSlack.seamJansonT2 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      PreToNoOvershootDischarge.SeamEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot :
      TerminalReachableOvershootResidual (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (tie :
      TerminalSeamTieResidual (L := L) (K := K) c₀ n
        (terminalWork
          (L := L) (K := K)
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry)
        seamP)
    (T : ℕ)
    (hT :
      let core :=
        terminalFaithfulWorkSeamCore
          (L := L) (K := K)
          c₀ hcard hValid
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
          seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot tie
      T = ∑ i, (phasesR core.asm i).t)
    (ht :
      let core :=
        terminalFaithfulWorkSeamCore
          (L := L) (K := K)
          c₀ hcard hValid
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
          seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot tie
      ∀ i, (phasesR core.asm i).t
        ≤ Atoms.C0_numeral * n * (L + 1))
    (hε :
      let core :=
        terminalFaithfulWorkSeamCore
          (L := L) (K := K)
          c₀ hcard hValid
          A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
          seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot tie
      ∀ i, ((phasesR core.asm i).ε : ℝ≥0∞)
        ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (Nat.clog 2 n + 1) := by
  let core :=
    terminalFaithfulWorkSeamCore
      (L := L) (K := K)
      c₀ hcard hValid
      A atoms hstatic_entry hstatic_stepClosed post ε3 htotal hentry
      seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot tie
  have herr0 := chainRestricted_bad_boundR
    (L := L) (K := K) core T hT
    (∑ i, ((phasesR core.asm i).ε : ℝ≥0∞)) rfl
  have herr : ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    refine le_trans herr0 ?_
    have h21 := BudgetTightening.sum_inv_sq_le
      (m := 21) (n := n) (fun i => (phasesR core.asm i).ε) hε
    simpa using h21
  have htime : T ≤ 21 * Atoms.C0_numeral * n * (L + 1) := by
    rw [hT]
    refine le_trans (total_time_le_W
      (fun i => (phasesR core.asm i).t)
      (fun _ => Atoms.C0_numeral) ht) ?_
    have hsum : (∑ _i : Fin 21, Atoms.C0_numeral) = 21 * Atoms.C0_numeral := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]
    rw [hsum]
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]
  exact htime

#print axioms slot3WorkFromAtoms
#print axioms terminalWork
#print axioms TerminalSeamTieResidual
#print axioms terminal_overshoot_half_budget_witness
#print axioms seamHalfBudget_double_le_invSq
#print axioms seamHalfBudget_add_overshoot_le_invSq
#print axioms terminal_seam_half_budget_sum_witness
#print axioms terminalReachableOvershoot_seamBudget
#print axioms terminalAssembly
#print axioms terminalWork_slot10_post
#print axioms terminalFaithfulWorkSeamCore
#print axioms chainRestricted_bad_boundR
#print axioms stable_majority_whp

end

end Theorem31
end ExactMajority

import Ripple.PopulationProtocol.ExactMajority.Probability.FaithfulCoreChainRestricted
import Ripple.PopulationProtocol.ExactMajority.Probability.FaithfulDeterministicFacts
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase035Work
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3EntryHypothesesOfTails
import Ripple.PopulationProtocol.ExactMajority.Probability.GenericPhaseAdvance
import Ripple.PopulationProtocol.ExactMajority.Probability.ReachablePhaseConvergence
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceBudgetSlack
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEntryNoOvershoot
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEntryPhaseCeiling
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

namespace Ripple.PopulationProtocol.ExactMajority
namespace Theorem31

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Generic Post₃ tail extracted from the slot-3 post-tail shape.

The adapter stored in `Phase3PostTailShape` has the universal `good0`
field `∀ c, Phase3EntryGap c → Good 0 (some c)`, so this is the reachable-preserved
phase-3 shape consumed by the work slot.  It deliberately does not pin the start
configuration to the concrete seam entry. -/
def phase3GenericPostTailFromShape
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry) :
    Phase3Post3.Phase3PostTail (L := L) (K := K) n ell M g₀ σ where
  snap :=
    Phase3Assembly.snapshot617Tail_of_markedCoreEngineProducers
      (L := L) (K := K) post.producers post.adapter

/-- Slot 3, built from the discharged post-tail shape through the generic
`Phase3EntryGap` work constructor.

The earlier signature carried entry-specific atomic/static hypotheses that
were not consumed by this generic constructor.  Keeping those phantom
parameters made a false blanket `StaticInvStepClosed` look load-bearing. -/
def phase3WorkFromPostShape
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase3Post3.phase3PostWork
    (L := L) (K := K)
    ((phase3GenericPostTailFromShape (L := L) (K := K) post).withBudget ε3 (by
      calc
        (((phase3GenericPostTailFromShape (L := L) (K := K) post).snap.ε : ℝ≥0) : ℝ≥0∞)
            = ((post.entryTail).ε : ℝ≥0∞) := rfl
        _ ≤ (ε3 : ℝ≥0∞) := hpost))

/-- The terminal 11-slot work family.  Slot 3 uses the reachable-preserved
`Phase3EntryGap` precondition, not equality with one canonical entry config. -/
def terminalWork
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞)) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        Phase035Work.phase0RoleSplitWork (L := L) (K := K) A.slot0
    | ⟨1, _⟩ =>
        PhaseWorkFamily.phase1Work_of_familyData
          (L := L) (K := K)
          (Phase035Work.toWorkFamilyData (L := L) (K := K) A)
    | ⟨2, _⟩ =>
        TightEpidemicWork.work2Tight (L := L) (K := K) A.hn
    | ⟨3, _⟩ =>
        phase3WorkFromPostShape
          (L := L) (K := K)
          post ε3 hpost
    | ⟨4, _⟩ =>
        TightEpidemicWork.work4Tight (L := L) (K := K) A.hn
    | ⟨5, _⟩ =>
        Phase035Work.phase5C5aWork (L := L) (K := K) A.slot5
    | ⟨6, _⟩ =>
        PhaseWorkFamily.phase6Work_of_familyData
          (L := L) (K := K)
          (Phase035Work.toWorkFamilyData (L := L) (K := K) A)
    | ⟨7, _⟩ =>
        PhaseWorkFamily.phase7Work_of_familyData
          (L := L) (K := K)
          (Phase035Work.toWorkFamilyData (L := L) (K := K) A)
    | ⟨8, _⟩ =>
        PhaseWorkFamily.phase8Work_of_familyData
          (L := L) (K := K)
          (Phase035Work.toWorkFamilyData (L := L) (K := K) A)
    | ⟨9, _⟩ =>
        TightEpidemicWork.work9Tight (L := L) (K := K) A.hn
    | ⟨10, _⟩ =>
        WorkBuilder.work10_from_concrete (L := L) (K := K) A.hn A.k10

/-- Deterministic seam-entry glue for the terminal assembly.

This residual carries the reset-band exactness fact and the one-step seed event.
The probabilistic handoff to the next work precondition is deliberately kept in
`TerminalAdvancePayloadHypotheses` below. -/
structure TerminalAdvanceEntryHypotheses
    (n : ℕ)
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) where
  hPostEqOnReset :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      (5 ≤ seamP k ∧ seamP k ≤ 7) →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c
  hEvent :
    ∀ k : Fin 10,
      GenericPhaseAdvance.SeedStepResidual
        (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post

/-- The fixed epidemic half-budget term used by the terminal seam assembly. -/
noncomputable def advanceHalfBudget (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / (2 * (n : ℝ) ^ 2))

/-- Honest probabilistic payload for each seam-to-next-work handoff.

The old interface asserted that an exact phase window deterministically implied every
next work precondition.  The concrete work preconditions contain substantially more
state, so that assertion was too strong.  This residual instead asks for the actual
reachable seam tail that produces the next work precondition, and charges its failure
probability explicitly to the per-seam budget. -/
structure TerminalAdvancePayloadHypotheses
    (c₀ : Config (AgentState L K))
    (n : ℕ)
    (m : ℕ)
    (work : Fin (m + 1) → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP seamT : Fin m → ℕ)
    (εovershoot : Fin m → ℝ≥0) where
  εpayload : Fin m → ℝ≥0
  hNextPre :
    ∀ (k : Fin m) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) (seamP k) n c →
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset
        (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ (work ⟨k.val + 1, by omega⟩).Pre c'}
        ≤ (εpayload k : ℝ≥0∞)
  hBudget : ∀ k,
    (((advanceHalfBudget n + εovershoot k + εpayload k : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2))

/--
Reachable, measure-level replacement for the old false blanket no-overshoot carries.

This is the honest shape: the tail is required only from genuine seam-entry
configurations reachable from the actual initial configuration.  The `AdvanceEntry`
premise includes `NoOvershoot` and counter freshness at the start, so this domain does
not include the already-overshot configurations that refute the weak `SeamPre` version.
The residual also carries an individual half-budget cap for `εovershoot`; the stronger
three-way fit with the payload tail is recorded by
`TerminalAdvancePayloadHypotheses.hBudget`.  The concentration proof producing this field is
the remaining Chernoff over-selection tail, not a deterministic zero claim.
-/
structure TerminalReachableOvershootHypotheses
    (c₀ : Config (AgentState L K)) (n : ℕ)
    (seamP seamT : Fin 10 → ℕ) (εovershoot : Fin 10 → ℝ≥0) where
  hNoOvershoot :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) (seamP k) n c →
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  hBudget : ∀ k, εovershoot k ≤ advanceHalfBudget n

/-- Acid-test projection: the repaired residual domain cannot already violate
`NoOvershoot`, because `AdvanceEntry` carries it as an entry fact. -/
theorem seamEntry_domain_noOvershoot {n p : ℕ} {c : Config (AgentState L K)}
    (h : AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c) :
    AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c :=
  AdvanceEntryNoOvershoot.AdvanceEntry.noOvershoot h

/-- Scalar witness for the repaired seam budget: the overshoot side can be assigned
`1/(2n²)` at every seam.  The concentration proof that this scalar bounds the reachable
tail is exactly the named residual `TerminalReachableOvershootHypotheses.hNoOvershoot`. -/
theorem terminal_overshoot_half_budget_witness (n : ℕ) :
    ∃ εovershoot : Fin 10 → ℝ≥0, ∀ k, εovershoot k ≤ advanceHalfBudget n :=
  ⟨fun _ => advanceHalfBudget n, fun _ => le_rfl⟩

/-- The epidemic and overshoot baseline split is arithmetically satisfiable:
`1/(2n²) + 1/(2n²) ≤ 1/n²`, including the harmless `n = 0` Lean convention case.
Any nonzero payload requires slack in the overshoot term. -/
theorem advanceHalfBudget_double_le_invSq (n : ℕ) :
    (((advanceHalfBudget n + advanceHalfBudget n : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) := by
  by_cases hn : n = 0
  · subst hn
    norm_num [advanceHalfBudget]
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hhalf : (advanceHalfBudget n : ℝ) = 1 / (2 * (n : ℝ)^2) := by
      rw [advanceHalfBudget]
      rw [Real.coe_toNNReal]
      positivity
    have hnn :
        (advanceHalfBudget n + advanceHalfBudget n : ℝ≥0) =
          Real.toNNReal (1 / (n : ℝ)^2) := by
      apply Subtype.ext
      change ((advanceHalfBudget n : ℝ) + (advanceHalfBudget n : ℝ)) =
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
theorem advanceHalfBudget_add_overshoot_le_invSq (n : ℕ) {εovershoot : ℝ≥0}
    (hε : εovershoot ≤ advanceHalfBudget n) :
    (((advanceHalfBudget n + εovershoot : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) := by
  have hnn : advanceHalfBudget n + εovershoot ≤ advanceHalfBudget n + advanceHalfBudget n :=
    add_le_add le_rfl hε
  exact le_trans (by exact_mod_cast hnn) (advanceHalfBudget_double_le_invSq n)

/-- Concrete witness for the two-term epidemic/overshoot baseline budget. -/
theorem terminal_advance_half_budget_sum_witness (n : ℕ) :
    ∃ (εepidemic : Fin 10 → ℝ≥0) (εovershoot : Fin 10 → ℝ≥0),
      (∀ k, εepidemic k = advanceHalfBudget n) ∧
      (∀ k, εovershoot k ≤ advanceHalfBudget n) ∧
      (∀ k, ((εepidemic k + εovershoot k : ℝ≥0) : ℝ≥0∞) ≤
        (1 / (n : ℝ≥0∞) ^ 2)) := by
  refine ⟨fun _ => advanceHalfBudget n, fun _ => advanceHalfBudget n, ?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k
    exact le_rfl
  · intro k
    exact advanceHalfBudget_double_le_invSq n

/-- The reachable overshoot residual fits the two baseline seam terms before payload. -/
theorem terminalReachableOvershoot_advanceBudget
    (c₀ : Config (AgentState L K)) (n : ℕ)
    (seamP seamT : Fin 10 → ℕ) (εovershoot : Fin 10 → ℝ≥0)
    (hOvershoot :
      TerminalReachableOvershootHypotheses (L := L) (K := K) c₀ n seamP seamT εovershoot) :
    ∀ k, (((advanceHalfBudget n + εovershoot k : ℝ≥0) : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) := by
  intro k
  exact advanceHalfBudget_add_overshoot_le_invSq n (hOvershoot.hBudget k)

/-- The reachable-scoped seam epidemic with an explicit next-work payload tail. -/
noncomputable def advanceEpidemicExactWR
    (c₀ : Config (AgentState L K)) (p n tseam : ℕ)
    (εepidemic εovershoot εpayload : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (AdvanceEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          AdvanceEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c →
        AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c →
        AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞))
    (nextPre : Config (AgentState L K) → Prop)
    (hNextPre : ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c →
        AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c →
        AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ nextPre c'}
          ≤ (εpayload : ℝ≥0∞)) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ where
  Pre := fun c =>
    AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c ∧
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c
  Post := fun c =>
    (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c) ∧
      nextPre c
  t := tseam
  ε := εepidemic + εovershoot + εpayload
  convergence := by
    intro c hreach hPreFull
    obtain ⟨hPre, hExact⟩ := hPreFull
    have hPreWeak : AdvanceEntryNoOvershoot.AdvancePre (L := L) (K := K) p n c :=
      AdvanceEntryNoOvershoot.AdvanceEntry.advancePre hPre
    have hA := hDrift c hPreWeak
    have hB := hNoOvershoot c hreach hPre hExact
    have hC := hNextPre c hreach hPre hExact
    have hcover :
        {c' : Config (AgentState L K) |
          ¬ ((AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
              AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c') ∧
              nextPre c')}
          ⊆
        ({c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ∪ {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'})
          ∪ {c' | ¬ nextPre c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ ((AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
              AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c') ∧
              nextPre c')}
        ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            (({c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
              ∪ {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'})
              ∪ {c' | ¬ nextPre c'}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            ({c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
              ∪ {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'})
          + ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ nextPre c'} :=
          measure_union_le _ _
      _ ≤ (((NonuniformMajority L K).transitionKernel ^ tseam) c
              {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
            + ((NonuniformMajority L K).transitionKernel ^ tseam) c
              {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'})
          + ((NonuniformMajority L K).transitionKernel ^ tseam) c
              {c' | ¬ nextPre c'} :=
        add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ((εepidemic : ℝ≥0∞) + (εovershoot : ℝ≥0∞)) + (εpayload : ℝ≥0∞) :=
        add_le_add (add_le_add hA hB) hC
      _ = ((εepidemic + εovershoot + εpayload : ℝ≥0) : ℝ≥0∞) := by
        push_cast
        rfl

/-- The one-step handoff from work `Post` to genuine seam-entry.  This is the
named residual left when the work-post interface has not yet exposed
no-overshoot-at-entry and counter freshness directly. -/
noncomputable def advanceEntryStepWR
    (c₀ : Config (AgentState L K)) (p n : ℕ)
    (workPre : Config (AgentState L K) → Prop)
    (hEntryFromWorkPost :
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) p n workPre)
    (hExactFromWorkPost :
      ∀ c : Config (AgentState L K), workPre c →
        ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c'} = 0) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ where
  Pre := workPre
  Post := fun c =>
    AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c ∧
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c
  t := 1
  ε := 0
  convergence := by
    intro c _hreach hPre
    have hA : ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c'} = 0 := by
      simpa [AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost] using hEntryFromWorkPost c hPre
    have hB := hExactFromWorkPost c hPre
    have hsub :
        {c' : Config (AgentState L K) |
          ¬ (AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c' ∧
              AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c')}
          ⊆
        {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c'}
          ∪ {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ (AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c' ∧
                AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c')}
          ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
              ({c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c'}
                ∪ {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c'}) :=
            measure_mono hsub
        _ ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
              {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c'}
            + ((NonuniformMajority L K).transitionKernel ^ 1) c
              {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c'} :=
            measure_union_le _ _
        _ = 0 := by rw [hA, hB]; simp
        _ ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by simp

/-- The shifted reachable seam `seed step ⊕ reachable seam with payload`. -/
noncomputable def advanceWithSeedWR
    (c₀ : Config (AgentState L K)) (p n tseam : ℕ)
    (εepidemic εovershoot εpayload : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (AdvanceEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          AdvanceEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c →
        AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c →
        AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞))
    (nextPre : Config (AgentState L K) → Prop)
    (hNextPre : ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c →
        AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c →
        AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ nextPre c'}
          ≤ (εpayload : ℝ≥0∞))
    (workPre : Config (AgentState L K) → Prop)
    (hEntryFromWorkPost :
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) p n workPre)
    (hExactFromWorkPost :
      ∀ c : Config (AgentState L K), workPre c →
        ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) p n c'} = 0) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ where
  Pre := workPre
  Post := (advanceEpidemicExactWR (L := L) (K := K) c₀ p n tseam
    εepidemic εovershoot εpayload hDrift hNoOvershoot nextPre hNextPre).Post
  t := 1 + tseam
  ε := 0 + (εepidemic + εovershoot + εpayload)
  convergence := by
    intro c hreach hPre
    let seed := advanceEntryStepWR (L := L) (K := K) c₀ p n workPre hEntryFromWorkPost
      hExactFromWorkPost
    let seam := advanceEpidemicExactWR (L := L) (K := K) c₀ p n tseam
      εepidemic εovershoot εpayload hDrift hNoOvershoot nextPre hNextPre
    have hcompose := composeWR_two_phases (NonuniformMajority L K) seed seam
      (fun x _hreach hx => by
        exact hx)
      c hreach hPre
    have hts : seed.t + seam.t = 1 + tseam := rfl
    have hes : (seed.ε + seam.ε : ℝ≥0∞) =
        ((0 + (εepidemic + εovershoot + εpayload) : ℝ≥0) : ℝ≥0∞) := by
      push_cast
      rfl
    simpa [seed, seam, hts, hes] using hcompose

@[simp] theorem advanceWithSeedWR_Post
    (c₀ : Config (AgentState L K)) (p n tseam : ℕ)
    (εepidemic εovershoot εpayload : ℝ≥0)
    (hDrift hNoOvershoot nextPre hNextPre workPre hEntryFromWorkPost hExactFromWorkPost)
    (c : Config (AgentState L K)) :
    (advanceWithSeedWR (L := L) (K := K) c₀ p n tseam
      εepidemic εovershoot εpayload hDrift hNoOvershoot nextPre hNextPre
      workPre hEntryFromWorkPost hExactFromWorkPost).Post c
      = ((AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
          AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c) ∧ nextPre c) := rfl

/-- Reachable-scoped terminal assembly. -/
structure TerminalAssemblyR
    (n : ℕ) (c₀ : Config (AgentState L K)) where
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  εepidemic : Fin 10 → ℝ≥0
  εovershoot : Fin 10 → ℝ≥0
  εpayload : Fin 10 → ℝ≥0
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEntryNoOvershoot.AdvancePre (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) (seamP k) n c →
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  hNextPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable c₀ c →
      AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) (seamP k) n c →
      AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) (seamP k) n c →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ (work ⟨k.val + 1, by omega⟩).Pre c'}
        ≤ (εpayload k : ℝ≥0∞)
  hSeamBudget : ∀ k,
      (((εepidemic k + εovershoot k + εpayload k : ℝ≥0) : ℝ≥0∞) ≤
        (1 / (n : ℝ≥0∞) ^ 2))
  hSeamEntryFromWorkPost : ∀ k : Fin 10,
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) (seamP k) n (work ⟨k.val, by omega⟩).Post
  hSeamExactFromWorkPost : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ AdvanceEntryPhaseCeiling.AdvanceEntryExactIfReset (L := L) (K := K) (seamP k) n c'} = 0
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0

/-- The `k`-th reachable shifted seam instance. -/
noncomputable def advanceInstanceR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) (k : Fin 10) :
    PhaseConvergenceWR (NonuniformMajority L K) c₀ :=
  advanceWithSeedWR (L := L) (K := K) c₀ (asm.seamP k) n (asm.seamT k)
    (asm.εepidemic k) (asm.εovershoot k) (asm.εpayload k)
    (asm.hDrift k) (asm.hNoOvershoot k)
    (fun c => (asm.work ⟨k.val + 1, by omega⟩).Pre c)
    (asm.hNextPre k)
    (fun c => (asm.work ⟨k.val, by omega⟩).Post c)
    (asm.hSeamEntryFromWorkPost k)
    (asm.hSeamExactFromWorkPost k)

/-- Every seam instance carries exactly the explicitly budgeted three tail terms. -/
theorem advanceInstanceR_epsilon_le_invSq {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) (k : Fin 10) :
    ((advanceInstanceR asm k).ε : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2) := by
  simpa [advanceInstanceR, advanceWithSeedWR] using asm.hSeamBudget k

/-- The reachable 21-instance family. -/
noncomputable def phasesR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    Fin 21 → PhaseConvergenceWR (NonuniformMajority L K) c₀ :=
  fun i =>
    if h : i.val % 2 = 0 then
      PhaseConvergenceWR.ofW (NonuniformMajority L K) c₀
        (asm.work (ExactAdvanceChain.workIdx i))
    else advanceInstanceR asm (ExactAdvanceChain.advanceIdx i (by omega))

@[simp] theorem phasesR_even {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (i : Fin 21) (h : i.val % 2 = 0) :
    phasesR asm i =
      PhaseConvergenceWR.ofW (NonuniformMajority L K) c₀
        (asm.work (ExactAdvanceChain.workIdx i)) := by
  simp only [phasesR, dif_pos h]

@[simp] theorem phasesR_odd {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (i : Fin 21) (h : i.val % 2 = 1) :
    phasesR asm i = advanceInstanceR asm (ExactAdvanceChain.advanceIdx i h) := by
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
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      AdvanceBudgetSlack.advanceJansonT6 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot :
      TerminalReachableOvershootHypotheses (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (payload :
      TerminalAdvancePayloadHypotheses (L := L) (K := K) c₀ n 10
        (terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
        seamP seamT εovershoot)
    (tie :
      TerminalAdvanceEntryHypotheses (L := L) (K := K) n
        (terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
        seamP) :
    TerminalAssemblyR (L := L) (K := K) n c₀ := by
  let work :=
    terminalWork
      (L := L) (K := K)
      A post ε3 hpost
  exact
    { work := work
      seamP := seamP
      seamT := seamT
      εepidemic := fun _ => advanceHalfBudget n
      εovershoot := εovershoot
      εpayload := payload.εpayload
      hDrift := AdvanceBudgetSlack.advance_hDrift_janson_half
        (L := L) (K := K) n A.hn seamP seamT hTjanson
      hNoOvershoot := hOvershoot.hNoOvershoot
      hNextPre := by
        intro k c hreach hentry hexact
        simpa [work] using payload.hNextPre k c hreach hentry hexact
      hSeamBudget := by
        intro k
        simpa using payload.hBudget k
      hSeamEntryFromWorkPost := by
        intro k
        simpa [work] using hSeamEntryFromWorkPost k
      hSeamExactFromWorkPost := by
        intro k c hpost
        exact AdvanceEntryPhaseCeiling.exactIfReset_measure_zero_of_allPhaseEqOnReset
          (L := L) (K := K) (seamP k) n c (fun hband => tie.hPostEqOnReset k c hpost hband)
      hSeedStep := by
        intro k c hpost
        have h :=
          ExactMajority.SeedStepAndSignThreading.hSeedStep_of_event
            (L := L) (K := K) work seamP tie.hEvent k c hpost
        simpa using h }

theorem terminalWork_phase10_post
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞)) :
    ∀ c,
      ((terminalWork
        (L := L) (K := K)
        A post ε3 hpost)
        ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c := by
  intro c hc
  simpa [terminalWork, WorkBuilder.work10_from_concrete] using hc

/-- Work-to-reachable-seam bridge. -/
theorem workPost_imp_advancePreR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (asm.work ⟨k.val, by omega⟩).Post c) :
    (advanceInstanceR asm k).Pre c := hpost

/-- Reachable seam-to-work bridge. -/
theorem advancePost_imp_workPreR {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (k : Fin 10) (c : Config (AgentState L K))
    (_hreach : (NonuniformMajority L K).Reachable c₀ c)
    (hpost : (advanceInstanceR asm k).Post c) :
    (asm.work ⟨k.val + 1, by omega⟩).Pre c := by
  have hP :
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (asm.seamP k + 1) n c ∧
        AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (asm.seamP k) c) ∧
        (asm.work ⟨k.val + 1, by omega⟩).Pre c := by
    simpa [advanceInstanceR] using hpost
  exact hP.2

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
    set k : Fin 10 := ExactAdvanceChain.advanceIdx ⟨i.val + 1, hi⟩ hsucc1 with hkdef
    have hkw : (⟨k.val, by omega⟩ : Fin 11) = ExactAdvanceChain.workIdx i := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by
        rw [hkdef, ExactAdvanceChain.advanceIdx_val, hjval]; omega
      rw [Fin.val_mk, hkval, ExactAdvanceChain.workIdx_val]
    have hbridge := workPost_imp_advancePreR asm k x
    rw [hkw] at hbridge
    exact hbridge hpost
  · have hi1 : i.val % 2 = 1 := Nat.odd_iff.mp hod
    have hsucc0 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 0 := by rw [hjval]; omega
    rw [phasesR_odd asm i hi1] at hpost
    rw [phasesR_even asm ⟨i.val + 1, hi⟩ hsucc0]
    set k : Fin 10 := ExactAdvanceChain.advanceIdx i hi1 with hkdef
    have hkw : (⟨k.val + 1, by omega⟩ : Fin 11) = ExactAdvanceChain.workIdx ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, ExactAdvanceChain.advanceIdx_val]
      rw [Fin.val_mk, hkval, ExactAdvanceChain.workIdx_val, hjval]
      omega
    have hbridge := advancePost_imp_workPreR asm k x hreach
    rw [hkw] at hbridge
    exact hbridge hpost

/-- Reachable-scoped terminal core used by the de-vacuumed final theorem. -/
structure TerminalReachableWorkAdvanceCore
    (n : ℕ) (c₀ : Config (AgentState L K)) where
  asm : TerminalAssemblyR (L := L) (K := K) n c₀
  hStart : (asm.work ⟨0, by omega⟩).Pre c₀
  hSlot10Post : ∀ c, (asm.work ⟨10, by omega⟩).Post c →
    Phase10Drop.Phase10Post (L := L) (K := K) c
  hValid : validInitial c₀

/-- Wrap the terminal reachable assembly as `TerminalReachableWorkAdvanceCore`. -/
def terminalWorkAdvanceCore
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    (hValid : validInitial c₀)
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      AdvanceBudgetSlack.advanceJansonT6 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot :
      TerminalReachableOvershootHypotheses (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (payload :
      TerminalAdvancePayloadHypotheses (L := L) (K := K) c₀ n 10
        (terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
        seamP seamT εovershoot)
    (tie :
      TerminalAdvanceEntryHypotheses (L := L) (K := K) n
        (terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
        seamP) :
    TerminalReachableWorkAdvanceCore (L := L) (K := K) n c₀ := by
  let asm :=
    terminalAssembly
      (L := L) (K := K)
      c₀ A post ε3 hpost
      seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
  exact
    { asm := asm
      hStart := by
        change RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
        exact FaithfulDeterministicFacts.phase0Initial_of_validInitial
          (L := L) (K := K) n c₀ hValid hcard
      hSlot10Post := by
        intro c hc
        exact
          terminalWork_phase10_post
            (L := L) (K := K)
            A post ε3 hpost c hc
      hValid := hValid }

/-- Chain-restricted final bad-set bound for reachable terminal assemblies. -/
theorem chainRestricted_bad_boundR {n : ℕ} {c₀ : Config (AgentState L K)}
    (core : TerminalReachableWorkAdvanceCore (L := L) (K := K) n c₀)
    (T : ℕ) (hT : T = ∑ i, (phasesR core.asm i).t)
    (Esum : ℝ≥0∞) (hEsum : Esum = ∑ i, ((phasesR core.asm i).ε : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ Esum := by
  have hx₀ : (phasesR core.asm ⟨0, by omega⟩).Pre c₀ := by
    rw [phasesR_even _ _ (by rfl)]
    show (core.asm.work (ExactAdvanceChain.workIdx ⟨0, by omega⟩)).Pre c₀
    rw [show ExactAdvanceChain.workIdx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin 11) from by
      apply Fin.ext; norm_num [ExactAdvanceChain.workIdx]]
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
        show (core.asm.work (ExactAdvanceChain.workIdx ⟨21 - 1, by omega⟩)).Post c
            = (core.asm.work ⟨10, by omega⟩).Post c
        rw [show ExactAdvanceChain.workIdx ⟨21 - 1, by omega⟩ = (⟨10, by omega⟩ : Fin 11) from by
          apply Fin.ext; norm_num [ExactAdvanceChain.workIdx]]
      exact core.hSlot10Post c (heq ▸ hPost)
    exact Or.inr (Or.inr (Or.inr
      (FaithfulCoreChainRestricted.majorityWitness_of_reachable_post core.hValid hreach hP10)))
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

/-- Conditional terminal reduction for the quantitative time bound.

This theorem is not a paper-facing headline: it carries the complete terminal
assembly residuals together with per-phase time and error calibrations.  For
the current concrete work family those calibrations are jointly inconsistent;
see `Theorem31.theorem31_calibration_hypotheses_unsatisfiable`.
The reduction itself remains useful once a sound work/calibration interface is
supplied. -/
theorem time_bound_of_terminal_hypotheses
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
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post :
      Phase3Assembly.Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      AdvanceBudgetSlack.advanceJansonT6 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot :
      TerminalReachableOvershootHypotheses (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (payload :
      TerminalAdvancePayloadHypotheses (L := L) (K := K) c₀ n 10
        (terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
        seamP seamT εovershoot)
    (tie :
      TerminalAdvanceEntryHypotheses (L := L) (K := K) n
        (terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
        seamP)
    (T : ℕ)
    (hT :
      let core :=
        terminalWorkAdvanceCore
          (L := L) (K := K)
          c₀ hcard hValid
          A post ε3 hpost
          seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
      T = ∑ i, (phasesR core.asm i).t)
    (ht :
      let core :=
        terminalWorkAdvanceCore
          (L := L) (K := K)
          c₀ hcard hValid
          A post ε3 hpost
          seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
      ∀ i, (phasesR core.asm i).t
        ≤ NumeralChainBounds.C0_numeral * n * (L + 1))
    (hε :
      let core :=
        terminalWorkAdvanceCore
          (L := L) (K := K)
          c₀ hcard hValid
          A post ε3 hpost
          seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
      ∀ i, ((phasesR core.asm i).ε : ℝ≥0∞)
        ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * NumeralChainBounds.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * NumeralChainBounds.C0_numeral * n * (Nat.clog 2 n + 1) := by
  let core :=
    terminalWorkAdvanceCore
      (L := L) (K := K)
      c₀ hcard hValid
      A post ε3 hpost
      seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
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
  have htime : T ≤ 21 * NumeralChainBounds.C0_numeral * n * (L + 1) := by
    rw [hT]
    refine le_trans (total_time_le_W
      (fun i => (phasesR core.asm i).t)
      (fun _ => NumeralChainBounds.C0_numeral) ht) ?_
    have hsum : (∑ _i : Fin 21, NumeralChainBounds.C0_numeral) = 21 * NumeralChainBounds.C0_numeral := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]
    rw [hsum]
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]
  exact htime

#print axioms phase3WorkFromPostShape
#print axioms terminalWork
#print axioms TerminalAdvanceEntryHypotheses
#print axioms TerminalAdvancePayloadHypotheses
#print axioms terminal_overshoot_half_budget_witness
#print axioms advanceHalfBudget_double_le_invSq
#print axioms advanceHalfBudget_add_overshoot_le_invSq
#print axioms terminal_advance_half_budget_sum_witness
#print axioms terminalReachableOvershoot_advanceBudget
#print axioms advanceEpidemicExactWR
#print axioms advanceWithSeedWR
#print axioms advanceInstanceR_epsilon_le_invSq
#print axioms terminalAssembly
#print axioms terminalWork_phase10_post
#print axioms terminalWorkAdvanceCore
#print axioms chainRestricted_bad_boundR
#print axioms time_bound_of_terminal_hypotheses

end

/-! ## Paper-facing aliases -/


/-- Qualitative exact-majority ExactMajority.stable_majority_correct in the paper's named parameter
regime.  This discharges `L = Nat.clog 2 n` and the sufficiently-large
population condition without adding any residual proof obligation. -/
theorem correctness_paper_regime {n L K : ℕ}
    (hReg : PaperRegime.Regime n L K) :
    Protocol.StablyComputes
      (NonuniformMajority L K)
      (doutPartition L K)
      (validInitialOfSize L K n)
      majorityVerdict := by
  have hlow : 11 ≤ n := by
    have hN : 11 ≤ Params.N₀ := by norm_num [Params.N₀]
    exact hN.trans hReg.hN
  rw [hReg.hLlog]
  exact stable_majority_correct_clog K n hlow

/- No paper-facing quantitative `time_bound` alias is exported.  The current
terminal assembly is a conditional reduction whose concrete calibration is
refuted in `Theorem31Counterexample`. -/

#print axioms correctness_paper_regime

end Theorem31
end Ripple.PopulationProtocol.ExactMajority

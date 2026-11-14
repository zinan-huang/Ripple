import Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePotential
import Ripple.PopulationProtocol.ExactMajority.Probability.ConditionalPhaseProgress
import Ripple.PopulationProtocol.ExactMajority.Probability.ExpectedHittingLadder
import Ripple.PopulationProtocol.ExactMajority.Probability.ReachableLadder
import Ripple.PopulationProtocol.ExactMajority.Probability.Recovery10ToStable
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOnlyWindows
import Ripple.PopulationProtocol.ExactMajority.Probability.MixedWindowClosure
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

namespace Ripple.PopulationProtocol.ExactMajority.UniformRecovery

open MeasureTheory ProbabilityTheory LatePotential
open scoped ENNReal BigOperators NNReal Classical

/-- The time theorem's threshold, reused without unfolding its outer power. -/
def timePopulationThreshold : ℕ := TimeTheorem.timePopulationThreshold

/-- The common input contract in N01 and N19. -/
def GoodInput (n : ℕ) (init : InputCfg n) : Prop :=
  timePopulationThreshold ≤ n ∧ validInitial init ∧ init.card = n

/-- R1's explicit uniform recovery budget, in interactions. -/
def recoveryBudget (n : ℕ) : ℕ :=
  30700 * n ^ 3 * PhaseThreeModel.Numeric.clockHours n

theorem time_population_threshold_ge_model :
    PhaseThreeModel.Numeric.populationThreshold ≤ timePopulationThreshold := by
  exact (TimeTheorem.time_population_bounds
    (n := TimeTheorem.timePopulationThreshold) le_rfl).1

theorem eleven_le_time_population_threshold :
    11 ≤ timePopulationThreshold := by
  exact (by decide : 11 ≤ 40).trans
    (TimeTheorem.time_population_bounds
      (n := TimeTheorem.timePopulationThreshold) le_rfl).2

theorem goodInput_population_lower {n : ℕ} {init : InputCfg n}
    (hinput : GoodInput n init) : 11 ≤ n :=
  eleven_le_time_population_threshold.trans hinput.1

theorem recoveryBudget_pos {n : ℕ} (hn : 0 < n) :
    0 < recoveryBudget n := by
  unfold recoveryBudget PhaseThreeModel.Numeric.clockHours
  positivity

/-- A stopped integer rank pays at most one scheduler denominator per level.
The probability premise is required only at positive levels. In particular,
the impossible demand of a positive drop from level zero is not imposed. -/
theorem expectedHitting_le_of_stopped_rank
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (P : Kernel α α) [IsMarkovKernel P]
    (Inv : α → Prop)
    (hclosed : ConditionalPhaseProgress.Engine.InvClosed P Inv)
    (Done : Set α) (rank : α → ℕ)
    (hzero : ∀ x, Inv x → rank x = 0 → x ∈ Done)
    (hmono : ConditionalPhaseProgress.Engine.PotNonincrOn Inv P rank)
    (N : ℕ) (hN : 0 < N)
    (hdrop : ∀ x, Inv x → 0 < rank x →
      P x {y | rank y < rank x}ᶜ ≤ 1 - (N : ℝ≥0∞)⁻¹)
    (M : ℕ) (c : α) (hc : rank c ≤ M) (hInv : Inv c) :
    expectedHitting P c Done ≤ ((M * N : ℕ) : ℝ≥0∞) := by
  classical
  let q : ℕ → ℝ≥0∞ := fun m =>
    if m = 0 then 1 else 1 - (N : ℝ≥0∞)⁻¹
  have hq : ∀ m, ∀ x, Inv x → rank x = m →
      P x (ConditionalPhaseProgress.Engine.potBelow rank m)ᶜ ≤ q m := by
    intro m x hx hxm
    by_cases hm : m = 0
    · simp only [q, hm, if_pos rfl]
      exact prob_le_one
    · simpa only [q, if_neg hm, ConditionalPhaseProgress.Engine.potBelow, hxm]
        using hdrop x hx (by omega)
  have hprob : (N : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr (by exact_mod_cast (show 1 ≤ N by omega))
  have hcap := ConditionalPhaseProgress.Engine.coupon_expectedHitting_le_uniform_on
    P Inv hclosed rank hmono q hq M c hc hInv (N : ℝ≥0∞)
    (by
      intro m hm _
      simp only [q, if_neg (by omega : m ≠ 0)]
      rw [ENNReal.sub_sub_cancel (by norm_num) hprob, inv_inv])
  have htransfer :
      expectedHitting P c Done ≤
        expectedHitting P c (ConditionalPhaseProgress.Engine.potBelow rank 1) := by
    unfold expectedHitting
    apply ENNReal.tsum_le_tsum
    intro t
    have hsub : Doneᶜ ⊆
        (ConditionalPhaseProgress.Engine.potBelow rank 1)ᶜ ∪ {x | ¬ Inv x} := by
      intro x hx
      by_cases hi : Inv x
      · left
        change ¬ rank x < 1
        intro hr
        exact hx (hzero x hi (by omega))
      · exact Or.inr hi
    calc
      (P ^ t) c Doneᶜ ≤
          (P ^ t) c
            ((ConditionalPhaseProgress.Engine.potBelow rank 1)ᶜ ∪
              {x | ¬ Inv x}) := measure_mono hsub
      _ ≤ (P ^ t) c (ConditionalPhaseProgress.Engine.potBelow rank 1)ᶜ +
          (P ^ t) c {x | ¬ Inv x} := measure_union_le _ _
      _ = (P ^ t) c (ConditionalPhaseProgress.Engine.potBelow rank 1)ᶜ := by
        rw [ConditionalPhaseProgress.Engine.pow_not_inv_eq_zero
          P Inv hclosed c hInv t, add_zero]
  simpa only [Nat.cast_mul] using htransfer.trans hcap

/-- Refining a target only on a closed invariant does not increase
the occupation-time bound from an invariant start. -/
theorem expectedHitting_le_of_target_on_invariant
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (P : Kernel α α) [IsMarkovKernel P] (Inv : α → Prop)
    (hclosed : ConditionalPhaseProgress.Engine.InvClosed P Inv)
    (Mid Done : Set α)
    (hrefine : ∀ x, Inv x → x ∈ Mid → x ∈ Done)
    (c : α) (hc : Inv c) :
    expectedHitting P c Done ≤ expectedHitting P c Mid := by
  unfold expectedHitting
  apply ENNReal.tsum_le_tsum
  intro t
  have hsub : Doneᶜ ⊆ Midᶜ ∪ {x | ¬ Inv x} := by
    intro x hx
    by_cases hi : Inv x
    · exact Or.inl (fun hm => hx (hrefine x hi hm))
    · exact Or.inr hi
  calc
    (P ^ t) c Doneᶜ ≤ (P ^ t) c (Midᶜ ∪ {x | ¬ Inv x}) := measure_mono hsub
    _ ≤ (P ^ t) c Midᶜ + (P ^ t) c {x | ¬ Inv x} := measure_union_le _ _
    _ = (P ^ t) c Midᶜ := by
      rw [ConditionalPhaseProgress.Engine.pow_not_inv_eq_zero
        P Inv hclosed c hc t, add_zero]

variable {L K : ℕ}

/-- The count of a present ordered occurrence pair is positive, also when
the two occurrences have the same state. -/
theorem interactionCount_pos_of_applicable
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) :
    0 < c.interactionCount s t := by
  have hcounts := Multiset.le_iff_count.mp happ
  by_cases heq : s = t
  · subst t
    have hs : 2 ≤ c.count s := by
      simpa [Config.count] using hcounts s
    simp only [Config.interactionCount, if_pos rfl]
    exact Nat.mul_pos (by omega) (by omega)
  · have hs : 1 ≤ c.count s := by
      simpa [Config.count, heq] using hcounts s
    have ht : 1 ≤ c.count t := by
      simpa [Config.count, heq, Ne.symm heq] using hcounts t
    simp only [Config.interactionCount, if_neg heq]
    exact Nat.mul_pos hs ht

/-- A single applicable ordered pair contributes at least one occurrence
pair's mass to any set containing its result. -/
theorem productive_pair_probability_lower
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hcard : c.card = n) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (S : Set (Config (AgentState L K)))
    (hresult : Protocol.stepOrSelf (NonuniformMajority L K) c s t ∈ S) :
    ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ ≤
      (NonuniformMajority L K).transitionKernel c S := by
  classical
  have hc : 2 ≤ c.card := by omega
  have hcount : 1 ≤ c.interactionCount s t :=
    interactionCount_pos_of_applicable c s t happ
  have hprob : (c.totalPairs : ℝ≥0∞)⁻¹ ≤ c.interactionProb s t := by
    unfold Config.interactionProb
    rw [div_eq_mul_inv]
    simpa only [one_mul] using
      mul_le_mul_right'
        (by exact_mod_cast hcount : (1 : ℝ≥0∞) ≤ (c.interactionCount s t : ℝ≥0∞))
        ((c.totalPairs : ℝ≥0∞)⁻¹)
  have hmeasure :
      (NonuniformMajority L K).transitionKernel c S =
        (c.interactionPMF hc).toMeasure
          (Protocol.scheduledStep (NonuniformMajority L K) c ⁻¹' S) := by
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure S = _
    rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
          unfold Protocol.stepDistOrSelf
          rw [dif_pos hc]]
    unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete)
      (DiscreteMeasurableSpace.forall_measurableSet S)]
  have hsub :
      (↑({(s, t)} : Finset (AgentState L K × AgentState L K)) : Set _) ⊆
        Protocol.scheduledStep (NonuniformMajority L K) c ⁻¹' S := by
    intro pair hp
    have hp' : pair = (s, t) := by simpa using hp
    subst pair
    exact hresult
  have hmass :
      (c.interactionPMF hc).toMeasure
        (↑({(s, t)} : Finset (AgentState L K × AgentState L K)) : Set _) =
      c.interactionProb s t := by
    rw [PMF.toMeasure_apply_finset, Finset.sum_singleton]
    rfl
  rw [hmeasure]
  calc
    ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ = (c.totalPairs : ℝ≥0∞)⁻¹ := by
      rw [Config.totalPairs, hcard]
    _ ≤ c.interactionProb s t := hprob
    _ = (c.interactionPMF hc).toMeasure
        (↑({(s, t)} : Finset (AgentState L K × AgentState L K)) : Set _) := hmass.symm
    _ ≤ (c.interactionPMF hc).toMeasure
        (Protocol.scheduledStep (NonuniformMajority L K) c ⁻¹' S) := measure_mono hsub

/-- Closed-window form of the seeded epidemic, without any restriction
on the roles of the agents. -/
theorem seeded_phase_window_closed (p n : ℕ) :
    ConditionalPhaseProgress.Engine.InvClosed
      (NonuniformMajority L K).transitionKernel
      (AdvanceEpidemics.SeededAdvanceWin (L := L) (K := K) p n) := by
  intro c hc
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {d | ¬ AdvanceEpidemics.SeededAdvanceWin p n d} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro d hd hbad
  exact hbad (AdvanceEpidemics.SeededAdvanceWin_absorbing p n c d hc hd)

/-- The threshold epidemic has mean completion time at most n squared,
from arbitrary roles and any phase floor p. -/
theorem seeded_phase_epidemic_expectedHitting_le
    (p n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hc : AdvanceEpidemics.SeededAdvanceWin (L := L) (K := K) p n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
      {d | AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n d} ≤
        ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  let P := (NonuniformMajority L K).transitionKernel
  let Inv := AdvanceEpidemics.SeededAdvanceWin (L := L) (K := K) p n
  let rank := TimedChainRungs.advancePot (L := L) (K := K) p n
  have hclosed : ConditionalPhaseProgress.Engine.InvClosed P Inv :=
    seeded_phase_window_closed p n
  have hmono : ConditionalPhaseProgress.Engine.PotNonincrOn Inv P rank := by
    intro b _
    change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      {d | rank b < rank d} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff _
      (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
    intro d hd hbad
    have hge := AdvanceEpidemics.geCount_ge_monotone
      (L := L) (K := K) (p + 1)
      (AdvanceEpidemics.geCount (L := L) (K := K) (p + 1) b)
      b d le_rfl hd
    change n - AdvanceEpidemics.geCount (p + 1) b <
      n - AdvanceEpidemics.geCount (p + 1) d at hbad
    omega
  have hdrop : ∀ m b, Inv b → rank b = m →
      P b (ConditionalPhaseProgress.Engine.potBelow rank m)ᶜ ≤
        TimedChainRungs.advanceQ n m := by
    intro m b hb hbm
    by_cases hm : m = 0
    · subst hm
      simp only [TimedChainRungs.advanceQ, Nat.mul_zero, Nat.cast_zero,
        zero_div, ENNReal.ofReal_zero, tsub_zero]
      exact prob_le_one (μ := P b)
        (s := (ConditionalPhaseProgress.Engine.potBelow rank 0)ᶜ)
    · have hpos : 1 ≤ m := by omega
      have hcount := TimedChainRungs.geCount_le_card
        (q := p + 1) (n := n) (c := b) hb.1.1
      have hsub := TimedChainRungs.advance_subset_potBelow
        (L := L) (K := K) p n b hb.1.1 m hpos hbm
      have hadv := AdvanceEpidemics.ge_advance_prob
        (L := L) (K := K) p n hn b hb.1
      have hrate := hadv.trans (measure_mono hsub)
      have hdef : n - AdvanceEpidemics.geCount (p + 1) b = m := hbm
      have hge : AdvanceEpidemics.geCount (p + 1) b = n - m := by omega
      rw [MeasureTheory.prob_compl_eq_one_sub
        (ConditionalPhaseProgress.Engine.potBelow_measurable rank m)]
      unfold TimedChainRungs.advanceQ
      apply tsub_le_tsub_left _ 1
      rw [hdef, hge] at hrate
      exact hrate
  have hstart : rank c ≤ n - 1 := by
    have hseed := hc.2
    change n - AdvanceEpidemics.geCount (p + 1) c ≤ n - 1
    omega
  have hcap := ConditionalPhaseProgress.Engine.coupon_expectedHitting_le_uniform_on
    P Inv hclosed rank hmono (TimedChainRungs.advanceQ n) hdrop
    (n - 1) c hstart hc (n : ℝ≥0∞)
    (fun m hm hmn => TimedChainRungs.advanceQ_inv_le n hn m hm hmn)
  have htransfer := expectedHitting_le_of_target_on_invariant P Inv hclosed
    (ConditionalPhaseProgress.Engine.potBelow rank 1)
    {d | AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n d}
    (fun d hd hr =>
      TimedChainRungs.drained_imp_allPhaseGe_succ p n d hd.1.1 hr)
    c hc
  calc
    expectedHitting P c
        {d | AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n d} ≤
        ((n - 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞) := htransfer.trans hcap
    _ ≤ (n : ℝ≥0∞) * (n : ℝ≥0∞) := by
      gcongr
      exact_mod_cast Nat.sub_le n 1
    _ = ((n * n : ℕ) : ℝ≥0∞) := by push_cast; rfl

/-- Scheduler conversion for an actual integer rank: nonincrease on every
pair and one productive applicable pair suffice. All protocol obligations
remain explicit in the two pairwise premises. -/
theorem expectedHitting_le_of_pairwise_rank
    (n : ℕ) (hn : 2 ≤ n)
    (Inv : Config (AgentState L K) → Prop)
    (hclosed : ConditionalPhaseProgress.Engine.InvClosed
      (NonuniformMajority L K).transitionKernel Inv)
    (hcard : ∀ b, Inv b → b.card = n)
    (Done : Set (Config (AgentState L K)))
    (rank : Config (AgentState L K) → ℕ)
    (hzero : ∀ b, Inv b → rank b = 0 → b ∈ Done)
    (hmono : ∀ b, Inv b → ∀ s t,
      rank (Protocol.stepOrSelf (NonuniformMajority L K) b s t) ≤ rank b)
    (hproductive : ∀ b, Inv b → 0 < rank b →
      ∃ s t, Protocol.Applicable b s t ∧
        rank (Protocol.stepOrSelf (NonuniformMajority L K) b s t) < rank b)
    (M : ℕ) (c : Config (AgentState L K)) (hc : Inv c) (hcap : rank c ≤ M) :
    expectedHitting (NonuniformMajority L K).transitionKernel c Done ≤
      ((M * (n * (n - 1)) : ℕ) : ℝ≥0∞) := by
  classical
  have hkernel : ConditionalPhaseProgress.Engine.PotNonincrOn Inv
      (NonuniformMajority L K).transitionKernel rank := by
    intro b hb
    have hsize : 2 ≤ b.card := by rw [hcard b hb]; exact hn
    change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      {d | rank b < rank d} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff _
      (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
    intro d hd hbad
    have hd' : d ∈ ((NonuniformMajority L K).stepDist b hsize).support := by
      simpa only [Protocol.stepDistOrSelf, dif_pos hsize] using hd
    obtain ⟨⟨s, t⟩, hst⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) b hsize d hd'
    have hle := hmono b hb s t
    change rank (Protocol.scheduledStep (NonuniformMajority L K) b (s, t)) ≤
      rank b at hle
    rw [hst] at hle
    exact (not_lt_of_ge hle) hbad
  have hN : 0 < n * (n - 1) :=
    Nat.mul_pos (by omega) (by omega)
  apply expectedHitting_le_of_stopped_rank
    (NonuniformMajority L K).transitionKernel Inv hclosed Done rank
    hzero hkernel (n * (n - 1)) hN ?_ M c hcap hc
  intro b hb hr
  obtain ⟨s, t, happ, hlt⟩ := hproductive b hb hr
  rw [MeasureTheory.prob_compl_eq_one_sub
    (DiscreteMeasurableSpace.forall_measurableSet {d | rank d < rank b})]
  exact tsub_le_tsub_left
    (productive_pair_probability_lower n hn b (hcard b hb) s t happ
      {d | rank d < rank b} hlt) 1

/-! Deterministic producers for Phase 0, the timed phases, and backup. -/

/-- Pairwise fixed means that every scheduler choice leaves the multiset fixed. -/
def PairwiseFixed (c : Config (AgentState L K)) : Prop :=
  ∀ s t, Protocol.stepOrSelf (NonuniformMajority L K) c s t = c

theorem reachable_eq_of_pairwiseFixed
    (c : Config (AgentState L K)) (hfixed : PairwiseFixed c)
    {d : Config (AgentState L K)}
    (hreach : (NonuniformMajority L K).Reachable c d) :
    d = c := by
  induction hreach with
  | refl => rfl
  | @tail b d _ hstep ih =>
      have hstep' : (NonuniformMajority L K).StepRel c d := by
        simpa only [ih] using hstep
      rcases hstep' with ⟨s, t, happ, hd⟩
      dsimp at hd
      calc
        d = Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
          simpa only [Protocol.stepOrSelf, if_pos happ] using hd
        _ = c := hfixed s t

/-- Qualitative endpoint reachability is enough to identify fixed reachable
states.  This does not give a quantitative bound for a nonfixed state. -/
theorem reachable_pairwiseFixed_mem_stableDone
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hlow : 11 ≤ init.card)
    (hsize : init.card ≤ 2 ^ L)
    (hreach : ReachableFrom L K init c)
    (hfixed : PairwiseFixed c) :
    c ∈ StableDone L K init := by
  obtain ⟨d, hcd, hd⟩ :=
    stable_majority_reaches_endpoint L K init hinit hlow hsize c hreach
  have hdc : d = c := reachable_eq_of_pairwiseFixed c hfixed hcd
  change majorityStableEndpoint (L := L) (K := K) init c
  simpa only [hdc] using hd

noncomputable def phaseTenDrainBudget (n : ℕ) : ℝ≥0∞ :=
  3 * (((n ^ 2 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal (1 + 2 * Real.log (n : ℝ)))

/-- Every reachable all-backup configuration has the active source needed by
the existing Phase-10 expected-time theorem, including the tie branch. -/
theorem reachable_allPhaseTen_ready
    (n : ℕ) (hn : 2 ≤ n)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : ReachableFrom L K init c)
    (hcard : c.card = n)
    (hAll : Phase10Drop.AllPhase10 c) :
    Phase10Drop.Phase10Ready (L := L) (K := K) n c := by
  have hactive : hasActiveAgent c :=
    hasActiveAgent_of_reachable_all_phase10
      init c hinit (by simpa only [hcard] using hn) hreach hAll
  exact Phase2EntryDispatcher.phase10Ready_of_allPhase10_card_active
    n c hAll hcard hactive

/-- Uniform backup estimate from any reachable Phase-10 seed.  The root may
contain agents in any earlier phase; no initializer-error provenance and no
ready-state hypothesis are assumed. -/
theorem reachable_phaseTen_seed_expectedHitting_le
    (n : ℕ) (hn : 2 ≤ n)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : ReachableFrom L K init c)
    (hcard : c.card = n)
    (hseed : ∃ a ∈ c, a.phase.val = 10) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
      (StableDone L K init) ≤
        ((n * n : ℕ) : ℝ≥0∞) + phaseTenDrainBudget n := by
  let ker := (NonuniformMajority L K).transitionKernel
  let Bare : Set (Config (AgentState L K)) :=
    ConditionalPhaseProgress.Engine.potBelow
      (Recovery10EntryTime.spreadPot (L := L) (K := K) n) 1
  have hinitcard : init.card = n :=
    (Protocol.reachable_card_eq
      (P := NonuniformMajority L K) hreach).symm.trans hcard
  have hspread : Recovery10EntryTime.SpreadInv
      (L := L) (K := K) n c := by
    refine ⟨hcard, ?_⟩
    rcases hseed with ⟨a, ha, hphase⟩
    unfold AdvanceEpidemics.geCount
    exact Multiset.countP_pos.mpr ⟨a, ha, by
      change 10 ≤ a.phase.val
      omega⟩
  have hbare : expectedHitting ker c Bare ≤ ((n * n : ℕ) : ℝ≥0∞) :=
    Recovery10EntryTime.spread_expectedHitting_le_nsq n hn c hspread
  apply expectedHitting_seqcomp_on_of_uniform ker
    (ReachableFrom L K init) (reachableFrom_kernel_closed init)
    (ConditionalPhaseProgress.Engine.potBelow_measurable _ _)
    (measurableSet_StableDone L K init)
    ((n * n : ℕ) : ℝ≥0∞) (phaseTenDrainBudget n) c hreach hbare
  intro y hyReach hyBare
  have hycard : y.card = n :=
    (Protocol.reachable_card_eq
      (P := NonuniformMajority L K) hyReach).trans hinitcard
  have hydrain : TimedChainRungs.advancePot
      (L := L) (K := K) 9 n y < 1 := by
    change n - AdvanceEpidemics.geCount (L := L) (K := K) 10 y < 1 at hyBare
    exact hyBare
  have hyAll : Phase10Drop.AllPhase10 y :=
    BackupEntry.advancePot_nine_drained_imp_allPhase10 n y hycard hydrain
  have hyReady : Phase10Drop.Phase10Ready (L := L) (K := K) n y :=
    reachable_allPhaseTen_ready n hn init y hinit hyReach hycard hyAll
  exact Recovery10ToStable.phase10Ready_reachable_expectedHitting_stableDone_le
    n hn init y hinit hyReach hyReady

/-- A convenient elementary polynomial envelope for the complete backup cost.
This bound uses only `log n ≤ n-1`; no population threshold is evaluated. -/
theorem phaseTen_seed_budget_le (n : ℕ) (hn : 2 ≤ n) :
    ((n * n : ℕ) : ℝ≥0∞) + phaseTenDrainBudget n ≤
      ((7 * n ^ 3 : ℕ) : ℝ≥0∞) := by
  have hnp : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_le_sub_one_of_pos hnp
  have hreal : 1 + 2 * Real.log (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    push_cast
    linarith
  have hcoef : ENNReal.ofReal (1 + 2 * Real.log (n : ℝ)) ≤
      ((2 * n : ℕ) : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_natCast] using
      (ENNReal.ofReal_le_ofReal hreal)
  have hsq : n * n ≤ n ^ 3 := by
    have hmul := Nat.mul_le_mul_left (n * n) (show 1 ≤ n by omega)
    nlinarith
  calc
    ((n * n : ℕ) : ℝ≥0∞) + phaseTenDrainBudget n
        ≤ ((n * n : ℕ) : ℝ≥0∞) +
          3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ((2 * n : ℕ) : ℝ≥0∞)) := by
            unfold phaseTenDrainBudget
            gcongr
    _ = ((n * n + 6 * n ^ 3 : ℕ) : ℝ≥0∞) := by
      push_cast
      ring
    _ ≤ ((7 * n ^ 3 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (show n * n + 6 * n ^ 3 ≤ 7 * n ^ 3 by omega)

def PurePhase (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = p

def phaseZeroWeight (a : AgentState L K) : ℕ :=
  (50 * (L + 1) + 1) *
      (if a.role = .mcr then 2 else if a.role = .cr then 1 else 0) +
    if a.role = .clock then a.counter.val else 0

def phaseZeroWork (c : Config (AgentState L K)) : ℕ :=
  (c.map (phaseZeroWeight (L := L) (K := K))).sum + 1

theorem phaseZeroWeight_le (a : AgentState L K) :
    phaseZeroWeight a ≤ 2 * (50 * (L + 1) + 1) := by
  have hc := a.counter.isLt
  cases hr : a.role <;> simp [phaseZeroWeight, hr] <;> omega

theorem phaseZeroWork_le (c : Config (AgentState L K)) :
    phaseZeroWork c ≤ 2 * (50 * (L + 1) + 1) * c.card + 1 := by
  have hsum : (c.map (phaseZeroWeight (L := L) (K := K))).sum ≤
      2 * (50 * (L + 1) + 1) * c.card := by
    induction c using Multiset.induction_on with
    | empty => simp
    | cons a c ih =>
        have ha := phaseZeroWeight_le a
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        nlinarith
  exact Nat.add_le_add_right hsum 1

theorem phaseZeroWeight_finish (before after : AgentState L K) :
    phaseZeroWeight (finishPhase10Entry L K before after) =
      phaseZeroWeight after := by
  simp only [phaseZeroWeight, finishPhase10Entry_role,
    finishPhase10Entry_counter]

/-- Every nontrivial pure Phase-0 pair either exits the phase or strictly lowers
the role-and-counter rank.  In particular, no role-count invariant is needed
to obtain a productive pair from qualitative endpoint reachability. -/
theorem phaseZero_pair_exit_fixed_or_drop
    (s t : AgentState L K)
    (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    (0 < (Phase0Transition L K s t).1.phase.val ∨
      0 < (Phase0Transition L K s t).2.phase.val) ∨
    Phase0Transition L K s t = (s, t) ∨
    phaseZeroWeight (Phase0Transition L K s t).1 +
      phaseZeroWeight (Phase0Transition L K s t).2 <
        phaseZeroWeight s + phaseZeroWeight t := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · have ho :
        Phase0Transition L K s t =
          (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
      simp [Phase0Transition, hcc.1, hcc.2]
    rw [ho]
    by_cases hsCounter : s.counter.val = 0
    · left
      left
      have hadv : s.phase.val + 1 ≤ (stdCounterSubroutine L K s).phase.val :=
        stdCounterSubroutine_zero_advances (L := L) (K := K)
          s hsCounter (by omega : s.phase.val < 10)
      exact lt_of_lt_of_le (Nat.succ_pos s.phase.val) hadv
    · by_cases htCounter : t.counter.val = 0
      · left
        right
        have hadv : t.phase.val + 1 ≤ (stdCounterSubroutine L K t).phase.val :=
          stdCounterSubroutine_zero_advances (L := L) (K := K)
            t htCounter (by omega : t.phase.val < 10)
        exact lt_of_lt_of_le (Nat.succ_pos t.phase.val) hadv
      · right
        right
        have hdrop := stdCounterSubroutine_counter_strict_descent
          s t hcc.1 hcc.2 (by omega) (by omega)
        simpa [phaseZeroWeight, hcc.1, hcc.2,
          stdCounterSubroutine_clock_role] using hdrop
  · right
    cases hsRole : s.role <;> cases htRole : t.role <;>
      cases hsAssigned : s.assigned <;> cases htAssigned : t.assigned <;>
      simp_all [Phase0Transition, phaseZeroWeight] <;> omega

theorem transition_phaseZero_exit_fixed_or_drop
    (s t : AgentState L K)
    (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    (0 < (Transition L K s t).1.phase.val ∨
      0 < (Transition L K s t).2.phase.val) ∨
    Transition L K s t = (s, t) ∨
    phaseZeroWeight (Transition L K s t).1 +
      phaseZeroWeight (Transition L K s t).2 <
        phaseZeroWeight s + phaseZeroWeight t := by
  have hsPhase : s.phase = ⟨0, by decide⟩ := Fin.ext hs
  have htPhase : t.phase = ⟨0, by decide⟩ := Fin.ext ht
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hsPhase htPhase
  have hfull : Transition L K s t =
      (finishPhase10Entry L K s (Phase0Transition L K s t).1,
        finishPhase10Entry L K t (Phase0Transition L K s t).2) := by
    unfold Transition
    rw [hepi]
    simp only [hsPhase]
  rcases phaseZero_pair_exit_fixed_or_drop s t hs ht with hexit | hfixed | hdrop
  · left
    simpa only [hfull, finishPhase10Entry_phase_val] using hexit
  · right
    left
    rw [hfull, hfixed]
    simp only [finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) s s (by omega : s.phase.val ≠ 10),
      finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) t t (by omega : t.phase.val ≠ 10)]
  · right
    right
    simpa only [hfull, phaseZeroWeight_finish] using hdrop

theorem phaseZero_step_exit_fixed_or_drop
    (c : Config (AgentState L K)) (hpure : PurePhase 0 c)
    (s t : AgentState L K) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c s t
    ¬ PurePhase 0 c' ∨ c' = c ∨ phaseZeroWork c' < phaseZeroWork c := by
  classical
  dsimp only
  by_cases happ : Protocol.Applicable c s t
  · have hsMem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have htMem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    rcases transition_phaseZero_exit_fixed_or_drop
      s t (hpure s hsMem) (hpure t htMem) with hexit | hfixed | hdrop
    · left
      intro hnew
      rcases hexit with hleft | hright
      · have hout : (Transition L K s t).1 ∈
            Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
          rw [hstep]
          simp
        have hz := hnew _ hout
        omega
      · have hout : (Transition L K s t).2 ∈
            Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
          rw [hstep]
          simp
        have hz := hnew _ hout
        omega
    · right
      left
      rw [hstep, hfixed]
      exact Multiset.sub_add_cancel happ
    · right
      right
      have hsplit := congrArg
        (fun x : Config (AgentState L K) => phaseZeroWork x)
        (Multiset.sub_add_cancel happ)
      rw [hstep]
      simp [phaseZeroWork] at hsplit ⊢
      omega
  · right
    left
    exact Protocol.stepOrSelf_eq_self_of_not_applicable happ

/-- From a reachable nonendpoint in pure Phase 0, some applicable ordered
pair exits Phase 0 or drops the bounded rank. -/
theorem phaseZero_exists_productive_pair
    (init c : Config (AgentState L K))
    (hinit : validInitial init) (hlow : 11 ≤ init.card)
    (hsize : init.card ≤ 2 ^ L)
    (hreach : ReachableFrom L K init c)
    (hpure : PurePhase 0 c)
    (hnot : c ∉ StableDone L K init) :
    ∃ s t, Protocol.Applicable c s t ∧
      let c' := Protocol.stepOrSelf (NonuniformMajority L K) c s t
      (¬ PurePhase 0 c' ∨ phaseZeroWork c' < phaseZeroWork c) := by
  classical
  have hnonfixed : ¬ PairwiseFixed c := by
    intro hfixed
    exact hnot (reachable_pairwiseFixed_mem_stableDone
      init c hinit hlow hsize hreach hfixed)
  change ¬ (∀ s t, Protocol.stepOrSelf (NonuniformMajority L K) c s t = c)
    at hnonfixed
  push_neg at hnonfixed
  obtain ⟨s, t, hchange⟩ := hnonfixed
  have happ : Protocol.Applicable c s t := by
    by_contra hnapp
    exact hchange (Protocol.stepOrSelf_eq_self_of_not_applicable hnapp)
  refine ⟨s, t, happ, ?_⟩
  rcases phaseZero_step_exit_fixed_or_drop c hpure s t with hexit | hsame | hdrop
  · exact Or.inl hexit
  · exact False.elim (hchange hsame)
  · exact Or.inr hdrop

def HasClockPair (c : Config (AgentState L K)) : Prop :=
  ∃ s t, Protocol.Applicable c s t ∧ s.role = .clock ∧ t.role = .clock

theorem phaseZero_nonclock_pair_keeps_phase
    (s t : AgentState L K)
    (hcc : ¬ (s.role = .clock ∧ t.role = .clock)) :
    (Phase0Transition L K s t).1.phase = s.phase ∧
      (Phase0Transition L K s t).2.phase = t.phase := by
  cases hsRole : s.role <;> cases htRole : t.role <;>
    cases hsAssigned : s.assigned <;> cases htAssigned : t.assigned <;>
    simp_all [Phase0Transition]

theorem transition_phaseZero_nonclock_pair_keeps_phase
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0)
    (hcc : ¬ (s.role = .clock ∧ t.role = .clock)) :
    (Transition L K s t).1.phase.val = 0 ∧
      (Transition L K s t).2.phase.val = 0 := by
  have hsPhase : s.phase = ⟨0, by decide⟩ := Fin.ext hs
  have htPhase : t.phase = ⟨0, by decide⟩ := Fin.ext ht
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hsPhase htPhase
  have hlocal := phaseZero_nonclock_pair_keeps_phase s t hcc
  unfold Transition
  rw [hepi]
  simp only [hsPhase, finishPhase10Entry_phase_val]
  exact ⟨by rw [hlocal.1, hs], by rw [hlocal.2, ht]⟩

theorem reachable_clockPair_or_phaseZero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : ReachableFrom L K init c) :
    HasClockPair c ∨ PurePhase 0 c := by
  induction hreach with
  | refl =>
      right
      intro a ha
      exact congrArg Fin.val (hinit a ha).1
  | @tail b d _ hstep ih =>
      rcases ih with hpair | hpure
      · left
        rcases hpair with ⟨s, t, happ, hs, ht⟩
        exact clock_pair_preserved_by_reachable_any
          b d ⟨happ, hs, ht⟩ (Relation.ReflTransGen.single hstep)
      · rcases hstep with ⟨s, t, happ, hd⟩
        have hs : s.phase.val = 0 :=
          hpure s (Multiset.mem_of_le happ (by simp))
        have ht : t.phase.val = 0 :=
          hpure t (Multiset.mem_of_le happ (by simp))
        by_cases hcc : s.role = .clock ∧ t.role = .clock
        · left
          exact clock_pair_preserved_by_reachable_any
            b d ⟨happ, hcc.1, hcc.2⟩
            (Relation.ReflTransGen.single ⟨s, t, happ, hd⟩)
        · right
          have hout := transition_phaseZero_nonclock_pair_keeps_phase
            s t hs ht hcc
          dsimp at hd
          intro a ha
          rw [hd] at ha
          rcases Multiset.mem_add.mp ha with hold | hnew
          · exact hpure a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
          · rcases Multiset.mem_cons.mp hnew with rfl | hsecond
            · exact hout.1
            · rw [Multiset.mem_singleton.mp hsecond]
              exact hout.2

theorem reachable_positive_phase_has_clockPair
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : ReachableFrom L K init c)
    (hc : 0 < c.card) (p : ℕ) (hp : 0 < p)
    (hpure : PurePhase p c) :
    HasClockPair c := by
  rcases reachable_clockPair_or_phaseZero init c hinit hreach with hpair | hzero
  · exact hpair
  · obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hc
    have hfirst := hzero a ha
    have hsecond := hpure a ha
    omega

def timedWork (p : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (ConditionalPhaseProgress.wtAt (L := L) (K := K) p)).sum + 1

theorem timedWork_le (p : ℕ) (c : Config (AgentState L K)) :
    timedWork p c ≤ 50 * (L + 1) * c.card + 1 := by
  have hsum :
      (c.map (ConditionalPhaseProgress.wtAt (L := L) (K := K) p)).sum ≤
        50 * (L + 1) * c.card := by
    induction c using Multiset.induction_on with
    | empty => simp
    | cons a c ih =>
        have ha : ConditionalPhaseProgress.wtAt p a ≤ 50 * (L + 1) := by
          have hcounter := a.counter.isLt
          unfold ConditionalPhaseProgress.wtAt
          split_ifs <;> omega
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        nlinarith
  exact Nat.add_le_add_right hsum 1

theorem timed_transition_left_clock
    (p : ℕ) (hp : p ∈ ({1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p) (hc : s.role = .clock) :
    (Transition L K s t).1 =
      finishPhase10Entry L K s (stdCounterSubroutine L K s) := by
  have hpbound : p < 10 := by fin_cases hp <;> omega
  have hsPhase : s.phase = ⟨p, by omega⟩ := Fin.ext hs
  have htPhase : t.phase = ⟨p, by omega⟩ := Fin.ext ht
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨p, by omega⟩ (by change p ≠ 10; omega) s t hsPhase htPhase
  unfold Transition
  rw [hepi]
  simp only [hsPhase]
  fin_cases hp <;>
    simp [Phase1Transition, Phase5Transition, Phase6Transition,
      Phase7Transition, Phase8Transition, clockCounterStep, hc]

theorem timed_transition_right_clock
    (p : ℕ) (hp : p ∈ ({1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p) (hc : t.role = .clock) :
    (Transition L K s t).2 =
      finishPhase10Entry L K t (stdCounterSubroutine L K t) := by
  have hpbound : p < 10 := by fin_cases hp <;> omega
  have hsPhase : s.phase = ⟨p, by omega⟩ := Fin.ext hs
  have htPhase : t.phase = ⟨p, by omega⟩ := Fin.ext ht
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨p, by omega⟩ (by change p ≠ 10; omega) s t hsPhase htPhase
  unfold Transition
  rw [hepi]
  simp only [hsPhase]
  fin_cases hp <;>
    simp [Phase1Transition, Phase5Transition, Phase6Transition,
      Phase7Transition, Phase8Transition, clockCounterStep, hc]

theorem wtAt_finish (p : ℕ) (before after : AgentState L K) :
    ConditionalPhaseProgress.wtAt p (finishPhase10Entry L K before after) =
      ConditionalPhaseProgress.wtAt p after := by
  simp only [ConditionalPhaseProgress.wtAt, finishPhase10Entry_role,
    finishPhase10Entry_phase_val, finishPhase10Entry_counter]

theorem timed_pair_weights_le
    (p : ℕ) (hp : p ∈ ({1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p) :
    ConditionalPhaseProgress.wtAt p (Transition L K s t).1 ≤
        ConditionalPhaseProgress.wtAt p s ∧
      ConditionalPhaseProgress.wtAt p (Transition L K s t).2 ≤
        ConditionalPhaseProgress.wtAt p t := by
  have hpbound : p < 10 := by fin_cases hp <;> omega
  constructor
  · by_cases hclock : s.role = .clock
    · rw [timed_transition_left_clock p hp s t hs ht hclock, wtAt_finish]
      have hsource : ConditionalPhaseProgress.wtAt p s = s.counter.val := by
        simp [ConditionalPhaseProgress.wtAt, hclock, hs]
      rw [hsource]
      exact ConditionalPhaseProgress.wtAt_std_le p hpbound s hclock hs
    · have hout : (Transition L K s t).1.role ≠ .clock := by
        by_cases hpone : p = 1
        · have hrole := (PhaseOnlyWindows.Transition_role_phase1 s t
            (by omega) (by omega)).1
          simpa only [hrole] using hclock
        · have hpthree : 3 ≤ p := by fin_cases hp <;> omega
          exact MixedWindowClosure.Transition_first_no_clock_creation_of_phase_ge_3
            s t (by omega) (by omega) hclock
      simpa only [ConditionalPhaseProgress.wtAt, hout, hclock, false_and, if_false]
        using (Nat.le_refl 0)
  · by_cases hclock : t.role = .clock
    · rw [timed_transition_right_clock p hp s t hs ht hclock, wtAt_finish]
      have hsource : ConditionalPhaseProgress.wtAt p t = t.counter.val := by
        simp [ConditionalPhaseProgress.wtAt, hclock, ht]
      rw [hsource]
      exact ConditionalPhaseProgress.wtAt_std_le p hpbound t hclock ht
    · have hout : (Transition L K s t).2.role ≠ .clock := by
        by_cases hpone : p = 1
        · have hrole := (PhaseOnlyWindows.Transition_role_phase1 s t
            (by omega) (by omega)).2
          simpa only [hrole] using hclock
        · have hpthree : 3 ≤ p := by fin_cases hp <;> omega
          exact MixedWindowClosure.Transition_second_no_clock_creation_of_phase_ge_3
            s t (by omega) (by omega) hclock
      simpa only [ConditionalPhaseProgress.wtAt, hout, hclock, false_and, if_false]
        using (Nat.le_refl 0)

theorem timedWork_step_le
    (p : ℕ) (hp : p ∈ ({1, 5, 6, 7, 8} : Finset ℕ))
    (c : Config (AgentState L K)) (hpure : PurePhase p c)
    (s t : AgentState L K) :
    timedWork p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      timedWork p c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := timed_pair_weights_le p hp s t (hpure s hs) (hpure t ht)
    have hsplit := congrArg (timedWork (L := L) (K := K) p)
      (Multiset.sub_add_cancel happ)
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    change timedWork p
      (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2}) ≤ _
    simp [timedWork] at hsplit ⊢
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem timed_exists_productive_pair
    (p : ℕ) (hp : p ∈ ({1, 5, 6, 7, 8} : Finset ℕ))
    (c : Config (AgentState L K)) (hpure : PurePhase p c)
    (hclocks : HasClockPair c) :
    ∃ s t, Protocol.Applicable c s t ∧
      let c' := Protocol.stepOrSelf (NonuniformMajority L K) c s t
      (¬ PurePhase p c' ∨ timedWork p c' < timedWork p c) := by
  classical
  obtain ⟨s, t, happ, hsClock, htClock⟩ := hclocks
  have hs : s.phase.val = p := hpure s (Multiset.mem_of_le happ (by simp))
  have ht : t.phase.val = p := hpure t (Multiset.mem_of_le happ (by simp))
  have hpall : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by
    fin_cases hp <;> simp
  refine ⟨s, t, happ, ?_⟩
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  by_cases hzero : s.counter.val = 0 ∨ t.counter.val = 0
  · left
    intro hpost
    have hleft : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hright : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hpLeft := hpost _ hleft
    have hpRight := hpost _ hright
    have hadv := Transition_timed_clock_counter_zero_advances
      p hpall s t hs ht hsClock htClock hzero
    omega
  · right
    have hpair := ConditionalPhaseProgress.transition_pair_wtAt_lt
      p hpall s t hsClock htClock hs ht (by omega)
    have hsplit := congrArg (timedWork (L := L) (K := K) p)
      (Multiset.sub_add_cancel happ)
    rw [hstep]
    simp [timedWork] at hsplit ⊢
    omega

def phaseThreeWeight (a : AgentState L K) : ℕ :=
  if a.role = .clock then K * (L + 1) - a.minute.val + a.counter.val else 0

def phaseThreeWork (c : Config (AgentState L K)) : ℕ :=
  (c.map (phaseThreeWeight (L := L) (K := K))).sum + 1

theorem phaseThreeWeight_le (a : AgentState L K) :
    phaseThreeWeight a ≤ K * (L + 1) + 50 * (L + 1) := by
  have hcounter := a.counter.isLt
  have hsub := Nat.sub_le (K * (L + 1)) a.minute.val
  unfold phaseThreeWeight
  split_ifs <;> omega

theorem phaseThreeWork_le (c : Config (AgentState L K)) :
    phaseThreeWork c ≤
      (K * (L + 1) + 50 * (L + 1)) * c.card + 1 := by
  have hsum : (c.map (phaseThreeWeight (L := L) (K := K))).sum ≤
      (K * (L + 1) + 50 * (L + 1)) * c.card := by
    induction c using Multiset.induction_on with
    | empty => simp
    | cons a c ih =>
        have ha := phaseThreeWeight_le a
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        nlinarith
  exact Nat.add_le_add_right hsum 1

theorem phaseThree_clock_pair_exit_or_drop
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsClock : s.role = .clock) (htClock : t.role = .clock) :
    (3 < (Transition L K s t).1.phase.val ∨
      3 < (Transition L K s t).2.phase.val) ∨
    phaseThreeWeight (Transition L K s t).1 +
      phaseThreeWeight (Transition L K s t).2 <
        phaseThreeWeight s + phaseThreeWeight t := by
  have hsPhase : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have htPhase : t.phase = ⟨3, by decide⟩ := Fin.ext ht
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨3, by decide⟩ (by decide) s t hsPhase htPhase
  by_cases hminute : s.minute = t.minute
  · by_cases hbelow : s.minute.val < K * (L + 1)
    · right
      obtain ⟨_, _, hleftRole, hrightRole, hleftMinute, hrightMinute, _⟩ :=
        Transition_phase3_clock_minute_drip_decreases
          s t hs ht hsClock htClock hminute hbelow
      have hbelowRight : t.minute.val < K * (L + 1) := by
        simpa only [hminute] using hbelow
      have hcounters :
          (Transition L K s t).1.counter = s.counter ∧
          (Transition L K s t).2.counter = t.counter := by
        unfold Transition
        rw [hepi]
        simp [hsPhase, htPhase, Phase3Transition,
          hsClock, htClock, hminute, hbelowRight]
      simp only [phaseThreeWeight, hleftRole, hrightRole, hsClock, htClock,
        if_true, hcounters.1, hcounters.2, hleftMinute, hrightMinute]
      omega
    · by_cases hzero : s.counter.val = 0 ∨ t.counter.val = 0
      · left
        have hexit := Transition_phase3_clock_done_counter_zero_advances
          s t hs ht hsClock htClock hminute hbelow hzero
        omega
      · right
        obtain ⟨_, _, hleftRole, hrightRole, hminutes, hdone, hcounter⟩ :=
          Transition_phase3_clock_done_positive_preserves_and_decreases
            s t hs ht hsClock htClock hminute hbelow (by omega) (by omega)
        have hsTop : s.minute.val = K * (L + 1) := by
          have h := s.minute.isLt
          omega
        have htTop : t.minute.val = K * (L + 1) := by
          rw [← hminute]
          exact hsTop
        have hleftTop : (Transition L K s t).1.minute.val = K * (L + 1) := by
          have h := (Transition L K s t).1.minute.isLt
          omega
        have hrightTop : (Transition L K s t).2.minute.val = K * (L + 1) := by
          rw [← hminutes]
          exact hleftTop
        simpa only [phaseThreeWeight, hleftRole, hrightRole,
          hsClock, htClock, if_true, hsTop, htTop, hleftTop, hrightTop,
          Nat.sub_self, Nat.zero_add] using hcounter
  · right
    obtain ⟨_, _, hleftRole, hrightRole, hleftMinute, hrightMinute, _⟩ :=
      Transition_phase3_clock_minute_sync_decreases
        s t hs ht hsClock htClock hminute
    have hcounters :
        (Transition L K s t).1.counter = s.counter ∧
        (Transition L K s t).2.counter = t.counter := by
      unfold Transition
      rw [hepi]
      simp [hsPhase, htPhase, Phase3Transition, hsClock, htClock, hminute]
    have hsMaxFin : s.minute ≤ max s.minute t.minute := le_max_left _ _
    have htMaxFin : t.minute ≤ max s.minute t.minute := le_max_right _ _
    have hsMax : s.minute.val ≤ (max s.minute t.minute).val := hsMaxFin
    have htMax : t.minute.val ≤ (max s.minute t.minute).val := htMaxFin
    have hmaxBound := (max s.minute t.minute).isLt
    have hsBound := s.minute.isLt
    have htBound := t.minute.isLt
    have hne : s.minute.val ≠ t.minute.val := by
      intro h
      exact hminute (Fin.ext h)
    simp only [phaseThreeWeight, hleftRole, hrightRole, hsClock, htClock,
      if_true, hcounters.1, hcounters.2, hleftMinute, hrightMinute]
    omega

theorem phaseThree_nonclock_pair_weights
    (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hcc : ¬ (s.role = .clock ∧ t.role = .clock)) :
    phaseThreeWeight (Transition L K s t).1 = phaseThreeWeight s ∧
      phaseThreeWeight (Transition L K s t).2 = phaseThreeWeight t := by
  have hsPhase : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have htPhase : t.phase = ⟨3, by decide⟩ := Fin.ext ht
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨3, by decide⟩ (by decide) s t hsPhase htPhase
  constructor
  · by_cases hsClock : s.role = .clock
    · have htNot : t.role ≠ .clock := by tauto
      have hleft : (Transition L K s t).1 = s := by
        unfold Transition
        rw [hepi]
        simp [hsPhase, htPhase, Phase3Transition, hsClock, htNot]
      rw [hleft]
    · have hout := MixedWindowClosure.Transition_first_no_clock_creation_of_phase_ge_3
        s t (by omega) (by omega) hsClock
      simp [phaseThreeWeight, hout, hsClock]
  · by_cases htClock : t.role = .clock
    · have hsNot : s.role ≠ .clock := by tauto
      have hright : (Transition L K s t).2 = t := by
        unfold Transition
        rw [hepi]
        simp [hsPhase, htPhase, Phase3Transition, htClock, hsNot]
      rw [hright]
    · have hout := MixedWindowClosure.Transition_second_no_clock_creation_of_phase_ge_3
        s t (by omega) (by omega) htClock
      simp [phaseThreeWeight, hout, htClock]

theorem phaseThreeWork_step_le_of_stays
    (c : Config (AgentState L K)) (hpure : PurePhase 3 c)
    (s t : AgentState L K)
    (hpost : PurePhase 3 (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    phaseThreeWork (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      phaseThreeWork c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s.phase.val = 3 := hpure s (Multiset.mem_of_le happ (by simp))
    have ht : t.phase.val = 3 := hpure t (Multiset.mem_of_le happ (by simp))
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hleft : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hright : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hpair :
        phaseThreeWeight (Transition L K s t).1 +
          phaseThreeWeight (Transition L K s t).2 ≤
            phaseThreeWeight s + phaseThreeWeight t := by
      by_cases hcc : s.role = .clock ∧ t.role = .clock
      · rcases phaseThree_clock_pair_exit_or_drop
          s t hs ht hcc.1 hcc.2 with hexit | hdrop
        · have hleftPhase := hpost _ hleft
          have hrightPhase := hpost _ hright
          omega
        · exact hdrop.le
      · obtain ⟨hfirst, hsecond⟩ := phaseThree_nonclock_pair_weights s t hs ht hcc
        rw [hfirst, hsecond]
    have hsplit := congrArg (phaseThreeWork (L := L) (K := K))
      (Multiset.sub_add_cancel happ)
    rw [hstep]
    simp [phaseThreeWork] at hsplit ⊢
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem phaseThree_exists_productive_pair
    (c : Config (AgentState L K)) (hpure : PurePhase 3 c)
    (hclocks : HasClockPair c) :
    ∃ s t, Protocol.Applicable c s t ∧
      let c' := Protocol.stepOrSelf (NonuniformMajority L K) c s t
      (¬ PurePhase 3 c' ∨ phaseThreeWork c' < phaseThreeWork c) := by
  classical
  obtain ⟨s, t, happ, hsClock, htClock⟩ := hclocks
  have hs : s.phase.val = 3 := hpure s (Multiset.mem_of_le happ (by simp))
  have ht : t.phase.val = 3 := hpure t (Multiset.mem_of_le happ (by simp))
  refine ⟨s, t, happ, ?_⟩
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  rcases phaseThree_clock_pair_exit_or_drop
      s t hs ht hsClock htClock with hexit | hdrop
  · left
    intro hpost
    have hleft : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hright : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hleftPhase := hpost _ hleft
    have hrightPhase := hpost _ hright
    omega
  · right
    have hsplit := congrArg (phaseThreeWork (L := L) (K := K))
      (Multiset.sub_add_cancel happ)
    rw [hstep]
    simp [phaseThreeWork] at hsplit ⊢
    omega

def phaseFourGuard (a : AgentState L K) : Bool :=
  match a.bias with
  | .zero => false
  | .dyadic _ i => if i.val < L then true else false

theorem phaseFourGuard_eq_false (a : AgentState L K) :
    phaseFourGuard a = false ↔ ¬ phase4HasBigBias (L := L) (K := K) a := by
  cases hb : a.bias <;> simp [phaseFourGuard, phase4HasBigBias, hb]

theorem phaseFour_pair_fixed_or_exit
    (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    Transition L K s t = (s, t) ∨
      4 < (Transition L K s t).1.phase.val := by
  by_cases hbig : phase4HasBigBias (L := L) (K := K) s ∨
      phase4HasBigBias (L := L) (K := K) t
  · right
    have h := Transition_phase4_advances_of_big_bias s t hs ht hbig
    omega
  · left
    have hsGuard : phaseFourGuard s = false :=
      (phaseFourGuard_eq_false s).mpr (by tauto)
    have htGuard : phaseFourGuard t = false :=
      (phaseFourGuard_eq_false t).mpr (by tauto)
    have hlocal : Phase4Transition L K s t = (s, t) := by
      change
        (if phaseFourGuard s || phaseFourGuard t then
          (advancePhaseWithInit L K s, advancePhaseWithInit L K t)
        else (s, t)) = (s, t)
      rw [hsGuard, htGuard]
      rfl
    have hsPhase : s.phase = ⟨4, by decide⟩ := Fin.ext hs
    have htPhase : t.phase = ⟨4, by decide⟩ := Fin.ext ht
    have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
      (L := L) (K := K) ⟨4, by decide⟩ (by decide) s t hsPhase htPhase
    unfold Transition
    rw [hepi]
    simp only [hsPhase]
    rw [hlocal]
    simp [hs, ht]

theorem phaseFour_exists_exit_pair
    (init c : Config (AgentState L K))
    (hinit : validInitial init) (hlow : 11 ≤ init.card)
    (hsize : init.card ≤ 2 ^ L)
    (hreach : ReachableFrom L K init c)
    (hpure : PurePhase 4 c)
    (hnot : c ∉ StableDone L K init) :
    ∃ s t, Protocol.Applicable c s t ∧
      ¬ PurePhase 4 (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hnonfixed : ¬ PairwiseFixed c := by
    intro hfixed
    exact hnot (reachable_pairwiseFixed_mem_stableDone
      init c hinit hlow hsize hreach hfixed)
  change ¬ (∀ s t, Protocol.stepOrSelf (NonuniformMajority L K) c s t = c)
    at hnonfixed
  push_neg at hnonfixed
  obtain ⟨s, t, hchange⟩ := hnonfixed
  have happ : Protocol.Applicable c s t := by
    by_contra hnapp
    exact hchange (Protocol.stepOrSelf_eq_self_of_not_applicable hnapp)
  have hs : s.phase.val = 4 := hpure s (Multiset.mem_of_le happ (by simp))
  have ht : t.phase.val = 4 := hpure t (Multiset.mem_of_le happ (by simp))
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨s, t, happ, ?_⟩
  rcases phaseFour_pair_fixed_or_exit s t hs ht with hfixed | hexit
  · apply False.elim
    apply hchange
    rw [hstep, hfixed]
    exact Multiset.sub_add_cancel happ
  · intro hpost
    have hmem : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hphase := hpost _ hmem
    omega

attribute [local instance] Classical.propDecidable

/-! Concrete work rank for homogeneous phases two and nine.
This contribution uses PurePhase and PairwiseFixed from the common recovery
part. Every opinion mask is a Fin 8, so the finite arithmetic below never
evaluates a population threshold. -/

def opinionDefect (u : Fin 8) : ℕ :=
  match u.val with
  | 0 => 3
  | 1 | 2 | 4 => 2
  | 3 | 5 | 6 => 1
  | _ => 0

theorem opinionDefect_le_three (u : Fin 8) : opinionDefect u ≤ 3 := by
  fin_cases u <;> decide

theorem opinionDefect_union_le (u v : Fin 8) :
    opinionDefect (opinionsUnion u v) + opinionDefect (opinionsUnion u v) ≤
      opinionDefect u + opinionDefect v := by
  fin_cases u <;> fin_cases v <;> decide

theorem opinionDefect_union_lt (u v : Fin 8) :
    u ≠ v →
      opinionDefect (opinionsUnion u v) + opinionDefect (opinionsUnion u v) <
        opinionDefect u + opinionDefect v := by
  fin_cases u <;> fin_cases v <;> decide

theorem opinionsUnion_self (u : Fin 8) : opinionsUnion u u = u := by
  fin_cases u <;> decide

def opinionRank (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => opinionDefect a.opinions)).sum

theorem opinionRank_le_three_card (c : Config (AgentState L K)) :
    opinionRank c ≤ 3 * c.card := by
  induction c using Multiset.induction_on with
  | empty => simp [opinionRank]
  | cons a c ih =>
    have ha := opinionDefect_le_three a.opinions
    simp only [opinionRank, Multiset.map_cons, Multiset.sum_cons,
      Multiset.card_cons] at ih ⊢
    omega

def UniformOpinions (c : Config (AgentState L K)) : Prop :=
  ∃ u : Fin 8, ∀ a ∈ c, a.opinions = u

theorem applicable_of_members_ne
    {c : Config (AgentState L K)} {s t : AgentState L K}
    (hs : s ∈ c) (ht : t ∈ c) (hne : s ≠ t) :
    Protocol.Applicable c s t := by
  classical
  rw [Protocol.Applicable, Multiset.le_iff_count]
  intro x
  by_cases hxs : x = s
  · subst x
    have hpos : 0 < Multiset.count s c := Multiset.count_pos.mpr hs
    simp [hne, Nat.succ_le_iff, hpos]
  · by_cases hxt : x = t
    · subst x
      have hpos : 0 < Multiset.count t c := Multiset.count_pos.mpr ht
      simp [hxs, Nat.succ_le_iff, hpos]
    · simp [hxs, hxt]

theorem exists_applicable_unequal_opinions
    (c : Config (AgentState L K)) (h : ¬ UniformOpinions c) :
    ∃ s t, Protocol.Applicable c s t ∧ s.opinions ≠ t.opinions := by
  classical
  have hc : 0 < c.card := by
    by_contra hcard
    have hz : c = 0 := Multiset.card_eq_zero.mp (by omega)
    apply h
    rw [hz]
    exact ⟨0, by simp⟩
  obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hc
  have hex : ∃ t ∈ c, t.opinions ≠ s.opinions := by
    by_contra hnone
    push_neg at hnone
    exact h ⟨s.opinions, hnone⟩
  obtain ⟨t, ht, hne⟩ := hex
  refine ⟨t, s, applicable_of_members_ne ht hs ?_, hne⟩
  intro heq
  exact hne (congrArg AgentState.opinions heq)

theorem opinionRank_pair_replace_le
    (c : Config (AgentState L K)) (s t s' t' : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hle : opinionDefect s'.opinions + opinionDefect t'.opinions ≤
      opinionDefect s.opinions + opinionDefect t.opinions) :
    opinionRank (c - {s, t} + {s', t'}) ≤ opinionRank c := by
  have hsplit := congrArg (opinionRank (L := L) (K := K))
    (Multiset.sub_add_cancel happ)
  simp [opinionRank] at hsplit ⊢
  omega

theorem opinionRank_pair_replace_lt
    (c : Config (AgentState L K)) (s t s' t' : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hlt : opinionDefect s'.opinions + opinionDefect t'.opinions <
      opinionDefect s.opinions + opinionDefect t.opinions) :
    opinionRank (c - {s, t} + {s', t'}) < opinionRank c := by
  have hsplit := congrArg (opinionRank (L := L) (K := K))
    (Multiset.sub_add_cancel happ)
  simp [opinionRank] at hsplit ⊢
  omega

theorem same_phase_epidemic (ph : Fin 11) (hph : ph.val ≠ 10)
    (s t : AgentState L K) (hs : s.phase = ph) (ht : t.phase = ph) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  exact ConditionalPhaseProgress.epidemic_inert_same_phase ph hph s t hs ht

theorem opinion_transition_no_conflict
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p)
    (hguard :
      (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
        hasPlusOne (opinionsUnion s.opinions t.opinions)) = false) :
    Transition L K s t = Phase2Transition L K s t := by
  let ph : Fin 11 := ⟨p, by rcases hp with rfl | rfl <;> omega⟩
  have hph : ph.val ≠ 10 := by
    change p ≠ 10
    omega
  have hepi := same_phase_epidemic (L := L) (K := K) ph hph s t
    (Fin.ext hs) (Fin.ext ht)
  have hlocal :
      (Phase2Transition L K s t).1.phase = s.phase ∧
        (Phase2Transition L K s t).2.phase = t.phase := by
    unfold Phase2Transition
    rw [if_neg (by simp [hguard])]
    split_ifs <;> simp
  have hsne : (Phase2Transition L K s t).1.phase.val ≠ 10 := by
    rw [hlocal.1, hs]
    omega
  have htne : (Phase2Transition L K s t).2.phase.val ≠ 10 := by
    rw [hlocal.2, ht]
    omega
  have hsfin := finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) s (Phase2Transition L K s t).1 hsne
  have htfin := finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) t (Phase2Transition L K s t).2 htne
  have hdispatch : Transition L K s t =
      (finishPhase10Entry L K s (Phase2Transition L K s t).1,
        finishPhase10Entry L K t (Phase2Transition L K s t).2) := by
    unfold Transition
    rw [hepi]
    rcases hp with hp | hp
    · have hsph : s.phase = ⟨2, by decide⟩ := Fin.ext (hs.trans hp)
      simp only [hsph]
    · have hsph : s.phase = ⟨9, by decide⟩ := Fin.ext (hs.trans hp)
      simp only [hsph, Phase9Transition]
  rw [hdispatch, hsfin, htfin]

theorem opinion_transition_union_or_exit
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p) :
    ((Transition L K s t).1.opinions = opinionsUnion s.opinions t.opinions ∧
      (Transition L K s t).2.opinions = opinionsUnion s.opinions t.opinions ∧
      (Transition L K s t).1.phase.val = p ∧
      (Transition L K s t).2.phase.val = p) ∨
    (p < (Transition L K s t).1.phase.val ∧
      p < (Transition L K s t).2.phase.val) := by
  by_cases hconf : hasMinusOne (opinionsUnion s.opinions t.opinions) = true ∧
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true
  · right
    rcases hp with rfl | rfl
    · have h := Transition_phase2_advances_of_union_has_opposite_signs
        (L := L) (K := K) s t hs ht hconf.1 hconf.2
      exact ⟨by omega, by omega⟩
    · have h := Transition_phase9_advances_of_union_has_opposite_signs
        (L := L) (K := K) s t hs ht hconf.1 hconf.2
      exact ⟨by omega, by omega⟩
  · left
    have hguard :
        (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
          hasPlusOne (opinionsUnion s.opinions t.opinions)) = false := by
      cases hm : hasMinusOne (opinionsUnion s.opinions t.opinions) <;>
        cases hp' : hasPlusOne (opinionsUnion s.opinions t.opinions) <;>
        simp_all
    rw [opinion_transition_no_conflict p hp s t hs ht hguard]
    unfold Phase2Transition
    rw [if_neg (by simp [hguard])]
    split_ifs <;> simp_all

theorem opinionRank_pos_of_not_uniform
    (c : Config (AgentState L K)) (h : ¬ UniformOpinions c) :
    0 < opinionRank c := by
  obtain ⟨s, t, happ, hne⟩ := exists_applicable_unequal_opinions c h
  have hlt := opinionDefect_union_lt s.opinions t.opinions hne
  have hsplit := congrArg (opinionRank (L := L) (K := K))
    (Multiset.sub_add_cancel happ)
  simp [opinionRank] at hsplit ⊢
  omega

theorem opinionRank_step_le_of_pure
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (s t : AgentState L K)
    (hpost : PurePhase p
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    opinionRank (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      opinionRank c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsout : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    rcases opinion_transition_union_or_exit p hp s t (hc s hs) (hc t ht)
      with hkeep | hexit
    · rw [hstep]
      apply opinionRank_pair_replace_le c s t _ _ happ
      rw [hkeep.1, hkeep.2.1]
      exact opinionDefect_union_le _ _
    · have hphase := hpost _ hsout
      omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem opinionRank_step_lt_of_pure
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hne : s.opinions ≠ t.opinions)
    (hpost : PurePhase p
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    opinionRank (Protocol.stepOrSelf (NonuniformMajority L K) c s t) <
      opinionRank c := by
  have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsout : (Transition L K s t).1 ∈
      Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
    rw [hstep]
    simp
  rcases opinion_transition_union_or_exit p hp s t (hc s hs) (hc t ht)
    with hkeep | hexit
  · rw [hstep]
    apply opinionRank_pair_replace_lt c s t _ _ happ
    rw [hkeep.1, hkeep.2.1]
    exact opinionDefect_union_lt _ _ hne
  · have hphase := hpost _ hsout
    omega

def opinionVerdict (u : Fin 8) : Output :=
  match u.val with
  | 1 | 3 => .B
  | 4 | 6 => .A
  | _ => .T

theorem opinion_cleanup_pair
    (p : ℕ) (hp : p = 2 ∨ p = 9) (u : Fin 8)
    (hne : u.val ≠ 0)
    (hguard : (hasMinusOne u && hasPlusOne u) = false)
    (s t : AgentState L K)
    (hs : s.phase.val = p) (ht : t.phase.val = p)
    (hso : s.opinions = u) (hto : t.opinions = u) :
    Transition L K s t =
      ({s with output := opinionVerdict u},
        {t with output := opinionVerdict u}) := by
  have hguard' :
      (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
        hasPlusOne (opinionsUnion s.opinions t.opinions)) = false := by
    simpa [hso, hto, opinionsUnion_self] using hguard
  rw [opinion_transition_no_conflict p hp s t hs ht hguard']
  rcases s with ⟨si, so, sp, sr, sa, sb, ssb, sh, sm, sf, sop, sc⟩
  rcases t with ⟨ti, tout, tp, tr, ta, tb, tsb, th, tm, tf, top, tc⟩
  fin_cases u <;>
    simp_all [Phase2Transition, opinionsUnion, hasMinusOne, hasPlusOne,
      opinionVerdict]

noncomputable def outputRank (out : Output)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.output ≠ out) c

theorem outputRank_le_card (out : Output)
    (c : Config (AgentState L K)) : outputRank out c ≤ c.card := by
  classical
  exact Multiset.countP_le_card _ _

theorem outputRank_eq_zero_iff (out : Output)
    (c : Config (AgentState L K)) :
    outputRank out c = 0 ↔ ∀ a ∈ c, a.output = out := by
  classical
  simp [outputRank, Multiset.countP_eq_zero]

theorem outputRank_step_accounting
    (out : Output) (c : Config (AgentState L K))
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsout : (Transition L K s t).1.output = out)
    (htout : (Transition L K s t).2.output = out) :
    outputRank out (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
      (if s.output = out then 0 else 1) +
      (if t.output = out then 0 else 1) = outputRank out c := by
  classical
  have hsingle (a : AgentState L K) :
      Multiset.countP (fun x : AgentState L K => x.output ≠ out)
        ({a} : Multiset (AgentState L K)) =
          if a.output = out then 0 else 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ out)
      (a ::ₘ (0 : Multiset (AgentState L K))) = _
    rw [Multiset.countP_cons, Multiset.countP_zero, zero_add]
    by_cases ha : a.output = out <;> simp [ha]
  have hsplit := congrArg (outputRank (L := L) (K := K) out)
    (Multiset.sub_add_cancel happ)
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  by_cases hs : s.output = out <;> by_cases ht : t.output = out <;>
    simp [outputRank, hstep, hsingle, hsout, htout, hs, ht] at hsplit ⊢ <;> omega

theorem opinion_cleanup_outputRank_le
    (p : ℕ) (hp : p = 2 ∨ p = 9) (u : Fin 8)
    (hne : u.val ≠ 0)
    (hguard : (hasMinusOne u && hasPlusOne u) = false)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hu : ∀ a ∈ c, a.opinions = u) (s t : AgentState L K) :
    outputRank (opinionVerdict u)
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      outputRank (opinionVerdict u) c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := opinion_cleanup_pair p hp u hne hguard s t
      (hc s hs) (hc t ht) (hu s hs) (hu t ht)
    have hacc := outputRank_step_accounting (opinionVerdict u) c s t happ
      (by rw [hpair]) (by rw [hpair])
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem applicable_partner_of_mem
    {c : Config (AgentState L K)} {a : AgentState L K}
    (ha : a ∈ c) (hcard : 2 ≤ c.card) :
    ∃ b, Protocol.Applicable c a b := by
  have herase_pos : 0 < (c.erase a).card := by
    have hcard_erase := Multiset.card_erase_add_one ha
    omega
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp herase_pos
  refine ⟨b, ?_⟩
  change a ::ₘ ({b} : Multiset (AgentState L K)) ≤ c
  rw [← Multiset.cons_erase ha]
  exact Multiset.cons_le_cons a (Multiset.singleton_le.mpr hb)

theorem opinion_cleanup_exists_drop
    (p : ℕ) (hp : p = 2 ∨ p = 9) (u : Fin 8)
    (hne : u.val ≠ 0)
    (hguard : (hasMinusOne u && hasPlusOne u) = false)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hu : ∀ a ∈ c, a.opinions = u) (hn : 2 ≤ c.card)
    (hbad : outputRank (opinionVerdict u) c ≠ 0) :
    ∃ s t, Protocol.Applicable c s t ∧
      outputRank (opinionVerdict u)
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) <
        outputRank (opinionVerdict u) c := by
  classical
  have hpos : 0 < outputRank (opinionVerdict u) c := Nat.pos_of_ne_zero hbad
  change 0 < Multiset.countP
    (fun a : AgentState L K => a.output ≠ opinionVerdict u) c at hpos
  obtain ⟨s, hs, hwrong⟩ := Multiset.countP_pos.mp hpos
  obtain ⟨t, happ⟩ := applicable_partner_of_mem hs hn
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := opinion_cleanup_pair p hp u hne hguard s t
    (hc s hs) (hc t ht) (hu s hs) (hu t ht)
  have hacc := outputRank_step_accounting (opinionVerdict u) c s t happ
    (by rw [hpair]) (by rw [hpair])
  refine ⟨s, t, happ, ?_⟩
  simp only [if_neg hwrong] at hacc
  omega

theorem opinion_cleanup_preserves
    (p : ℕ) (hp : p = 2 ∨ p = 9) (u : Fin 8)
    (hne : u.val ≠ 0)
    (hguard : (hasMinusOne u && hasPlusOne u) = false)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hu : ∀ a ∈ c, a.opinions = u) (s t : AgentState L K) :
    PurePhase p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ∧
      ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
        a.opinions = u := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := opinion_cleanup_pair p hp u hne hguard s t
      (hc s hs) (hc t ht) (hu s hs) (hu t ht)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hinv : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
        a.phase.val = p ∧ a.opinions = u := by
      intro a ha
      rw [hstep] at ha
      have ha' : a = (Transition L K s t).1 ∨
          a ∈ c - {s, t} ∨ a = (Transition L K s t).2 := by
        rcases Multiset.mem_add.mp ha with hold | hnew
        · exact Or.inr (Or.inl hold)
        · rcases Multiset.mem_cons.mp hnew with hfirst | hsecond
          · exact Or.inl hfirst
          · exact Or.inr (Or.inr (Multiset.mem_singleton.mp hsecond))
      rcases ha' with hfirst | hold | hsecond
      · rw [hfirst, hpair]
        exact ⟨hc s hs, hu s hs⟩
      · have hamem := Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold
        exact ⟨hc a hamem, hu a hamem⟩
      · rw [hsecond, hpair]
        exact ⟨hc t ht, hu t ht⟩
    exact ⟨fun a ha => (hinv a ha).1, fun a ha => (hinv a ha).2⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact ⟨hc, hu⟩

theorem opinion_zero_pairwiseFixed
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hu : ∀ a ∈ c, a.opinions = (0 : Fin 8)) :
    PairwiseFixed c := by
  classical
  intro s t
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hso := hu s hs
    have hto := hu t ht
    have hguard :
        (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
          hasPlusOne (opinionsUnion s.opinions t.opinions)) = false := by
      simp [hso, hto, opinionsUnion, hasMinusOne, hasPlusOne]
    have hlocal : Phase2Transition L K s t = (s, t) := by
      rcases s with ⟨si, so, sp, sr, sa, sb, ssb, sh, sm, sf, sop, sc⟩
      rcases t with ⟨ti, tout, tp, tr, ta, tb, tsb, th, tm, tf, top, tc⟩
      simp_all [Phase2Transition, opinionsUnion, hasMinusOne, hasPlusOne]
    have htrans : Transition L K s t = (s, t) :=
      (opinion_transition_no_conflict p hp s t (hc s hs) (hc t ht) hguard).trans hlocal
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    change c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} = c
    rw [htrans]
    exact Multiset.sub_add_cancel happ
  · exact Protocol.stepOrSelf_eq_self_of_not_applicable happ

theorem opinion_cleanup_pairwiseFixed
    (p : ℕ) (hp : p = 2 ∨ p = 9) (u : Fin 8)
    (hne : u.val ≠ 0)
    (hguard : (hasMinusOne u && hasPlusOne u) = false)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hu : ∀ a ∈ c, a.opinions = u)
    (hout : ∀ a ∈ c, a.output = opinionVerdict u) :
    PairwiseFixed c := by
  classical
  intro s t
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := opinion_cleanup_pair p hp u hne hguard s t
      (hc s hs) (hc t ht) (hu s hs) (hu t ht)
    have hsfix : ({s with output := opinionVerdict u} : AgentState L K) = s := by
      rw [← hout s hs]
    have htfix : ({t with output := opinionVerdict u} : AgentState L K) = t := by
      rw [← hout t ht]
    have htrans : Transition L K s t = (s, t) := by
      rw [hpair, hsfix, htfix]
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    change c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} = c
    rw [htrans]
    exact Multiset.sub_add_cancel happ
  · exact Protocol.stepOrSelf_eq_self_of_not_applicable happ

theorem uniform_conflict_pair_advances
    (p : ℕ) (hp : p = 2 ∨ p = 9) (u : Fin 8)
    (hminus : hasMinusOne u = true) (hplus : hasPlusOne u = true)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hu : ∀ a ∈ c, a.opinions = u)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    ∃ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      p < a.phase.val := by
  have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hm : hasMinusOne (opinionsUnion s.opinions t.opinions) = true := by
    simpa [hu s hs, hu t ht, opinionsUnion_self] using hminus
  have hpl : hasPlusOne (opinionsUnion s.opinions t.opinions) = true := by
    simpa [hu s hs, hu t ht, opinionsUnion_self] using hplus
  refine ⟨(Transition L K s t).1, ?_, ?_⟩
  · unfold Protocol.stepOrSelf
    rw [if_pos happ]
    change (Transition L K s t).1 ∈
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2}
    simp
  · rcases hp with rfl | rfl
    · have h := Transition_phase2_advances_of_union_has_opposite_signs
        (L := L) (K := K) s t (hc s hs) (hc t ht) hm hpl
      omega
    · have h := Transition_phase9_advances_of_union_has_opposite_signs
        (L := L) (K := K) s t (hc s hs) (hc t ht) hm hpl
      omega

noncomputable def uniformOpinion (c : Config (AgentState L K)) : Fin 8 :=
  if h : UniformOpinions c then Classical.choose h else 0

theorem uniformOpinion_spec (c : Config (AgentState L K))
    (h : UniformOpinions c) : ∀ a ∈ c, a.opinions = uniformOpinion c := by
  rw [uniformOpinion, dif_pos h]
  exact Classical.choose_spec h

theorem uniformOpinion_eq_of_uniform
    (c : Config (AgentState L K)) (hc : 0 < c.card)
    (u : Fin 8) (hu : ∀ a ∈ c, a.opinions = u) :
    uniformOpinion c = u := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hc
  exact (uniformOpinion_spec c ⟨u, hu⟩ a ha).symm.trans (hu a ha)

noncomputable def opinionWorkRank (c : Config (AgentState L K)) : ℕ :=
  if UniformOpinions c then outputRank (opinionVerdict (uniformOpinion c)) c + 1
  else c.card + 1 + opinionRank c

theorem opinionWork_uniform (c : Config (AgentState L K))
    (h : UniformOpinions c) :
    opinionWorkRank c = outputRank (opinionVerdict (uniformOpinion c)) c + 1 := by
  simp [opinionWorkRank, h]

theorem opinionWork_nonuniform (c : Config (AgentState L K))
    (h : ¬ UniformOpinions c) :
    opinionWorkRank c = c.card + 1 + opinionRank c := by
  simp [opinionWorkRank, h]

theorem opinionWork_uniform_le_card (c : Config (AgentState L K))
    (h : UniformOpinions c) : opinionWorkRank c ≤ c.card + 1 := by
  rw [opinionWork_uniform c h]
  exact Nat.add_le_add_right (outputRank_le_card _ c) 1

theorem opinionWork_le_four_card (c : Config (AgentState L K)) :
    opinionWorkRank c ≤ 4 * c.card + 1 := by
  classical
  by_cases h : UniformOpinions c
  · have hb := opinionWork_uniform_le_card c h
    omega
  · rw [opinionWork_nonuniform c h]
    have hb := opinionRank_le_three_card c
    omega

theorem opinionWork_pos (c : Config (AgentState L K)) :
    0 < opinionWorkRank c := by
  classical
  unfold opinionWorkRank
  split_ifs <;> omega

theorem opinionWork_step_le_of_stays
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (s t : AgentState L K)
    (hpost : PurePhase p
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    opinionWorkRank (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      opinionWorkRank c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · let d := Protocol.stepOrSelf (NonuniformMajority L K) c s t
    change PurePhase p d at hpost
    change opinionWorkRank d ≤ opinionWorkRank c
    have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hcpos : 0 < c.card := Multiset.card_pos_iff_exists_mem.mpr ⟨s, hs⟩
    have hdcard : d.card = c.card := by
      dsimp [d]
      rw [Protocol.stepOrSelf_card_eq]
    have hdpos : 0 < d.card := by omega
    by_cases hu : UniformOpinions c
    · let u := uniformOpinion c
      have hual : ∀ a ∈ c, a.opinions = u := uniformOpinion_spec c hu
      by_cases hz : u.val = 0
      · have hu0 : u = (0 : Fin 8) := Fin.ext hz
        have hfixed := opinion_zero_pairwiseFixed p hp c hc
          (fun a ha => (hual a ha).trans hu0)
        have heq : d = c := hfixed s t
        rw [heq]
      · by_cases hguard : (hasMinusOne u && hasPlusOne u) = false
        · have hinv := opinion_cleanup_preserves p hp u hz hguard c hc hual s t
          have hdu : UniformOpinions d := ⟨u, hinv.2⟩
          have hmask : uniformOpinion d = u :=
            uniformOpinion_eq_of_uniform d hdpos u hinv.2
          rw [opinionWork_uniform d hdu, hmask, opinionWork_uniform c hu]
          exact Nat.add_le_add_right
            (opinion_cleanup_outputRank_le p hp u hz hguard c hc hual s t) 1
        · have hconf : hasMinusOne u = true ∧ hasPlusOne u = true := by
            cases hm : hasMinusOne u <;> cases hpl : hasPlusOne u <;> simp_all
          obtain ⟨a, ha, hpa⟩ := uniform_conflict_pair_advances p hp u
            hconf.1 hconf.2 c hc hual s t happ
          have heq := hpost a ha
          omega
    · rw [opinionWork_nonuniform c hu]
      by_cases hdu : UniformOpinions d
      · have hbound := opinionWork_uniform_le_card d hdu
        have hpositive := opinionRank_pos_of_not_uniform c hu
        omega
      · rw [opinionWork_nonuniform d hdu]
        have hle := opinionRank_step_le_of_pure p hp c hc s t hpost
        change opinionRank d ≤ opinionRank c at hle
        omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem opinionWork_exists_productive_pair
    (p : ℕ) (hp : p = 2 ∨ p = 9)
    (c : Config (AgentState L K)) (hc : PurePhase p c)
    (hn : 2 ≤ c.card) (hnotFixed : ¬ PairwiseFixed c) :
    ∃ s t, Protocol.Applicable c s t ∧
      (¬ PurePhase p (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ∨
        opinionWorkRank (Protocol.stepOrSelf (NonuniformMajority L K) c s t) <
          opinionWorkRank c) := by
  classical
  by_cases hu : UniformOpinions c
  · let u := uniformOpinion c
    have hual : ∀ a ∈ c, a.opinions = u := uniformOpinion_spec c hu
    by_cases hz : u.val = 0
    · have hu0 : u = (0 : Fin 8) := Fin.ext hz
      exact False.elim (hnotFixed (opinion_zero_pairwiseFixed p hp c hc
        (fun a ha => (hual a ha).trans hu0)))
    · by_cases hguard : (hasMinusOne u && hasPlusOne u) = false
      · by_cases hzero : outputRank (opinionVerdict u) c = 0
        · exact False.elim (hnotFixed (opinion_cleanup_pairwiseFixed p hp u hz
            hguard c hc hual ((outputRank_eq_zero_iff _ _).mp hzero)))
        · obtain ⟨s, t, happ, hdrop⟩ :=
            opinion_cleanup_exists_drop p hp u hz hguard c hc hual hn hzero
          refine ⟨s, t, happ, Or.inr ?_⟩
          let d := Protocol.stepOrSelf (NonuniformMajority L K) c s t
          change opinionWorkRank d < opinionWorkRank c
          have hdcard : d.card = c.card := by
            dsimp [d]
            rw [Protocol.stepOrSelf_card_eq]
          have hdpos : 0 < d.card := by omega
          have hinv := opinion_cleanup_preserves p hp u hz hguard c hc hual s t
          have hdu : UniformOpinions d := ⟨u, hinv.2⟩
          have hmask : uniformOpinion d = u :=
            uniformOpinion_eq_of_uniform d hdpos u hinv.2
          rw [opinionWork_uniform d hdu, hmask, opinionWork_uniform c hu]
          exact Nat.add_lt_add_right hdrop 1
      · have hconf : hasMinusOne u = true ∧ hasPlusOne u = true := by
          cases hm : hasMinusOne u <;> cases hpl : hasPlusOne u <;> simp_all
        have hpos : 0 < c.card := by omega
        obtain ⟨s, hs⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
        obtain ⟨t, happ⟩ := applicable_partner_of_mem hs hn
        refine ⟨s, t, happ, Or.inl ?_⟩
        intro hpost
        obtain ⟨a, ha, hpa⟩ := uniform_conflict_pair_advances p hp u
          hconf.1 hconf.2 c hc hual s t happ
        have heq := hpost a ha
        omega
  · obtain ⟨s, t, happ, hne⟩ := exists_applicable_unequal_opinions c hu
    refine ⟨s, t, happ, ?_⟩
    by_cases hpost : PurePhase p
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
    · right
      let d := Protocol.stepOrSelf (NonuniformMajority L K) c s t
      change opinionWorkRank d < opinionWorkRank c
      have hdcard : d.card = c.card := by
        dsimp [d]
        rw [Protocol.stepOrSelf_card_eq]
      rw [opinionWork_nonuniform c hu]
      by_cases hdu : UniformOpinions d
      · have hbound := opinionWork_uniform_le_card d hdu
        have hpositive := opinionRank_pos_of_not_uniform c hu
        omega
      · rw [opinionWork_nonuniform d hdu]
        have hlt := opinionRank_step_lt_of_pure p hp c hc s t happ hne hpost
        change opinionRank d < opinionRank c at hlt
        omega
    · exact Or.inl hpost

/-! Stopping phase work at a stable endpoint or a higher-phase seed. -/

def phaseWorkTarget (p : ℕ) (init : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  StableDone L K init ∪ {c | ∃ a ∈ c, p < a.phase.val}

def phaseWorkInv (p n : ℕ) (init c : Config (AgentState L K)) : Prop :=
  ReachableFrom L K init c ∧ AdvanceEpidemics.allPhaseGe p n c

noncomputable def phaseWorkRank (p : ℕ) (init : Config (AgentState L K))
    (work : Config (AgentState L K) → ℕ) (c : Config (AgentState L K)) : ℕ := by
  classical
  exact if c ∈ phaseWorkTarget p init then 0 else work c

private theorem phase_seed_iff_count_pos (p : ℕ) (c : Config (AgentState L K)) :
    (∃ a ∈ c, p < a.phase.val) ↔
      0 < AdvanceEpidemics.geCount (p + 1) c := by
  constructor
  · rintro ⟨a, ha, hp⟩
    apply Multiset.countP_pos.mpr
    refine ⟨a, ha, ?_⟩
    change p + 1 ≤ a.phase.val
    omega
  · intro hcount
    obtain ⟨a, ha, hp⟩ := Multiset.countP_pos.mp hcount
    refine ⟨a, ha, ?_⟩
    change p + 1 ≤ a.phase.val at hp
    omega

theorem phaseWorkTarget_step (p : ℕ) (init c : Config (AgentState L K))
    (hc : c ∈ phaseWorkTarget p init) (s t : AgentState L K) :
    Protocol.stepOrSelf (NonuniformMajority L K) c s t ∈ phaseWorkTarget p init := by
  change c ∈ StableDone L K init ∨ (∃ a ∈ c, p < a.phase.val) at hc
  rcases hc with hd | hs
  · apply Or.inl
    exact majorityStableEndpoint_preserved_by_reachable
      (L := L) (K := K) init c _ hd
      (Protocol.reachable_stepOrSelf c s t)
  · apply Or.inr
    apply (phase_seed_iff_count_pos p _).2
    exact lt_of_lt_of_le ((phase_seed_iff_count_pos p c).1 hs)
      (AdvanceEpidemics.geCount_stepOrSelf_ge (p + 1) c s t)

theorem phaseWorkTarget_support (p : ℕ) (init c c' : Config (AgentState L K))
    (hc : c ∈ phaseWorkTarget p init)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    c' ∈ phaseWorkTarget p init := by
  change c ∈ StableDone L K init ∨ (∃ a ∈ c, p < a.phase.val) at hc
  rcases hc with hd | hs
  · apply Or.inl
    exact majorityStableEndpoint_preserved_by_reachable
      (L := L) (K := K) init c c' hd
      (Protocol.stepDistOrSelf_support_reachable
        (NonuniformMajority L K) c c' hsupp)
  · apply Or.inr
    apply (phase_seed_iff_count_pos p c').2
    have hcount : 1 ≤ AdvanceEpidemics.geCount (p + 1) c :=
      (phase_seed_iff_count_pos p c).1 hs
    exact AdvanceEpidemics.geCount_ge_monotone (p + 1) 1 c c' hcount hsupp

theorem phaseWorkTarget_kernel_absorbing
    (p : ℕ) (init c : Config (AgentState L K))
    (hc : c ∈ phaseWorkTarget p init) :
    (NonuniformMajority L K).transitionKernel c (phaseWorkTarget p init)ᶜ = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    (phaseWorkTarget p init)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro c' hsupp hnot
  exact hnot (phaseWorkTarget_support p init c c' hc hsupp)

theorem phaseWorkInv_closed
    (p n : ℕ) (init : Config (AgentState L K)) :
    ConditionalPhaseProgress.Engine.InvClosed
      (NonuniformMajority L K).transitionKernel (phaseWorkInv p n init) := by
  intro c hc
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ phaseWorkInv p n init c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro c' hsupp hnot
  exact hnot ⟨reachableFrom_step_closed init c c' hc.1 hsupp,
    AdvanceEpidemics.allPhaseGe_absorbing p n c c' hc.2 hsupp⟩

theorem purePhase_of_ge_not_phaseWorkTarget
    (p n : ℕ) (init c : Config (AgentState L K))
    (hge : AdvanceEpidemics.allPhaseGe p n c)
    (hnot : c ∉ phaseWorkTarget p init) :
    PurePhase p c := by
  intro a ha
  have hlo := hge.2 a ha
  have hhi : ¬ p < a.phase.val := by
    intro h
    exact hnot (Or.inr ⟨a, ha, h⟩)
  omega

/-- Stop phase work on either a certified endpoint or the first phase above p.
The hypotheses are deterministic work facts; the rank and kernel obligations
are discharged here. -/
theorem stopped_phase_work_expectedHitting_le
    (p n : ℕ) (hn : 2 ≤ n)
    (init : Config (AgentState L K)) (work : Config (AgentState L K) → ℕ)
    (hpositive : ∀ b, ReachableFrom L K init b → PurePhase p b →
      b ∉ StableDone L K init → 0 < work b)
    (hmono : ∀ b, ReachableFrom L K init b → PurePhase p b →
      b ∉ StableDone L K init → ∀ s t,
      PurePhase p (Protocol.stepOrSelf (NonuniformMajority L K) b s t) →
      Protocol.stepOrSelf (NonuniformMajority L K) b s t ∉ StableDone L K init →
      work (Protocol.stepOrSelf (NonuniformMajority L K) b s t) ≤ work b)
    (hproductive : ∀ b, ReachableFrom L K init b → PurePhase p b →
      b ∉ StableDone L K init → ∃ s t,
      Protocol.Applicable b s t ∧
        (Protocol.stepOrSelf (NonuniformMajority L K) b s t ∈ StableDone L K init ∨
         ¬ PurePhase p (Protocol.stepOrSelf (NonuniformMajority L K) b s t) ∨
         work (Protocol.stepOrSelf (NonuniformMajority L K) b s t) < work b))
    (M : ℕ) (c : Config (AgentState L K))
    (hc : phaseWorkInv p n init c) (hcap : work c ≤ M) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
      (phaseWorkTarget p init) ≤ ((M * (n * (n - 1)) : ℕ) : ℝ≥0∞) := by
  classical
  apply expectedHitting_le_of_pairwise_rank n hn
    (phaseWorkInv p n init) (phaseWorkInv_closed p n init)
    (fun b hb => hb.2.1) (phaseWorkTarget p init)
    (phaseWorkRank p init work) ?_ ?_ ?_ M c hc ?_
  · intro b hb hz
    by_contra hnot
    have hpure := purePhase_of_ge_not_phaseWorkTarget p n init b hb.2 hnot
    have hnotDone : b ∉ StableDone L K init := fun hd => hnot (Or.inl hd)
    have hpos := hpositive b hb.1 hpure hnotDone
    have hz' : work b = 0 := by simpa [phaseWorkRank, hnot] using hz
    omega
  · intro b hb s t
    by_cases hdone : b ∈ phaseWorkTarget p init
    · have hpost := phaseWorkTarget_step p init b hdone s t
      simp [phaseWorkRank, hdone, hpost]
    · by_cases hpost :
          Protocol.stepOrSelf (NonuniformMajority L K) b s t ∈ phaseWorkTarget p init
      · simp [phaseWorkRank, hdone, hpost]
      · have hpure := purePhase_of_ge_not_phaseWorkTarget p n init b hb.2 hdone
        have hpostGe := AdvanceEpidemics.allPhaseGe_stepOrSelf p n b hb.2 s t
        have hpostPure := purePhase_of_ge_not_phaseWorkTarget p n init _ hpostGe hpost
        have hnotDone : b ∉ StableDone L K init := fun hd => hdone (Or.inl hd)
        have hpostNotDone :
            Protocol.stepOrSelf (NonuniformMajority L K) b s t ∉ StableDone L K init :=
          fun hd => hpost (Or.inl hd)
        simpa [phaseWorkRank, hdone, hpost] using
          hmono b hb.1 hpure hnotDone s t hpostPure hpostNotDone
  · intro b hb hpos
    have hnot : b ∉ phaseWorkTarget p init := by
      intro hd
      simp [phaseWorkRank, hd] at hpos
    have hpure := purePhase_of_ge_not_phaseWorkTarget p n init b hb.2 hnot
    have hnotDone : b ∉ StableDone L K init := fun hd => hnot (Or.inl hd)
    obtain ⟨s, t, happ, hresult⟩ := hproductive b hb.1 hpure hnotDone
    refine ⟨s, t, happ, ?_⟩
    by_cases hpost :
        Protocol.stepOrSelf (NonuniformMajority L K) b s t ∈ phaseWorkTarget p init
    · simpa [phaseWorkRank, hpost, hnot] using hpos
    · have hpostGe := AdvanceEpidemics.allPhaseGe_stepOrSelf p n b hb.2 s t
      have hpostPure := purePhase_of_ge_not_phaseWorkTarget p n init _ hpostGe hpost
      rcases hresult with hd | hexit | hdrop
      · exact False.elim (hpost (Or.inl hd))
      · exact False.elim (hexit hpostPure)
      · simpa [phaseWorkRank, hnot, hpost] using hdrop
  · by_cases hdone : c ∈ phaseWorkTarget p init
    · simp [phaseWorkRank, hdone]
    · simpa [phaseWorkRank, hdone] using hcap

/-- Concrete work estimate in every reachable pre-backup phase.  Every rank
and productive ordered pair is constructed from the transition rules.
The numerical envelope deliberately leaves room in the paper's recovery
budget and does not require a good role-split event. -/
theorem phase_work_expectedHitting_le
    (L n : ℕ) (hn : 11 ≤ n)
    (init : Config (AgentState L 256))
    (hinit : validInitial init) (hcardInit : init.card = n)
    (hsize : n ≤ 2 ^ L)
    (p : ℕ) (hp : p < 10)
    (c : Config (AgentState L 256))
    (hreach : ReachableFrom L 256 init c)
    (hfloor : AdvanceEpidemics.allPhaseGe p n c) :
    expectedHitting (NonuniformMajority L 256).transitionKernel c
      (phaseWorkTarget p init) ≤
        ((1000 * n * (L + 1) * (n * (n - 1)) : ℕ) : ℝ≥0∞) := by
  classical
  have hnTwo : 2 ≤ n := by omega
  have hlowInit : 11 ≤ init.card := by omega
  have hsizeInit : init.card ≤ 2 ^ L := by omega
  have hcard : ∀ b : Config (AgentState L 256),
      ReachableFrom L 256 init b → b.card = n := by
    intro b hb
    exact (Protocol.reachable_card_eq
      (P := NonuniformMajority L 256) hb).trans hcardInit
  have hcardc : c.card = n := hcard c hreach
  have hNL : 0 ≤ n * L := Nat.zero_le _
  by_cases hpZero : p = 0
  · subst p
    refine stopped_phase_work_expectedHitting_le 0 n hnTwo init
      (phaseZeroWork (L := L) (K := 256))
      ?_ ?_ ?_ (1000 * n * (L + 1)) c ⟨hreach, hfloor⟩ ?_
    · intro b _ _ _
      simp [phaseZeroWork]
    · intro b _ hpure _ s t hpost _
      rcases phaseZero_step_exit_fixed_or_drop b hpure s t
          with hexit | hsame | hdrop
      · exact False.elim (hexit hpost)
      · rw [hsame]
      · exact hdrop.le
    · intro b hb hpure hnot
      obtain ⟨s, t, happ, hprogress⟩ :=
        phaseZero_exists_productive_pair init b hinit hlowInit hsizeInit
          hb hpure hnot
      exact ⟨s, t, happ, Or.inr hprogress⟩
    · have hcap := phaseZeroWork_le c
      rw [hcardc] at hcap
      nlinarith
  · by_cases hpTimed : p ∈ ({1, 5, 6, 7, 8} : Finset ℕ)
    · refine stopped_phase_work_expectedHitting_le p n hnTwo init
        (timedWork (L := L) (K := 256) p)
        ?_ ?_ ?_ (1000 * n * (L + 1)) c ⟨hreach, hfloor⟩ ?_
      · intro b _ _ _
        simp [timedWork]
      · intro b _ hpure _ s t _ _
        exact timedWork_step_le p hpTimed b hpure s t
      · intro b hb hpure _
        have hbcard := hcard b hb
        have hpPos : 0 < p := by fin_cases hpTimed <;> omega
        have hclocks := reachable_positive_phase_has_clockPair
          init b hinit hb (by omega : 0 < b.card) p hpPos hpure
        obtain ⟨s, t, happ, hprogress⟩ :=
          timed_exists_productive_pair p hpTimed b hpure hclocks
        exact ⟨s, t, happ, Or.inr hprogress⟩
      · have hcap := timedWork_le p c
        rw [hcardc] at hcap
        nlinarith
    · by_cases hpThree : p = 3
      · subst p
        refine stopped_phase_work_expectedHitting_le 3 n hnTwo init
          (phaseThreeWork (L := L) (K := 256))
          ?_ ?_ ?_ (1000 * n * (L + 1)) c ⟨hreach, hfloor⟩ ?_
        · intro b _ _ _
          simp [phaseThreeWork]
        · intro b _ hpure _ s t hpost _
          exact phaseThreeWork_step_le_of_stays b hpure s t hpost
        · intro b hb hpure _
          have hbcard := hcard b hb
          have hclocks := reachable_positive_phase_has_clockPair
            init b hinit hb (by omega : 0 < b.card) 3 (by decide) hpure
          obtain ⟨s, t, happ, hprogress⟩ :=
            phaseThree_exists_productive_pair b hpure hclocks
          exact ⟨s, t, happ, Or.inr hprogress⟩
        · have hcap := phaseThreeWork_le c
          rw [hcardc] at hcap
          nlinarith
      · by_cases hpFour : p = 4
        · subst p
          refine stopped_phase_work_expectedHitting_le 4 n hnTwo init
            (fun _ => 1)
            ?_ ?_ ?_ (1000 * n * (L + 1)) c ⟨hreach, hfloor⟩ ?_
          · intro b _ _ _
            exact Nat.zero_lt_one
          · intro b _ _ _ s t _ _
            exact le_rfl
          · intro b hb hpure hnot
            obtain ⟨s, t, happ, hexit⟩ :=
              phaseFour_exists_exit_pair init b hinit hlowInit hsizeInit
                hb hpure hnot
            exact ⟨s, t, happ, Or.inr (Or.inl hexit)⟩
          · nlinarith
        · have hpOpinion : p = 2 ∨ p = 9 := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hpTimed
            omega
          refine stopped_phase_work_expectedHitting_le p n hnTwo init
            (opinionWorkRank (L := L) (K := 256))
            ?_ ?_ ?_ (1000 * n * (L + 1)) c ⟨hreach, hfloor⟩ ?_
          · intro b _ _ _
            exact opinionWork_pos b
          · intro b _ hpure _ s t hpost _
            exact opinionWork_step_le_of_stays p hpOpinion b hpure s t hpost
          · intro b hb hpure hnot
            have hbcard := hcard b hb
            have hnotFixed : ¬ PairwiseFixed b := by
              intro hfixed
              exact hnot (reachable_pairwiseFixed_mem_stableDone
                init b hinit hlowInit hsizeInit hb hfixed)
            obtain ⟨s, t, happ, hprogress⟩ :=
              opinionWork_exists_productive_pair p hpOpinion b hpure
                (by omega : 2 ≤ b.card) hnotFixed
            exact ⟨s, t, happ, Or.inr hprogress⟩
          · have hcap := opinionWork_le_four_card c
            rw [hcardc] at hcap
            nlinarith

/-- Enlarging an occupation-time target can only lower its value. -/
theorem expectedHitting_antitone_target
    {α : Type*} [MeasurableSpace α]
    (P : Kernel α α) (c : α) (S T : Set α) (hST : S ⊆ T) :
    expectedHitting P c T ≤ expectedHitting P c S := by
  unfold expectedHitting
  exact ENNReal.tsum_le_tsum
    (fun t => measure_mono (Set.compl_subset_compl.mpr hST))

/-- A deliberately loose per-phase work allowance plus its epidemic. -/
def phaseRecoveryCost (L n : ℕ) : ℕ :=
  1000 * n * (L + 1) * (n * (n - 1)) + n * n

/-- Complete one phase rung: work until a higher seed or a stable
endpoint, then spread the seed through all remaining agents. -/
theorem recovery_phase_step
    (L n : ℕ) (hn : 11 ≤ n)
    (init : Config (AgentState L 256)) (hinit : validInitial init)
    (hcardInit : init.card = n) (hsize : n ≤ 2 ^ L)
    (p : ℕ) (hp : p < 10) (c : Config (AgentState L 256))
    (hreach : ReachableFrom L 256 init c)
    (hfloor : AdvanceEpidemics.allPhaseGe (L := L) (K := 256) p n c) :
    expectedHitting (NonuniformMajority L 256).transitionKernel c
      (StableDone L 256 init ∪
        {d | AdvanceEpidemics.allPhaseGe (L := L) (K := 256) (p + 1) n d}) ≤
      (phaseRecoveryCost L n : ℝ≥0∞) := by
  let P := (NonuniformMajority L 256).transitionKernel
  let Next : Set (Config (AgentState L 256)) :=
    StableDone L 256 init ∪
      {d | AdvanceEpidemics.allPhaseGe (L := L) (K := 256) (p + 1) n d}
  have hwork := phase_work_expectedHitting_le
    L n hn init hinit hcardInit hsize p hp c hreach hfloor
  have hafter : ∀ y, phaseWorkInv p n init y →
      y ∈ phaseWorkTarget p init →
      expectedHitting P y Next ≤ ((n * n : ℕ) : ℝ≥0∞) := by
    intro y hy hyt
    rcases hyt with hdone | hseed
    · have hz := expectedHitting_eq_zero_of_mem P
        (measurableSet_StableDone L 256 init)
        (fun x hx => StableDone_kernel_absorbing L 256 init x hx) hdone
      calc
        expectedHitting P y Next ≤
            expectedHitting P y (StableDone L 256 init) :=
          expectedHitting_antitone_target P y _ _ Set.subset_union_left
        _ = 0 := hz
        _ ≤ ((n * n : ℕ) : ℝ≥0∞) := zero_le'
    · have hseedCount : 1 ≤ AdvanceEpidemics.geCount
          (L := L) (K := 256) (p + 1) y := by
        obtain ⟨a, ha, hpa⟩ := hseed
        unfold AdvanceEpidemics.geCount
        exact Multiset.countP_pos.mpr ⟨a, ha, by
          change p + 1 ≤ a.phase.val
          omega⟩
      have hepidemic := seeded_phase_epidemic_expectedHitting_le
        (L := L) (K := 256) p n (by omega) y ⟨hy.2, hseedCount⟩
      exact (expectedHitting_antitone_target P y
        {d | AdvanceEpidemics.allPhaseGe (L := L) (K := 256) (p + 1) n d}
        Next Set.subset_union_right).trans hepidemic
  have htower := expectedHitting_seqcomp_on_of_uniform P
    (phaseWorkInv p n init) (phaseWorkInv_closed p n init)
    (DiscreteMeasurableSpace.forall_measurableSet (phaseWorkTarget p init))
    (DiscreteMeasurableSpace.forall_measurableSet Next)
    ((1000 * n * (L + 1) * (n * (n - 1)) : ℕ) : ℝ≥0∞)
    ((n * n : ℕ) : ℝ≥0∞) c ⟨hreach, hfloor⟩ hwork hafter
  simpa only [phaseRecoveryCost, Nat.cast_add] using htower

/-- The finite recovery telescope. It covers every reachable phase-floor
state, including early stabilization and every possible backup entry. -/
theorem recovery_from_phase_floor
    (L n : ℕ) (hn : 11 ≤ n)
    (init : Config (AgentState L 256)) (hinit : validInitial init)
    (hcardInit : init.card = n) (hsize : n ≤ 2 ^ L)
    (p : ℕ) (hp : p ≤ 10) (c : Config (AgentState L 256))
    (hreach : ReachableFrom L 256 init c)
    (hfloor : AdvanceEpidemics.allPhaseGe (L := L) (K := 256) p n c) :
    expectedHitting (NonuniformMajority L 256).transitionKernel c
      (StableDone L 256 init) ≤
        (((10 - p) * phaseRecoveryCost L n + 7 * n ^ 3 : ℕ) : ℝ≥0∞) := by
  let P := (NonuniformMajority L 256).transitionKernel
  suffices h : ∀ d p : ℕ, 10 - p = d → p ≤ 10 →
      ∀ c : Config (AgentState L 256), ReachableFrom L 256 init c →
        AdvanceEpidemics.allPhaseGe (L := L) (K := 256) p n c →
        expectedHitting P c (StableDone L 256 init) ≤
          (((10 - p) * phaseRecoveryCost L n + 7 * n ^ 3 : ℕ) : ℝ≥0∞) by
    exact h (10 - p) p rfl hp c hreach hfloor
  intro d
  induction d with
  | zero =>
      intro p hd hp c hreach hfloor
      have hpTen : p = 10 := by omega
      subst p
      have hcpos : 0 < c.card := by rw [hfloor.1]; omega
      obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcpos
      have hpa : a.phase.val = 10 := by
        have hlo := hfloor.2 a ha
        have hhi := a.phase.isLt
        omega
      have hbackup := reachable_phaseTen_seed_expectedHitting_le
        n (by omega) init c hinit hreach hfloor.1 ⟨a, ha, hpa⟩
      have hbound := hbackup.trans (phaseTen_seed_budget_le n (by omega))
      simpa only [Nat.sub_self, Nat.zero_mul, Nat.zero_add] using hbound
  | succ d ih =>
      intro p hd hp c hreach hfloor
      have hpNext : p + 1 ≤ 10 := by omega
      have hdist : 10 - (p + 1) = d := by omega
      let Next : Set (Config (AgentState L 256)) :=
        StableDone L 256 init ∪
          {y | AdvanceEpidemics.allPhaseGe (L := L) (K := 256) (p + 1) n y}
      have hstage := recovery_phase_step L n hn init hinit hcardInit hsize
        p (by omega) c hreach hfloor
      have htail : ∀ y, ReachableFrom L 256 init y → y ∈ Next →
          expectedHitting P y (StableDone L 256 init) ≤
            (((10 - (p + 1)) * phaseRecoveryCost L n + 7 * n ^ 3 : ℕ) : ℝ≥0∞) := by
        intro y hy hnext
        rcases hnext with hdone | hfloorNext
        · rw [expectedHitting_eq_zero_of_mem P
            (measurableSet_StableDone L 256 init)
            (fun x hx => StableDone_kernel_absorbing L 256 init x hx) hdone]
          exact zero_le'
        · exact ih (p + 1) hdist hpNext y hy hfloorNext
      have htower := expectedHitting_seqcomp_on_of_uniform P
        (ReachableFrom L 256 init) (reachableFrom_kernel_closed init)
        (DiscreteMeasurableSpace.forall_measurableSet Next)
        (measurableSet_StableDone L 256 init)
        (phaseRecoveryCost L n : ℝ≥0∞)
        ((((10 - (p + 1)) * phaseRecoveryCost L n + 7 * n ^ 3 : ℕ)) : ℝ≥0∞)
        c hreach hstage htail
      have harith : phaseRecoveryCost L n +
          ((10 - (p + 1)) * phaseRecoveryCost L n + 7 * n ^ 3) =
          (10 - p) * phaseRecoveryCost L n + 7 * n ^ 3 := by
        rw [show 10 - p = (10 - (p + 1)) + 1 by omega]
        ring
      calc
        expectedHitting P c (StableDone L 256 init) ≤
            (phaseRecoveryCost L n : ℝ≥0∞) +
              (((10 - (p + 1)) * phaseRecoveryCost L n + 7 * n ^ 3 : ℕ) : ℝ≥0∞) :=
          htower
        _ = ((phaseRecoveryCost L n +
              ((10 - (p + 1)) * phaseRecoveryCost L n + 7 * n ^ 3) : ℕ) : ℝ≥0∞) :=
          (Nat.cast_add _ _).symm
        _ = (((10 - p) * phaseRecoveryCost L n + 7 * n ^ 3 : ℕ) : ℝ≥0∞) := by
          rw [harith]

theorem recovery_telescope_budget_le (n : ℕ) (hn : 1 ≤ n) :
    10 * phaseRecoveryCost (PhaseThreeModel.Numeric.hourIndex n) n +
      7 * n ^ 3 ≤ recoveryBudget n := by
  let H := PhaseThreeModel.Numeric.clockHours n
  have hH : 1 ≤ H := by
    simp [H, PhaseThreeModel.Numeric.clockHours]
  have hN : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hsq : n * n ≤ n ^ 3 := by
    have h := Nat.mul_le_mul_left (n * n) hn
    nlinarith only [h]
  have hwork :
      10 * (1000 * n * H * (n * (n - 1))) ≤ 10000 * n ^ 3 * H := by
    calc
      10 * (1000 * n * H * (n * (n - 1))) ≤
          10 * (1000 * n * H * (n * n)) :=
        Nat.mul_le_mul_left 10 (Nat.mul_le_mul_left (1000 * n * H) hN)
      _ = 10000 * n ^ 3 * H := by ring
  have hrest : 10 * (n * n) + 7 * n ^ 3 ≤ 17 * n ^ 3 * H := by
    calc
      10 * (n * n) + 7 * n ^ 3 ≤ 17 * n ^ 3 := by omega
      _ ≤ 17 * n ^ 3 * H := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (17 * n ^ 3) hH
  change 10 * (1000 * n * H * (n * (n - 1)) + n * n) +
    7 * n ^ 3 ≤ 30700 * n ^ 3 * H
  calc
    10 * (1000 * n * H * (n * (n - 1)) + n * n) + 7 * n ^ 3 ≤
        10017 * n ^ 3 * H := by nlinarith only [hwork, hrest]
    _ ≤ 30700 * n ^ 3 * H :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))

/-- N19: the explicit paper recovery budget from every reachable state. -/
theorem reachable_recovery_estimate
    {n : ℕ} (init : InputCfg n) (hinput : GoodInput n init)
    (c : InputCfg n)
    (hreach :
      ReachableFrom (PhaseThreeModel.Numeric.hourIndex n) 256 init c)
    (hnot :
      c ∈ (StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init)ᶜ) :
    expectedHitting
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
      c (StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ≤
        (recoveryBudget n : ℝ≥0∞) := by
  have hlow : 11 ≤ n := goodInput_population_lower hinput
  have hinit : validInitial init := hinput.2.1
  have hcardInit : init.card = n := hinput.2.2
  clear hinput hnot
  have hsize : n ≤ 2 ^ PhaseThreeModel.Numeric.hourIndex n := by
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n
  have hcard : c.card = n :=
    (Protocol.reachable_card_eq
      (P := NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256) hreach).trans
        hcardInit
  have hfloor : AdvanceEpidemics.allPhaseGe
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 0 n c :=
    ⟨hcard, fun _ _ => Nat.zero_le _⟩
  have h := recovery_from_phase_floor
    (PhaseThreeModel.Numeric.hourIndex n) n hlow init hinit hcardInit hsize
    0 (by decide) c hreach hfloor
  have hbudget : ((10 * phaseRecoveryCost
      (PhaseThreeModel.Numeric.hourIndex n) n + 7 * n ^ 3 : ℕ) : ℝ≥0∞) ≤
        (recoveryBudget n : ℝ≥0∞) := by
    exact_mod_cast recovery_telescope_budget_le n (by omega)
  simpa only [Nat.sub_zero] using h.trans hbudget

end Ripple.PopulationProtocol.ExactMajority.UniformRecovery

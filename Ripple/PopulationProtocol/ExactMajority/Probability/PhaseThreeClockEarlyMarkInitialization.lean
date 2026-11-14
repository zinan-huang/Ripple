-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarkInitialization.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalRise

/-!
# Zero normal-high count at the observed early cutoff

Before the lower front reaches the chosen cutoff, every upper-front birth
is tagged as an immigration, and every copy from a marked upper source
propagates its mark. The actual upper front therefore equals the natural
mark set through the first cutoff. The induction starts at the genuine
fresh first seed, where every effective Clock minute is zero.

The result is pointwise on an observed current phase-cap guard. The
first-cutoff fibre is measurable at that time; no future good event is
used as a conditioning event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkInitialization

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbeddingBridge
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkEmbedding PhaseThreeClockNormalRise
  PhaseThreeClockActivationLaw PhaseThreeClockActivationSeed PhaseThreeClockSeedTails

variable {L K m : ℕ}

/-- Below the early cutoff, every upper-front tick adds a natural mark. -/
theorem gatedTick_imp_mark_event (f : Fin m → AgentState L K)
    (M : Finset (Fin m)) (ℓ cutoff : ℕ)
    (hM : M = aboveSet f (ℓ + 1)) (hsmall : frontCount f ℓ < cutoff)
    (hcap : ℓ < K * (L + 1)) (i j : Fin m) (hg : GatedTick (ℓ + 1) f i j) :
    EarlyDrip (clockSet f) f ℓ cutoff i j ∨ Propagation (clockSet f) M i j := by
  classical
  rcases hg.1 with hcopy | hcopy | hdrip
  · right
    have hi : (f i).role = .clock ∧ ¬ (ℓ + 1 ≤ effMinute (f i)) := by
      simpa only [belowSet, Finset.mem_filter, Finset.mem_univ, true_and] using hcopy.1
    have hic : i ∈ clockSet f := by
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi.1
    have hin : i ∉ M := by
      rw [hM]
      intro him
      exact hi.2 (Finset.mem_filter.mp him).2.2
    have hjm : j ∈ M := by simpa only [hM] using hcopy.2
    exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hic, hin⟩, hjm⟩
  · right
    have hj : (f j).role = .clock ∧ ¬ (ℓ + 1 ≤ effMinute (f j)) := by
      simpa only [belowSet, Finset.mem_filter, Finset.mem_univ, true_and] using hcopy.2
    have hjc : j ∈ clockSet f := by
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj.1
    have hjn : j ∉ M := by
      rw [hM]
      intro hjm
      exact hj.2 (Finset.mem_filter.mp hjm).2.2
    have him : i ∈ M := by simpa only [hM] using hcopy.1
    exact Or.inl ⟨him, Finset.mem_sdiff.mpr ⟨hjc, hjn⟩⟩
  · left
    refine ⟨hsmall, hcap, ?_, ?_⟩
    · rw [sourceSet_eq_exactSet]
      simpa only [Nat.add_sub_cancel] using hdrip.1
    · rw [sourceSet_eq_exactSet]
      simpa only [Nat.add_sub_cancel] using hdrip.2

/-- The actual selected-pair ledger preserves equality of marks and the
upper front as long as the pre-step lower front is below the cutoff. -/
theorem markedAt_eq_above_step (init : Cfg L 256)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L 256)
    (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (hlevel : ℓ + 1 ≤ 256 * (L + 1))
    (henv : ClockEnvironment (virtualLabels init ω t))
    (hmask : C = clockSet (virtualLabels init ω t))
    (hM : markedAt init C ℓ cutoff s ω t = aboveSet (virtualLabels init ω t) (ℓ + 1))
    (hsmall : frontCount (virtualLabels init ω t) ℓ < cutoff)
    (hpost : ∀ i, (virtualLabels init ω (t + 1) i).phase.val ≤ 3) :
    markedAt init C ℓ cutoff s ω (t + 1) =
      aboveSet (virtualLabels init ω (t + 1)) (ℓ + 1) := by
  classical
  have hMsub : markedAt init C ℓ cutoff s ω t ⊆
      aboveSet (virtualLabels init ω t) (ℓ + 1) := by
    intro i hi
    simpa only [hM] using hi
  have hMnext := markedAt_step_subset_above init (by decide) C ℓ cutoff s t ω hst hℓ
    henv hmask hMsub hpost
  have hMcard : (markedAt init C ℓ cutoff s ω t).card =
      frontCount (virtualLabels init ω t) (ℓ + 1) := congrArg Finset.card hM
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      simpa only [markedAt_succ, if_pos hst, hd, markStep,
        virtualLabels_succ, auxStep] using hM
  | some ij =>
      rcases ij with ⟨i, j⟩
      have hf := frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
        henv.phase_range (fun k hk => henv.carrier k (Or.inr (Or.inr hk)))
        hpost (ℓ + 1) (by omega) hlevel
      have hm :
          (markedAt init C ℓ cutoff s ω (t + 1)).card =
            (markedAt init C ℓ cutoff s ω t).card +
              (if EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j then 1 else 0) +
              (if Propagation C (markedAt init C ℓ cutoff s ω t) i j then 1 else 0) := by
        simpa only [markedAt_succ, if_pos hst, hd, markStep] using
          markUpdate_card C (markedAt init C ℓ cutoff s ω t)
            (virtualLabels init ω t) ℓ cutoff i j
            (marks_source_disjoint C _ _ ℓ hMsub)
      apply Finset.eq_of_subset_of_card_le hMnext
      change frontCount (virtualLabels init ω (t + 1)) (ℓ + 1) ≤ _
      by_cases hg : GatedTick (ℓ + 1) (virtualLabels init ω t) i j
      · have hadd : EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j ∨
            Propagation C (markedAt init C ℓ cutoff s ω t) i j := by
          simpa only [hmask] using
            gatedTick_imp_mark_event (virtualLabels init ω t)
              (markedAt init C ℓ cutoff s ω t) ℓ cutoff hM hsmall (by omega) i j hg
        rw [if_pos hg] at hf
        rcases hadd with he | hp
        · rw [if_pos he] at hm
          split_ifs at hm <;> omega
        · rw [if_pos hp] at hm
          split_ifs at hm <;> omega
      · rw [if_neg hg] at hf
        split_ifs at hm <;> omega

variable {n : ℕ}

theorem clock_effMinute_zero_at_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) (i : Fin init.card)
    (hc : (virtualLabels init ω s i).role = .clock) :
    effMinute (virtualLabels init ω s i) = 0 := by
  rw [virtual_eq_actual_at_seedPrefix init ω s hseed] at hc ⊢
  have hmem := labelsAt_mem_trace init ω s i
  have hp := (hseed.2.phase_range _ hmem).2
  by_cases ha : 3 ≤ (labelsAt init ω s i).phase.val
  · have heq : (labelsAt init ω s i).phase.val = 3 := by omega
    have hmin := Phase3Pre3.clock_minute_zero_of_Phase3EntryAgent
      (hseed.2.fresh _ hmem heq) hc
    simp only [effMinute, if_pos ha, hmin]
  · simp only [effMinute, if_neg ha]

theorem aboveSet_at_seedPrefix_eq_empty (init : InputCfg n) (ω : InputLog n)
    (s r : ℕ) (hseed : ω ∈ seedPrefix init s) (hr : 1 ≤ r) :
    aboveSet (virtualLabels init ω s) r = ∅ := by
  ext i
  constructor
  · intro hi
    have hm : (virtualLabels init ω s i).role = .clock ∧
        r ≤ effMinute (virtualLabels init ω s i) := by
      simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hz := clock_effMinute_zero_at_seedPrefix init ω s hseed i hm.1
    exfalso
    omega
  · intro hi
    exact False.elim (by simpa using hi)

/-- Equality holds at an observed endpoint whose entire strict past is
below the cutoff. An endpoint phase cap supplies all preceding safe-step
guards by phase monotonicity. -/
theorem markedAt_eq_above_of_seed_before_cutoff (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hlevel : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hmask : C = clockSet (labelsAt init ω s))
    (hphase : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3)
    (hsmall : ∀ t, s ≤ t → t < u → frontCount (virtualLabels init ω t) ℓ < cutoff) :
    markedAt init C ℓ cutoff s ω u = aboveSet (virtualLabels init ω u) (ℓ + 1) := by
  have henv (t : ℕ) (hst : s ≤ t) (htu : t ≤ u) :
      ClockEnvironment (virtualLabels init ω t) := by
    refine ⟨?_, virtual_carrier_from_seedPrefix init ω s hseed t hst⟩
    intro i
    exact ⟨virtual_phase_floor_from_seedPrefix init ω s t hseed hst i,
      (virtualLabels_phase_mono init ω i htu).trans (hphase i)⟩
  have hall : ∀ t, s ≤ t → t ≤ u →
      markedAt init C ℓ cutoff s ω t =
        aboveSet (virtualLabels init ω t) (ℓ + 1) := by
    intro t hst
    induction t, hst using Nat.le_induction with
    | base =>
        intro _
        rw [markedAt_empty_before_seed init C ℓ cutoff s ω s le_rfl,
          aboveSet_at_seedPrefix_eq_empty init ω s (ℓ + 1) hseed (by omega)]
    | succ t hst ih =>
        intro htu
        have hcur := henv t hst (by omega)
        have hnext := henv (t + 1) (by omega) htu
        have hmaskt : C = clockSet (virtualLabels init ω t) :=
          hmask.trans (virtual_clockSet_eq_seed_of_current_phase_cap init ω s t hseed hst
            (fun i => (hcur.phase_range i).2)).symm
        exact markedAt_eq_above_step init C ℓ cutoff s t ω hst hℓ hlevel hcur hmaskt
          (ih (by omega)) (hsmall t hst (by omega)) (fun i => (hnext.phase_range i).2)
  exact hall u hsu le_rfl

def earlyCutoffFibre (init : Cfg L K) (s ℓ cutoff u : ℕ) : Set (Ω L K) :=
  {ω | s ≤ u ∧ cutoff ≤ frontCount (virtualLabels init ω u) ℓ ∧
    ∀ t, s ≤ t → t < u → frontCount (virtualLabels init ω t) ℓ < cutoff}

theorem earlyCutoffFibre_measurable (init : Cfg L K) (s ℓ cutoff u : ℕ) :
    MeasurableSet[pairLogFiltration L K u] (earlyCutoffFibre init s ℓ cutoff u) := by
  have hcurrent : MeasurableSet[pairLogFiltration L K u]
      {ω | cutoff ≤ frontCount (virtualLabels init ω u) ℓ} :=
    (show MeasurableSet {f : Fin init.card → AgentState L K | cutoff ≤ frontCount f ℓ} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)
  have hprior (t : ℕ) : MeasurableSet[pairLogFiltration L K u]
      {ω | s ≤ t → t < u → frontCount (virtualLabels init ω t) ℓ < cutoff} := by
    by_cases hs : s ≤ t
    · by_cases ht : t < u
      · have hobs : MeasurableSet[pairLogFiltration L K t]
            {ω | frontCount (virtualLabels init ω t) ℓ < cutoff} :=
          (show MeasurableSet {f : Fin init.card → AgentState L K | frontCount f ℓ < cutoff} from
            (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init t)
        simpa only [hs, ht, true_implies] using
          (((pairLogFiltration L K).mono ht.le) _ hobs)
      · simp only [ht, false_implies, implies_true, Set.setOf_true, MeasurableSet.univ]
    · simp only [hs, false_implies, Set.setOf_true, MeasurableSet.univ]
  by_cases hsu : s ≤ u
  · have heq : earlyCutoffFibre init s ℓ cutoff u =
        {ω | cutoff ≤ frontCount (virtualLabels init ω u) ℓ} ∩
          ⋂ t, {ω | s ≤ t → t < u → frontCount (virtualLabels init ω t) ℓ < cutoff} := by
      ext ω
      simp only [earlyCutoffFibre, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_iInter, hsu, true_and]
    rw [heq]
    exact hcurrent.inter (MeasurableSet.iInter hprior)
  · simp only [earlyCutoffFibre, hsu, false_and, Set.setOf_false, MeasurableSet.empty]

theorem normalCount_zero_at_earlyCutoff (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hℓ : 1 ≤ ℓ)
    (hlevel : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hmask : C = clockSet (labelsAt init ω s))
    (hphase : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3)
    (hcut : ω ∈ earlyCutoffFibre init s ℓ cutoff u) :
    normalCount (virtualLabels init ω u) (markedAt init C ℓ cutoff s ω u) ℓ = 0 := by
  have heq := markedAt_eq_above_of_seed_before_cutoff init ω C ℓ cutoff s u
    hseed hcut.1 hℓ hlevel hmask hphase hcut.2.2
  simp only [heq, normalCount, normalSet, Finset.sdiff_self, Finset.card_empty]

/-- The initialization failure has probability zero on every prefix
intersection; the initial P4 normal-high count needs no error allowance. -/
theorem earlyCutoff_normal_failure_null (init : InputCfg n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hℓ : 1 ≤ ℓ) (hlevel : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) :
    law init (E ∩ {ω | ω ∈ seedPrefix init s ∧
      C = clockSet (labelsAt init ω s) ∧
      (∀ i, (virtualLabels init ω u i).phase.val ≤ 3) ∧
      ω ∈ earlyCutoffFibre init s ℓ cutoff u ∧
      normalCount (virtualLabels init ω u) (markedAt init C ℓ cutoff s ω u) ℓ ≠ 0}) = 0 := by
  have he : E ∩ {ω | ω ∈ seedPrefix init s ∧
      C = clockSet (labelsAt init ω s) ∧
      (∀ i, (virtualLabels init ω u i).phase.val ≤ 3) ∧
      ω ∈ earlyCutoffFibre init s ℓ cutoff u ∧
      normalCount (virtualLabels init ω u) (markedAt init C ℓ cutoff s ω u) ℓ ≠ 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hω.2.2.2.2.2
      (normalCount_zero_at_earlyCutoff init ω C ℓ cutoff s u
        hω.2.1 hℓ hlevel hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1)
  rw [he, measure_empty]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkInitialization

end

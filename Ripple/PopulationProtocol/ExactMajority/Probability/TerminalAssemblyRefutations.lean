import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEntryNoOvershoot
import Ripple.PopulationProtocol.ExactMajority.Probability.TightEpidemicWork

/-!
# Terminal assembly interface refutations

The concrete slot-4 work witness admits the empty configuration through its
bare `StableTie4` disjunct.  The work-to-seam residual, however, requires a
one-step transition into a card-`n` `AdvanceEntry`.  On the empty configuration
the protocol kernel is the deterministic self-loop, so these two surfaces
cannot be inhabited together when `2 ≤ n`.
-/

namespace Ripple.PopulationProtocol.ExactMajority
namespace TerminalAssemblyRefutations

open MeasureTheory ProbabilityTheory

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A phase-2 consensus state that deliberately keeps an at-risk clock at
counter zero.  It witnesses that the bare phase-2 work postcondition does not
carry the freshness part of `AdvanceEntry`. -/
private def phase2AtRiskAgent : AgentState L K :=
  { input := .A
    output := .A
    phase := ⟨2, by decide⟩
    role := .clock
    assigned := false
    bias := .zero
    smallBias := ⟨0, by decide⟩
    hour := ⟨0, by omega⟩
    minute := ⟨0, by omega⟩
    full := false
    opinions := TightEpidemicWork.opU
    counter := ⟨0, by omega⟩ }

private theorem phase2AtRiskAgent_transition_self :
    Transition L K (phase2AtRiskAgent (L := L) (K := K))
        (phase2AtRiskAgent (L := L) (K := K)) =
      (phase2AtRiskAgent (L := L) (K := K),
        phase2AtRiskAgent (L := L) (K := K)) := by
  simp [Transition, phaseEpidemicUpdate, runInitsBetween_self,
    Phase2Transition, phase2AtRiskAgent, TightEpidemicWork.opU,
    opinionsUnion, hasMinusOne, hasPlusOne, finishPhase10Entry,
    canonicalPhase10Entry]

/-- The current concrete slot-4 `Post` is too weak to feed the universal
work-to-seam entry residual: it admits the empty stable-tie configuration,
whose one-step kernel cannot reach a card-`n` seam entry. -/
theorem not_advanceEntryFromWorkPost_work4Tight
    {n : ℕ} (hn : 2 ≤ n) (p : ℕ) :
    ¬ AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) p n
        (TightEpidemicWork.work4Tight (L := L) (K := K) hn).Post := by
  intro hEntryFromPost
  let c : Config (AgentState L K) := 0
  have hPost :
      (TightEpidemicWork.work4Tight (L := L) (K := K) hn).Post c := by
    change Phase4Convergence.StableTie4 (L := L) (K := K) c ∨
      Phase4Convergence.advFinished (L := L) (K := K) n c
    left
    intro a ha
    simp [c] at ha
  have hNotEntry :
      ¬ AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c := by
    intro hEntry
    have hcard : c.card = n := hEntry.1.1.1
    simp [c] at hcard
    omega
  have hzero := hEntryFromPost c hPost
  have hone :
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
            (L := L) (K := K) p n c'} = 1 := by
    rw [pow_one]
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
          (L := L) (K := K) p n c'} = 1
    rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c from by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg]
      simp [c]]
    rw [PMF.toMeasure_pure_apply]
    · simp [hNotEntry]
    · exact MeasurableSet.of_discrete
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- Slot 2 has a separate interface failure.  Its postcondition constrains only
phase and epidemic opinions, so it admits a population of phase-2 clocks whose
counters are already zero.  The population is a deterministic self-loop; for
`p = 1` it violates seam freshness, while for every other `p` it violates the
phase/no-overshoot part of `AdvanceEntry`. -/
theorem not_advanceEntryFromWorkPost_work2Tight
    {n : ℕ} (hn : 2 ≤ n) (p : ℕ) :
    ¬ AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) p n
        (TightEpidemicWork.work2Tight (L := L) (K := K) hn).Post := by
  intro hEntryFromPost
  let a : AgentState L K := phase2AtRiskAgent (L := L) (K := K)
  let c : Config (AgentState L K) := Multiset.replicate n a
  have hnpos : 0 < n := by omega
  have haMem : a ∈ c := by
    exact Multiset.mem_replicate.mpr ⟨hnpos.ne', rfl⟩
  have hinformed :
      Phase2Convergence.informedU (L := L) (K := K)
        TightEpidemicWork.opU c = n := by
    unfold Phase2Convergence.informedU
    rw [Multiset.countP_eq_card.mpr]
    · simp [c]
    · intro b hb
      have hb_eq : b = a := Multiset.eq_of_mem_replicate (by
        simpa [c] using hb)
      subst b
      simp [a, phase2AtRiskAgent, Phase2Convergence.informedP,
        TightEpidemicWork.opU]
  have hPost :
      (TightEpidemicWork.work2Tight (L := L) (K := K) hn).Post c := by
    change
      (Phase2Convergence.SeededConsensusWin (L := L) (K := K)
          TightEpidemicWork.opU TightEpidemicWork.opV n c ∧
        Phase2Convergence.oFinished (L := L) (K := K)
          TightEpidemicWork.opU n c)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine ⟨by simp [c], ?_⟩
      intro b hb
      have hb_eq : b = a := Multiset.eq_of_mem_replicate (by
        simpa [c] using hb)
      subst b
      simp [a, phase2AtRiskAgent]
    · rw [hinformed]
      omega
    · unfold Phase2Convergence.oFinished
      rw [hinformed]
  have hNotEntry :
      ¬ AdvanceEntryNoOvershoot.AdvanceEntry (L := L) (K := K) p n c := by
    intro hEntry
    rcases hEntry with ⟨⟨hAllGe, hTriggered⟩, hNoOvershoot, hFresh⟩
    cases p with
    | zero =>
        have hlt := hNoOvershoot a haMem
        simp [a, phase2AtRiskAgent] at hlt
    | succ p =>
        cases p with
        | zero =>
            apply hFresh
            refine ⟨a, haMem, ?_, ?_, ?_⟩ <;>
              simp [a, phase2AtRiskAgent]
        | succ p =>
            unfold AdvanceEpidemics.advTriggered at hTriggered
            have hpos :
                0 < Multiset.countP
                  (fun x : AgentState L K =>
                    decide (p + 1 + 1 + 1 ≤ x.phase.val)) c := by
              omega
            rcases Multiset.countP_pos.mp hpos with ⟨b, hb, hbPhase⟩
            have hb_eq : b = a := Multiset.eq_of_mem_replicate (by
              simpa [c] using hb)
            subst b
            simp [a, phase2AtRiskAgent] at hbPhase
  have hstepPure :
      (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c := by
    unfold Protocol.stepDistOrSelf
    rw [dif_pos]
    · unfold Protocol.stepDist
      rw [show Protocol.scheduledStep (NonuniformMajority L K) c =
          Function.const (AgentState L K × AgentState L K) c from by
        funext pair
        rcases pair with ⟨r₁, r₂⟩
        unfold Protocol.scheduledStep
        by_cases happ : Protocol.Applicable c r₁ r₂
        · have hr₁mem : r₁ ∈ c :=
            Multiset.mem_of_le happ (by simp)
          have hr₂mem : r₂ ∈ c :=
            Multiset.mem_of_le happ (by simp)
          have hr₁ : r₁ = a := Multiset.eq_of_mem_replicate (by
            simpa [c] using hr₁mem)
          have hr₂ : r₂ = a := Multiset.eq_of_mem_replicate (by
            simpa [c] using hr₂mem)
          subst r₁
          subst r₂
          unfold Protocol.stepOrSelf
          rw [if_pos happ, show (NonuniformMajority L K).δ a a = (a, a) by
            simpa [NonuniformMajority, a] using
              (phase2AtRiskAgent_transition_self (L := L) (K := K))]
          exact Multiset.sub_add_cancel happ
        · exact Protocol.stepOrSelf_eq_self_of_not_applicable happ,
        PMF.map_const]
    · simp [c, hn]
  have hzero := hEntryFromPost c hPost
  have hone :
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
            (L := L) (K := K) p n c'} = 1 := by
    rw [pow_one]
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ¬ AdvanceEntryNoOvershoot.AdvanceEntry
          (L := L) (K := K) p n c'} = 1
    rw [hstepPure, PMF.toMeasure_pure_apply]
    · simp [hNotEntry]
    · exact MeasurableSet.of_discrete
  rw [hone] at hzero
  exact one_ne_zero hzero

#print axioms not_advanceEntryFromWorkPost_work4Tight
#print axioms not_advanceEntryFromWorkPost_work2Tight

end TerminalAssemblyRefutations
end Ripple.PopulationProtocol.ExactMajority

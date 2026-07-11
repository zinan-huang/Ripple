import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamOvershootBridge
import Mathlib.Tactic

namespace ExactMajority
namespace SeamEntryPhaseCeiling

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/--
A deterministic seam-entry provenance predicate.

This is the timing information missing from the bare seam precondition
`allPhaseGe p n ∧ advTriggered (p+1)`: the current seam-entry config is a one-step
successor of a well-formed exact-phase-`p` predecessor.
-/
def SeamEntryFromExactStep (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∃ cPrev : Config (AgentState L K),
    SeamEpidemics.allPhaseEq (L := L) (K := K) p n cPrev ∧
    c ∈ ((NonuniformMajority L K).stepDistOrSelf cPrev).support

/--
One real protocol step from a well-formed exact-phase-`p` config has phase ceiling
`≤ p+1`.

For `p ≤ 8`, this uses the landed per-side transition bounds
`Transition_left_phase_le_ep_succ_of_wf` and `Transition_right_phase_le_ep_succ_of_wf`
plus the epidemic max identity.  For `p ≥ 9`, the ceiling is automatic from
`AgentState.phase : Fin 11`.
-/
theorem phaseCeiling_of_one_step_from_allPhaseEq
    (p n : ℕ)
    (cPrev cEntry : Config (AgentState L K))
    (hwf : SeamNoOvershoot.Wf (L := L) (K := K) cPrev)
    (hexact : SeamEpidemics.allPhaseEq (L := L) (K := K) p n cPrev)
    (hentry : cEntry ∈ ((NonuniformMajority L K).stepDistOrSelf cPrev).support) :
    ∀ a ∈ cEntry, a.phase.val ≤ p + 1 := by
  classical
  by_cases hp8 : p ≤ 8
  · obtain ⟨_hcard, hphase⟩ := hexact
    by_cases hc : 2 ≤ cPrev.card
    · rw [show (NonuniformMajority L K).stepDistOrSelf cPrev =
          (NonuniformMajority L K).stepDist cPrev hc by
          unfold Protocol.stepDistOrSelf
          rw [dif_pos hc]] at hentry
      obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
        Protocol.stepDist_support (NonuniformMajority L K) cPrev hc cEntry hentry
      rw [← hr]
      simp only [Protocol.scheduledStep]
      by_cases happ : Protocol.Applicable cPrev r₁ r₂
      · have hr₁mem : r₁ ∈ cPrev := Multiset.mem_of_le happ (by simp)
        have hr₂mem : r₂ ∈ cPrev := Multiset.mem_of_le happ (by simp)
        have hwf₁ : SeamNoOvershoot.WfAgent (L := L) (K := K) r₁ := hwf r₁ hr₁mem
        have hwf₂ : SeamNoOvershoot.WfAgent (L := L) (K := K) r₂ := hwf r₂ hr₂mem
        have hr₁phase : r₁.phase.val = p := hphase r₁ hr₁mem
        have hr₂phase : r₂.phase.val = p := hphase r₂ hr₂mem

        have hleft :
            (Transition L K r₁ r₂).1.phase.val ≤ p + 1 := by
          have h :=
            SeamNoOvershoot.Transition_left_phase_le_ep_succ_of_wf
              (L := L) (K := K) r₁ r₂ hwf₁ hwf₂
              (by omega) (by omega)
          rw [hr₁phase, hr₂phase] at h
          simpa using h

        have hright :
            (Transition L K r₁ r₂).2.phase.val ≤ p + 1 := by
          have h :=
            SeamNoOvershoot.Transition_right_phase_le_ep_succ_of_wf
              (L := L) (K := K) r₁ r₂ hwf₁ hwf₂
              (by omega) (by omega)
          have hepRight :
              (phaseEpidemicUpdate L K r₁ r₂).2.phase.val =
                max r₁.phase.val r₂.phase.val :=
            SeamNoOvershoot.phaseEpidemicUpdate_right_phase_eq_max_of_wf
              (L := L) (K := K) r₁ r₂ hwf₁ hwf₂
              (by omega) (by omega)
          rw [hepRight, hr₁phase, hr₂phase] at h
          simpa using h

        intro a ha
        have hstep :
            Protocol.stepOrSelf (NonuniformMajority L K) cPrev r₁ r₂ =
              cPrev - ({r₁, r₂} : Multiset (AgentState L K)) +
                ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
                  : Multiset (AgentState L K)) := by
          unfold Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        rw [hstep] at ha
        rcases Multiset.mem_add.mp ha with hsurv | hout
        · have hacPrev : a ∈ cPrev :=
            Multiset.mem_of_le (Multiset.sub_le_self _ _) hsurv
          have haphase : a.phase.val = p := hphase a hacPrev
          omega
        · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K)) =
              (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0
              from rfl] at hout
          rcases Multiset.mem_cons.mp hout with rfl | hout
          · omega
          · rcases Multiset.mem_cons.mp hout with rfl | hout
            · omega
            · simp at hout
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        intro a ha
        have haphase : a.phase.val = p := hphase a ha
        omega
    · rw [show (NonuniformMajority L K).stepDistOrSelf cPrev = PMF.pure cPrev by
          unfold Protocol.stepDistOrSelf
          rw [dif_neg hc]] at hentry
      rw [PMF.mem_support_pure_iff] at hentry
      subst hentry
      intro a ha
      have haphase : a.phase.val = p := hphase a ha
      omega
  · intro a _ha
    have hp9 : 9 ≤ p := by omega
    have hphase_lt : a.phase.val < 11 := a.phase.2
    omega

/--
A one-step exact-phase seam entry is already a `NoOvershoot` start.
-/
theorem noOvershoot_of_one_step_from_allPhaseEq
    (p n : ℕ)
    (cPrev cEntry : Config (AgentState L K))
    (hwf : SeamNoOvershoot.Wf (L := L) (K := K) cPrev)
    (hexact : SeamEpidemics.allPhaseEq (L := L) (K := K) p n cPrev)
    (hentry : cEntry ∈ ((NonuniformMajority L K).stepDistOrSelf cPrev).support) :
    SeamNoOvershoot.NoOvershoot (L := L) (K := K) p cEntry := by
  intro a ha
  have hceil :
      a.phase.val ≤ p + 1 :=
    phaseCeiling_of_one_step_from_allPhaseEq
      (L := L) (K := K) p n cPrev cEntry hwf hexact hentry a ha
  omega

/-- **Generic one-step measure-zero supply.**  From an `allPhaseEq p n` config, every one-step
successor (`stepDistOrSelf` support point) is a `SeamEntryFromExactStep p n` (witness `cPrev = c`),
so the entry predicate holds a.s. after one step (complement null).  Wf-free: only exact-phase
provenance is used. -/
theorem exactStep_measure_zero_of_allPhaseEq
    (p n : ℕ) (c : Config (AgentState L K))
    (hc : SeamEpidemics.allPhaseEq (L := L) (K := K) p n c) :
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEntryFromExactStep (L := L) (K := K) p n c'} = 0 := by
  classical
  have hbad_meas : MeasurableSet
      {c' : Config (AgentState L K) | ¬ SeamEntryFromExactStep (L := L) (K := K) p n c'} :=
    MeasurableSet.of_discrete
  rw [pow_one]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ hbad_meas, Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad ⟨c, hc, hsupp⟩

/-- **Reset-gated entry provenance.**  Genuine exact-step provenance is only NEEDED for the reset
seams `p ∈ {5,6,7}` (where the no-overshoot tail must start at a full-counter seam entry).  Off the
reset band the predicate is vacuously true, so the assembly carries one uniform field whose discharge
is trivial off-band and the genuine `exactStep` engine on-band. -/
def SeamEntryExactIfReset (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (5 ≤ p ∧ p ≤ 7) → SeamEntryFromExactStep (L := L) (K := K) p n c

/-- **Reset-gated measure-zero supply** (`allPhaseEq` only required on the reset band).  Off-band the
complement is empty; on-band the `allPhaseEq` witness drives `exactStep_measure_zero_of_allPhaseEq`. -/
theorem exactIfReset_measure_zero_of_allPhaseEqOnReset
    (p n : ℕ) (c : Config (AgentState L K))
    (hc : (5 ≤ p ∧ p ≤ 7) → SeamEpidemics.allPhaseEq (L := L) (K := K) p n c) :
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEntryExactIfReset (L := L) (K := K) p n c'} = 0 := by
  classical
  by_cases hp : 5 ≤ p ∧ p ≤ 7
  · -- reset band: the gated complement is exactly `¬ exactStep`
    have hset :
        {c' : Config (AgentState L K) | ¬ SeamEntryExactIfReset (L := L) (K := K) p n c'}
          = {c' | ¬ SeamEntryFromExactStep (L := L) (K := K) p n c'} := by
      ext c'
      simp only [Set.mem_setOf_eq, SeamEntryExactIfReset]
      constructor
      · intro h he; exact h (fun _ => he)
      · intro h hg; exact h (hg hp)
    rw [hset]
    exact exactStep_measure_zero_of_allPhaseEq (L := L) (K := K) p n c (hc hp)
  · -- off the reset band: the gated predicate is vacuously true, complement is empty
    have hempty :
        {c' : Config (AgentState L K) | ¬ SeamEntryExactIfReset (L := L) (K := K) p n c'} = ∅ := by
      ext c'
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not,
        SeamEntryExactIfReset]
      intro hreset; exact absurd hreset hp
    rw [hempty]
    simp

/--
Status marker for import smoke tests.
-/
theorem seam_entry_phase_ceiling_status : True := trivial

end SeamEntryPhaseCeiling
end ExactMajority

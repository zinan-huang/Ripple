-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockNormalBarrierStarts.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkInitialization
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalRiseStoppedLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkSeedTail

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalBarrierStarts

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkInitialization
  PhaseThreeClockEarlyMarkSeedTail PhaseThreeClockNormalRise
  PhaseThreeClockNormalRiseStoppedLaw PhaseThreeClockSeedTails

variable {L K n : ℕ}

theorem earlyCutoffFibre_unique (init : Cfg L K) (s ell cutoff u v : ℕ)
    (ω : Ω L K) (hu : ω ∈ earlyCutoffFibre init s ell cutoff u)
    (hv : ω ∈ earlyCutoffFibre init s ell cutoff v) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · exact False.elim (not_lt_of_ge hu.2.1 (hv.2.2 u hu.1 h))
  · exact h
  · exact False.elim (not_lt_of_ge hv.2.1 (hu.2.2 v hv.1 h))

theorem exists_earlyCutoffFibre (init : Cfg L K) (s ell cutoff v : ℕ)
    (ω : Ω L K) (hsv : s ≤ v)
    (hv : cutoff ≤ frontCount (virtualLabels init ω v) ell) :
    ∃ u ≤ v, ω ∈ earlyCutoffFibre init s ell cutoff u := by
  classical
  have hex : ∃ u, s ≤ u ∧ cutoff ≤ frontCount (virtualLabels init ω u) ell :=
    ⟨v, hsv, hv⟩
  let u := Nat.find hex
  have hu : s ≤ u ∧ cutoff ≤ frontCount (virtualLabels init ω u) ell :=
    Nat.find_spec hex
  refine ⟨u, Nat.find_min' hex ⟨hsv, hv⟩, hu.1, hu.2, ?_⟩
  intro t hst htu
  by_contra hnot
  have hmin : u ≤ t :=
    Nat.find_min' hex ⟨hst, Nat.le_of_not_lt hnot⟩
  omega

theorem earlyCutoff_prefix_measurable (init : Cfg L K) (s ell cutoff u : ℕ)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E) :
    MeasurableSet[pairLogFiltration L K u]
      (E ∩ earlyCutoffFibre init s ell cutoff u) := by
  by_cases hsu : s ≤ u
  · exact (((pairLogFiltration L K).mono hsu) _ hE).inter
      (earlyCutoffFibre_measurable init s ell cutoff u)
  · have he : E ∩ earlyCutoffFibre init s ell cutoff u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hsu hω.2.1
    rw [he]
    exact MeasurableSpace.measurableSet_empty _

def observedCutoffPrefix (init : InputCfg n) (s ell cutoff : ℕ)
    (E : Set (InputLog n)) (u : ℕ) : Set (InputLog n) :=
  (E ∩ earlyCutoffFibre init s ell cutoff u) ∩ phaseCapAt init u

theorem observedCutoffPrefix_measurable (init : InputCfg n)
    (s ell cutoff u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    MeasurableSet[pairLogFiltration _ _ u]
      (observedCutoffPrefix init s ell cutoff E u) :=
  (earlyCutoff_prefix_measurable init s ell cutoff u E hE).inter
    (phaseCapAt_measurable init u)

theorem observedCutoffPrefix_pairwiseDisjoint (init : InputCfg n)
    (s ell cutoff : ℕ) (E : Set (InputLog n)) :
    Pairwise (fun u v => Disjoint
      (observedCutoffPrefix init s ell cutoff E u)
      (observedCutoffPrefix init s ell cutoff E v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro ω hu hv
  exact huv (earlyCutoffFibre_unique init s ell cutoff u v ω hu.1.2 hv.1.2)

theorem observedCutoffPrefix_tsum_le (init : InputCfg n)
    (s ell cutoff : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    (∑' u, law init (observedCutoffPrefix init s ell cutoff E u)) ≤
      law init E := by
  rw [← measure_iUnion (observedCutoffPrefix_pairwiseDisjoint init s ell cutoff E)
    (fun u => ((pairLogFiltration _ _).le u) _
      (observedCutoffPrefix_measurable init s ell cutoff u E hE))]
  apply measure_mono
  intro ω hω
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
  exact hu.1.1

theorem observedCutoffPrefix_guard (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell cutoff u : ℕ) (hell : 1 ≤ ell)
    (E : Set (InputLog n))
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s))
    (ω : InputLog n) (hω : ω ∈ observedCutoffPrefix init s ell cutoff E u) :
    CurrentMarkedGuard init C ell cutoff s u ω := by
  have hs := hseed ω hω.1.1
  exact currentMarkedGuard_of_seedPrefix init ω C ell cutoff s u
    hs.1 hω.1.2.1 hell hs.2 hω.2

theorem observedCutoffPrefix_front_lower (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell u : ℕ) (E : Set (InputLog n))
    (ω : InputLog n)
    (hω : ω ∈ observedCutoffPrefix init s ell
      (PhaseThreeModel.Numeric.earlyCutoff C.card) E u) :
    (C.card : ℝ) ^ (51 / 100 : ℝ) ≤
      (frontCount (virtualLabels init ω u) ell : ℝ) := by
  have hcast : (PhaseThreeModel.Numeric.earlyCutoff C.card : ℝ) ≤
      (frontCount (virtualLabels init ω u) ell : ℝ) := by
    exact_mod_cast hω.1.2.2.1
  exact (Nat.le_ceil _).trans hcast

theorem observedCutoffPrefix_normal_zero (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell cutoff u : ℕ)
    (hell : 1 ≤ ell)
    (hlevel : ell + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n))
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s))
    (ω : InputLog n) (hω : ω ∈ observedCutoffPrefix init s ell cutoff E u) :
    normalCount (virtualLabels init ω u) (markedAt init C ell cutoff s ω u) ell = 0 := by
  have hs := hseed ω hω.1.1
  exact normalCount_zero_at_earlyCutoff init ω C ell cutoff s u
    hs.1 hell hlevel hs.2 hω.2 hω.1.2

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalBarrierStarts

end

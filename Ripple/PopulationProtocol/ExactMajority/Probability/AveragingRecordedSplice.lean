-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingRecordedSplice.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedExpectation
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer

/-!
# Returning recorded-continuation estimates to the original law

The prefix event is arbitrary and measurable at the start. The future event
is integrated under the ordinary trajectory kernel. No future success event
is used as a conditional probability space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingRecordedSplice

open TimeTheorem PairLog PhaseOneDrain AveragingRecordedExpectation

variable {L K : ℕ}

theorem recordedFuture_prefix_map (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    Measure.map (frestrictLe (π := fun _ : ℕ => Draw L K) s)
      (recordedFuture init s p) = Measure.dirac p := by
  unfold recordedFuture
  rw [Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => Draw L K), Kernel.partialTraj_self, Kernel.id_apply]

theorem recordedFuture_prefix_mass (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (A : Set ((i : Finset.Iic s) → Draw L K)) :
    recordedFuture init s p
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} =
      Measure.dirac p A := by
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  change recordedFuture init s p
    (frestrictLe (π := fun _ : ℕ => Draw L K) s ⁻¹' A) = _
  rw [← Measure.map_apply
    (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) s) hA,
    recordedFuture_prefix_map]

theorem law_recordedFuture_integral (init : Cfg L K) (s : ℕ)
    (B : Set (Ω L K)) (hB : MeasurableSet B) :
    law init B =
      ∫⁻ p, recordedFuture init s p B
        ∂Kernel.partialTraj (X := fun _ : ℕ => Draw L K)
          (fun t => pairKernel init t) 0 s (fun _ => none) := by
  change
    Kernel.traj (X := fun _ : ℕ => Draw L K)
      (fun t => pairKernel init t) 0 (fun _ => none) B = _
  rw [← Kernel.traj_comp_partialTraj
    (X := fun _ : ℕ => Draw L K) (κ := fun t => pairKernel init t)
    (a := 0) (b := s) (Nat.zero_le s)]
  exact Kernel.comp_apply' _ _ _ hB

open Classical in
theorem law_prefix_joint_bound (init : Cfg L K) (s : ℕ)
    (A : Set ((i : Finset.Iic s) → Draw L K))
    (B : Set (Ω L K)) (hB : MeasurableSet B) (ε : ℝ≥0∞)
    (hlocal : ∀ p ∈ A, recordedFuture init s p B ≤ ε) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧ ω ∈ B} ≤
      ε * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let P : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hP : MeasurableSet P :=
    hA.preimage (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) s)
  have hpoint (p : (i : Finset.Iic s) → Draw L K) :
      recordedFuture init s p (P ∩ B) ≤ A.indicator (fun _ => ε) p := by
    by_cases hp : p ∈ A
    · rw [Set.indicator_of_mem hp]
      exact (measure_mono Set.inter_subset_right).trans (hlocal p hp)
    · rw [Set.indicator_of_notMem hp]
      calc
        recordedFuture init s p (P ∩ B) ≤ recordedFuture init s p P :=
          measure_mono Set.inter_subset_left
        _ = Measure.dirac p A := recordedFuture_prefix_mass init s p A
        _ = 0 := by rw [Measure.dirac_apply' p hA]; simp [hp]
  change law init (P ∩ B) ≤ ε * law init P
  calc
    law init (P ∩ B) =
        ∫⁻ p, recordedFuture init s p (P ∩ B)
          ∂Kernel.partialTraj (X := fun _ : ℕ => Draw L K)
            (fun t => pairKernel init t) 0 s (fun _ => none) :=
      law_recordedFuture_integral init s (P ∩ B) (hP.inter hB)
    _ ≤ ∫⁻ p, A.indicator (fun _ => ε) p
          ∂Kernel.partialTraj (X := fun _ : ℕ => Draw L K)
            (fun t => pairKernel init t) 0 s (fun _ => none) :=
      lintegral_mono hpoint
    _ = ε * Kernel.partialTraj (X := fun _ : ℕ => Draw L K)
          (fun t => pairKernel init t) 0 s (fun _ => none) A :=
      lintegral_indicator_const hA ε
    _ = ε * law init P := by rw [← law_prefix init s A]

/-- Uniform local estimates over recorded prefixes splice at a pair-log
stopping time. The future event may depend on its finite start time. -/
theorem law_at_past_time_bound (init : Cfg L K)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ)
    (B : ℕ → Set (Ω L K)) (hB : ∀ s, MeasurableSet (B s))
    (ε : ℝ≥0∞)
    (hlocal : ∀ s p, recordedFuture init s p (B s) ≤ ε) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧ ω ∈ B s} ≤ ε := by
  let E : Set (Ω L K) :=
    {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧ ω ∈ B s}
  apply PhaseThreeClockProducer.splice_of_local (law init) σ E ε
    (fun s => (pairLogFiltration L K).le s _ (hσ s))
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨A, hA, hEq⟩ := hσs
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈
          (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' A ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hEq]
    have hevent :
        E ∩ {ω | σ ω = (s : WithTop ℕ)} =
          {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧ ω ∈ B s} := by
      ext ω
      constructor
      · rintro ⟨⟨r, hr, hb⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨(hmem ω).mpr hs, hb⟩
      · rintro ⟨ha, hb⟩
        have hs := (hmem ω).mp ha
        exact ⟨⟨s, hs, hb⟩, hs⟩
    rw [hevent]
    have hbound := law_prefix_joint_bound init s A (B s) (hB s) ε
      (fun p _ => hlocal s p)
    simpa only [show {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} =
        {ω | σ ω = (s : WithTop ℕ)} from Set.ext hmem] using hbound

end Ripple.PopulationProtocol.ExactMajority.AveragingRecordedSplice

end

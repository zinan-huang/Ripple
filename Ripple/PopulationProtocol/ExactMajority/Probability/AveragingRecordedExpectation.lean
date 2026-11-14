-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingRecordedExpectation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PairLogAuxiliary
import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

/-!
# Bounded real increments on recorded continuations

The measure is the ordinary trajectory kernel after a recorded prefix.
The conditional expectation formula applies to arbitrary bounded real
functions of that prefix and the next sampled draw. It does not condition
on a future clock or averaging event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingRecordedExpectation

open TimeTheorem PairLog TraceDrain

variable {L K : ℕ}

def recordedFuture (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) : Measure (Ω L K) :=
  Kernel.traj (X := fun _ : ℕ => Draw L K)
    (fun t => pairKernel init t) s p

instance recordedFuture_isProbabilityMeasure (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) :
    IsProbabilityMeasure (recordedFuture init s p) := by
  unfold recordedFuture
  infer_instance

def shiftedPairLog (L K s : ℕ) : Filtration ℕ
    (inferInstance : MeasurableSpace (Ω L K)) where
  seq := fun t => pairLogFiltration L K (s + t)
  mono' := fun _ _ h => (pairLogFiltration L K).mono (Nat.add_le_add_left h s)
  le' := fun t => (pairLogFiltration L K).le (s + t)

def recordedNext (t : ℕ)
    (F : ((i : Finset.Iic t) → Draw L K) → Draw L K → ℝ)
    (ω : Ω L K) : ℝ :=
  F (frestrictLe (π := fun _ : ℕ => Draw L K) t ω) (ω (t + 1))

theorem recordedNext_stronglyMeasurable (t : ℕ)
    (F : ((i : Finset.Iic t) → Draw L K) → Draw L K → ℝ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)] (recordedNext t F) := by
  let H : ((i : Finset.Iic (t + 1)) → Draw L K) → ℝ :=
    fun p => F (restrictPrefix (Nat.le_succ t) p)
      (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)
  have hm := ((measurable_of_countable H).comp
    (measurable_pairLog_prefix L K (t + 1))).stronglyMeasurable
  simpa only [H, recordedNext, restrictPrefix_frestrictLe, frestrictLe_apply] using hm

theorem recordedNext_measurable (t : ℕ)
    (F : ((i : Finset.Iic t) → Draw L K) → Draw L K → ℝ) :
    Measurable (recordedNext t F) :=
  (recordedNext_stronglyMeasurable t F).measurable.mono
    ((pairLogFiltration L K).le (t + 1)) le_rfl

theorem recordedNext_integrable (μ : Measure (Ω L K)) [IsFiniteMeasure μ]
    (t : ℕ) (F : ((i : Finset.Iic t) → Draw L K) → Draw L K → ℝ)
    (b : ℝ) (hbound : ∀ p d, |F p d| ≤ b) :
    Integrable (recordedNext t F) μ := by
  refine (integrable_const b).mono'
    (recordedNext_measurable t F).aestronglyMeasurable ?_
  exact ae_of_all μ fun ω => by
    rw [Real.norm_eq_abs]
    exact hbound _ _

/-- Conditional expectation under a genuine recorded continuation. The
initial prefix time s may be any time not exceeding the observation time t. -/
theorem recordedNext_condExp (init : Cfg L K) (s t : ℕ) (hst : s ≤ t)
    (p : (i : Finset.Iic s) → Draw L K)
    (F : ((i : Finset.Iic t) → Draw L K) → Draw L K → ℝ)
    (b : ℝ) (hbound : ∀ q d, |F q d| ≤ b) :
    (recordedFuture init s p)[recordedNext t F | pairLogFiltration L K t]
      =ᵐ[recordedFuture init s p]
        (fun ω => ∫ d, F (frestrictLe (π := fun _ : ℕ => Draw L K) t ω) d
          ∂pairKernel init t (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)) := by
  let κ := fun u => pairKernel init u
  have hfm : Measurable (recordedNext t F) := recordedNext_measurable t F
  have hfi : Integrable (recordedNext t F) (recordedFuture init s p) :=
    recordedNext_integrable _ t F b hbound
  have hce :
      (recordedFuture init s p)[recordedNext t F | pairLogFiltration L K t]
        =ᵐ[recordedFuture init s p]
          (fun ω => ∫ y, recordedNext t F y
            ∂Kernel.traj (X := fun _ : ℕ => Draw L K) κ t
              (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)) := by
    change (Kernel.traj (X := fun _ : ℕ => Draw L K) κ s p)[recordedNext t F | Filtration.piLE (X := fun _ : ℕ => Draw L K) t]
        =ᵐ[Kernel.traj (X := fun _ : ℕ => Draw L K) κ s p] _
    exact Kernel.condExp_traj (X := fun _ : ℕ => Draw L K)
      (κ := κ) (a := s) (b := t) (x₀ := p) hst hfi
  have htraj (q : (i : Finset.Iic t) → Draw L K) :
      (∫ y, recordedNext t F y
        ∂Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q) =
      ∫ d, F q d ∂pairKernel init t q := by
    have hfreeze :
        (fun y : Ω L K =>
          recordedNext t F (Function.updateFinset y (Finset.Iic t) q)) =
        (fun y => F q (y (t + 1))) := by
      funext y
      dsimp [recordedNext]
      rw [frestrictLe_updateFinset]
      simp [Function.updateFinset, Finset.mem_Iic, Nat.not_succ_le_self]
    have hmap :
        Measure.map (fun y : Ω L K => y (t + 1))
          (Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q) =
        pairKernel init t q := by
      change (Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q).map
        (fun y : Ω L K => y (t + 1)) = κ t q
      rw [← Kernel.map_apply _ (measurable_pi_apply (t + 1)),
        Kernel.map_traj_succ_self]
    calc
      (∫ y, recordedNext t F y
          ∂Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q) =
          ∫ y, recordedNext t F (Function.updateFinset y (Finset.Iic t) q)
            ∂Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q :=
        Kernel.integral_traj (X := fun _ : ℕ => Draw L K) (κ := κ) q
          hfm.aestronglyMeasurable
      _ = ∫ y : Ω L K, F q (y (t + 1))
          ∂Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q := by rw [hfreeze]
      _ = ∫ d, F q d ∂pairKernel init t q := by
        rw [← hmap]
        exact (integral_map
          (μ := Kernel.traj (X := fun _ : ℕ => Draw L K) κ t q)
          (f := F q) (measurable_pi_apply (t + 1)).aemeasurable
          (measurable_of_countable (F q)).aestronglyMeasurable).symm
  filter_upwards [hce] with ω hω
  exact hω.trans (htraj (frestrictLe (π := fun _ : ℕ => Draw L K) t ω))

end Ripple.PopulationProtocol.ExactMajority.AveragingRecordedExpectation

end

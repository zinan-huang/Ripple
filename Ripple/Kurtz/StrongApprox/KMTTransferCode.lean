-- Ripple/Kurtz/StrongApprox/KMTTransferCode.lean
import Ripple.Kurtz.StrongApprox.KMTCoefficientAdapter
import Ripple.Kurtz.StrongApprox.CellRandomTimeEvaluation
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Code spaces for the KMT transfer to a prescribed Brownian family

A Brownian path is coded by its values on the nonnegative rationals, a Poisson path by its
unit-cell array (`poissonCellSeq`). Both code spaces are standard Borel. The reference joint law of
the all-time KMT coupling on the code spaces is disintegrated over the Brownian code, giving the
Markov kernel `kmtConditionalPoisson`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open AllTimeKMT AllTimeKurtzMoment AllTimeKMTPoissonLaw

abbrev KMTNonnegRat := {q : ℚ // 0 ≤ q}
abbrev KMTBrownianCode := KMTNonnegRat → ℝ
abbrev KMTPoissonCode := ℕ → CellSpace

example : StandardBorelSpace KMTBrownianCode := inferInstance
example : StandardBorelSpace KMTPoissonCode := inferInstance
example : Nonempty KMTPoissonCode := inferInstance

def nnrealOfNonnegRat (q : KMTNonnegRat) : ℝ≥0 := ⟨(q.1 : ℝ), by exact_mod_cast q.2⟩

def allTimeKMTBrownianCode (ω : AllTimeKMTSpace) : KMTBrownianCode :=
  fun q => allTimeKMTBrownian (q.1 : ℝ) ω

def brownianCodeOf {Ω : Type*} (β : ℝ≥0 → Ω → ℝ) (ω : Ω) : KMTBrownianCode :=
  fun q => β (nnrealOfNonnegRat q) ω

theorem measurable_allTimeKMTBrownianCode : Measurable allTimeKMTBrownianCode :=
  measurable_pi_iff.2 fun q => measurable_allTimeKMTBrownian (q.1 : ℝ)

theorem measurable_brownianCodeOf {Ω : Type*} [MeasurableSpace Ω] {β : ℝ≥0 → Ω → ℝ}
    (hβ : ∀ t, Measurable (β t)) : Measurable (brownianCodeOf β) :=
  measurable_pi_iff.2 fun _ => hβ _

/-! ## The reference joint law and its disintegration -/

def kmtReferenceJointLaw : Measure (KMTBrownianCode × KMTPoissonCode) :=
  allTimeKMTMeasure.map (fun ω => (allTimeKMTBrownianCode ω, poissonCellSeq ω))

def kmtBrownianCodeLaw : Measure KMTBrownianCode :=
  allTimeKMTMeasure.map allTimeKMTBrownianCode

theorem measurable_referencePair :
    Measurable (fun ω : AllTimeKMTSpace => (allTimeKMTBrownianCode ω, poissonCellSeq ω)) :=
  measurable_allTimeKMTBrownianCode.prodMk measurable_poissonCellSeq

instance : IsProbabilityMeasure kmtReferenceJointLaw := by
  unfold kmtReferenceJointLaw
  exact Measure.isProbabilityMeasure_map measurable_referencePair.aemeasurable

instance : IsProbabilityMeasure kmtBrownianCodeLaw := by
  unfold kmtBrownianCodeLaw
  exact Measure.isProbabilityMeasure_map measurable_allTimeKMTBrownianCode.aemeasurable

def kmtConditionalPoisson : Kernel KMTBrownianCode KMTPoissonCode :=
  kmtReferenceJointLaw.condKernel

instance : IsMarkovKernel kmtConditionalPoisson := by
  unfold kmtConditionalPoisson
  infer_instance

theorem kmtReferenceJointLaw_fst : kmtReferenceJointLaw.fst = kmtBrownianCodeLaw := by
  unfold kmtReferenceJointLaw kmtBrownianCodeLaw
  rw [Measure.fst, Measure.map_map measurable_fst measurable_referencePair]
  rfl

theorem kmtReferenceJointLaw_snd : kmtReferenceJointLaw.map Prod.snd = cellArrayLaw := by
  unfold kmtReferenceJointLaw
  rw [Measure.map_map measurable_snd measurable_referencePair]
  exact poissonCellSeq_law

theorem kmtConditionalPoisson_disintegrates :
    kmtBrownianCodeLaw ⊗ₘ kmtConditionalPoisson = kmtReferenceJointLaw := by
  rw [← kmtReferenceJointLaw_fst]
  exact Measure.disintegrate kmtReferenceJointLaw kmtReferenceJointLaw.condKernel

/-! ## The coefficient on codes -/

def kmtCodeXi (b : KMTBrownianCode) (c : KMTPoissonCode) : ℝ≥0∞ :=
  ⨆ q : KMTNonnegRat, ENNReal.ofReal
    (|(cellPath (q.1 : ℝ) c : ℝ) - (q.1 : ℝ) - b q| / Real.log (max 2 (q.1 : ℝ)))

theorem measurable_kmtCodeXi : Measurable (Function.uncurry kmtCodeXi) := by
  unfold kmtCodeXi Function.uncurry
  refine Measurable.iSup fun q => ?_
  have h1 : Measurable fun p : KMTBrownianCode × KMTPoissonCode =>
      (cellPath (q.1 : ℝ) p.2 : ℝ) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      ((measurable_cellPath (q.1 : ℝ)).comp measurable_snd)
  have h2 : Measurable fun p : KMTBrownianCode × KMTPoissonCode => p.1 q :=
    (measurable_pi_apply q).comp measurable_fst
  exact ((((h1.sub measurable_const).sub h2).abs).div_const _).ennreal_ofReal

theorem kmtCodeXi_reference (ω : AllTimeKMTSpace) :
    kmtCodeXi (allTimeKMTBrownianCode ω) (poissonCellSeq ω) = allTimeKMTXi ω := by
  unfold kmtCodeXi allTimeKMTXi
  refine iSup_congr fun q => ?_
  unfold allTimeKMTRatio allTimeKMTBrownianCode
  rw [allTimeKMTPoisson_eq_cellPath (by exact_mod_cast q.2) ω]

end Ripple.Kurtz.StrongApprox.KMTTransfer

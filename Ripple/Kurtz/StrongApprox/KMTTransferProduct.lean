-- Ripple/Kurtz/StrongApprox/KMTTransferProduct.lean
import Ripple.Kurtz.StrongApprox.KMTTransfer

/-!
# KMT transfer for a countable array of prescribed Brownian paths

Attach to a Brownian-code array `b : Ω → J → KMTBrownianCode` an array of Poisson cell codes
through the product kernel `independentPi J kmtConditionalPoisson`. Conditionally on the Brownian
array the Poisson codes are independent, and each coordinate carries the reference joint law.

Unconditionally, independence holds exactly where the Brownian paths are independent: for a
fixed `N`, over the channels `l`. No independence across different `N` is claimed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open AllTimeKMT AllTimeKurtzMoment AllTimeKMTPoissonLaw KMTTransferGeneral

instance instStdBorelPoissonArray (J : Type*) [Countable J] :
    StandardBorelSpace (J → KMTPoissonCode) :=
  StandardBorelSpace.pi_countable (α := fun _ : J => KMTPoissonCode)

variable {Ω : Type*} [MeasurableSpace Ω] {J : Type*}

def kmtArrayTransferMeasure (P : Measure Ω) (b : Ω → J → KMTBrownianCode)
    (hb : Measurable b) : Measure (Ω × (J → KMTPoissonCode)) :=
  P ⊗ₘ Kernel.comap (independentPi J kmtConditionalPoisson) b hb

theorem kmtTransferMeasure_congr {P : Measure Ω} {b₁ b₂ : Ω → KMTBrownianCode}
    {h₁ : Measurable b₁} {h₂ : Measurable b₂} (h : b₁ = b₂) :
    kmtTransferMeasure P b₁ h₁ = kmtTransferMeasure P b₂ h₂ := by
  subst h
  rfl

section Array

variable {P : Measure Ω} [IsProbabilityMeasure P] {b : Ω → J → KMTBrownianCode}
  {hb : Measurable b}

theorem measurable_coord (hb : Measurable b) (j : J) : Measurable fun ω => b ω j :=
  (measurable_pi_apply j).comp hb

instance : IsProbabilityMeasure (kmtArrayTransferMeasure P b hb) := by
  unfold kmtArrayTransferMeasure
  infer_instance

theorem kmtArray_fst : (kmtArrayTransferMeasure P b hb).fst = P :=
  Measure.fst_compProd _ _

/-- Given the Brownian array, the Poisson array has the product conditional law. -/
theorem kmtArray_condDistrib [Countable J] :
    condDistrib Prod.snd (fun z : Ω × (J → KMTPoissonCode) => b z.1)
        (kmtArrayTransferMeasure P b hb)
      =ᵐ[(kmtArrayTransferMeasure P b hb).map (fun z => b z.1)]
        independentPi J kmtConditionalPoisson :=
  condDistrib_marking P kmtConditionalPoisson b hb

/-- Each coordinate pair has the reference joint law. -/
theorem kmtArray_coordinate_jointLaw
    (hlaw : ∀ j, P.map (fun ω => b ω j) = kmtBrownianCodeLaw) (j : J) :
    (kmtArrayTransferMeasure P b hb).map (fun z => (b z.1 j, z.2 j)) = kmtReferenceJointLaw := by
  unfold kmtArrayTransferMeasure
  rw [map_marked_coord P kmtConditionalPoisson b hb j, hlaw j,
    kmtConditionalPoisson_disintegrates]

/-- Reading one coordinate gives the scalar transfer measure of that coordinate. -/
theorem kmtArray_coordinate_transfer (j : J) :
    (kmtArrayTransferMeasure P b hb).map (fun z => (z.1, z.2 j)) =
      kmtTransferMeasure P (fun ω => b ω j) (measurable_coord hb j) :=
  map_marked_coord_comap P kmtConditionalPoisson b hb j

theorem kmtArray_coordinate_poissonCode_law
    (hlaw : ∀ j, P.map (fun ω => b ω j) = kmtBrownianCodeLaw) (j : J) :
    (kmtArrayTransferMeasure P b hb).map (fun z => z.2 j) = cellArrayLaw := by
  have hm : Measurable (fun z : Ω × (J → KMTPoissonCode) => (z.1, z.2 j)) :=
    measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have h := kmtTransfer_poissonCode_law (hb := measurable_coord hb j) (hlaw j)
  rw [← kmtArray_coordinate_transfer j, Measure.map_map measurable_snd hm] at h
  exact h

theorem kmtArray_coordinate_Xi_law
    (hlaw : ∀ j, P.map (fun ω => b ω j) = kmtBrownianCodeLaw) (j : J) :
    (kmtArrayTransferMeasure P b hb).map (fun z => kmtCodeXi (b z.1 j) (z.2 j)) =
      allTimeKMTMeasure.map allTimeKMTXi := by
  have hm : Measurable (fun z : Ω × (J → KMTPoissonCode) => (z.1, z.2 j)) :=
    measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have h := kmtTransfer_Xi_law (hb := measurable_coord hb j) (hlaw j)
  rw [← kmtArray_coordinate_transfer j] at h
  have hX : Measurable (fun z : Ω × KMTPoissonCode => kmtCodeXi (b z.1 j) z.2) := by
    have h' : Measurable (Function.uncurry kmtCodeXi ∘
        fun z : Ω × KMTPoissonCode => (b z.1 j, z.2)) :=
      measurable_kmtCodeXi.comp (measurable_codePair (measurable_coord hb j))
    exact h'
  rw [Measure.map_map hX hm] at h
  exact h

/-- The KMT bound holds simultaneously for all channels and all real times. -/
theorem kmtArray_bound_ae [Countable J] {β : J → ℝ≥0 → Ω → ℝ}
    (hβ : ∀ j t, Measurable (β j t))
    (hbβ : ∀ j ω, b ω j = brownianCodeOf (β j) ω)
    (hcont : ∀ j, ∀ᵐ ω ∂P, Continuous fun t => β j t ω)
    (hlaw : ∀ j, P.map (brownianCodeOf (β j)) = kmtBrownianCodeLaw) :
    ∀ᵐ z ∂kmtArrayTransferMeasure P b hb, ∀ (j : J) (t : ℝ≥0),
      |(cellPath (t : ℝ) (z.2 j) : ℝ) - (t : ℝ) - β j t z.1| ≤
        (kmtCodeXi (b z.1 j) (z.2 j)).toReal * Real.log (max 2 (t : ℝ)) := by
  rw [ae_all_iff]
  intro j
  simp_rw [hbβ j]
  have hbj : (fun ω => b ω j) = brownianCodeOf (β j) := funext (hbβ j)
  have hm : Measurable (fun z : Ω × (J → KMTPoissonCode) => (z.1, z.2 j)) :=
    measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have hmeas : Measurable (brownianCodeOf (β j)) := measurable_brownianCodeOf (hβ j)
  have hb' := kmtTransfer_bound_ae (hβ j) (hcont j) (hlaw j)
  refine ae_of_ae_map (p := fun w : Ω × KMTPoissonCode => ∀ t : ℝ≥0,
      |(cellPath (t : ℝ) w.2 : ℝ) - (t : ℝ) - β j t w.1| ≤
        (kmtCodeXi (brownianCodeOf (β j) w.1) w.2).toReal * Real.log (max 2 (t : ℝ)))
    hm.aemeasurable ?_
  have hT : kmtTransferMeasure P (brownianCodeOf (β j)) hmeas =
      kmtTransferMeasure P (fun ω => b ω j) (measurable_coord hb j) := by
    exact (kmtTransferMeasure_congr hbj.symm)
  rw [kmtArray_coordinate_transfer j, ← hT]
  exact hb'

end Array

section FixedN

variable {ι : Type*} [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P]
  {b : Ω → ℕ × ι → KMTBrownianCode} {hb : Measurable b}

/-- For a fixed `N`, the marked pairs are independent over the channels `l` as soon as the
Brownian codes are. -/
theorem kmtArray_fixedN_iIndep_pairs
    (hind : ∀ N, iIndepFun (fun (l : ι) ω => b ω (N, l)) P) (N : ℕ) :
    iIndepFun (fun (l : ι) (z : Ω × (ℕ × ι → KMTPoissonCode)) => (b z.1 (N, l), z.2 (N, l)))
      (kmtArrayTransferMeasure P b hb) :=
  iIndepFun_pairs_of_independent_marking P kmtConditionalPoisson b (fun l => (N, l)) hb
    (fun _ _ h => (Prod.mk.inj h).2) (hind N)

theorem kmtArray_fixedN_iIndep
    (hind : ∀ N, iIndepFun (fun (l : ι) ω => b ω (N, l)) P) (N : ℕ) :
    iIndepFun (fun (l : ι) (z : Ω × (ℕ × ι → KMTPoissonCode)) => z.2 (N, l))
      (kmtArrayTransferMeasure P b hb) :=
  (kmtArray_fixedN_iIndep_pairs hind N).comp (fun _ p => p.2) (fun _ => measurable_snd)

end FixedN

/-! ## Adapter from independent processes to independent codes -/

def pathCode (x : ℝ≥0 → ℝ) : KMTBrownianCode := fun q => x (nnrealOfNonnegRat q)

theorem measurable_pathCode : Measurable pathCode :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

omit [MeasurableSpace Ω] in
theorem brownianCodeOf_eq_pathCode (β : ℝ≥0 → Ω → ℝ) :
    brownianCodeOf β = fun ω => pathCode (fun t => β t ω) := rfl

/-- If processes are independent as path-valued random elements, their codes are independent. -/
theorem brownianCode_iIndep_of_independentProcesses {ι : Type*} {P : Measure Ω}
    {β : ι → ℝ≥0 → Ω → ℝ}
    (hind : iIndepFun (fun (l : ι) ω => fun t => β l t ω) P) :
    iIndepFun (fun (l : ι) ω => brownianCodeOf (β l) ω) P :=
  hind.comp (fun _ => pathCode) (fun _ => measurable_pathCode)

end Ripple.Kurtz.StrongApprox.KMTTransfer

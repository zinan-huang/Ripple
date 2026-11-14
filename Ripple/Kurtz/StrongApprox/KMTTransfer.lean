-- Ripple/Kurtz/StrongApprox/KMTTransfer.lean
import Ripple.Kurtz.StrongApprox.KMTTransferCode
import Ripple.Kurtz.StrongApprox.KMTTransferGeneral

/-!
# KMT transfer to a prescribed Brownian path

Given a process `β` whose rational-time code has the law `kmtBrownianCodeLaw`, the measure
`P ⊗ₘ Kernel.comap kmtConditionalPoisson (brownianCodeOf β)` carries a Poisson cell array `z.2`
such that `(brownianCodeOf β z.1, z.2)` has the law of the all-time KMT coupling. The coefficient
`kmtCodeXi` has the law of `allTimeKMTXi`, and the KMT bound holds for all real times.

The hypothesis is equality of the full rational-time path-code laws, not one-time marginals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open AllTimeKMT AllTimeKurtzMoment AllTimeKMTPoissonLaw CellRandomTimeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω]

def kmtTransferMeasure (P : Measure Ω) (b : Ω → KMTBrownianCode) (hb : Measurable b) :
    Measure (Ω × KMTPoissonCode) :=
  P ⊗ₘ Kernel.comap kmtConditionalPoisson b hb

section Basic

variable {P : Measure Ω} {b : Ω → KMTBrownianCode} {hb : Measurable b}

theorem measurable_codePair (hb : Measurable b) :
    Measurable (fun z : Ω × KMTPoissonCode => (b z.1, z.2)) :=
  (hb.comp measurable_fst).prodMk measurable_snd

instance [IsProbabilityMeasure P] : IsProbabilityMeasure (kmtTransferMeasure P b hb) := by
  unfold kmtTransferMeasure
  infer_instance

theorem kmtTransfer_fst [IsProbabilityMeasure P] :
    (kmtTransferMeasure P b hb).fst = P :=
  Measure.fst_compProd _ _

theorem kmtTransfer_jointCodeLaw [IsProbabilityMeasure P]
    (hlaw : P.map b = kmtBrownianCodeLaw) :
    (kmtTransferMeasure P b hb).map (fun z => (b z.1, z.2)) = kmtReferenceJointLaw := by
  unfold kmtTransferMeasure
  rw [KMTTransferGeneral.map_compProd_comap, hlaw, kmtConditionalPoisson_disintegrates]

theorem kmtTransfer_poissonCode_law [IsProbabilityMeasure P]
    (hlaw : P.map b = kmtBrownianCodeLaw) :
    (kmtTransferMeasure P b hb).map Prod.snd = cellArrayLaw := by
  have h := congrArg (Measure.map Prod.snd) (kmtTransfer_jointCodeLaw (hb := hb) hlaw)
  rw [Measure.map_map measurable_snd (measurable_codePair hb)] at h
  exact h.trans kmtReferenceJointLaw_snd

theorem kmtTransfer_Xi_law [IsProbabilityMeasure P]
    (hlaw : P.map b = kmtBrownianCodeLaw) :
    (kmtTransferMeasure P b hb).map (fun z => kmtCodeXi (b z.1) z.2) =
      allTimeKMTMeasure.map allTimeKMTXi := by
  have h : (fun z : Ω × KMTPoissonCode => kmtCodeXi (b z.1) z.2) =
      Function.uncurry kmtCodeXi ∘ (fun z => (b z.1, z.2)) := rfl
  rw [h, ← Measure.map_map measurable_kmtCodeXi (measurable_codePair hb),
    kmtTransfer_jointCodeLaw (hb := hb) hlaw]
  unfold kmtReferenceJointLaw
  rw [Measure.map_map measurable_kmtCodeXi measurable_referencePair]
  congr 1
  funext ω
  exact kmtCodeXi_reference ω

theorem kmtTransfer_Xi_ae_ne_top [IsProbabilityMeasure P]
    (hlaw : P.map b = kmtBrownianCodeLaw) :
    ∀ᵐ z ∂kmtTransferMeasure P b hb, kmtCodeXi (b z.1) z.2 ≠ ⊤ := by
  have hm' : Measurable (Function.uncurry kmtCodeXi ∘ fun z : Ω × KMTPoissonCode => (b z.1, z.2)) :=
    measurable_kmtCodeXi.comp (measurable_codePair hb)
  have hm : Measurable (fun z : Ω × KMTPoissonCode => kmtCodeXi (b z.1) z.2) := hm'
  refine ae_of_ae_map (p := fun x : ℝ≥0∞ => x ≠ ⊤) hm.aemeasurable ?_
  rw [kmtTransfer_Xi_law (hb := hb) hlaw]
  exact (ae_map_iff measurable_allTimeKMTXi.aemeasurable
    (measurableSet_singleton ⊤).compl).2 allTimeKMTXi_ae_ne_top

end Basic

/-! ## The KMT bound for a fixed pair of paths -/

theorem nnrealOfNonnegRat_eq (q : KMTNonnegRat) :
    Real.toNNReal (q.1 : ℝ) = nnrealOfNonnegRat q := by
  apply NNReal.eq
  simp only [Real.coe_toNNReal', nnrealOfNonnegRat]
  exact max_eq_left (by exact_mod_cast q.2)

/-- Deterministic bound: a continuous path `β` with code `b` and a cell array with finite
code coefficient. -/
theorem kmtCodeXi_bound (β : ℝ≥0 → ℝ) (hβ : Continuous β) (c : KMTPoissonCode)
    (hXi : kmtCodeXi (fun q => β (nnrealOfNonnegRat q)) c ≠ ⊤) (t : ℝ≥0) :
    |(cellPath (t : ℝ) c : ℝ) - (t : ℝ) - β t| ≤
      (kmtCodeXi (fun q => β (nnrealOfNonnegRat q)) c).toReal * Real.log (max 2 (t : ℝ)) := by
  set f : ℝ → ℝ := fun s =>
    |(cellPath s c : ℝ) - s - β s.toNNReal| / Real.log (max 2 s) with hf
  have hlogpos : ∀ s : ℝ, 0 < Real.log (max 2 s) := fun s =>
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hrc : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt f (Ici s) s := by
    intro s hs
    have hc : ContinuousWithinAt (fun r : ℝ => (cellPath r c : ℝ)) (Ici s) s := by
      refine (continuousWithinAt_const (b := (cellPath s c : ℝ))).congr_of_eventuallyEq ?_ rfl
      filter_upwards [cellPath_eventually_right c s] with r hr using by simp [hr]
    have hβc : Continuous fun r : ℝ => β r.toNNReal := hβ.comp continuous_real_toNNReal
    have hnum : ContinuousWithinAt
        (fun r : ℝ => |(cellPath r c : ℝ) - r - β r.toNNReal|) (Ici s) s :=
      ((hc.sub continuous_id.continuousWithinAt).sub hβc.continuousWithinAt).abs
    have hden : ContinuousAt (fun r : ℝ => Real.log (max 2 r)) s :=
      ContinuousAt.log (continuous_const.max continuous_id).continuousAt
        (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).ne'
    exact hnum.div hden.continuousWithinAt (hlogpos s).ne'
  have hsup := KurtzLemmaThreeOne.iSup_real_eq_iSup_rat f hrc
  have hrat : kmtCodeXi (fun q => β (nnrealOfNonnegRat q)) c =
      ⨆ q : KMTNonnegRat, ENNReal.ofReal (f (q.1 : ℝ)) := by
    unfold kmtCodeXi
    refine iSup_congr fun q => ?_
    simp only [hf]
    rw [nnrealOfNonnegRat_eq]
  have hle : ENNReal.ofReal (f (t : ℝ)) ≤ kmtCodeXi (fun q => β (nnrealOfNonnegRat q)) c := by
    rw [hrat, ← hsup]
    exact le_iSup (fun s : {s : ℝ // 0 ≤ s} => ENNReal.ofReal (f s.1)) ⟨(t : ℝ), t.2⟩
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hXi).mp hle
  have hft : f (t : ℝ) = |(cellPath (t : ℝ) c : ℝ) - (t : ℝ) - β t| / Real.log (max 2 (t : ℝ)) := by
    simp only [hf, Real.toNNReal_coe]
  rw [hft] at hreal
  exact (div_le_iff₀ (hlogpos _)).mp hreal

/-- The KMT bound for every real time, for a prescribed continuous Brownian path whose
rational-time code has the law of the all-time KMT Brownian code. -/
theorem kmtTransfer_bound_ae [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (hβ : ∀ t, Measurable (β t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => β t ω)
    (hlaw : P.map (brownianCodeOf β) = kmtBrownianCodeLaw) :
    ∀ᵐ z ∂kmtTransferMeasure P (brownianCodeOf β) (measurable_brownianCodeOf hβ),
      ∀ t : ℝ≥0,
        |(cellPath (t : ℝ) z.2 : ℝ) - (t : ℝ) - β t z.1| ≤
          (kmtCodeXi (brownianCodeOf β z.1) z.2).toReal * Real.log (max 2 (t : ℝ)) := by
  have hfst : ∀ᵐ z ∂kmtTransferMeasure P (brownianCodeOf β) (measurable_brownianCodeOf hβ),
      Continuous fun t => β t z.1 := by
    refine ae_of_ae_map (p := fun ω => Continuous fun t => β t ω)
      measurable_fst.aemeasurable ?_
    have h : (kmtTransferMeasure P (brownianCodeOf β) (measurable_brownianCodeOf hβ)).map
        Prod.fst = P := kmtTransfer_fst
    rw [h]
    exact hcont
  filter_upwards [hfst, kmtTransfer_Xi_ae_ne_top (hb := measurable_brownianCodeOf hβ) hlaw]
    with z h1 h2 t
  exact kmtCodeXi_bound (fun t => β t z.1) h1 z.2 h2 t


/-- Non-vacuity witness: the hypotheses of `kmtTransfer_bound_ae` hold for the reference
all-time Brownian path itself. -/
theorem kmtTransfer_bound_ae_reference :
    ∀ᵐ z ∂kmtTransferMeasure allTimeKMTMeasure
        (brownianCodeOf fun (t : ℝ≥0) ω => allTimeKMTBrownian (t : ℝ) ω)
        (measurable_brownianCodeOf fun t => measurable_allTimeKMTBrownian (t : ℝ)),
      ∀ t : ℝ≥0,
        |(cellPath (t : ℝ) z.2 : ℝ) - (t : ℝ) - allTimeKMTBrownian (t : ℝ) z.1| ≤
          (kmtCodeXi (brownianCodeOf (fun (t : ℝ≥0) ω => allTimeKMTBrownian (t : ℝ) ω) z.1)
            z.2).toReal * Real.log (max 2 (t : ℝ)) :=
  kmtTransfer_bound_ae (fun t => measurable_allTimeKMTBrownian (t : ℝ))
    (Filter.Eventually.of_forall fun ω =>
      (AllTimeKMTLaws.allTimeKMTBrownian_continuous ω).comp NNReal.continuous_coe)
    rfl

end Ripple.Kurtz.StrongApprox.KMTTransfer

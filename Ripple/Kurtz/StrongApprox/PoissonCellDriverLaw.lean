-- Ripple/Kurtz/StrongApprox/PoissonCellDriverLaw.lean
import Ripple.Kurtz.StrongApprox.PoissonPath
import Mathlib.Probability.Independence.InfinitePi

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ → Ω → ℕ}

/-- A Poisson counting path read directly from its iid unit-cell data. -/
noncomputable def cellPath (t : ℝ) (c : ℕ → CellSpace) : ℕ :=
  (∑ i ∈ Finset.range ⌊t⌋₊, (c i).1) +
    cellHit (Ioc 0 (t - ⌊t⌋₊)) (c ⌊t⌋₊)

@[fun_prop]
theorem measurable_cellPath (t : ℝ) :
    Measurable (cellPath t) := by
  unfold cellPath
  exact
    (Finset.measurable_sum _ fun i _ =>
      measurable_fst.comp (measurable_pi_apply i)).add
      ((measurable_cellHit measurableSet_Ioc).comp
        (measurable_pi_apply ⌊t⌋₊))

/-- The complete counting path as a product-space random element. -/
noncomputable def cellPathMap (c : ℕ → CellSpace) : ℝ → ℕ :=
  fun t => cellPath t c

@[fun_prop]
theorem measurable_cellPathMap : Measurable cellPathMap := by
  apply measurable_pi_lambda
  intro t
  exact measurable_cellPath t

/-- All unit cells carried by one `PathSpace` sample. -/
def cellSequence (N : ℕ → Ω → ℕ) (x : PathSpace Ω) : ℕ → CellSpace :=
  fun i => cellData N i x

@[fun_prop]
theorem measurable_cellSequence
    (hNm : ∀ i, Measurable (N i)) :
    Measurable (cellSequence N) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_cellData hNm i

/-- `poisPath` is definitionally the readout of the complete cell sequence. -/
theorem poisPath_eq_cellPath
    (N : ℕ → Ω → ℕ) (t : ℝ) (x : PathSpace Ω) :
    poisPath N t x = cellPath t (cellSequence N x) := by
  rfl

/-- Universal iid law of the full unit-cell sequence. -/
noncomputable def cellArrayLaw : Measure (ℕ → CellSpace) :=
  Measure.infinitePi fun _ : ℕ => cellLaw

instance cellArrayLaw_isProbabilityMeasure :
    IsProbabilityMeasure cellArrayLaw := by
  unfold cellArrayLaw
  infer_instance

/-- The law of all cells is independent of the particular iid Poisson-count
realization used on the base space. -/
theorem cellSequence_law
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    (pathMeasure P).map (cellSequence N) = cellArrayLaw := by
  have hind := iIndepFun_cellData_path hNm hN
  calc
    (pathMeasure P).map (cellSequence N) =
        Measure.infinitePi fun i : ℕ =>
          (pathMeasure P).map (cellData N i) := by
      exact hind.map_fun_eq_infinitePi_map
        (fun i => measurable_cellData hNm i)
    _ = Measure.infinitePi (fun _ : ℕ => cellLaw) := by
      congr 1
      funext i
      exact pathMeasure_map_cellData hNm hNl i
    _ = cellArrayLaw := rfl

/-- Universal law of one complete unit-rate Poisson counting path. -/
theorem cellPath_law
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    (pathMeasure P).map (fun x t => poisPath N t x) =
      cellArrayLaw.map cellPathMap := by
  have hfun : (fun x : PathSpace Ω => fun t => poisPath N t x) =
      cellPathMap ∘ cellSequence N := by
    funext x t
    exact poisPath_eq_cellPath N t x
  rw [hfun, ← Measure.map_map measurable_cellPathMap
    (measurable_cellSequence hNm), cellSequence_law hNm hN hNl]

/-- A finite or arbitrary family of complete cell sequences. -/
abbrev CellFamily (ι : Type*) := ι → ℕ → CellSpace

/-- Universal independent family law on cell sequences. -/
noncomputable def cellFamilyLaw (ι : Type*) : Measure (CellFamily ι) :=
  Measure.infinitePi fun _ : ι => cellArrayLaw

instance cellFamilyLaw_isProbabilityMeasure (ι : Type*) :
    IsProbabilityMeasure (cellFamilyLaw ι) := by
  unfold cellFamilyLaw
  infer_instance

/-- Extract every channel's complete cell sequence. -/
def familyCellSequence (ι : Type*)
    (N : ℕ → Ω → ℕ) (ω : ι → PathSpace Ω) : CellFamily ι :=
  fun l => cellSequence N (ω l)

@[fun_prop]
theorem measurable_familyCellSequence
    (ι : Type*) (hNm : ∀ i, Measurable (N i)) :
    Measurable (familyCellSequence ι N) := by
  apply measurable_pi_lambda
  intro l
  exact (measurable_cellSequence hNm).comp (measurable_pi_apply l)

/-- Universal law of the complete independent cell family. -/
theorem familyCellSequence_law
    (ι : Type*)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    (familyMeasure ι P).map (familyCellSequence ι N) =
      cellFamilyLaw ι := by
  have hind : iIndepFun
      (fun l (ω : ι → PathSpace Ω) => cellSequence N (ω l))
      (familyMeasure ι P) :=
    iIndepFun_infinitePi
      (P := fun _ : ι => pathMeasure P)
      (X := fun _ x => cellSequence N x)
      (fun _ => measurable_cellSequence hNm)
  calc
    (familyMeasure ι P).map (familyCellSequence ι N) =
        Measure.infinitePi fun l : ι =>
          (familyMeasure ι P).map
            (fun ω : ι → PathSpace Ω => cellSequence N (ω l)) := by
      exact hind.map_fun_eq_infinitePi_map
        (fun l => (measurable_cellSequence hNm).comp
          (measurable_pi_apply l))
    _ = Measure.infinitePi (fun _ : ι => cellArrayLaw) := by
      congr 1
      funext l
      change Measure.map (cellSequence N ∘ fun ω : ι → PathSpace Ω => ω l)
        (familyMeasure ι P) = _
      rw [← Measure.map_map (measurable_cellSequence hNm)
        (measurable_pi_apply l), familyMeasure_map_eval,
        cellSequence_law hNm hN hNl]
    _ = cellFamilyLaw ι := rfl

/-- Driver family read from universal cell data. -/
noncomputable def cellFamilyDriver (ι : Type*)
    (c : CellFamily ι) : ι → ℝ → ℕ :=
  fun l t => cellPath t (c l)

@[fun_prop]
theorem measurable_cellFamilyDriver (ι : Type*) :
    Measurable (cellFamilyDriver ι) := by
  apply measurable_pi_lambda
  intro l
  apply measurable_pi_lambda
  intro t
  exact (measurable_cellPath t).comp (measurable_pi_apply l)

/-- Actual `poisFamily` driver as one path-space random element. -/
noncomputable def poissonFamilyDriver (ι : Type*)
    (N : ℕ → Ω → ℕ) (ω : ι → PathSpace Ω) : ι → ℝ → ℕ :=
  fun l t => poisFamily ι N l t ω

@[fun_prop]
theorem measurable_poissonFamilyDriver
    (ι : Type*) (hNm : ∀ i, Measurable (N i)) :
    Measurable (poissonFamilyDriver ι N) := by
  apply measurable_pi_lambda
  intro l
  apply measurable_pi_lambda
  intro t
  exact (measurable_poisPath hNm t).comp (measurable_pi_apply l)

/-- Pointwise factorization of the actual family driver through its cells. -/
theorem poissonFamilyDriver_eq_cellFamilyDriver
    (ι : Type*) (N : ℕ → Ω → ℕ)
    (ω : ι → PathSpace Ω) :
    poissonFamilyDriver ι N ω =
      cellFamilyDriver ι (familyCellSequence ι N ω) := by
  funext l t
  exact poisPath_eq_cellPath N t (ω l)

/-- Canonical law of an independent family of unit Poisson paths. -/
noncomputable def universalPoissonDriverLaw (ι : Type*) :
    Measure (ι → ℝ → ℕ) :=
  (cellFamilyLaw ι).map (cellFamilyDriver ι)

instance universalPoissonDriverLaw_isProbabilityMeasure (ι : Type*) :
    IsProbabilityMeasure (universalPoissonDriverLaw ι) := by
  unfold universalPoissonDriverLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_cellFamilyDriver ι).aemeasurable

/-- The full `poisFamily` path law is universal.  This is stronger than merely
matching all finite-dimensional distributions. -/
theorem poissonFamilyDriver_law
    (ι : Type*)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    (familyMeasure ι P).map (poissonFamilyDriver ι N) =
      universalPoissonDriverLaw ι := by
  have hfun : poissonFamilyDriver ι N =
      cellFamilyDriver ι ∘ familyCellSequence ι N := by
    funext ω
    exact poissonFamilyDriver_eq_cellFamilyDriver ι N ω
  rw [hfun, ← Measure.map_map (measurable_cellFamilyDriver ι)
    (measurable_familyCellSequence ι hNm),
    familyCellSequence_law ι hNm hN hNl]
  rfl

/-- Two count/uniform realizations satisfying the Poisson hypotheses have the
same complete driver-family law. -/
theorem poissonFamilyDriver_law_eq
    {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {N' : ℕ → Ω' → ℕ}
    (ι : Type*)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    (hNm' : ∀ i, Measurable (N' i))
    (hN' : iIndepFun N' P')
    (hNl' : ∀ i k,
      P' {ω | N' i ω = k} = ENNReal.ofReal (poisTerm k 1)) :
    (familyMeasure ι P).map (poissonFamilyDriver ι N) =
      (familyMeasure ι P').map (poissonFamilyDriver ι N') := by
  rw [poissonFamilyDriver_law ι hNm hN hNl,
    poissonFamilyDriver_law ι hNm' hN' hNl']

end Ripple.Kurtz.StrongApprox

end

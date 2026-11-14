-- Ripple/Kurtz/StrongApprox/PoissonCellTimeChangeFactor.lean
import Ripple.Kurtz.StrongApprox.PoissonCellDriverLaw
import Ripple.Kurtz.StrongApprox.PoissonTimeChangeGlobal
import Ripple.Kurtz.StrongApprox.ConstructedDensityProcess

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Canonical base carrying only the unit-cell counts. -/
abbrev CanonicalCountSpace := ℕ → ℕ

/-- Coordinate count on the canonical base. -/
def canonicalCount (i : ℕ) (z : CanonicalCountSpace) : ℕ := z i

@[fun_prop]
theorem measurable_canonicalCount (i : ℕ) :
    Measurable (canonicalCount i) :=
  measurable_pi_apply i

/-- Repackage a complete cell sequence as one canonical `PathSpace` sample. -/
def cellSample (c : ℕ → CellSpace) : PathSpace CanonicalCountSpace :=
  (fun i => (c i).1, fun i m => (c i).2 m)

@[fun_prop]
theorem measurable_cellSample : Measurable cellSample := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro m
    exact measurable_pi_apply m |>.comp
      (measurable_snd.comp (measurable_pi_apply i))

@[simp]
theorem cellData_cellSample (c : ℕ → CellSpace) (i : ℕ) :
    cellData canonicalCount i (cellSample c) = c i := by
  rfl

/-- Canonical repackaging preserves the complete counting path pointwise. -/
theorem poisPath_cellSample (c : ℕ → CellSpace) (t : ℝ) :
    poisPath canonicalCount t (cellSample c) = cellPath t c := by
  rw [poisPath_eq_cellPath]
  congr 1

/-- Canonical family sample associated to universal cell data. -/
def cellFamilySample (c : CellFamily ι) :
    ι → PathSpace CanonicalCountSpace :=
  fun l => cellSample (c l)

@[fun_prop]
theorem measurable_cellFamilySample :
    Measurable (cellFamilySample (ι := ι)) := by
  apply measurable_pi_lambda
  intro l
  exact measurable_cellSample.comp (measurable_pi_apply l)

/-- The canonical repackaging has exactly the universal driver. -/
theorem canonicalFamilyDriver_eq
    (c : CellFamily ι) :
    poissonFamilyDriver ι canonicalCount (cellFamilySample c) =
      cellFamilyDriver ι c := by
  funext l t
  exact poisPath_cellSample (c l) t

variable {β : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ} {b : ι → ℝ}

/-- The time-change solution selected on the canonical universal cell source. -/
noncomputable def cellTimeChangePath
    {n : ℕ} (hn : 0 < n)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (c : CellFamily ι) :
    ℝ → Fin d → ℝ :=
  globalPoissonPath (Ω := CanonicalCountSpace)
    (N := canonicalCount) (v := v)
    hn hβ0 hβb hβm x₀ (cellFamilySample c)

/-- Physical-time measurability supplied by the time-change solution. -/
theorem cellTimeChangePath_measurable_time
    {n : ℕ} (hn : 0 < n)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (c : CellFamily ι) :
    Measurable (cellTimeChangePath (β := β) (v := v) (b := b)
      hn hβ0 hβb hβm x₀ c) :=
  globalPoissonPath_measurable
    (N := canonicalCount) (v := v)
    hn hβ0 hβb hβm x₀ (cellFamilySample c)

/-- Repacking the source cells does not change any driver value. -/
theorem sourceDriver_eq_canonicalDriver
    (ω : ι → PathSpace Ω) (l : ι) (u : ℝ) :
    poisFamily ι canonicalCount l u
        (cellFamilySample (familyCellSequence ι N ω)) =
      poisFamily ι N l u ω := by
  change poisPath canonicalCount u
      (cellSample (cellSequence N (ω l))) =
    poisPath N u (ω l)
  rw [poisPath_cellSample, poisPath_eq_cellPath]

/-- The path `globalPoissonPath` factors pointwise through the universal cells on every
nonnegative time.  The proof uses extensional uniqueness, not sample
measurability. -/
theorem globalPoissonPath_eq_cellTimeChangePath
    {n : ℕ} (hn : 0 < n)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {t : ℝ} (ht : 0 ≤ t) :
    globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω t =
      cellTimeChangePath (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm x₀
          (familyCellSequence ι N ω) t := by
  let m := globalHorizonIndex t
  let canonicalSample :=
    cellFamilySample (familyCellSequence ι N ω)
  let X := globalPoissonPath (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω
  let Z := cellTimeChangePath (β := β) (v := v) (b := b)
    hn hβ0 hβb hβm x₀ (familyCellSequence ι N ω)
  have htm : t < (m : ℕ) :=
    lt_globalHorizonIndex_of_nonneg ht
  have hX : IsPoissonTimeChangeSolution (N := canonicalCount)
      n β v (m : ℝ) x₀ canonicalSample X := by
    refine
      { measurable_path := globalPoissonPath_measurable
          (N := N) (v := v)
          hn hβ0 hβb hβm x₀ ω
        initial_eq := globalPoissonPath_initial
          (N := N) (v := v)
          hn hβ0 hβb hβm x₀ ω
        equation := ?_ }
    intro s hs
    have heq := globalPoissonPath_equation
      (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω hs.1
    dsimp only [X]
    rw [heq]
    congr 1
  have hZ : IsPoissonTimeChangeSolution (N := canonicalCount)
      n β v (m : ℝ) x₀ canonicalSample Z := by
    refine
      { measurable_path := cellTimeChangePath_measurable_time
          (β := β) (v := v) (b := b)
          hn hβ0 hβb hβm x₀
            (familyCellSequence ι N ω)
        initial_eq := globalPoissonPath_initial
          (N := canonicalCount) (v := v)
          hn hβ0 hβb hβm x₀ canonicalSample
        equation := ?_ }
    intro s hs
    exact globalPoissonPath_equation
      (N := canonicalCount) (v := v)
      hn hβ0 hβb hβm x₀ canonicalSample hs.1
  have hEq := poisson_timeChangeSolution_unique
    (N := canonicalCount) hn hβ0 hβb hβm
      (Nat.cast_nonneg m) x₀ canonicalSample hX hZ
  exact hEq ⟨ht, htm.le⟩

/-- Nonnegative-time readout of the universal-cell solution. -/
noncomputable def cellTimeChangeNonnegative
    {n : ℕ} (hn : 0 < n)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (c : CellFamily ι) :
    ℝ≥0 → Fin d → ℝ :=
  fun t => cellTimeChangePath (β := β) (v := v) (b := b)
    hn hβ0 hβb hβm x₀ c t

/-- Nonnegative-time readout of the original path. -/
noncomputable def globalNonnegativePath
    {n : ℕ} (hn : 0 < n)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) :
    ℝ≥0 → Fin d → ℝ :=
  fun t => globalPoissonPath (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω t

/-- Pointwise factorization of the complete nonnegative path. -/
theorem globalNonnegativePath_eq_cellFactor
    {n : ℕ} (hn : 0 < n)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) :
    globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm x₀ ω =
      cellTimeChangeNonnegative (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm x₀
          (familyCellSequence ι N ω) := by
  funext t
  exact globalPoissonPath_eq_cellTimeChangePath
    (N := N) (β := β) (v := v) (b := b)
      hn hβ0 hβb hβm x₀ ω t.2

/-- The exact missing R1(c) object.  It is stronger than an arbitrary
measure-space isomorphism: it must preserve the time-change path pointwise. -/
structure AlignedCellCoupling
    (M : DensityDepCTMC d)
    (xLattice : Fin d → Fin (M.N + 1))
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (xDensity : Fin d → ℝ) : Type _ where
  map : CellFamily ι → DensityDepCTMC.ConstructedΩ M
  measurable_map : Measurable map
  map_law :
    (cellFamilyLaw ι).map map = DensityDepCTMC.constructedMeasure M
  path_eq : ∀ c t,
    cellTimeChangeNonnegative (β := β) (v := v) (b := b)
        M.hN hβ0 hβb hβm xDensity c t =
      DensityDepCTMC.constructedX M xLattice (map c) t

namespace AlignedCellCoupling

variable {M : DensityDepCTMC d}
variable {xLattice : Fin d → Fin (M.N + 1)}
variable {hβ0 : ∀ l y, 0 ≤ β l y}
variable {hβb : ∀ l y, β l y ≤ b l}
variable {hβm : ∀ l, Measurable (β l)}
variable {xDensity : Fin d → ℝ}

/-- An aligned coupling supplies the previously missing sample measurability
of the universal-cell solution. -/
theorem measurable_cellTimeChangeNonnegative
    (H : AlignedCellCoupling (v := v) M xLattice hβ0 hβb hβm xDensity) :
    Measurable
      (cellTimeChangeNonnegative (β := β) (v := v) (b := b)
        M.hN hβ0 hβb hβm xDensity) := by
  have hfun :
      cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity =
        fun (c : CellFamily ι) (t : ℝ≥0) =>
          DensityDepCTMC.constructedX M xLattice (H.map c) t := by
    funext c t
    exact H.path_eq c t
  rw [hfun]
  apply measurable_pi_lambda
  intro t
  exact (DensityDepCTMC.measurable_constructedX M xLattice t).comp
    H.measurable_map

/-- Canonical density path restricted to nonnegative time. -/
noncomputable def canonicalDensityNonnegative
    (M : DensityDepCTMC d)
    (records : M.canonicalRecordΩ) : ℝ≥0 → Fin d → ℝ :=
  fun t => M.scaledState
    ((M.canonicalPathMap records).frozenStateAt t)

@[fun_prop]
theorem canonicalDensityNonnegative_measurable
    (M : DensityDepCTMC d) :
    Measurable (canonicalDensityNonnegative M) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_of_countable M.scaledState).comp
    (M.measurable_canonicalPathMap_frozenStateAt t)

/-- The complete path law, restricted to the canonical nonnegative
readout. -/
private theorem constructed_nonnegative_path_law
    (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1)) :
    (DensityDepCTMC.constructedMeasure M).map
        (fun (ω : DensityDepCTMC.ConstructedΩ M) (t : ℝ≥0) =>
          DensityDepCTMC.constructedX M x₀ ω t) =
      (M.canonicalRecordMeasure x₀).map
        (canonicalDensityNonnegative M) := by
  let restrictNonnegative := fun X : ℝ → Fin d → ℝ =>
    fun t : ℝ≥0 => X t
  have hrestrict : Measurable restrictNonnegative := by
    apply measurable_pi_lambda
    intro t
    exact measurable_pi_apply (t : ℝ)
  have hfull := DensityDepCTMC.constructedX_path_law M x₀
  calc
    (DensityDepCTMC.constructedMeasure M).map
        (fun (ω : DensityDepCTMC.ConstructedΩ M) (t : ℝ≥0) =>
          DensityDepCTMC.constructedX M x₀ ω t) =
      ((DensityDepCTMC.constructedMeasure M).map
        (fun (ω : DensityDepCTMC.ConstructedΩ M) (t : ℝ) =>
          DensityDepCTMC.constructedX M x₀ ω t)).map
          restrictNonnegative := by
        rw [Measure.map_map hrestrict
          (DensityDepCTMC.measurable_constructedXPath M x₀)]
        rfl
    _ = ((M.canonicalRecordMeasure x₀).map
        (fun (records : M.canonicalRecordΩ) (t : ℝ) =>
          M.scaledState
            ((M.canonicalPathMap records).frozenStateAt t))).map
          restrictNonnegative := by rw [hfull]
    _ = (M.canonicalRecordMeasure x₀).map
        (canonicalDensityNonnegative M) := by
      rw [Measure.map_map hrestrict]
      · rfl
      · apply measurable_pi_lambda
        intro t
        exact (measurable_of_countable M.scaledState).comp
          (M.measurable_canonicalPathMap_frozenStateAt t)

/-- The universal-cell time-change path has the canonical density-dependent
CTMC law once the aligned coupling exists. -/
theorem cellTimeChange_canonical_law
    (H : AlignedCellCoupling (v := v) M xLattice hβ0 hβb hβm xDensity) :
    (cellFamilyLaw ι).map
        (cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity) =
      (M.canonicalRecordMeasure xLattice).map
        (canonicalDensityNonnegative M) := by
  have hfun :
      cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity =
        (fun (ω : DensityDepCTMC.ConstructedΩ M) (t : ℝ≥0) =>
          DensityDepCTMC.constructedX M xLattice ω t) ∘ H.map := by
    funext c t
    exact H.path_eq c t
  have hXp : Measurable (fun (ω : DensityDepCTMC.ConstructedΩ M) (t : ℝ≥0) =>
      DensityDepCTMC.constructedX M xLattice ω t) := by
    apply measurable_pi_lambda
    intro t
    exact DensityDepCTMC.measurable_constructedX M xLattice t
  rw [hfun, ← Measure.map_map hXp H.measurable_map,
    H.map_law]
  exact constructed_nonnegative_path_law M xLattice

end AlignedCellCoupling

/-- The aligned coupling also proves sample measurability of the original SIP
path through the universal-cell factorization. -/
theorem sipGlobalPoissonPath_measurable_sample
    (hNm : ∀ i, Measurable (N i))
    {M : DensityDepCTMC d}
    {xLattice : Fin d → Fin (M.N + 1)}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (xDensity : Fin d → ℝ)
    (H : AlignedCellCoupling (v := v) M xLattice hβ0 hβb hβm xDensity) :
    Measurable
      (globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
        M.hN hβ0 hβb hβm xDensity) := by
  have hfun :
      globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity =
        cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity ∘
            familyCellSequence ι N := by
    funext ω
    exact globalNonnegativePath_eq_cellFactor
      (N := N) (β := β) (v := v) (b := b)
        M.hN hβ0 hβb hβm xDensity ω
  rw [hfun]
  exact H.measurable_cellTimeChangeNonnegative.comp
    (measurable_familyCellSequence ι hNm)

/-- **Law transfer to the actual SIP-built time-change path.** -/
theorem sipGlobalPoissonPath_canonical_law
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    {M : DensityDepCTMC d}
    {xLattice : Fin d → Fin (M.N + 1)}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (xDensity : Fin d → ℝ)
    (H : AlignedCellCoupling (v := v) M xLattice hβ0 hβb hβm xDensity) :
    (familyMeasure ι P).map
        (globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity) =
      (M.canonicalRecordMeasure xLattice).map
        (AlignedCellCoupling.canonicalDensityNonnegative M) := by
  have hfactor :
      globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity =
        cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          M.hN hβ0 hβb hβm xDensity ∘
            familyCellSequence ι N := by
    funext ω
    exact globalNonnegativePath_eq_cellFactor
      (N := N) (β := β) (v := v) (b := b)
        M.hN hβ0 hβb hβm xDensity ω
  rw [hfactor, ← Measure.map_map
      H.measurable_cellTimeChangeNonnegative
      (measurable_familyCellSequence ι hNm),
    familyCellSequence_law ι hNm hN hNl]
  exact H.cellTimeChange_canonical_law

end Ripple.Kurtz.StrongApprox

end

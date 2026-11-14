-- Ripple/Kurtz/StrongApprox/DyadicConditionalPoissonPath.lean
import Ripple.Kurtz.StrongApprox.DyadicTreeFiniteHorizon
import Ripple.Kurtz.StrongApprox.PoissonDriverFamily
import Ripple.Kurtz.StrongApprox.CellFamilySimplePoints
import Ripple.Kurtz.StrongApprox.PoissonPathArrivals

/-!
# K19: conditional uniform filling of the committed dyadic Poisson skeleton

The first factor is the existing Gaussian/Poisson dyadic-tree source.  The
second factor contains one iid uniform sequence for every spatial unit cell.
The first `M_j` coordinates of row `j` are used, where `M_j` is the committed
Poisson count of that unit cell.

The finite-dimensional theorem is an identity of joint laws on `Fin r → ℕ`.
The final section records the corrected Brownian statement: the added position
array is independent of the tree, but the filled path is not independent of
the Gaussian skeleton because its integer values retain the original coupling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal NNReal BigOperators Nat

namespace Ripple.Kurtz.StrongApprox.DyadicConditionalPoissonPath

open DyadicGaussianTree DyadicPoissonTree DyadicSpatialSkeleton
open DyadicTreeFiniteHorizon
open PoissonDriverFamily
open CellFamilySimplePoints

/-! ## Product source and finite cell data -/

/-- One infinite uniform-position sequence for each of the `2^K` unit cells. -/
abbrev DyadicPositionArray (K : ℕ) :=
  Fin (2 ^ K) → ℕ → ℝ

/-- The finite outer product and countable inner products of uniform laws. -/
noncomputable def dyadicPositionMeasure (K : ℕ) :
    Measure (DyadicPositionArray K) :=
  Measure.infinitePi fun _ : Fin (2 ^ K) => posSeq

instance dyadicPositionMeasure_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (dyadicPositionMeasure K) := by
  unfold dyadicPositionMeasure
  infer_instance

/-- Tree noise together with the independent within-cell positions. -/
abbrev DyadicContinuousSpace (K : ℕ) :=
  DyadicNoiseSpace K × DyadicPositionArray K

noncomputable def dyadicContinuousMeasure (K : ℕ) :
    Measure (DyadicContinuousSpace K) :=
  (dyadicNoiseMeasure K).prod (dyadicPositionMeasure K)

instance dyadicContinuousMeasure_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (dyadicContinuousMeasure K) := by
  unfold dyadicContinuousMeasure
  infer_instance

/-- Every position row has the iid `U(0,1)` sequence law. -/
theorem dyadicPositionMeasure_map_eval
    (K : ℕ) (j : Fin (2 ^ K)) :
    (dyadicPositionMeasure K).map
        (fun u : DyadicPositionArray K => u j) = posSeq := by
  simpa only [dyadicPositionMeasure] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin (2 ^ K) => posSeq) j)

/-- The position rows are mutually independent. -/
theorem dyadicPositionRows_iIndep (K : ℕ) :
    iIndepFun (fun j (u : DyadicPositionArray K) => u j)
      (dyadicPositionMeasure K) :=
  iIndepFun_infinitePi
    (P := fun _ : Fin (2 ^ K) => posSeq)
    (X := fun _ => id) (fun _ => measurable_id)

/-- The count and position sequence attached to one spatial unit cell. -/
def dyadicCellData (K : ℕ) (j : Fin (2 ^ K))
    (x : DyadicContinuousSpace K) : CellSpace :=
  (spatialPoissonUnitIncrement K j x.1, x.2 j)

/-- All cell data on the finite dyadic horizon. -/
def dyadicCellBlock (K : ℕ) (x : DyadicContinuousSpace K) :
    Fin (2 ^ K) → CellSpace :=
  fun j => dyadicCellData K j x

@[fun_prop]
theorem measurable_spatialPoissonUnitIncrement
    (K : ℕ) (j : Fin (2 ^ K)) :
    Measurable (spatialPoissonUnitIncrement K j) :=
  (measurable_pi_apply (spatialLeafCell K j)).comp
    (poissonLevel_measurePreserving K K).measurable

@[fun_prop]
theorem measurable_dyadicCellData
    (K : ℕ) (j : Fin (2 ^ K)) :
    Measurable (dyadicCellData K j) :=
  ((measurable_spatialPoissonUnitIncrement K j).comp measurable_fst).prodMk
    ((measurable_pi_apply j).comp measurable_snd)

@[fun_prop]
theorem measurable_dyadicCellBlock (K : ℕ) :
    Measurable (dyadicCellBlock K) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_dyadicCellData K j

/-! ## A finite-cell counting path -/

/-- Extend a finite block by zero-count cells.  The default positions are
irrelevant because the corresponding count is zero. -/
def extendCellBlock (n : ℕ) (c : Fin n → CellSpace) : ℕ → CellSpace :=
  fun j => if h : j < n then c ⟨j, h⟩
    else ((0, fun _ : ℕ => (1 : ℝ)) : CellSpace)

@[fun_prop]
theorem measurable_extendCellBlock (n : ℕ) :
    Measurable (extendCellBlock n) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j < n
  · simpa [extendCellBlock, h] using
      (measurable_pi_apply (⟨j, h⟩ : Fin n))
  · simp only [extendCellBlock, h, dite_false]
    exact measurable_const

/-- Counting path carried by a finite family of unit cells. -/
noncomputable def finiteCellPath
    (n : ℕ) (c : Fin n → CellSpace) (t : ℝ) : ℕ :=
  cellPath t (extendCellBlock n c)

@[fun_prop]
theorem measurable_finiteCellPath (n : ℕ) (t : ℝ) :
    Measurable (fun c : Fin n → CellSpace => finiteCellPath n c t) :=
  (measurable_cellPath t).comp (measurable_extendCellBlock n)

/-- Natural-index count of an extended finite block. -/
def finiteCellCountNat (n : ℕ) (c : Fin n → CellSpace) (j : ℕ) : ℕ :=
  if h : j < n then (c ⟨j, h⟩).1 else 0

/-- Finite paths have the usual integer-time partial sums. -/
theorem finiteCellPath_natCast
    (n m : ℕ) (c : Fin n → CellSpace) :
    finiteCellPath n c (m : ℝ) =
      ∑ j ∈ Finset.range m, finiteCellCountNat n c j := by
  calc
    finiteCellPath n c (m : ℝ) =
        poisPath canonicalCount (m : ℝ)
          (cellSample (extendCellBlock n c)) :=
      (poisPath_cellSample (extendCellBlock n c) (m : ℝ)).symm
    _ = ∑ j ∈ Finset.range m,
          canonicalCount j (cellSample (extendCellBlock n c)).1 :=
      poisPath_natCast canonicalCount m
        (cellSample (extendCellBlock n c))
    _ = ∑ j ∈ Finset.range m, finiteCellCountNat n c j := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hjn : j < n
      · simp [canonicalCount, cellSample, extendCellBlock,
          finiteCellCountNat, hjn]
      · simp [canonicalCount, cellSample, extendCellBlock,
          finiteCellCountNat, hjn]

/-- On a bounded horizon the path is the sum of the visible pieces of all
finite cells. -/
theorem finiteCellPath_eq_sum
    (n : ℕ) (c : Fin n → CellSpace) {t : ℝ}
    (ht : t ≤ n) :
    finiteCellPath n c t =
      ∑ j : Fin n, cellHit (Ioc 0 (t - (j : ℕ))) (c j) := by
  have hlt : t < ((n + 1 : ℕ) : ℝ) := by
    exact lt_of_le_of_lt ht (by exact_mod_cast Nat.lt_succ_self n)
  calc
    finiteCellPath n c t =
        poisPath canonicalCount t
          (cellSample (extendCellBlock n c)) :=
      (poisPath_cellSample (extendCellBlock n c) t).symm
    _ = ∑ j ∈ Finset.range (n + 1),
          cellHit (Ioc 0 (t - j))
            (cellData canonicalCount j
              (cellSample (extendCellBlock n c))) :=
      poisPath_eq_sum canonicalCount hlt _
    _ = ∑ j : Fin n,
          cellHit (Ioc 0 (t - (j : ℕ))) (c j) := by
      simp only [cellData_cellSample, Finset.sum_range_succ]
      rw [← Fin.sum_univ_eq_sum_range]
      have hlast :
          cellHit (Ioc 0 (t - (n : ℝ)))
              (extendCellBlock n c n) = 0 := by
        simp [extendCellBlock, cellHit, hitCount]
      rw [hlast, add_zero]
      apply Finset.sum_congr rfl
      intro j _hj
      simp [extendCellBlock, j.isLt]

/-- Monotonicity is pointwise and does not require a probability hypothesis. -/
theorem finiteCellPath_mono
    (n : ℕ) (c : Fin n → CellSpace) {s t : ℝ} (hst : s ≤ t) :
    finiteCellPath n c s ≤ finiteCellPath n c t := by
  calc
    finiteCellPath n c s =
        poisPath canonicalCount s (cellSample (extendCellBlock n c)) :=
      (poisPath_cellSample (extendCellBlock n c) s).symm
    _ ≤ poisPath canonicalCount t (cellSample (extendCellBlock n c)) :=
      poisPath_mono canonicalCount hst _
    _ = finiteCellPath n c t :=
      poisPath_cellSample (extendCellBlock n c) t

/-- The finite path is constant on a right neighbourhood of every time. -/
theorem finiteCellPath_eventually_right
    (n : ℕ) (c : Fin n → CellSpace) (t : ℝ) :
    ∀ᶠ s in 𝓝[≥] t, finiteCellPath n c s = finiteCellPath n c t := by
  simpa only [finiteCellPath, poisPath_cellSample] using
    (poisPath_eventually_right canonicalCount t
      (cellSample (extendCellBlock n c)))

/-- Real-cast right continuity of every finite-cell path. -/
theorem finiteCellPath_continuousWithinAt
    (n : ℕ) (c : Fin n → CellSpace) (t : ℝ) :
    ContinuousWithinAt (fun s => (finiteCellPath n c s : ℝ)) (Ici t) t := by
  simpa only [finiteCellPath, poisPath_cellSample] using
    (continuousWithinAt_poisPath canonicalCount t
      (cellSample (extendCellBlock n c)))

/-! ## The committed continuous Poisson path -/

/-- Fill every committed unit count with its own independent uniform row. -/
noncomputable def committedContinuousPoisson
    (K : ℕ) (t : ℝ) (x : DyadicContinuousSpace K) : ℕ :=
  finiteCellPath (2 ^ K) (dyadicCellBlock K x) t

@[fun_prop]
theorem measurable_committedContinuousPoisson (K : ℕ) (t : ℝ) :
    Measurable (committedContinuousPoisson K t) :=
  (measurable_finiteCellPath (2 ^ K) t).comp
    (measurable_dyadicCellBlock K)

/-- Literal floor/current-cell formula requested in K19. -/
theorem committedContinuousPoisson_formula
    (K : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htn : t < (2 ^ K : ℕ))
    (x : DyadicContinuousSpace K) :
    committedContinuousPoisson K t x =
      DyadicSpatialSkeleton.spatialPoissonSkeleton K x.1 ⌊t⌋₊ +
        cellHit (Ioc 0 (t - ⌊t⌋₊))
          (dyadicCellData K ⟨⌊t⌋₊, (Nat.floor_lt ht0).2 htn⟩ x) := by
  have hf : ⌊t⌋₊ < 2 ^ K := (Nat.floor_lt ht0).2 htn
  unfold committedContinuousPoisson finiteCellPath cellPath
    DyadicSpatialSkeleton.spatialPoissonSkeleton
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro j hj
    have hjh : j < 2 ^ K :=
      (Finset.mem_range.mp hj).trans hf
    simp [extendCellBlock, dyadicCellBlock, dyadicCellData,
      spatialPoissonUnitIncrementNat, hjh]
  · simp [extendCellBlock, dyadicCellBlock, hf]

/-- Agreement with the committed integer skeleton, including the endpoint
`j = 2^K`. -/
theorem committedContinuousPoisson_natCast
    (K j : ℕ) (x : DyadicContinuousSpace K) :
    committedContinuousPoisson K (j : ℝ) x =
      DyadicSpatialSkeleton.spatialPoissonSkeleton K x.1 j := by
  simpa [committedContinuousPoisson, DyadicSpatialSkeleton.spatialPoissonSkeleton,
    finiteCellCountNat, dyadicCellBlock, dyadicCellData,
    spatialPoissonUnitIncrementNat] using
      (finiteCellPath_natCast (2 ^ K) j (dyadicCellBlock K x))

/-- Every path is nondecreasing. -/
theorem committedContinuousPoisson_mono
    (K : ℕ) (x : DyadicContinuousSpace K) {s t : ℝ} (hst : s ≤ t) :
    committedContinuousPoisson K s x ≤
      committedContinuousPoisson K t x :=
  finiteCellPath_mono (2 ^ K) (dyadicCellBlock K x) hst

/-- Every value is integer-valued, stated after coercion to `ℝ`. -/
theorem committedContinuousPoisson_integerValued
    (K : ℕ) (t : ℝ) (x : DyadicContinuousSpace K) :
    ∃ m : ℕ, (committedContinuousPoisson K t x : ℝ) = m :=
  ⟨committedContinuousPoisson K t x, rfl⟩

/-- Pointwise right continuity. -/
theorem committedContinuousPoisson_continuousWithinAt
    (K : ℕ) (t : ℝ) (x : DyadicContinuousSpace K) :
    ContinuousWithinAt
      (fun s => (committedContinuousPoisson K s x : ℝ)) (Ici t) t :=
  finiteCellPath_continuousWithinAt (2 ^ K) (dyadicCellBlock K x) t

/-! ## Finite labelled arrivals and unit jumps -/

/-- Labels of all arrivals in one finite cell block. -/
abbrev FiniteCellArrival {n : ℕ} (c : Fin n → CellSpace) :=
  Σ j : Fin n, Fin (c j).1

/-- Absolute time of one labelled arrival. -/
noncomputable def finiteCellArrivalTime {n : ℕ}
    (c : Fin n → CellSpace) (q : FiniteCellArrival c) : ℝ :=
  (q.1.1 : ℝ) + clip ((c q.1).2 q.2.1)

/-- On `[0,n]`, the finite-cell path is exactly the counting function of its
finite labelled arrival family. -/
theorem finiteCellPath_eq_finiteArrivalCount
    (n : ℕ) (c : Fin n → CellSpace) {t : ℝ} (ht : t ≤ n) :
    finiteCellPath n c t =
      finiteArrivalCount (finiteCellArrivalTime c) t := by
  rw [finiteCellPath_eq_sum n c ht]
  symm
  classical
  unfold finiteArrivalCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold cellHit hitCount finiteCellArrivalTime
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hq :
      (j.1 : ℝ) + clip ((c j).2 m.1) ≤ t
  · have hmem :
        clip ((c j).2 m.1) ∈ Ioc 0 (t - (j.1 : ℝ)) :=
      ⟨clip_pos _, by linarith⟩
    simp [hq, Set.indicator_of_mem hmem]
  · have hnot :
        clip ((c j).2 m.1) ∉ Ioc 0 (t - (j.1 : ℝ)) := by
      intro hm
      apply hq
      linarith [hm.2]
    simp [hq, Set.indicator_of_notMem hnot]

/-- Arrivals strictly before a time. -/
noncomputable def finiteArrivalLeftCount {κ : Type*} [Fintype κ]
    (a : κ → ℝ) (t : ℝ) : ℕ :=
  ((Finset.univ : Finset κ).filter fun q => a q < t).card

/-- Multiplicity of the jump at a time. -/
noncomputable def finiteArrivalMultiplicity {κ : Type*} [Fintype κ]
    (a : κ → ℝ) (t : ℝ) : ℕ :=
  ((Finset.univ : Finset κ).filter fun q => a q = t).card

/-- Decompose the counting value into arrivals before and exactly at `t`. -/
theorem finiteArrivalCount_eq_left_add_multiplicity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℝ) (t : ℝ) :
    finiteArrivalCount a t =
      finiteArrivalLeftCount a t + finiteArrivalMultiplicity a t := by
  classical
  unfold finiteArrivalCount finiteArrivalLeftCount finiteArrivalMultiplicity
  have hsplit :
      (Finset.univ.filter fun q : κ => a q ≤ t) =
        (Finset.univ.filter fun q : κ => a q < t) ∪
          (Finset.univ.filter fun q : κ => a q = t) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    exact le_iff_lt_or_eq
  have hdisj :
      Disjoint
        (Finset.univ.filter fun q : κ => a q < t)
        (Finset.univ.filter fun q : κ => a q = t) := by
    rw [Finset.disjoint_left]
    intro q hq hqt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hqt
    linarith
  rw [hsplit, Finset.card_union_of_disjoint hdisj]

/-- An injective arrival-time map has multiplicity at most one. -/
theorem finiteArrivalMultiplicity_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {a : κ → ℝ} (ha : Function.Injective a) (t : ℝ) :
    finiteArrivalMultiplicity a t ≤ 1 := by
  classical
  unfold finiteArrivalMultiplicity
  apply Finset.card_le_one.mpr
  intro q hq r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hr
  exact ha (hq.trans hr.symm)

/-- Pairwise distinct position coordinates in every finite cell. -/
def SimpleFiniteCellBlock {n : ℕ} (c : Fin n → CellSpace) : Prop :=
  ∀ j, SimplePositionSequence (c j).2

/-- Distinct positions within cells imply distinct absolute arrival times;
different cells lie in disjoint intervals `(j,j+1]`. -/
theorem finiteCellArrivalTime_injective
    {n : ℕ} {c : Fin n → CellSpace}
    (hsimple : SimpleFiniteCellBlock c) :
    Function.Injective (finiteCellArrivalTime c) := by
  intro q r htime
  have hqlo : (q.1.1 : ℝ) < finiteCellArrivalTime c q := by
    unfold finiteCellArrivalTime
    linarith [clip_pos ((c q.1).2 q.2.1)]
  have hqhi : finiteCellArrivalTime c q ≤ (q.1.1 : ℝ) + 1 := by
    unfold finiteCellArrivalTime
    linarith [clip_le_one ((c q.1).2 q.2.1)]
  have hrlo : (r.1.1 : ℝ) < finiteCellArrivalTime c r := by
    unfold finiteCellArrivalTime
    linarith [clip_pos ((c r.1).2 r.2.1)]
  have hrhi : finiteCellArrivalTime c r ≤ (r.1.1 : ℝ) + 1 := by
    unfold finiteCellArrivalTime
    linarith [clip_le_one ((c r.1).2 r.2.1)]
  have hjval : q.1.1 = r.1.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hstep : q.1.1 + 1 ≤ r.1.1 := Nat.succ_le_iff.mpr hlt
      have hstepR : (q.1.1 : ℝ) + 1 ≤ r.1.1 := by
        exact_mod_cast hstep
      linarith
    · have hstep : r.1.1 + 1 ≤ q.1.1 := Nat.succ_le_iff.mpr hlt
      have hstepR : (r.1.1 : ℝ) + 1 ≤ q.1.1 := by
        exact_mod_cast hstep
      linarith
  have hj : q.1 = r.1 := Fin.ext hjval
  rcases q with ⟨j, p⟩
  rcases r with ⟨j', p'⟩
  dsimp at hj
  subst j'
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Fin.ext
    by_contra hp
    apply hsimple j p.1 p'.1 hp
    unfold finiteCellArrivalTime at htime
    dsimp at htime
    linarith

/-- Simplicity of every position row. -/
def SimpleDyadicPositions
    (K : ℕ) (u : DyadicPositionArray K) : Prop :=
  ∀ j, SimplePositionSequence (u j)

/-- All finitely many position rows are simple almost surely. -/
theorem simpleDyadicPositions_ae_positions (K : ℕ) :
    ∀ᵐ u ∂dyadicPositionMeasure K, SimpleDyadicPositions K u := by
  unfold SimpleDyadicPositions
  rw [ae_all_iff]
  intro j
  exact MeasureTheory.ae_of_ae_map
    (p := fun u : ℕ → ℝ => SimplePositionSequence u)
    (measurable_pi_apply j).aemeasurable
    (by
      rw [dyadicPositionMeasure_map_eval K j]
      exact simplePositionSequence_ae)

/-- Lift row simplicity to the full tree-times-position source. -/
theorem simpleDyadicPositions_ae (K : ℕ) :
    ∀ᵐ x ∂dyadicContinuousMeasure K,
      SimpleDyadicPositions K x.2 := by
  refine MeasureTheory.ae_of_ae_map
    (p := fun u : DyadicPositionArray K => SimpleDyadicPositions K u)
    measurable_snd.aemeasurable ?_
  simpa only [dyadicContinuousMeasure, Measure.map_snd_prod,
    measure_univ, one_smul] using
      (simpleDyadicPositions_ae_positions K)

/-- Left count for the committed filled path. -/
noncomputable def dyadicArrivalLeftCount
    (K : ℕ) (x : DyadicContinuousSpace K) (t : ℝ) : ℕ :=
  finiteArrivalLeftCount
    (finiteCellArrivalTime (dyadicCellBlock K x)) t

/-- Jump multiplicity for the committed filled path. -/
noncomputable def dyadicArrivalMultiplicity
    (K : ℕ) (x : DyadicContinuousSpace K) (t : ℝ) : ℕ :=
  finiteArrivalMultiplicity
    (finiteCellArrivalTime (dyadicCellBlock K x)) t

/-- Exact jump decomposition on the finite horizon. -/
theorem committedContinuousPoisson_jumpDecomposition
    (K : ℕ) (x : DyadicContinuousSpace K) {t : ℝ}
    (ht : t ≤ (2 ^ K : ℕ)) :
    committedContinuousPoisson K t x =
      dyadicArrivalLeftCount K x t +
        dyadicArrivalMultiplicity K x t := by
  exact
    (finiteCellPath_eq_finiteArrivalCount
      (2 ^ K) (dyadicCellBlock K x) ht).trans
      (finiteArrivalCount_eq_left_add_multiplicity
        (finiteCellArrivalTime (dyadicCellBlock K x)) t)

/-- Almost surely every positive jump on `[0,2^K]` has size exactly one.  The
left count is the left limit because the path has finitely many arrivals. -/
theorem committedContinuousPoisson_unitJumps_ae (K : ℕ) :
    ∀ᵐ x ∂dyadicContinuousMeasure K,
      ∀ t : ℝ, 0 ≤ t → t ≤ (2 ^ K : ℕ) →
        committedContinuousPoisson K t x =
            dyadicArrivalLeftCount K x t +
              dyadicArrivalMultiplicity K x t ∧
          dyadicArrivalMultiplicity K x t ≤ 1 ∧
          (0 < committedContinuousPoisson K t x -
                dyadicArrivalLeftCount K x t →
            committedContinuousPoisson K t x -
                dyadicArrivalLeftCount K x t = 1) := by
  filter_upwards [simpleDyadicPositions_ae K] with x hsimple
  intro t _ht0 htn
  have hblock : SimpleFiniteCellBlock (dyadicCellBlock K x) := by
    intro j
    exact hsimple j
  have hinj := finiteCellArrivalTime_injective hblock
  have hdec := committedContinuousPoisson_jumpDecomposition K x htn
  have hmult := finiteArrivalMultiplicity_le_one hinj t
  change
    committedContinuousPoisson K t x =
        dyadicArrivalLeftCount K x t +
          dyadicArrivalMultiplicity K x t ∧
      dyadicArrivalMultiplicity K x t ≤ 1 ∧ _
  refine ⟨hdec, hmult, ?_⟩
  intro hpos
  have hm : dyadicArrivalMultiplicity K x t ≤ 1 := hmult
  omega

/-! ## Universal finite-cell law -/

/-- Product of `n` independent Poisson-count/uniform-position cell laws. -/
noncomputable def finiteCellLaw (n : ℕ) : Measure (Fin n → CellSpace) :=
  Measure.infinitePi fun _ : Fin n => cellLaw

instance finiteCellLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (finiteCellLaw n) := by
  unfold finiteCellLaw
  infer_instance

/-- The actual dyadic cell data are independent. -/
theorem dyadicCellData_iIndep (K : ℕ) :
    iIndepFun (dyadicCellData K) (dyadicContinuousMeasure K) := by
  simpa only [dyadicCellData, dyadicContinuousMeasure] using
    (iIndepFun_prod_pair
      (spatialPoissonUnitIncrement_iIndep K)
      (dyadicPositionRows_iIndep K)
      (fun j => measurable_spatialPoissonUnitIncrement K j)
      (fun j => measurable_pi_apply j))

/-- Each actual dyadic cell has the universal `cellLaw`. -/
theorem dyadicCellData_map
    (K : ℕ) (j : Fin (2 ^ K)) :
    (dyadicContinuousMeasure K).map (dyadicCellData K j) = cellLaw := by
  unfold dyadicContinuousMeasure cellLaw
  rw [← spatialPoissonUnitIncrement_map K j,
    ← dyadicPositionMeasure_map_eval K j,
    Measure.map_prod_map _ _
      (measurable_spatialPoissonUnitIncrement K j)
      (measurable_pi_apply j)]
  congr 1

/-- The whole finite block has the product cell law. -/
theorem dyadicCellBlock_law (K : ℕ) :
    (dyadicContinuousMeasure K).map (dyadicCellBlock K) =
      finiteCellLaw (2 ^ K) := by
  have hind := dyadicCellData_iIndep K
  calc
    (dyadicContinuousMeasure K).map (dyadicCellBlock K) =
        Measure.infinitePi fun j : Fin (2 ^ K) =>
          (dyadicContinuousMeasure K).map (dyadicCellData K j) := by
      exact hind.map_fun_eq_infinitePi_map
        (fun j => measurable_dyadicCellData K j)
    _ = Measure.infinitePi (fun _ : Fin (2 ^ K) => cellLaw) := by
      congr 1
      funext j
      exact dyadicCellData_map K j
    _ = finiteCellLaw (2 ^ K) := rfl

/-! ## Canonical comparison and finite-dimensional law -/

/-- First `n` cells of the canonical iid Poisson path source. -/
def canonicalCellBlock
    (n : ℕ) (x : PathSpace CanonicalCountSpace) : Fin n → CellSpace :=
  fun j => cellData canonicalCount j.1 x

@[fun_prop]
theorem measurable_canonicalCellBlock (n : ℕ) :
    Measurable (canonicalCellBlock n) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_cellData driver_measurable j.1

/-- The first `n` canonical cells have the same finite product law. -/
theorem canonicalCellBlock_law (n : ℕ) :
    (pathMeasure driverMeasure).map (canonicalCellBlock n) =
      finiteCellLaw n := by
  have hind : iIndepFun
      (fun j : Fin n => cellData canonicalCount j.1)
      (pathMeasure driverMeasure) :=
    (iIndepFun_cellData_path driver_measurable driver_indep).precomp
      Fin.val_injective
  calc
    (pathMeasure driverMeasure).map (canonicalCellBlock n) =
        Measure.infinitePi fun j : Fin n =>
          (pathMeasure driverMeasure).map
            (cellData canonicalCount j.1) := by
      exact hind.map_fun_eq_infinitePi_map
        (fun j => measurable_cellData driver_measurable j.1)
    _ = Measure.infinitePi (fun _ : Fin n => cellLaw) := by
      congr 1
      funext j
      exact pathMeasure_map_cellData
        driver_measurable driver_law j.1
    _ = finiteCellLaw n := rfl

/-- Restricting a complete cell array to its first `n` cells does not change
its path before or at time `n`. -/
theorem finiteCellPath_restrict_eq_cellPath
    (n : ℕ) (a : ℕ → CellSpace) {t : ℝ} (ht : t ≤ n) :
    finiteCellPath n (fun j => a j.1) t = cellPath t a := by
  have hlt : t < ((n + 1 : ℕ) : ℝ) := by
    exact lt_of_le_of_lt ht (by exact_mod_cast Nat.lt_succ_self n)
  symm
  calc
    cellPath t a =
        poisPath canonicalCount t (cellSample a) :=
      (poisPath_cellSample a t).symm
    _ = ∑ j ∈ Finset.range (n + 1),
          cellHit (Ioc 0 (t - j))
            (cellData canonicalCount j (cellSample a)) :=
      poisPath_eq_sum canonicalCount hlt _
    _ = ∑ j : Fin n,
          cellHit (Ioc 0 (t - (j : ℕ))) (a j.1) := by
      simp only [cellData_cellSample, Finset.sum_range_succ]
      rw [← Fin.sum_univ_eq_sum_range]
      have hlast : cellHit (Ioc 0 (t - (n : ℝ))) (a n) = 0 := by
        exact hitCount_Ioc_of_nonpos (by linarith) (a n).1 (a n).2
      rw [hlast, add_zero]
    _ = finiteCellPath n (fun j => a j.1) t :=
      (finiteCellPath_eq_sum n (fun j => a j.1) ht).symm

/-- Canonical finite block and canonical infinite path agree on `[0,n]`. -/
theorem canonicalFiniteCellPath_eq_poisPath
    (n : ℕ) {t : ℝ} (ht : t ≤ n)
    (x : PathSpace CanonicalCountSpace) :
    finiteCellPath n (canonicalCellBlock n x) t =
      poisPath canonicalCount t x := by
  calc
    finiteCellPath n (canonicalCellBlock n x) t =
        cellPath t (cellSequence canonicalCount x) := by
      exact finiteCellPath_restrict_eq_cellPath
        n (cellSequence canonicalCount x) ht
    _ = poisPath canonicalCount t x :=
      (poisPath_eq_cellPath canonicalCount t x).symm

/-- Increment vector of one finite cell block along a real grid. -/
def finiteIncrementVector
    (n : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ)
    (c : Fin n → CellSpace) : Fin r → ℕ :=
  fun i => finiteCellPath n c (t i.succ) -
    finiteCellPath n c (t i.castSucc)

@[fun_prop]
theorem measurable_finiteIncrementVector
    (n : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ) :
    Measurable (finiteIncrementVector n t) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_finiteCellPath n (t i.succ)).sub
    (measurable_finiteCellPath n (t i.castSucc))

/-- Product of the requested Poisson increment laws. -/
noncomputable def poissonIncrementProduct
    {r : ℕ} (t : Fin (r + 1) → ℝ) : Measure (Fin r → ℕ) :=
  Measure.infinitePi fun i : Fin r =>
    poisMeasure (t i.succ - t i.castSucc)

private theorem grid_time_nonneg
    {r : ℕ} {t : Fin (r + 1) → ℝ}
    (hzero : t 0 = 0) (ht : Monotone t) (i : Fin (r + 1)) :
    0 ≤ t i := by
  have h := ht (show (0 : Fin (r + 1)) ≤ i from bot_le)
  simpa only [hzero] using h

/-- Canonical joint increment law on a finite horizon. -/
theorem canonicalFiniteIncrementVector_law
    {r n : ℕ} (t : Fin (r + 1) → ℝ)
    (hzero : t 0 = 0) (hstrict : StrictMono t)
    (hlast : t (Fin.last r) ≤ n) :
    (pathMeasure driverMeasure).map
        (fun x => finiteIncrementVector n t
          (canonicalCellBlock n x)) =
      poissonIncrementProduct t := by
  have hmono : Monotone t := hstrict.monotone
  have hle : ∀ i : Fin (r + 1), t i ≤ n := fun i =>
    (hmono (Fin.le_last i)).trans hlast
  have hfun :
      (fun x : PathSpace CanonicalCountSpace =>
        finiteIncrementVector n t (canonicalCellBlock n x)) =
      (fun x i =>
        poisPath canonicalCount (t i.succ) x -
          poisPath canonicalCount (t i.castSucc) x) := by
    funext x i
    unfold finiteIncrementVector
    rw [canonicalFiniteCellPath_eq_poisPath n (hle i.succ),
      canonicalFiniteCellPath_eq_poisPath n (hle i.castSucc)]
  rw [hfun]
  have hind := hasIndepIncrements_poisPath
    driver_measurable driver_indep driver_law r t hmono
  have hmeas : ∀ i : Fin r, Measurable
      (fun x : PathSpace CanonicalCountSpace =>
        poisPath canonicalCount (t i.succ) x -
          poisPath canonicalCount (t i.castSucc) x) := fun i =>
    (measurable_poisPath driver_measurable (t i.succ)).sub
      (measurable_poisPath driver_measurable (t i.castSucc))
  calc
    (pathMeasure driverMeasure).map
        (fun x i =>
          poisPath canonicalCount (t i.succ) x -
            poisPath canonicalCount (t i.castSucc) x) =
      Measure.infinitePi fun i : Fin r =>
        (pathMeasure driverMeasure).map
          (fun x =>
            poisPath canonicalCount (t i.succ) x -
              poisPath canonicalCount (t i.castSucc) x) := by
        exact hind.map_fun_eq_infinitePi_map hmeas
    _ = Measure.infinitePi (fun i : Fin r =>
        poisMeasure (t i.succ - t i.castSucc)) := by
      congr 1
      funext i
      apply Measure.ext_of_singleton
      intro k
      rw [Measure.map_apply (hmeas i) (measurableSet_singleton k),
        poisMeasure_singleton]
      exact pathMeasure_increment_eq
        driver_measurable driver_indep driver_law
        (grid_time_nonneg hzero hmono i.castSucc)
        (hmono (Fin.castSucc_le_succ i)) k
    _ = poissonIncrementProduct t := rfl

/-- **K19 finite-dimensional law.**  The increments of the filled committed
path have the product of the corresponding Poisson laws. -/
theorem committedContinuousPoisson_incrementVector_law
    (K : ℕ) {r : ℕ} (t : Fin (r + 1) → ℝ)
    (hzero : t 0 = 0) (hstrict : StrictMono t)
    (hlast : t (Fin.last r) ≤ (2 ^ K : ℕ)) :
    (dyadicContinuousMeasure K).map
        (fun x => finiteIncrementVector (2 ^ K) t
          (dyadicCellBlock K x)) =
      poissonIncrementProduct t := by
  calc
    (dyadicContinuousMeasure K).map
        (fun x => finiteIncrementVector (2 ^ K) t
          (dyadicCellBlock K x)) =
      ((dyadicContinuousMeasure K).map (dyadicCellBlock K)).map
        (finiteIncrementVector (2 ^ K) t) :=
      (Measure.map_map
        (measurable_finiteIncrementVector (2 ^ K) t)
        (measurable_dyadicCellBlock K)).symm
    _ = (finiteCellLaw (2 ^ K)).map
        (finiteIncrementVector (2 ^ K) t) := by
      rw [dyadicCellBlock_law]
    _ = ((pathMeasure driverMeasure).map
          (canonicalCellBlock (2 ^ K))).map
        (finiteIncrementVector (2 ^ K) t) := by
      rw [canonicalCellBlock_law]
    _ = (pathMeasure driverMeasure).map
        (fun x => finiteIncrementVector (2 ^ K) t
          (canonicalCellBlock (2 ^ K) x)) :=
      Measure.map_map
        (measurable_finiteIncrementVector (2 ^ K) t)
        (measurable_canonicalCellBlock (2 ^ K))
    _ = poissonIncrementProduct t :=
      canonicalFiniteIncrementVector_law
        t hzero hstrict hlast

/-! ## Correct joint statement with the Gaussian skeleton -/

/-- The extension does not alter the tree marginal. -/
theorem dyadicContinuousMeasure_map_fst (K : ℕ) :
    (dyadicContinuousMeasure K).map Prod.fst = dyadicNoiseMeasure K := by
  unfold dyadicContinuousMeasure
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Any measurable tree event has exactly the same probability after adding
uniform positions.  This is the property used by K20's union bound. -/
theorem dyadicContinuousMeasure_treeEvent
    (K : ℕ) {A : Set (DyadicNoiseSpace K)} (hA : MeasurableSet A) :
    dyadicContinuousMeasure K (Prod.fst ⁻¹' A) =
      dyadicNoiseMeasure K A := by
  rw [← Measure.map_apply measurable_fst hA,
    dyadicContinuousMeasure_map_fst]

@[fun_prop]
theorem measurable_spatialGaussianUnitIncrement
    (K : ℕ) (j : Fin (2 ^ K)) :
    Measurable (spatialGaussianUnitIncrement K j) :=
  (measurable_pi_apply (spatialLeafCell K j)).comp
    (gaussianLevel_measurePreserving K K).measurable

@[fun_prop]
theorem measurable_spatialPoissonUnitIncrementNat
    (K j : ℕ) :
    Measurable (fun x : DyadicNoiseSpace K =>
      spatialPoissonUnitIncrementNat K x j) := by
  unfold spatialPoissonUnitIncrementNat
  split_ifs with h
  · exact measurable_spatialPoissonUnitIncrement K ⟨j, h⟩
  · exact measurable_const

@[fun_prop]
theorem measurable_spatialGaussianUnitIncrementNat
    (K j : ℕ) :
    Measurable (fun x : DyadicNoiseSpace K =>
      spatialGaussianUnitIncrementNat K x j) := by
  unfold spatialGaussianUnitIncrementNat
  split_ifs with h
  · exact measurable_spatialGaussianUnitIncrement K ⟨j, h⟩
  · exact measurable_const

@[fun_prop]
theorem measurable_spatialPoissonSkeleton
    (K t : ℕ) :
    Measurable (fun x : DyadicNoiseSpace K =>
      DyadicSpatialSkeleton.spatialPoissonSkeleton K x t) := by
  unfold DyadicSpatialSkeleton.spatialPoissonSkeleton
  exact Finset.measurable_sum _ fun j _ =>
    measurable_spatialPoissonUnitIncrementNat K j

@[fun_prop]
theorem measurable_spatialGaussianSkeleton
    (K t : ℕ) :
    Measurable (fun x : DyadicNoiseSpace K =>
      DyadicSpatialSkeleton.spatialGaussianSkeleton K x t) := by
  unfold DyadicSpatialSkeleton.spatialGaussianSkeleton
  exact Finset.measurable_sum _ fun j _ =>
    measurable_spatialGaussianUnitIncrementNat K j

/-- Integer-time Poisson/Gaussian skeleton pair on the original tree. -/
def treeIntegerSkeletonPair (K : ℕ) (x : DyadicNoiseSpace K) :
    (Fin (2 ^ K + 1) → ℕ) × (Fin (2 ^ K + 1) → ℝ) :=
  (fun j => DyadicSpatialSkeleton.spatialPoissonSkeleton K x j.1,
    fun j => DyadicSpatialSkeleton.spatialGaussianSkeleton K x j.1)

/-- The same pair, with the Poisson coordinate read from the filled path. -/
def continuousIntegerSkeletonPair
    (K : ℕ) (x : DyadicContinuousSpace K) :
    (Fin (2 ^ K + 1) → ℕ) × (Fin (2 ^ K + 1) → ℝ) :=
  (fun j => committedContinuousPoisson K (j.1 : ℝ) x,
    fun j => DyadicSpatialSkeleton.spatialGaussianSkeleton K x.1 j.1)

@[fun_prop]
theorem measurable_treeIntegerSkeletonPair (K : ℕ) :
    Measurable (treeIntegerSkeletonPair K) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro j
    exact measurable_spatialPoissonSkeleton K j.1
  · apply measurable_pi_lambda
    intro j
    exact measurable_spatialGaussianSkeleton K j.1

/-- Pointwise preservation of the original integer coupling. -/
theorem continuousIntegerSkeletonPair_eq
    (K : ℕ) (x : DyadicContinuousSpace K) :
    continuousIntegerSkeletonPair K x =
      treeIntegerSkeletonPair K x.1 := by
  apply Prod.ext
  · funext j
    exact committedContinuousPoisson_natCast K j.1 x
  · rfl

/-- **Corrected item 4.**  The joint law of the filled Poisson path at integer
times and the Gaussian integer skeleton is exactly the original dyadic-tree
joint law.  No independence between those two coordinates is asserted. -/
theorem continuousIntegerSkeletonPair_law (K : ℕ) :
    (dyadicContinuousMeasure K).map
        (continuousIntegerSkeletonPair K) =
      (dyadicNoiseMeasure K).map (treeIntegerSkeletonPair K) := by
  have hfun : continuousIntegerSkeletonPair K =
      treeIntegerSkeletonPair K ∘ Prod.fst := by
    funext x
    exact continuousIntegerSkeletonPair_eq K x
  rw [hfun, ← Measure.map_map
    (measurable_treeIntegerSkeletonPair K) measurable_fst,
    dyadicContinuousMeasure_map_fst]

/-!
THEOREM LIST
* `dyadicPositionRows_iIndep`, `dyadicCellBlock_law`
* `committedContinuousPoisson_formula`
* `committedContinuousPoisson_natCast`
* `committedContinuousPoisson_mono`
* `committedContinuousPoisson_continuousWithinAt`
* `committedContinuousPoisson_unitJumps_ae`
* `committedContinuousPoisson_incrementVector_law`
* `dyadicContinuousMeasure_treeEvent`
* `continuousIntegerSkeletonPair_law`

CLOSES
* Item 1: the tree product with finitely many independent `posSeq` rows, each
  itself a countable `Measure.infinitePi` product of `U(0,1)` coordinates.
* Item 2: the literal floor/current-cell formula, exact integer agreement,
  monotonicity, integer values, right continuity, and almost-sure simple jumps.
* Item 3: the joint `Measure.map` identity to the product of
  `poisMeasure (t_i-t_{i-1})`; conditional multinomial thinning and Poisson
  mixing are reused through the compiled cell-law/Poisson-path library.
* Item 4, corrected: the extension preserves the tree marginal and the exact
  integer Poisson/Gaussian joint law.  Ordinary independence is not claimed.

UNFINISHED
* Brownian bridge filling between consecutive integer times belongs to K20.
* No K19 mathematical premise is left open.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicConditionalPoissonPath

end

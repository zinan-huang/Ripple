-- Ripple/Kurtz/StrongApprox/DyadicInterpolationOvershoot.lean
import Ripple.Kurtz.StrongApprox.DyadicConditionalPoissonPath
import Ripple.Kurtz.StrongApprox.PoissonMgf

/-!
# K20: interpolation overshoot and finite-horizon assembly

Declarations used from
`DyadicConditionalPoissonPath.lean`:
* `committedContinuousPoisson_natCast`;
* `committedContinuousPoisson_mono`;
* `measurable_spatialPoissonUnitIncrement`;
* `measurable_spatialPoissonSkeleton` and
  `measurable_spatialGaussianSkeleton`;
* `dyadicContinuousMeasure_map_fst`.

The K18 input is
`DyadicTreeFiniteHorizon.committedSpatialSkeleton_finiteHorizon_tail`:
for `x >= 0`, the integer skeleton maximum above
`2094 * log(2^(K+1)) + x` has real probability at most
`6 * exp (-(9/16384) * x)`.

No cross-independence between the Poisson path and `W` is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal Nat

namespace Ripple.Kurtz.StrongApprox.DyadicInterpolationOvershoot

open DyadicGaussianTree DyadicFiniteHorizonUnion DyadicTreeFiniteHorizon
open DyadicTreePointTail DyadicSpatialSkeleton
open DyadicConditionalPoissonPath

/-! ## Abstract path data -/

/-- The deterministic interface needed by K20.  The continuous counting path
agrees with the committed Poisson skeleton at integers, and the supplied real
path agrees with the committed Gaussian skeleton there. -/
structure InterpolationData
    (K : ℕ) (Omega : Type*) [MeasurableSpace Omega] where
  tree : Omega → DyadicNoiseSpace K
  tree_measurable : Measurable tree
  poissonPath : Omega → ℝ → ℕ
  poisson_mono : ∀ omega, Monotone (poissonPath omega)
  poisson_integer : ∀ (omega : Omega) (j : ℕ),
    poissonPath omega (j : ℝ) =
      DyadicSpatialSkeleton.spatialPoissonSkeleton K (tree omega) j
  gaussianPath : Omega → ℝ → ℝ
  gaussian_integer : ∀ omega j, j ≤ dyadicHorizon K →
    gaussianPath omega (j : ℝ) =
      DyadicSpatialSkeleton.spatialGaussianSkeleton K (tree omega) j

/-- The `DyadicConditionalPoissonPath` product source instantiates the abstract Poisson half.  The
Brownian construction only has to supply `W` and its integer agreement. -/
def committedInterpolationData
    (K : ℕ) (W : DyadicContinuousSpace K → ℝ → ℝ)
    (hW : ∀ omega j, j ≤ dyadicHorizon K →
      W omega (j : ℝ) =
        DyadicSpatialSkeleton.spatialGaussianSkeleton K omega.1 j) :
    InterpolationData K (DyadicContinuousSpace K) where
  tree := Prod.fst
  tree_measurable := measurable_fst
  poissonPath := fun omega t => committedContinuousPoisson K t omega
  poisson_mono := fun omega _ _ hst =>
    committedContinuousPoisson_mono K omega hst
  poisson_integer := fun omega j =>
    committedContinuousPoisson_natCast K j omega
  gaussianPath := W
  gaussian_integer := hW

variable {K : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-- The committed count in spatial unit cell `j`. -/
noncomputable def poissonCellCount
    (D : InterpolationData K Omega)
    (j : Fin (dyadicHorizon K)) (omega : Omega) : ℕ :=
  spatialPoissonUnitIncrement K j (D.tree omega)

/-- Maximum of the `2^K` unit-cell counts. -/
noncomputable def poissonCellMaximum
    (D : InterpolationData K Omega) (omega : Omega) : ℝ :=
  (Finset.univ : Finset (Fin (dyadicHorizon K))).sup'
    ⟨⟨0, by unfold dyadicHorizon; positivity⟩, Finset.mem_univ _⟩
    (fun j => (poissonCellCount D j omega : ℝ))

/-- K18's maximum integer-skeleton discrepancy, pulled back by `D.tree`. -/
noncomputable def skeletonMaximum
    (D : InterpolationData K Omega) (omega : Omega) : ℝ :=
  committedSpatialKMTMaximum K (D.tree omega)

/-- Discrepancy at an integer time. -/
def integerDeviation
    (D : InterpolationData K Omega) (omega : Omega) (j : ℕ) : ℝ :=
  |(D.poissonPath omega (j : ℝ) : ℝ) -
      (j : ℝ) - D.gaussianPath omega (j : ℝ)|

/-- The committed cell count is the actual path increment across that unit
cell. -/
theorem poissonCellCount_eq_path_sub
    (D : InterpolationData K Omega) (omega : Omega)
    (j : Fin (dyadicHorizon K)) :
    D.poissonPath omega ((j.1 + 1 : ℕ) : ℝ) -
        D.poissonPath omega (j.1 : ℝ) =
      poissonCellCount D j omega := by
  rw [D.poisson_integer omega (j.1 + 1),
    D.poisson_integer omega j.1]
  simpa [dyadicHorizon, poissonCellCount] using
    spatialPoissonSkeleton_succ_sub K j.1
      (by simpa [dyadicHorizon] using j.2) (D.tree omega)

/-- Real-cast form of the preceding identity. -/
theorem poissonCellCount_cast_eq_path_sub
    (D : InterpolationData K Omega) (omega : Omega)
    (j : Fin (dyadicHorizon K)) :
    (poissonCellCount D j omega : ℝ) =
      (D.poissonPath omega ((j.1 + 1 : ℕ) : ℝ) : ℝ) -
        (D.poissonPath omega (j.1 : ℝ) : ℝ) := by
  have hmono :
      D.poissonPath omega (j.1 : ℝ) ≤
        D.poissonPath omega ((j.1 + 1 : ℕ) : ℝ) := by
    apply D.poisson_mono omega
    norm_num
  rw [← poissonCellCount_eq_path_sub D omega j,
    Nat.cast_sub hmono]

/-- Each cell count is bounded by the finite maximum. -/
theorem poissonCellCount_le_maximum
    (D : InterpolationData K Omega) (omega : Omega)
    (j : Fin (dyadicHorizon K)) :
    (poissonCellCount D j omega : ℝ) ≤
      poissonCellMaximum D omega := by
  unfold poissonCellMaximum
  exact Finset.le_sup'
    (fun q : Fin (dyadicHorizon K) =>
      (poissonCellCount D q omega : ℝ))
    (Finset.mem_univ j)

/-- The cell maximum is nonnegative. -/
theorem poissonCellMaximum_nonneg
    (D : InterpolationData K Omega) (omega : Omega) :
    0 ≤ poissonCellMaximum D omega := by
  let j : Fin (dyadicHorizon K) :=
    ⟨0, by unfold dyadicHorizon; positivity⟩
  exact (Nat.cast_nonneg (poissonCellCount D j omega)).trans
    (poissonCellCount_le_maximum D omega j)

/-- Integer agreement identifies the abstract discrepancy with K18's tree
error. -/
theorem integerDeviation_eq_treeError
    (D : InterpolationData K Omega) (omega : Omega)
    (j : ℕ) (hj : j ≤ dyadicHorizon K) :
    integerDeviation D omega j =
      spatialTreeError K j (D.tree omega) := by
  unfold integerDeviation spatialTreeError
  rw [D.poisson_integer omega j,
    D.gaussian_integer omega j hj]

/-- Every integer discrepancy is at most K18's finite maximum. -/
theorem integerDeviation_le_skeletonMaximum
    (D : InterpolationData K Omega) (omega : Omega)
    (j : ℕ) (hj : j ≤ dyadicHorizon K) :
    integerDeviation D omega j ≤ skeletonMaximum D omega := by
  rw [integerDeviation_eq_treeError D omega j hj]
  let q : Fin (dyadicHorizon K + 1) :=
    ⟨j, Nat.lt_succ_iff.mpr hj⟩
  unfold skeletonMaximum committedSpatialKMTMaximum kmtHorizonMaximum
  simpa [q] using
    (Finset.le_sup'
      (fun t : Fin (dyadicHorizon K + 1) =>
        spatialTreeError K t.1 (D.tree omega))
      (Finset.mem_univ q))

/-! ## Deterministic interpolation bound -/

/-- The one-cell overshoot.  Monotonicity puts the Poisson increment up to
`j+s` between `0` and the full cell count. -/
theorem cell_overshoot
    (D : InterpolationData K Omega) (omega : Omega)
    (j : Fin (dyadicHorizon K)) {s O : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hOsc :
      |D.gaussianPath omega ((j.1 : ℝ) + s) -
        D.gaussianPath omega (j.1 : ℝ)| ≤ O) :
    |((D.poissonPath omega ((j.1 : ℝ) + s) : ℝ) -
          (D.poissonPath omega (j.1 : ℝ) : ℝ)) - s -
        (D.gaussianPath omega ((j.1 : ℝ) + s) -
          D.gaussianPath omega (j.1 : ℝ))| ≤
      (poissonCellCount D j omega : ℝ) + 1 + O := by
  have hleft :
      D.poissonPath omega (j.1 : ℝ) ≤
        D.poissonPath omega ((j.1 : ℝ) + s) := by
    apply D.poisson_mono omega
    linarith [hs.1]
  have hright :
      D.poissonPath omega ((j.1 : ℝ) + s) ≤
        D.poissonPath omega ((j.1 + 1 : ℕ) : ℝ) := by
    apply D.poisson_mono omega
    push_cast
    linarith [hs.2]
  have hleftR :
      (D.poissonPath omega (j.1 : ℝ) : ℝ) ≤
        (D.poissonPath omega ((j.1 : ℝ) + s) : ℝ) := by
    exact_mod_cast hleft
  have hrightR :
      (D.poissonPath omega ((j.1 : ℝ) + s) : ℝ) ≤
        (D.poissonPath omega ((j.1 + 1 : ℕ) : ℝ) : ℝ) := by
    exact_mod_cast hright
  let a : ℝ :=
    (D.poissonPath omega ((j.1 : ℝ) + s) : ℝ) -
      (D.poissonPath omega (j.1 : ℝ) : ℝ)
  let b : ℝ :=
    D.gaussianPath omega ((j.1 : ℝ) + s) -
      D.gaussianPath omega (j.1 : ℝ)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have haM : a ≤ (poissonCellCount D j omega : ℝ) := by
    dsimp [a]
    calc
      (D.poissonPath omega ((j.1 : ℝ) + s) : ℝ) -
          (D.poissonPath omega (j.1 : ℝ) : ℝ) ≤
        (D.poissonPath omega ((j.1 + 1 : ℕ) : ℝ) : ℝ) -
          (D.poissonPath omega (j.1 : ℝ) : ℝ) :=
        sub_le_sub_right hrightR _
      _ = (poissonCellCount D j omega : ℝ) :=
        (poissonCellCount_cast_eq_path_sub D omega j).symm
  change |a - s - b| ≤
    (poissonCellCount D j omega : ℝ) + 1 + O
  have hb : |b| ≤ O := by simpa [b] using hOsc
  calc
    |a - s - b| ≤ |a - s| + |b| := abs_sub _ _
    _ ≤ (|a| + |s|) + |b| := by
      gcongr
      exact abs_sub _ _
    _ = a + s + |b| := by
      rw [abs_of_nonneg ha0, abs_of_nonneg hs.1]
    _ ≤ (poissonCellCount D j omega : ℝ) + 1 + O := by
      linarith [hs.2]

/-- Pointwise global interpolation bound on `[0,2^K]`. -/
theorem continuousDeviation_le
    (D : InterpolationData K Omega) (omega : Omega)
    {t O : ℝ} (ht : t ∈ Icc (0 : ℝ) (dyadicHorizon K : ℝ))
    (hO : 0 ≤ O)
    (hOsc : ∀ (j : Fin (dyadicHorizon K)) (u : ℝ),
      u ∈ Icc (0 : ℝ) 1 →
      |D.gaussianPath omega ((j.1 : ℝ) + u) -
        D.gaussianPath omega (j.1 : ℝ)| ≤ O) :
    |(D.poissonPath omega t : ℝ) - t -
        D.gaussianPath omega t| ≤
      skeletonMaximum D omega + poissonCellMaximum D omega + 1 + O := by
  by_cases htend : t = (dyadicHorizon K : ℝ)
  · subst t
    have hbase := integerDeviation_le_skeletonMaximum
      D omega (dyadicHorizon K) le_rfl
    have htail : skeletonMaximum D omega ≤
        skeletonMaximum D omega + poissonCellMaximum D omega + 1 + O := by
      nlinarith [poissonCellMaximum_nonneg D omega]
    simpa [integerDeviation] using hbase.trans htail
  · have htlt : t < (dyadicHorizon K : ℝ) :=
      lt_of_le_of_ne ht.2 htend
    let jNat : ℕ := ⌊t⌋₊
    have hjlt : jNat < dyadicHorizon K := by
      dsimp [jNat]
      exact (Nat.floor_lt ht.1).2 htlt
    let j : Fin (dyadicHorizon K) := ⟨jNat, hjlt⟩
    let s : ℝ := t - (jNat : ℝ)
    have hfloor : (jNat : ℝ) ≤ t := by
      dsimp [jNat]
      exact Nat.floor_le ht.1
    have hnext : t < (jNat : ℝ) + 1 := by
      dsimp [jNat]
      simpa using Nat.lt_floor_add_one t
    have hs : s ∈ Icc (0 : ℝ) 1 := by
      dsimp [s]
      constructor <;> linarith
    have htEq : t = (jNat : ℝ) + s := by
      dsimp [s]
      ring
    have hlocal := cell_overshoot D omega j hs (hOsc j s hs)
    have hbase :
        |(D.poissonPath omega (jNat : ℝ) : ℝ) -
            (jNat : ℝ) - D.gaussianPath omega (jNat : ℝ)| ≤
          skeletonMaximum D omega := by
      simpa [integerDeviation] using
        integerDeviation_le_skeletonMaximum D omega jNat hjlt.le
    rw [htEq]
    have hsplit :
        (D.poissonPath omega ((jNat : ℝ) + s) : ℝ) -
            ((jNat : ℝ) + s) -
              D.gaussianPath omega ((jNat : ℝ) + s) =
          ((D.poissonPath omega (jNat : ℝ) : ℝ) -
              (jNat : ℝ) - D.gaussianPath omega (jNat : ℝ)) +
            (((D.poissonPath omega ((jNat : ℝ) + s) : ℝ) -
                (D.poissonPath omega (jNat : ℝ) : ℝ)) - s -
              (D.gaussianPath omega ((jNat : ℝ) + s) -
                D.gaussianPath omega (jNat : ℝ))) := by
      ring
    rw [hsplit]
    calc
      |_ + _| ≤
          |(D.poissonPath omega (jNat : ℝ) : ℝ) -
              (jNat : ℝ) - D.gaussianPath omega (jNat : ℝ)| +
            |((D.poissonPath omega ((jNat : ℝ) + s) : ℝ) -
                (D.poissonPath omega (jNat : ℝ) : ℝ)) - s -
              (D.gaussianPath omega ((jNat : ℝ) + s) -
                D.gaussianPath omega (jNat : ℝ))| := abs_add_le _ _
      _ ≤ skeletonMaximum D omega +
          ((poissonCellCount D j omega : ℝ) + 1 + O) :=
        add_le_add hbase hlocal
      _ ≤ skeletonMaximum D omega +
          poissonCellMaximum D omega + 1 + O := by
        have hcell := poissonCellCount_le_maximum D omega j
        linarith

/-- Values used by the literal continuous supremum. -/
def continuousDeviationRange
    (D : InterpolationData K Omega) (omega : Omega) : Set ℝ :=
  {r | ∃ t : ℝ, t ∈ Icc (0 : ℝ) (dyadicHorizon K : ℝ) ∧
    r = |(D.poissonPath omega t : ℝ) - t - D.gaussianPath omega t|}

/-- The literal supremum of the continuous discrepancy. -/
noncomputable def continuousDeviationSup
    (D : InterpolationData K Omega) (omega : Omega) : ℝ :=
  sSup (continuousDeviationRange D omega)

/-- Values used by the literal maximum-over-cells oscillation supremum. -/
def oscillationRange
    (D : InterpolationData K Omega) (omega : Omega) : Set ℝ :=
  {r | ∃ j : Fin (dyadicHorizon K), ∃ u : ℝ,
    u ∈ Icc (0 : ℝ) 1 ∧
      r = |D.gaussianPath omega ((j.1 : ℝ) + u) -
        D.gaussianPath omega (j.1 : ℝ)|}

/-- This single `sSup` is the literal `max_j sup_{u∈[0,1]} osc(j,u)`. -/
noncomputable def brownianOscillationSup
    (D : InterpolationData K Omega) (omega : Omega) : ℝ :=
  sSup (oscillationRange D omega)

private theorem oscillationRange_nonempty
    (D : InterpolationData K Omega) (omega : Omega) :
    (oscillationRange D omega).Nonempty := by
  let j : Fin (dyadicHorizon K) :=
    ⟨0, by unfold dyadicHorizon; positivity⟩
  refine ⟨0, j, 0, by simp, ?_⟩
  simp

/-- Each unit oscillation is below the literal oscillation supremum when the
path is bounded on the finite horizon. -/
theorem oscillation_le_brownianOscillationSup
    (D : InterpolationData K Omega) (omega : Omega)
    (hbounded : BddAbove (oscillationRange D omega))
    (j : Fin (dyadicHorizon K)) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    |D.gaussianPath omega ((j.1 : ℝ) + u) -
        D.gaussianPath omega (j.1 : ℝ)| ≤
      brownianOscillationSup D omega := by
  apply le_csSup hbounded
  exact ⟨j, u, hu, rfl⟩

/-- The literal oscillation supremum is nonnegative. -/
theorem brownianOscillationSup_nonneg
    (D : InterpolationData K Omega) (omega : Omega)
    (hbounded : BddAbove (oscillationRange D omega)) :
    0 ≤ brownianOscillationSup D omega := by
  apply le_csSup hbounded
  refine ⟨⟨0, by unfold dyadicHorizon; positivity⟩, 0, by simp, ?_⟩
  simp

/-- Requested supremum form of the deterministic K20 inequality. -/
theorem continuousDeviationSup_le
    (D : InterpolationData K Omega) (omega : Omega)
    (hbounded : BddAbove (oscillationRange D omega)) :
    continuousDeviationSup D omega ≤
      skeletonMaximum D omega + poissonCellMaximum D omega + 1 +
        brownianOscillationSup D omega := by
  have hnonneg := brownianOscillationSup_nonneg D omega hbounded
  have hdevNonempty : (continuousDeviationRange D omega).Nonempty := by
    refine ⟨|(D.poissonPath omega 0 : ℝ) -
      D.gaussianPath omega 0|, 0, ?_, ?_⟩
    · constructor
      · norm_num
      · positivity
    · ring
  apply csSup_le hdevNonempty
  rintro r ⟨t, ht, rfl⟩
  exact continuousDeviation_le D omega ht hnonneg
    (fun j u hu =>
      oscillation_le_brownianOscillationSup
        D omega hbounded j u hu)

/-! ## Threshold events (no uncountable-sup measurability assumption) -/

/-- Continuous discrepancy exceeds `R` somewhere on the horizon. -/
def continuousDeviationFailure
    (D : InterpolationData K Omega) (R : ℝ) : Set Omega :=
  {omega | ∃ t : ℝ,
    t ∈ Icc (0 : ℝ) (dyadicHorizon K : ℝ) ∧
      R < |(D.poissonPath omega t : ℝ) - t -
        D.gaussianPath omega t|}

/-- Some unit-interval oscillation exceeds `R`.  This is exactly the threshold
form of `max_j sup_u osc_j > R`. -/
def oscillationFailure
    (D : InterpolationData K Omega) (R : ℝ) : Set Omega :=
  {omega | ∃ j : Fin (dyadicHorizon K), ∃ u : ℝ,
    u ∈ Icc (0 : ℝ) 1 ∧
      R < |D.gaussianPath omega ((j.1 : ℝ) + u) -
        D.gaussianPath omega (j.1 : ℝ)|}

/-- Deterministic three-event cover used by the final union bound. -/
theorem continuousDeviationFailure_subset
    (D : InterpolationData K Omega)
    {S P O R : ℝ} (hO : 0 ≤ O)
    (hR : S + P + 1 + O ≤ R) :
    continuousDeviationFailure D R ⊆
      {omega | S < skeletonMaximum D omega} ∪
        ({omega | P < poissonCellMaximum D omega} ∪
          oscillationFailure D O) := by
  rintro omega ⟨t, ht, hbad⟩
  by_cases hs : S < skeletonMaximum D omega
  · exact Or.inl hs
  by_cases hp : P < poissonCellMaximum D omega
  · exact Or.inr (Or.inl hp)
  by_cases ho : omega ∈ oscillationFailure D O
  · exact Or.inr (Or.inr ho)
  exfalso
  have hOsc : ∀ (j : Fin (dyadicHorizon K)) (u : ℝ),
      u ∈ Icc (0 : ℝ) 1 →
      |D.gaussianPath omega ((j.1 : ℝ) + u) -
        D.gaussianPath omega (j.1 : ℝ)| ≤ O := by
    intro j u hu
    by_contra hnot
    apply ho
    exact ⟨j, u, hu, lt_of_not_ge hnot⟩
  have hdet := continuousDeviation_le D omega ht hO hOsc
  have hsle := not_lt.mp hs
  have hple := not_lt.mp hp
  linarith

/-! ## Pullback of K18 -/

private theorem measurable_spatialTreeError
    (K t : ℕ) :
    Measurable (spatialTreeError K t) := by
  have hPoisson : Measurable
      (fun z : DyadicNoiseSpace K =>
        (DyadicSpatialSkeleton.spatialPoissonSkeleton K z t : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      (measurable_spatialPoissonSkeleton K t)
  exact ((hPoisson.sub measurable_const).sub
    (measurable_spatialGaussianSkeleton K t)).abs

private theorem measurableSet_committedSpatialMaximum_gt
    (K : ℕ) (R : ℝ) :
    MeasurableSet
      {z : DyadicNoiseSpace K |
        R < committedSpatialKMTMaximum K z} := by
  have heq :
      {z : DyadicNoiseSpace K |
        R < committedSpatialKMTMaximum K z} =
        ⋃ t : Fin (dyadicHorizon K + 1),
          {z | R < spatialTreeError K t.1 z} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    unfold committedSpatialKMTMaximum kmtHorizonMaximum
    rw [Finset.lt_sup'_iff]
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun t =>
    measurableSet_lt measurable_const
      (measurable_spatialTreeError K t.1)

variable {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- K18 transported to any source whose tree projection has the committed
noise law. -/
theorem skeletonMaximum_tail
    (D : InterpolationData K Omega)
    (hTreeLaw : mu.map D.tree = dyadicNoiseMeasure K)
    {x : ℝ} (hx : 0 ≤ x) :
    mu.real
        {omega |
          2094 * kmtHorizonLog K + x <
            skeletonMaximum D omega} ≤
      6 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
  let A : Set (DyadicNoiseSpace K) :=
    {z | 2094 * kmtHorizonLog K + x <
      committedSpatialKMTMaximum K z}
  have hA : MeasurableSet A :=
    measurableSet_committedSpatialMaximum_gt K _
  have hmeasure :
      mu {omega |
          2094 * kmtHorizonLog K + x <
            skeletonMaximum D omega} =
        dyadicNoiseMeasure K A := by
    rw [show {omega |
        2094 * kmtHorizonLog K + x <
          skeletonMaximum D omega} = D.tree ⁻¹' A by
      rfl]
    rw [← Measure.map_apply D.tree_measurable hA, hTreeLaw]
  change (mu {omega |
      2094 * kmtHorizonLog K + x <
        skeletonMaximum D omega}).toReal ≤ _
  rw [hmeasure]
  simpa [A, kmtHorizonLog] using
    committedSpatialSkeleton_finiteHorizon_tail K hx

/-! ## Poisson unit-cell maximum -/

private theorem measurable_poissonCellCount
    (D : InterpolationData K Omega)
    (j : Fin (dyadicHorizon K)) :
    Measurable (poissonCellCount D j) :=
  (measurable_spatialPoissonUnitIncrement K j).comp
    D.tree_measurable

/-- Each pulled-back cell count still has the `Poisson(1)` law. -/
theorem poissonCellCount_map
    (D : InterpolationData K Omega)
    (hTreeLaw : mu.map D.tree = dyadicNoiseMeasure K)
    (j : Fin (dyadicHorizon K)) :
    mu.map (poissonCellCount D j) = poisMeasure 1 := by
  have hcomp : poissonCellCount D j =
      spatialPoissonUnitIncrement K j ∘ D.tree := rfl
  rw [hcomp, ← Measure.map_map
    (measurable_spatialPoissonUnitIncrement K j)
    D.tree_measurable, hTreeLaw]
  exact spatialPoissonUnitIncrement_map K j

/-- Chernoff at `theta = 1` for one `Poisson(1)` variable. -/
theorem poissonOne_upper_tail
    (N : Omega → ℕ) (hN : Measurable N)
    (hmap : mu.map N = poisMeasure 1) (r : ℝ) :
    mu.real {omega | r < (N omega : ℝ)} ≤
      Real.exp (Real.exp 1 - 1 - r) := by
  have hlaw (k : ℕ) :
      mu {omega | N omega = k} =
        ENNReal.ofReal (poisTerm k 1) := by
    rw [show {omega | N omega = k} = N ⁻¹' {k} from rfl,
      ← Measure.map_apply hN (measurableSet_singleton k),
      hmap, poisMeasure_singleton]
  obtain ⟨hInt, hVal⟩ :=
    integral_exp_mul_of_poisson_masses
      mu hN (by norm_num : (0 : ℝ) ≤ 1) hlaw 1
  have hInt' : Integrable
      (fun omega => Real.exp (N omega : ℝ)) mu := by
    simpa using hInt
  have hVal' :
      (∫ omega, Real.exp (N omega : ℝ) ∂mu) =
        Real.exp (Real.exp 1 - 1) := by
    simpa using hVal
  have hsub :
      {omega | r < (N omega : ℝ)} ⊆
        {omega | Real.exp r ≤ Real.exp (N omega : ℝ)} := by
    intro omega homega
    exact Real.exp_le_exp.mpr homega.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all mu fun omega => Real.exp_nonneg (N omega : ℝ))
    hInt' (Real.exp r)
  have hmul :
      Real.exp r * mu.real {omega | r < (N omega : ℝ)} ≤
        Real.exp (Real.exp 1 - 1) :=
    (mul_le_mul_of_nonneg_left
      (measureReal_mono hsub) (Real.exp_nonneg r)).trans
      (hmarkov.trans_eq hVal')
  calc
    mu.real {omega | r < (N omega : ℝ)} ≤
        Real.exp (Real.exp 1 - 1) / Real.exp r := by
      apply (le_div_iff₀ (Real.exp_pos r)).2
      simpa only [mul_comm] using hmul
    _ = Real.exp (Real.exp 1 - 1 - r) :=
      (Real.exp_sub (Real.exp 1 - 1) r).symm

private theorem measureReal_iUnion_fintype_le
    {I : Type*} [Fintype I] (A : I → Set Omega) :
    mu.real (⋃ i, A i) ≤ ∑ i, mu.real (A i) := by
  classical
  change (mu (⋃ i, A i)).toReal ≤
    ∑ i, (mu (A i)).toReal
  have hmeasure :
      mu (⋃ i, A i) ≤ ∑ i, mu (A i) :=
    measure_iUnion_fintype_le mu A
  have htop : (∑ i, mu (A i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i _
    exact measure_ne_top mu (A i)
  have hreal := ENNReal.toReal_mono htop hmeasure
  rw [ENNReal.toReal_sum
    (fun i _ => measure_ne_top mu (A i))] at hreal
  exact hreal

/-- Requested Poisson maximum bound.  The strict real threshold handles all
integer rounding automatically.  Independence is not needed for this union
bound; the `Poisson(1)` marginals suffice. -/
theorem poissonCellMaximum_tail
    (D : InterpolationData K Omega)
    (hTreeLaw : mu.map D.tree = dyadicNoiseMeasure K)
    {x : ℝ} (hx : 0 ≤ x) :
    mu.real
        {omega |
          Real.exp 1 - 1 +
              Real.log (dyadicHorizon K : ℝ) + x <
            poissonCellMaximum D omega} ≤
      Real.exp (-x) := by
  classical
  let r : ℝ := Real.exp 1 - 1 +
    Real.log (dyadicHorizon K : ℝ) + x
  let A : Fin (dyadicHorizon K) → Set Omega := fun j =>
    {omega | r < (poissonCellCount D j omega : ℝ)}
  have hsubset :
      {omega | r < poissonCellMaximum D omega} ⊆ ⋃ j, A j := by
    intro omega homega
    unfold poissonCellMaximum at homega
    rw [Set.mem_setOf_eq, Finset.lt_sup'_iff] at homega
    rcases homega with ⟨j, _hj, hj⟩
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  have hEach (j : Fin (dyadicHorizon K)) :
      mu.real (A j) ≤
        Real.exp (Real.exp 1 - 1 - r) := by
    exact poissonOne_upper_tail
      (mu := mu) (poissonCellCount D j)
      (measurable_poissonCellCount D j)
      (poissonCellCount_map D hTreeLaw j) r
  have hnpos : (0 : ℝ) < dyadicHorizon K := by
    unfold dyadicHorizon
    positivity
  calc
    mu.real
        {omega |
          Real.exp 1 - 1 +
              Real.log (dyadicHorizon K : ℝ) + x <
            poissonCellMaximum D omega} =
      mu.real {omega | r < poissonCellMaximum D omega} := by rfl
    _ ≤ mu.real (⋃ j, A j) := measureReal_mono hsubset
    _ ≤ ∑ j, mu.real (A j) :=
      measureReal_iUnion_fintype_le A
    _ ≤ ∑ _j : Fin (dyadicHorizon K),
        Real.exp (Real.exp 1 - 1 - r) :=
      Finset.sum_le_sum fun j _ => hEach j
    _ = (dyadicHorizon K : ℝ) *
        Real.exp (Real.exp 1 - 1 - r) := by
      rw [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ = Real.exp (-x) := by
      have h := Real.exp_log hnpos
      have h2 : Real.exp (Real.exp 1 - 1 - r) =
          Real.exp (-x) * Real.exp (-(Real.log (dyadicHorizon K : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [r]
        ring
      rw [h2, Real.exp_neg (Real.log (dyadicHorizon K : ℝ)), h]
      field_simp

/-! ## Constants and threshold absorption -/

/-- Oscillation tail threshold from the Brownian input. -/
def oscillationThreshold
    (K : ℕ) (A B x : ℝ) : ℝ :=
  A * Real.sqrt (kmtHorizonLog K + x) + B * (1 + x)

/-- The fraction of the final excess assigned to the oscillation tail. -/
def interpolationOscillationRate (A B : ℝ) : ℝ :=
  1 / (4 * (A + B + 1))

/-- Oscillation-tail parameter used in the three-way union bound. -/
def interpolationOscillationShare (A B x : ℝ) : ℝ :=
  interpolationOscillationRate A B * x

/-- Final logarithmic constant. -/
def interpolationConstant (A B : ℝ) : ℝ :=
  2095 + A + 2 * (Real.exp 1 + A / 4 + B)

/-- Final prefactor. -/
def interpolationPrefactor (c : ℝ) : ℝ := 7 + c

/-- Final exponential rate. -/
def interpolationRate (A B : ℝ) : ℝ :=
  min (9 / 65536 : ℝ)
    (min (1 / 4 : ℝ) (interpolationOscillationRate A B))

/-- Positivity of all advertised constants. -/
theorem interpolationConstants_pos
    {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    0 < interpolationConstant A B ∧
      0 < interpolationPrefactor c ∧
        0 < interpolationRate A B := by
  have hden : 0 < 4 * (A + B + 1) := by
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold interpolationConstant
    positivity
  · unfold interpolationPrefactor
    linarith
  · unfold interpolationRate interpolationOscillationRate
    exact lt_min (by norm_num)
      (lt_min (by norm_num) (one_div_pos.mpr hden))

private theorem kmtHorizonLog_ge_half (K : ℕ) :
    (1 / 2 : ℝ) ≤ kmtHorizonLog K := by
  unfold kmtHorizonLog
  rw [Real.log_pow]
  have hk : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ K + 1 by omega)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num)).le
  calc
    (1 / 2 : ℝ) ≤ 1 * Real.log 2 := by simpa using hhalf
    _ ≤ ((K + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hk hlog

private theorem log_dyadicHorizon_le_kmtHorizonLog (K : ℕ) :
    Real.log (dyadicHorizon K : ℝ) ≤ kmtHorizonLog K := by
  unfold dyadicHorizon kmtHorizonLog
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow, Real.log_pow]
  have hk : (K : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ K
  exact mul_le_mul_of_nonneg_right hk
    (Real.log_nonneg (by norm_num))

private theorem sqrt_le_self_add_quarter
    {z : ℝ} (hz : 0 ≤ z) :
    Real.sqrt z ≤ z + 1 / 4 := by
  have hs := Real.sq_sqrt hz
  have hsq := sq_nonneg (Real.sqrt z - 1 / 2)
  nlinarith

/-- The three component thresholds fit below `C log(2n) + x`. -/
theorem interpolation_threshold_absorption
    (K : ℕ) {A B x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) :
    2094 * kmtHorizonLog K + x / 4 +
        (Real.exp 1 - 1 +
          Real.log (dyadicHorizon K : ℝ) + x / 4) + 1 +
        oscillationThreshold K A B
          (interpolationOscillationShare A B x) ≤
      interpolationConstant A B * kmtHorizonLog K + x := by
  let H := kmtHorizonLog K
  let y := interpolationOscillationShare A B x
  let C0 := Real.exp 1 + A / 4 + B
  have hH : (1 / 2 : ℝ) ≤ H := by
    simpa [H] using kmtHorizonLog_ge_half K
  have hlog : Real.log (dyadicHorizon K : ℝ) ≤ H := by
    simpa [H] using log_dyadicHorizon_le_kmtHorizonLog K
  have hden : 0 < A + B + 1 := by linarith
  have hrate : 0 ≤ interpolationOscillationRate A B := by
    unfold interpolationOscillationRate
    positivity
  have hy : 0 ≤ y := by
    dsimp [y, interpolationOscillationShare]
    positivity
  have hroot : 0 ≤ H + y := by linarith
  have hsqrt := sqrt_le_self_add_quarter hroot
  have hAsqrt :
      A * Real.sqrt (H + y) ≤ A * (H + y + 1 / 4) :=
    mul_le_mul_of_nonneg_left hsqrt hA
  have hratio : (A + B) / (A + B + 1) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  have hshare : (A + B) * y ≤ x / 4 := by
    dsimp [y, interpolationOscillationShare,
      interpolationOscillationRate]
    calc
      (A + B) * (1 / (4 * (A + B + 1)) * x) =
          (x / 4) * ((A + B) / (A + B + 1)) := by
        field_simp [hden.ne']
      _ ≤ (x / 4) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = x / 4 := by ring
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC0absorb : C0 ≤ 2 * C0 * H := by
    have hmul := mul_le_mul_of_nonneg_left hH hC0
    nlinarith
  have hosc :
      oscillationThreshold K A B y ≤
        A * (H + y + 1 / 4) + B * (1 + y) := by
    unfold oscillationThreshold
    have hadd := add_le_add hAsqrt (le_refl (B * (1 + y)))
    simpa [H] using hadd
  calc
    2094 * kmtHorizonLog K + x / 4 +
          (Real.exp 1 - 1 +
            Real.log (dyadicHorizon K : ℝ) + x / 4) + 1 +
          oscillationThreshold K A B
            (interpolationOscillationShare A B x) ≤
        2094 * H + x / 4 +
          (Real.exp 1 - 1 + H + x / 4) + 1 +
          (A * (H + y + 1 / 4) + B * (1 + y)) := by
      dsimp [H, y]
      gcongr
    _ = (2095 + A) * H + C0 + x / 2 + (A + B) * y := by
      dsimp [C0]
      ring
    _ ≤ (2095 + A) * H + 2 * C0 * H + x / 2 + x / 4 := by
      nlinarith [hC0absorb, hshare]
    _ ≤ interpolationConstant A B * kmtHorizonLog K + x := by
      dsimp [interpolationConstant, H, C0]
      nlinarith

private theorem interpolationRate_le_skeleton
    (A B : ℝ) : interpolationRate A B ≤ 9 / 65536 := by
  unfold interpolationRate
  exact min_le_left _ _

private theorem interpolationRate_le_poisson
    (A B : ℝ) : interpolationRate A B ≤ 1 / 4 := by
  unfold interpolationRate
  exact (min_le_right _ _).trans (min_le_left _ _)

private theorem interpolationRate_le_oscillation
    (A B : ℝ) :
    interpolationRate A B ≤ interpolationOscillationRate A B := by
  unfold interpolationRate
  exact (min_le_right _ _).trans (min_le_right _ _)

/-! ## Final K20 theorem -/

/-- Abstract K20 assembly.  `hOsc` is precisely hypothesis `(H_osc)` in
threshold-event form. -/
theorem continuousInterpolation_tail
    (D : InterpolationData K Omega)
    (hTreeLaw : mu.map D.tree = dyadicNoiseMeasure K)
    (A B c : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hOsc : ∀ y : ℝ, 0 ≤ y →
      mu.real
          (oscillationFailure D (oscillationThreshold K A B y)) ≤
        c * Real.exp (-y))
    {x : ℝ} (hx : 0 ≤ x) :
    mu.real
        (continuousDeviationFailure D
          (interpolationConstant A B * kmtHorizonLog K + x)) ≤
      interpolationPrefactor c *
        Real.exp (-(interpolationRate A B * x)) := by
  let S := 2094 * kmtHorizonLog K + x / 4
  let P := Real.exp 1 - 1 +
    Real.log (dyadicHorizon K : ℝ) + x / 4
  let y := interpolationOscillationShare A B x
  let O := oscillationThreshold K A B y
  let R := interpolationConstant A B * kmtHorizonLog K + x
  have hy : 0 ≤ y := by
    dsimp [y, interpolationOscillationShare,
      interpolationOscillationRate]
    have hden : 0 < 4 * (A + B + 1) := by nlinarith
    positivity
  have hO : 0 ≤ O := by
    dsimp [O, oscillationThreshold]
    have hH : 0 ≤ kmtHorizonLog K :=
      (kmtHorizonLog_ge_half K).trans' (by norm_num)
    positivity
  have habsorb : S + P + 1 + O ≤ R := by
    simpa [S, P, y, O, R] using
      interpolation_threshold_absorption K hA hB hx
  have hcover := continuousDeviationFailure_subset
    D hO habsorb
  have hsk := skeletonMaximum_tail
    (mu := mu) D hTreeLaw (x := x / 4) (by positivity)
  have hsk' :
      mu.real {omega | S < skeletonMaximum D omega} ≤
        6 * Real.exp (-((9 / 65536 : ℝ) * x)) := by
    rw [show (9 / 16384 : ℝ) * (x / 4) =
      (9 / 65536 : ℝ) * x by ring] at hsk
    simpa [S] using hsk
  have hp := poissonCellMaximum_tail
    (mu := mu) D hTreeLaw (x := x / 4) (by positivity)
  have hp' :
      mu.real {omega | P < poissonCellMaximum D omega} ≤
        Real.exp (-((1 / 4 : ℝ) * x)) := by
    rw [show -(x / 4) = -((1 / 4 : ℝ) * x) by ring] at hp
    simpa [P] using hp
  have ho :
      mu.real (oscillationFailure D O) ≤
        c * Real.exp (-y) := by
    simpa [O] using hOsc y hy
  let E := Real.exp (-(interpolationRate A B * x))
  have expRate (r : ℝ) (hr : interpolationRate A B ≤ r) :
      Real.exp (-(r * x)) ≤ E := by
    dsimp [E]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hr hx
    linarith
  have hskFinal :
      6 * Real.exp (-((9 / 65536 : ℝ) * x)) ≤ 6 * E :=
    mul_le_mul_of_nonneg_left
      (expRate _ (interpolationRate_le_skeleton A B)) (by norm_num)
  have hpFinal :
      Real.exp (-((1 / 4 : ℝ) * x)) ≤ E :=
    expRate _ (interpolationRate_le_poisson A B)
  have hoFinal : c * Real.exp (-y) ≤ c * E := by
    apply mul_le_mul_of_nonneg_left _ hc
    dsimp [y, interpolationOscillationShare]
    exact expRate _ (interpolationRate_le_oscillation A B)
  calc
    mu.real
        (continuousDeviationFailure D
          (interpolationConstant A B * kmtHorizonLog K + x)) ≤
      mu.real
        ({omega | S < skeletonMaximum D omega} ∪
          ({omega | P < poissonCellMaximum D omega} ∪
            oscillationFailure D O)) :=
      measureReal_mono (by simpa [R] using hcover)
    _ ≤ mu.real {omega | S < skeletonMaximum D omega} +
        (mu.real {omega | P < poissonCellMaximum D omega} +
          mu.real (oscillationFailure D O)) := by
      exact (measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ 6 * Real.exp (-((9 / 65536 : ℝ) * x)) +
        (Real.exp (-((1 / 4 : ℝ) * x)) +
          c * Real.exp (-y)) :=
      add_le_add hsk' (add_le_add hp' ho)
    _ ≤ 6 * E + (E + c * E) :=
      add_le_add hskFinal (add_le_add hpFinal hoFinal)
    _ = interpolationPrefactor c *
        Real.exp (-(interpolationRate A B * x)) := by
      dsimp [E, interpolationPrefactor]
      ring

/-- Product-source corollary for the continuous Poisson path constructed in
`DyadicConditionalPoissonPath` and any supplied Brownian interpolation agreeing at integers. -/
theorem committedContinuousPoisson_interpolation_tail
    (K : ℕ) (W : DyadicContinuousSpace K → ℝ → ℝ)
    (hW : ∀ omega j, j ≤ dyadicHorizon K →
      W omega (j : ℝ) =
        DyadicSpatialSkeleton.spatialGaussianSkeleton K omega.1 j)
    (A B c : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hOsc : ∀ y : ℝ, 0 ≤ y →
      (dyadicContinuousMeasure K).real
          (oscillationFailure
            (committedInterpolationData K W hW)
            (oscillationThreshold K A B y)) ≤
        c * Real.exp (-y))
    {x : ℝ} (hx : 0 ≤ x) :
    (dyadicContinuousMeasure K).real
        (continuousDeviationFailure
          (committedInterpolationData K W hW)
          (interpolationConstant A B * kmtHorizonLog K + x)) ≤
      interpolationPrefactor c *
        Real.exp (-(interpolationRate A B * x)) := by
  apply continuousInterpolation_tail
    (mu := dyadicContinuousMeasure K)
    (D := committedInterpolationData K W hW)
    (A := A) (B := B) (c := c)
  · simpa [committedInterpolationData] using
      dyadicContinuousMeasure_map_fst K
  · exact hA
  · exact hB
  · exact hc
  · exact hOsc
  · exact hx

/-!
THEOREM LIST
* `committedInterpolationData`
* `poissonCellCount_eq_path_sub`
* `cell_overshoot`
* `continuousDeviation_le`
* `continuousDeviationSup_le`
* `continuousDeviationFailure_subset`
* `skeletonMaximum_tail`
* `poissonOne_upper_tail`
* `poissonCellMaximum_tail`
* `interpolationConstants_pos`
* `interpolation_threshold_absorption`
* `continuousInterpolation_tail`
* `committedContinuousPoisson_interpolation_tail`

CLOSES
* Item 1: the one-cell overshoot, the pointwise horizon bound, and the literal
  `sSup` form with `max_j sup_u` represented by `brownianOscillationSup`.
* Item 2: `P(max_j M_j > e-1+log n+x) <= exp(-x)`, with strict real threshold
  handling rounding and with only the `Poisson(1)` marginals used.
* Item 3: the combined finite-horizon tail with explicit `C`, `a`, and `b`,
  including the elementary `sqrt z <= z+1/4` absorption.
* The `DyadicConditionalPoissonPath` product source is instantiated explicitly.

UNFINISHED
* Only the separately requested Brownian construction must discharge `hW` and
  `(H_osc)`.  No Brownian or Poisson/Brownian independence premise is needed.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicInterpolationOvershoot

end

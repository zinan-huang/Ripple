-- Ripple/Kurtz/StrongApprox/DyadicTreeFiniteHorizon.lean
import Ripple.Kurtz.StrongApprox.DyadicTreePointTail
import Ripple.Kurtz.StrongApprox.DyadicFiniteHorizonUnion
import Ripple.Kurtz.StrongApprox.BrownianEntropyModulus

/-!
# K18 coarse-node tail and final finite-horizon KMT wiring

This file closes the two items left open by `DyadicTreePointTail`:

* H1 for the exact raw-coordinate event `treeKMTCoarseFailure`;
* the final call to `finiteHorizonKMT_union_tail` for the committed spatial
  Poisson and Gaussian skeletons.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal NNReal Nat

namespace Ripple.Kurtz.StrongApprox.DyadicTreeFiniteHorizon

open DyadicGaussianTree DyadicPoissonTree
open DyadicSpatialSkeleton
open DyadicChainEstimate
open DyadicTreePointTail
open DyadicFiniteHorizonUnion

/-! ## Raw split coordinates -/

private theorem card_dyadicNoise_eq_pow_two :
    ∀ K : ℕ, Fintype.card (DyadicNoise K) = 2 ^ K
  | 0 => by simp [DyadicNoise]
  | K + 1 => by
      change Fintype.card (DyadicNoise K ⊕ DyadicCell K) = 2 ^ (K + 1)
      rw [Fintype.card_sum, card_dyadicNoise_eq_pow_two K,
        card_dyadicCell, pow_succ]
      omega

/-- The unique endpoint-normal coordinate.  Every other raw coordinate is a
split normal. -/
private def treeEndpointNoise : (K : ℕ) → DyadicNoise K
  | 0 => ()
  | K + 1 => Sum.inl (treeEndpointNoise K)

private theorem treeNoiseGeneration_endpoint :
    ∀ K : ℕ,
      treeNoiseGeneration K (treeEndpointNoise K) = none
  | 0 => rfl
  | K + 1 => by
      simpa [treeEndpointNoise, treeNoiseGeneration] using
        treeNoiseGeneration_endpoint K

/-- All raw coordinates except the endpoint normal. -/
private noncomputable def treeSplitCoordinates (K : ℕ) :
    Finset (DyadicNoise K) := by
  classical
  exact Finset.univ.erase (treeEndpointNoise K)

private theorem card_treeSplitCoordinates (K : ℕ) :
    (treeSplitCoordinates K).card = dyadicHorizon K - 1 := by
  classical
  change ((Finset.univ : Finset (DyadicNoise K)).erase
      (treeEndpointNoise K)).card = dyadicHorizon K - 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_dyadicNoise_eq_pow_two]
  rfl

private theorem coordinate_ne_endpoint_of_generation_some
    {K j : ℕ} {i : DyadicNoise K}
    (h : treeNoiseGeneration K i = some j) :
    i ≠ treeEndpointNoise K := by
  intro hi
  subst i
  simpa [treeNoiseGeneration_endpoint] using h

/-- The contribution of one raw coordinate to the exact coarse event. -/
private def treeRawCoarseEvent
    (K : ℕ) (L : ℝ) (i : DyadicNoise K) :
    Set (DyadicNoiseSpace K) :=
  {z |
    (∃ j : ℕ,
      treeNoiseGeneration K i = some j ∧
        L ≤ dyadicLength K j) ∧
      Real.sqrt L / 4 < |z i|}

private theorem treeKMTCoarseFailure_eq_biUnion
    (K : ℕ) (L : ℝ) :
    treeKMTCoarseFailure K L =
      ⋃ i ∈ treeSplitCoordinates K, treeRawCoarseEvent K L i := by
  classical
  ext z
  constructor
  · rintro ⟨i, j, hgeneration, hlength, hlarge⟩
    have hi : i ∈ treeSplitCoordinates K := by
      change i ∈ (Finset.univ : Finset (DyadicNoise K)).erase
        (treeEndpointNoise K)
      rw [Finset.mem_erase]
      exact ⟨coordinate_ne_endpoint_of_generation_some hgeneration,
        Finset.mem_univ i⟩
    refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, ?_⟩⟩
    change
      (∃ j : ℕ,
        treeNoiseGeneration K i = some j ∧
          L ≤ dyadicLength K j) ∧
        Real.sqrt L / 4 < |z i|
    exact ⟨⟨j, hgeneration, hlength⟩, hlarge⟩
  · intro hz
    rcases Set.mem_iUnion.1 hz with ⟨i, hz⟩
    rcases Set.mem_iUnion.1 hz with ⟨_hi, hz⟩
    change
      (∃ j : ℕ,
        treeNoiseGeneration K i = some j ∧
          L ≤ dyadicLength K j) ∧
        Real.sqrt L / 4 < |z i| at hz
    rcases hz with ⟨⟨j, hgeneration, hlength⟩, hlarge⟩
    exact ⟨i, j, hgeneration, hlength, hlarge⟩

private theorem dyadicLength_le_horizon (K j : ℕ) :
    dyadicLength K j ≤ (dyadicHorizon K : ℝ) := by
  have hpow :
      (2 : ℝ) ^ (K - j) ≤ (2 : ℝ) ^ K := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact Nat.sub_le K j
  simpa [dyadicLength, dyadicHorizon] using hpow

/-- If the cutoff exceeds the root length, there are no coarse cells. -/
theorem treeKMTCoarseFailure_eq_empty_of_horizon_lt
    (K : ℕ) {L : ℝ}
    (hlarge : (dyadicHorizon K : ℝ) < L) :
    treeKMTCoarseFailure K L = ∅ := by
  ext z
  constructor
  · rintro ⟨_i, j, _hgeneration, hlength, _hlargeCoordinate⟩
    have hbound := dyadicLength_le_horizon K j
    exfalso
    linarith
  · simp

/-! ## Gaussian coordinate tail and finite union -/

private theorem rawCoordinate_map
    (K : ℕ) (i : DyadicNoise K) :
    (dyadicNoiseMeasure K).map
        (fun z : DyadicNoiseSpace K => z i) =
      gaussianReal 0 1 := by
  simpa [dyadicNoiseMeasure] using
    (measurePreserving_eval
      (fun _ : DyadicNoise K => gaussianReal 0 1) i).map_eq

private theorem rawCoordinate_tail
    (K : ℕ) (i : DyadicNoise K)
    {L : ℝ} (hL : 0 ≤ L) :
    (dyadicNoiseMeasure K).real
        {z | Real.sqrt L / 4 < |z i|} ≤
      2 * Real.exp (-(L / 32)) := by
  have htail := gaussian_abs_tail_le
    (P := dyadicNoiseMeasure K)
    (X := fun z : DyadicNoiseSpace K => z i)
    (variance := (1 : ℝ≥0))
    (x := Real.sqrt L / 4)
    (measurable_pi_apply i)
    (rawCoordinate_map K i)
    (by norm_num)
    (by positivity)
  change
    ((dyadicNoiseMeasure K)
      {z | Real.sqrt L / 4 < |z i|}).toReal ≤ _
  calc
    ((dyadicNoiseMeasure K)
        {z | Real.sqrt L / 4 < |z i|}).toReal ≤
      (ENNReal.ofReal
        (2 * Real.exp
          (-((Real.sqrt L / 4) ^ 2) /
            (2 * (1 : ℝ≥0))))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
    _ = 2 * Real.exp (-(L / 32)) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
      congr 1
      rw [div_pow, Real.sq_sqrt hL]
      norm_num
      ring

private theorem treeRawCoarseEvent_tail
    (K : ℕ) (i : DyadicNoise K)
    {L : ℝ} (hL : 0 ≤ L) :
    (dyadicNoiseMeasure K).real
        (treeRawCoarseEvent K L i) ≤
      2 * Real.exp (-(L / 32)) := by
  have hsubset :
      treeRawCoarseEvent K L i ⊆
        {z | Real.sqrt L / 4 < |z i|} := by
    intro z hz
    exact hz.2
  calc
    (dyadicNoiseMeasure K).real
        (treeRawCoarseEvent K L i) ≤
      (dyadicNoiseMeasure K).real
        {z | Real.sqrt L / 4 < |z i|} :=
      measureReal_mono hsubset
    _ ≤ 2 * Real.exp (-(L / 32)) :=
      rawCoordinate_tail K i hL

private theorem measureReal_biUnion_finset_le
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) :
    μ.real (⋃ i ∈ s, A i) ≤
      ∑ i ∈ s, μ.real (A i) := by
  classical
  change
    (μ (⋃ i ∈ s, A i)).toReal ≤
      ∑ i ∈ s, (μ (A i)).toReal
  have hmeasure :
      μ (⋃ i ∈ s, A i) ≤
        ∑ i ∈ s, μ (A i) :=
    measure_biUnion_finset_le s A
  have hsum_ne_top :
      (∑ i ∈ s, μ (A i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i _hi
    exact measure_ne_top μ (A i)
  have hreal := ENNReal.toReal_mono hsum_ne_top hmeasure
  rw [ENNReal.toReal_sum
    (fun i _hi => measure_ne_top μ (A i))] at hreal
  exact hreal

/-- H1 for an arbitrary nonnegative cutoff.  The proof is uniform; the first
branch records explicitly that the event is empty when `L > 2^K`. -/
theorem treeKMTCoarseFailure_tail
    (K : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (dyadicNoiseMeasure K).real
        (treeKMTCoarseFailure K L) ≤
      4 * (dyadicHorizon K : ℝ) *
        Real.exp (-(L / 32)) := by
  classical
  by_cases hlarge : (dyadicHorizon K : ℝ) < L
  · rw [treeKMTCoarseFailure_eq_empty_of_horizon_lt K hlarge,
      measureReal_empty]
    positivity
  · rw [treeKMTCoarseFailure_eq_biUnion]
    have hcardNat :
        (treeSplitCoordinates K).card ≤ dyadicHorizon K := by
      rw [card_treeSplitCoordinates]
      exact Nat.sub_le _ _
    have hcard :
        ((treeSplitCoordinates K).card : ℝ) ≤
          (dyadicHorizon K : ℝ) := by
      exact_mod_cast hcardNat
    calc
      (dyadicNoiseMeasure K).real
          (⋃ i ∈ treeSplitCoordinates K,
            treeRawCoarseEvent K L i) ≤
        ∑ i ∈ treeSplitCoordinates K,
          (dyadicNoiseMeasure K).real
            (treeRawCoarseEvent K L i) :=
        measureReal_biUnion_finset_le
          (treeSplitCoordinates K) (treeRawCoarseEvent K L)
      _ ≤ ∑ _i ∈ treeSplitCoordinates K,
          2 * Real.exp (-(L / 32)) :=
        Finset.sum_le_sum fun i _hi =>
          treeRawCoarseEvent_tail K i hL
      _ = ((treeSplitCoordinates K).card : ℝ) *
          (2 * Real.exp (-(L / 32))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (dyadicHorizon K : ℝ) *
          (2 * Real.exp (-(L / 32))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * (dyadicHorizon K : ℝ) *
          Real.exp (-(L / 32)) := by ring
      _ ≤ 4 * (dyadicHorizon K : ℝ) *
          Real.exp (-(L / 32)) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right
            (by norm_num : (2 : ℝ) ≤ 4) (by positivity)
        · exact Real.exp_nonneg _

/-! ## The K17 cutoff -/

private theorem kmtHorizonLog_ge_half (K : ℕ) :
    (1 / 2 : ℝ) ≤ kmtHorizonLog K := by
  unfold kmtHorizonLog
  rw [Real.log_pow]
  have hkNat : 1 ≤ K + 1 := by omega
  have hk : (1 : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hkNat
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogNonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num)).le
  calc
    (1 / 2 : ℝ) ≤ 1 * Real.log 2 := by simpa using hhalf
    _ ≤ (((K + 1 : ℕ) : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hk hlogNonneg

private theorem kmtCoarseScale_nonneg
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ kmtCoarseScale K x := by
  unfold kmtCoarseScale
  nlinarith [kmtHorizonLog_ge_half K]

private theorem kmtCoarseScale_ge_one
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ kmtCoarseScale K x := by
  unfold kmtCoarseScale
  nlinarith [kmtHorizonLog_ge_half K]

/-- H1 in exactly the form consumed by `finiteHorizonKMT_union_tail`. -/
theorem treeKMTCoarseFailure_horizon_tail
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (dyadicNoiseMeasure K).real
        (treeKMTCoarseFailure K (kmtCoarseScale K x)) ≤
      4 * (dyadicHorizon K : ℝ) *
        Real.exp (-(kmtCoarseScale K x / 32)) :=
  treeKMTCoarseFailure_tail K (kmtCoarseScale_nonneg K hx)

/-! ## Final finite-horizon theorem -/

/-- The literal maximum of the committed errors at integer times
`0, ..., 2^K`. -/
def committedSpatialKMTMaximum
    (K : ℕ) (z : DyadicNoiseSpace K) : ℝ :=
  kmtHorizonMaximum K (spatialTreeError K) z

/-- The finite-horizon KMT tail for the committed spatial tree skeletons. -/
theorem committedSpatialSkeleton_finiteHorizon_tail
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (dyadicNoiseMeasure K).real
        {z |
          2094 * Real.log ((2 : ℝ) ^ (K + 1)) + x <
            committedSpatialKMTMaximum K z} ≤
      6 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
  have hcoarse :
      ∀ y : ℝ, 0 ≤ y →
        (dyadicNoiseMeasure K).real
            (treeKMTCoarseFailure K (kmtCoarseScale K y)) ≤
          4 * (dyadicHorizon K : ℝ) *
            Real.exp (-(kmtCoarseScale K y / 32)) := by
    intro y hy
    exact treeKMTCoarseFailure_horizon_tail K hy
  have hpoint :
      ∀ t : ℕ, t ≤ dyadicHorizon K →
      ∀ y u : ℝ, 0 ≤ y → 0 ≤ u →
        (dyadicNoiseMeasure K).real
            ({z | kmtPointThreshold K u < spatialTreeError K t z} \
              treeKMTCoarseFailure K (kmtCoarseScale K y)) ≤
          Real.exp (-(3 * u / 512)) +
            (2 : ℝ) ^ (K + 1) *
              Real.exp
                (-(9 * u ^ 2 /
                  (128 * kmtCoarseScale K y))) := by
    intro t ht y u hy hu
    have ht' : t ≤ 2 ^ K := by
      simpa [dyadicHorizon] using ht
    have htail := spatialTreeError_point_tail K t ht'
      (L := kmtCoarseScale K y) (u := u)
      (kmtCoarseScale_ge_one K hy) hu
    simpa [kmtPointThreshold] using htail
  have htail := finiteHorizonKMT_union_tail
    (μ := dyadicNoiseMeasure K)
    K (spatialTreeError K)
    (fun y => treeKMTCoarseFailure K (kmtCoarseScale K y))
    hcoarse hpoint hx
  simpa [committedSpatialKMTMaximum, kmtHorizonLog] using htail

/-- The tail theorem together with the iid unit-increment laws of both
committed skeletons on the same finite Gaussian product space. -/
theorem committedSpatialSkeleton_finiteHorizon_KMT
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (iIndepFun (spatialGaussianUnitIncrement K)
        (dyadicNoiseMeasure K) ∧
      (∀ j, (dyadicNoiseMeasure K).map
        (spatialGaussianUnitIncrement K j) = gaussianReal 0 1) ∧
      iIndepFun (spatialPoissonUnitIncrement K)
        (dyadicNoiseMeasure K) ∧
      (∀ j, (dyadicNoiseMeasure K).map
        (spatialPoissonUnitIncrement K j) = poisMeasure 1)) ∧
    (dyadicNoiseMeasure K).real
        {z |
          2094 * Real.log ((2 : ℝ) ^ (K + 1)) + x <
            committedSpatialKMTMaximum K z} ≤
      6 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
  exact ⟨committedSpatialSkeleton_increment_laws K,
    committedSpatialSkeleton_finiteHorizon_tail K hx⟩

/-!
THEOREM LIST
* `treeKMTCoarseFailure_eq_empty_of_horizon_lt`
* `treeKMTCoarseFailure_tail`
* `treeKMTCoarseFailure_horizon_tail`
* `committedSpatialKMTMaximum`
* `committedSpatialSkeleton_finiteHorizon_tail`
* `committedSpatialSkeleton_finiteHorizon_KMT`

CLOSES
* Item 1 / H1, including the empty regime `L > 2^K` and the exact
  raw-coordinate generation/length event.
* Item 3, by applying `finiteHorizonKMT_union_tail` to
  `spatialTreeError_point_tail` and the H1 theorem above.
* The final theorem cites `committedSpatialSkeleton_increment_laws`, so the
  iid `Poisson(1)` and iid `N(0,1)` unit-increment laws are included on the
  same source space.

UNFINISHED
* Nothing mathematical is intentionally omitted.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicTreeFiniteHorizon

end

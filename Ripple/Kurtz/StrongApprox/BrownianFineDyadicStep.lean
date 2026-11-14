-- Ripple/Kurtz/StrongApprox/BrownianFineDyadicStep.lean
import Ripple.Kurtz.StrongApprox.BrownianFinePath
import Ripple.Kurtz.StrongApprox.BlockIid

/-!
# Brownian candidate: dyadic increment base and one-level law

Declarations of `BrownianFinePath` used here:
* `BrownianFinePath.brownianFineMeasure` and its first/second marginal lemmas;
* `BrownianFinePath.coarseGaussianInterpolation`;
* `BrownianFinePath.brownianCandidate` and
  `brownianCandidate_natCast`.

Declarations of `FineSchauderSeries` used here:
* `fineGaussian_iIndep`, `fineGaussianCoordinate_map`;
* `fineLeft`, `fineRight`, `fineMidpoint`, `fineTent`;
* `fineLevelTerm`, `finePartial`, `fineSchauderRawLimit`,
  `fineSchauderLimit`, and `fineSchauderConvergenceEvent_ae`.

The child vector is indexed by
`FineLevelIndex K r ⊕ FineLevelIndex K r`: `inl q` is the left half of parent
`q`, and `inr q` is its right half.  This is a bijective enumeration of all
level-`r+1` cells, although the chronological reindexing is intentionally not
packaged in this file.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.BrownianFineDyadicStep

open BrownianFinePath FineSchauderSeries
open DyadicGaussianTree DyadicSpatialSkeleton
open DyadicConditionalPoissonPath

/-! ## Paths, increments, and the paired child vector -/

noncomputable def brownianDyadicIncrement
    (K r : ℕ) (q : FineLevelIndex K r)
    (omega : BrownianFineSpace K) : ℝ :=
  brownianCandidate K (fineRight K r q) omega -
    brownianCandidate K (fineLeft K r q) omega

noncomputable def brownianDyadicIncrementVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    FineLevelIndex K r → ℝ :=
  fun q => brownianDyadicIncrement K r q omega

noncomputable def partialBrownianCandidate
    (K r : ℕ) (t : ℝ) (omega : BrownianFineSpace K) : ℝ :=
  coarseGaussianInterpolation K omega.1 t +
    finePartial K r omega.2 t

noncomputable def fineLevelReadout
    (K r : ℕ) (z : FineNoiseSpace K) : FineLevelIndex K r → ℝ :=
  fun q => fineGaussianCoordinate K r q z

noncomputable def fineLevelVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    FineLevelIndex K r → ℝ :=
  fineLevelReadout K r omega.2

noncomputable def brownianChildPairVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    FineLevelIndex K r ⊕ FineLevelIndex K r → ℝ
  | Sum.inl q =>
      brownianCandidate K (fineMidpoint K r q) omega -
        brownianCandidate K (fineLeft K r q) omega
  | Sum.inr q =>
      brownianCandidate K (fineRight K r q) omega -
        brownianCandidate K (fineMidpoint K r q) omega

/-- The only deterministic geometry still required for the full induction:
the tree interpolation plus all levels below `r` are affine on every
level-`r` parent cell. -/
def PartialMidpointAffine (K r : ℕ) : Prop :=
  ∀ omega q,
    partialBrownianCandidate K r (fineMidpoint K r q) omega =
      (partialBrownianCandidate K r (fineLeft K r q) omega +
        partialBrownianCandidate K r (fineRight K r q) omega) / 2

@[fun_prop]
theorem measurable_brownianDyadicIncrementVector (K r : ℕ) :
    Measurable (brownianDyadicIncrementVector K r) := by
  apply measurable_pi_lambda
  intro q
  exact (measurable_brownianCandidate K (fineRight K r q)).sub
    (measurable_brownianCandidate K (fineLeft K r q))

@[fun_prop]
theorem measurable_fineLevelReadout (K r : ℕ) :
    Measurable (fineLevelReadout K r) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_fineGaussianCoordinate K r q

@[fun_prop]
theorem measurable_fineLevelVector (K r : ℕ) :
    Measurable (fineLevelVector K r) :=
  (measurable_fineLevelReadout K r).comp measurable_snd

@[fun_prop]
theorem measurable_brownianChildPairVector (K r : ℕ) :
    Measurable (brownianChildPairVector K r) := by
  apply measurable_pi_lambda
  intro c
  cases c with
  | inl q =>
      exact (measurable_brownianCandidate K (fineMidpoint K r q)).sub
        (measurable_brownianCandidate K (fineLeft K r q))
  | inr q =>
      exact (measurable_brownianCandidate K (fineRight K r q)).sub
        (measurable_brownianCandidate K (fineMidpoint K r q))

/-! ## (a): all levels at or above the grid vanish at grid points -/

/-- A level-`m` tent vanishes at every level-`r` grid point when `r ≤ m`. -/
theorem fineTent_grid_zero_of_le
    (K r m k : ℕ) (hrm : r ≤ m) (q : FineLevelIndex K m) :
    fineTent K m q ((k : ℝ) / (2 : ℝ) ^ r) = 0 := by
  apply le_antisymm
  · apply not_lt.mp
    intro hpos
    have hmem := (fineTent_pos_iff K m q _).mp hpos
    let d := m - r
    have hm : r + d = m := Nat.add_sub_of_le hrm
    have hpow :
        (2 : ℝ) ^ m = (2 : ℝ) ^ r * (2 : ℝ) ^ d := by
      rw [← pow_add, hm]
    have hrpos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
    have hdpos : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
    have hleft := hmem.1
    have hright := hmem.2
    simp only [fineLeft, fineRight, hpow] at hleft hright
    have hcrossLeft :=
      (div_lt_div_iff₀ (mul_pos hrpos hdpos) hrpos).mp hleft
    have hcrossRight :=
      (div_lt_div_iff₀ hrpos (mul_pos hrpos hdpos)).mp hright
    have hflat :
        (fineFlatIndex K m q : ℝ) <
          (k : ℝ) * (2 : ℝ) ^ d := by
      refine lt_of_mul_lt_mul_right ?_ hrpos.le
      linarith
    have hnext :
        (k : ℝ) * (2 : ℝ) ^ d <
          (fineFlatIndex K m q : ℝ) + 1 := by
      refine lt_of_mul_lt_mul_right ?_ hrpos.le
      linarith
    have hflatNat : fineFlatIndex K m q < k * 2 ^ d := by
      exact_mod_cast hflat
    have hnextNat : k * 2 ^ d < fineFlatIndex K m q + 1 := by
      exact_mod_cast hnext
    omega
  · exact fineTent_nonneg K m q _

/-- Consequently every complete level term at or above `r` vanishes on the
level-`r` grid. -/
theorem fineLevelTerm_grid_zero_of_le
    (K r m k : ℕ) (hrm : r ≤ m) (z : FineNoiseSpace K) :
    fineLevelTerm K m z ((k : ℝ) / (2 : ℝ) ^ r) = 0 := by
  unfold fineLevelTerm
  have hsum :
      (∑ q : FineLevelIndex K m,
        fineGaussianCoordinate K m q z *
          fineTent K m q ((k : ℝ) / (2 : ℝ) ^ r)) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [fineTent_grid_zero_of_le K r m k hrm q, mul_zero]
  rw [hsum, mul_zero]

/-- At a level-`r` grid point the raw infinite series is exactly its first
`r` levels. -/
theorem fineSchauderRawLimit_grid_eq_partial
    (K r k : ℕ) (z : FineNoiseSpace K) :
    fineSchauderRawLimit K z ((k : ℝ) / (2 : ℝ) ^ r) =
      finePartial K r z ((k : ℝ) / (2 : ℝ) ^ r) := by
  unfold fineSchauderRawLimit finePartial
  rw [tsum_eq_sum (s := Finset.range r) (by
    intro m hm
    have hrm : r ≤ m := by
      simpa only [Finset.mem_range, not_lt] using hm
    exact fineLevelTerm_grid_zero_of_le K r m k hrm z)]

/-- The same identity for the totalized limit on its probability-one
convergence event. -/
theorem fineSchauderLimit_grid_eq_partial_of_mem
    (K r k : ℕ) (z : FineNoiseSpace K)
    (hz : z ∈ FineSchauderConvergenceEvent K) :
    fineSchauderLimit K z ((k : ℝ) / (2 : ℝ) ^ r) =
      finePartial K r z ((k : ℝ) / (2 : ℝ) ^ r) := by
  unfold fineSchauderLimit
  rw [if_pos hz]
  exact fineSchauderRawLimit_grid_eq_partial K r k z

/-- The parent midpoint is the odd point of the next dyadic grid. -/
theorem fineMidpoint_eq_next_grid
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineMidpoint K r q =
      ((2 * fineFlatIndex K r q + 1 : ℕ) : ℝ) /
        (2 : ℝ) ^ (r + 1) := by
  unfold fineMidpoint fineLeft fineRight
  rw [pow_succ]
  push_cast
  field_simp [pow_ne_zero r (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Exact contribution of the current coefficient at its parent midpoint. -/
theorem fineLevelTerm_midpoint
    (K r : ℕ) (z : FineNoiseSpace K) (q : FineLevelIndex K r) :
    fineLevelTerm K r z (fineMidpoint K r q) =
      fineScale r * fineGaussianCoordinate K r q z := by
  classical
  have hlr : fineLeft K r q < fineRight K r q := by
    unfold fineLeft fineRight
    apply div_lt_div_of_pos_right _ (pow_pos (by norm_num) r)
    push_cast
    norm_num
  have htq :
      fineMidpoint K r q ∈
        Ioo (fineLeft K r q) (fineRight K r q) := by
    unfold fineMidpoint
    constructor <;> linarith
  have hzero : ∀ p : FineLevelIndex K r, p ≠ q →
      fineTent K r p (fineMidpoint K r q) = 0 := by
    intro p hp
    apply le_antisymm
    · apply not_lt.mp
      intro hpos
      have htp := (fineTent_pos_iff K r p _).mp hpos
      exact Set.disjoint_left.mp
        (fineOpenSupports_disjoint K r hp) htp htq
    · exact fineTent_nonneg K r p _
  have hsum :
      (∑ p : FineLevelIndex K r,
        fineGaussianCoordinate K r p z *
          fineTent K r p (fineMidpoint K r q)) =
        fineGaussianCoordinate K r q z := by
    calc
      _ = fineGaussianCoordinate K r q z *
          fineTent K r q (fineMidpoint K r q) := by
        apply Finset.sum_eq_single q
        · intro p _ hp
          rw [hzero p hp, mul_zero]
        · simp
      _ = fineGaussianCoordinate K r q z := by
        rw [fineTent_midpoint, mul_one]
  unfold fineLevelTerm
  rw [hsum]

/-- Adding one stored level adds exactly its level term. -/
theorem finePartial_succ
    (K r : ℕ) (z : FineNoiseSpace K) (t : ℝ) :
    finePartial K (r + 1) z t =
      finePartial K r z t + fineLevelTerm K r z t := by
  unfold finePartial
  rw [Finset.sum_range_succ]

/-! ## The coefficient is exactly sqrt(length)/2 -/

private theorem fineScale_succ_eq (r : ℕ) :
    fineScale (r + 1) = fineScale r / Real.sqrt 2 := by
  unfold fineScale
  rw [show r + 1 + 2 = (r + 2) + 1 by omega, pow_succ]
  simp [div_eq_mul_inv]

private theorem two_mul_fineScale_sq : ∀ r : ℕ,
    (2 * fineScale r) ^ 2 = (dyadicVariance 0 r : ℝ)
  | 0 => by
      rw [dyadicVariance_self]
      simp [fineScale, inv_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  | r + 1 => by
      rw [fineScale_succ_eq, dyadicVariance_succ]
      change
        (2 * (fineScale r / Real.sqrt 2)) ^ 2 =
          (dyadicVariance 0 r : ℝ) / 2
      calc
        (2 * (fineScale r / Real.sqrt 2)) ^ 2 =
            (2 * fineScale r) ^ 2 / (Real.sqrt 2) ^ 2 := by ring
        _ = (dyadicVariance 0 r : ℝ) / 2 := by
          rw [two_mul_fineScale_sq r,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The stored Schauder coefficient is `sqrt(2^(-r))/2`. -/
theorem fineScale_eq_sqrt_variance_div_two (r : ℕ) :
    fineScale r = Real.sqrt (dyadicVariance 0 r : ℝ) / 2 := by
  have hsquare := two_mul_fineScale_sq r
  have hroot := Real.sq_sqrt (show 0 ≤ (dyadicVariance 0 r : ℝ) by positivity)
  have hleft : 0 ≤ 2 * fineScale r := by
    unfold fineScale
    positivity
  have hright : 0 ≤ Real.sqrt (dyadicVariance 0 r : ℝ) :=
    Real.sqrt_nonneg _
  have heq : 2 * fineScale r = Real.sqrt (dyadicVariance 0 r : ℝ) := by
    nlinarith
  linarith

/-! ## Midpoint identity from the single remaining affine lemma -/

private theorem brownianFine_convergence_ae (K : ℕ) :
    ∀ᵐ omega ∂brownianFineMeasure K,
      omega.2 ∈ FineSchauderConvergenceEvent K := by
  refine MeasureTheory.ae_of_ae_map
    (p := fun z : FineNoiseSpace K => z ∈ FineSchauderConvergenceEvent K)
    measurable_snd.aemeasurable ?_
  rw [brownianFineMeasure_map_snd]
  exact fineSchauderConvergenceEvent_ae K

/-- On the convergence event, lower affinity plus the exact current-level
midpoint term gives the Brownian bridge midpoint identity. -/
theorem brownianCandidate_midpoint_identity_ae
    (K r : ℕ) (hAffine : PartialMidpointAffine K r) :
    ∀ᵐ omega ∂brownianFineMeasure K, ∀ q : FineLevelIndex K r,
      brownianCandidate K (fineMidpoint K r q) omega =
        (brownianCandidate K (fineLeft K r q) omega +
          brownianCandidate K (fineRight K r q) omega) / 2 +
        fineScale r * fineGaussianCoordinate K r q omega.2 := by
  filter_upwards [brownianFine_convergence_ae K] with omega hconv
  intro q
  have hleft :=
    fineSchauderLimit_grid_eq_partial_of_mem K r
      (fineFlatIndex K r q) omega.2 hconv
  have hright :=
    fineSchauderLimit_grid_eq_partial_of_mem K r
      (fineFlatIndex K r q + 1) omega.2 hconv
  have hmid :=
    fineSchauderLimit_grid_eq_partial_of_mem K (r + 1)
      (2 * fineFlatIndex K r q + 1) omega.2 hconv
  have hleft' :
      fineSchauderLimit K omega.2 (fineLeft K r q) =
        finePartial K r omega.2 (fineLeft K r q) := by
    simpa only [fineLeft] using hleft
  have hright' :
      fineSchauderLimit K omega.2 (fineRight K r q) =
        finePartial K r omega.2 (fineRight K r q) := by
    have hright2 := hright
    push_cast at hright2
    simpa only [fineRight] using hright2
  have hmid' :
      fineSchauderLimit K omega.2 (fineMidpoint K r q) =
        finePartial K r omega.2 (fineMidpoint K r q) +
          fineScale r * fineGaussianCoordinate K r q omega.2 := by
    rw [fineMidpoint_eq_next_grid K r q] at ⊢
    calc
      fineSchauderLimit K omega.2
          (((2 * fineFlatIndex K r q + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (r + 1)) =
        finePartial K (r + 1) omega.2
          (((2 * fineFlatIndex K r q + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (r + 1)) := hmid
      _ = finePartial K r omega.2
            (((2 * fineFlatIndex K r q + 1 : ℕ) : ℝ) /
              (2 : ℝ) ^ (r + 1)) +
          fineLevelTerm K r omega.2
            (((2 * fineFlatIndex K r q + 1 : ℕ) : ℝ) /
              (2 : ℝ) ^ (r + 1)) :=
        finePartial_succ K r omega.2 _
      _ = _ := by
        rw [← fineMidpoint_eq_next_grid K r q,
          fineLevelTerm_midpoint]
  have hbase := hAffine omega q
  unfold partialBrownianCandidate at hbase
  unfold brownianCandidate
  rw [hleft', hright', hmid']
  linarith

/-! ## Fresh coefficient vector and the base vector law -/

private theorem fineSigma_injective (K r : ℕ) :
    Function.Injective
      (fun q : FineLevelIndex K r =>
        (⟨r, q⟩ : FineNoiseIndex K)) := by
  intro q p h
  cases h
  rfl

/-- The entire current-level coefficient vector is iid standard Gaussian. -/
theorem fineLevelReadout_map (K r : ℕ) :
    (fineGaussianMeasure K).map (fineLevelReadout K r) =
      Measure.pi (fun _ : FineLevelIndex K r => gaussianReal 0 1) := by
  have hind0 := (fineGaussian_iIndep K).precomp (fineSigma_injective K r)
  have hind :
      iIndepFun (fun q => fineGaussianCoordinate K r q)
        (fineGaussianMeasure K) := by
    simpa [fineGaussianCoordinate] using hind0
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun q => (measurable_fineGaussianCoordinate K r q).aemeasurable)] at hind
  calc
    (fineGaussianMeasure K).map (fineLevelReadout K r) =
        Measure.pi (fun q : FineLevelIndex K r =>
          (fineGaussianMeasure K).map
            (fineGaussianCoordinate K r q)) := by
      simpa [fineLevelReadout] using hind
    _ = Measure.pi (fun _ : FineLevelIndex K r => gaussianReal 0 1) := by
      congr 1
      funext q
      exact fineGaussianCoordinate_map K r q

/-- The same fresh-vector law on the tree-times-fine product source. -/
theorem fineLevelVector_map (K r : ℕ) :
    (brownianFineMeasure K).map (fineLevelVector K r) =
      Measure.pi (fun _ : FineLevelIndex K r => gaussianReal 0 1) := by
  rw [show fineLevelVector K r = fineLevelReadout K r ∘ Prod.snd by rfl,
    ← Measure.map_map (measurable_fineLevelReadout K r) measurable_snd,
    brownianFineMeasure_map_snd,
    fineLevelReadout_map]

private theorem zeroLevel_fst_injective (K : ℕ) :
    Function.Injective
      (fun q : FineLevelIndex K 0 => q.1) := by
  intro q p h
  apply Prod.ext h
  apply Fin.ext
  have h1 := q.2.isLt
  have h2 := p.2.isLt
  simp only [pow_zero] at h1 h2
  omega

noncomputable def treeUnitReadout
    (K : ℕ) (x : DyadicNoiseSpace K) : FineLevelIndex K 0 → ℝ :=
  fun q => spatialGaussianUnitIncrement K q.1 x

@[fun_prop]
theorem measurable_treeUnitReadout (K : ℕ) :
    Measurable (treeUnitReadout K) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_spatialGaussianUnitIncrement K q.1

private theorem treeUnitReadout_map (K : ℕ) :
    (dyadicNoiseMeasure K).map (treeUnitReadout K) =
      Measure.pi (fun _ : FineLevelIndex K 0 => gaussianReal 0 1) := by
  have hind :=
    (spatialGaussianUnitIncrement_iIndep K).precomp
      (zeroLevel_fst_injective K)
  replace hind := (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun q : FineLevelIndex K 0 => spatialGaussianUnitIncrement K q.1)
    (fun q => (measurable_spatialGaussianUnitIncrement K q.1).aemeasurable)).mp hind
  calc
    (dyadicNoiseMeasure K).map (treeUnitReadout K) =
        Measure.pi (fun q : FineLevelIndex K 0 =>
          (dyadicNoiseMeasure K).map
            (spatialGaussianUnitIncrement K q.1)) := by
      simpa [treeUnitReadout] using hind
    _ = Measure.pi (fun _ : FineLevelIndex K 0 => gaussianReal 0 1) := by
      congr 1
      funext q
      exact spatialGaussianUnitIncrement_map K q.1

/-- At level zero the Brownian candidate increments are exactly the committed
unit Gaussian increments. -/
theorem brownianDyadicIncrement_zero_eq_treeUnit
    (K : ℕ) (q : FineLevelIndex K 0)
    (omega : BrownianFineSpace K) :
    brownianDyadicIncrement K 0 q omega = treeUnitReadout K omega.1 q := by
  have hsecond : q.2.1 = 0 := by omega
  have hleft : fineLeft K 0 q = (q.1.1 : ℝ) := by
    unfold fineLeft fineFlatIndex
    norm_num [hsecond]
  have hright : fineRight K 0 q = ((q.1.1 + 1 : ℕ) : ℝ) := by
    unfold fineRight fineFlatIndex
    norm_num [hsecond]
  unfold brownianDyadicIncrement
  rw [hleft, hright,
    brownianCandidate_natCast K (q.1.1 + 1) (by omega),
    brownianCandidate_natCast K q.1.1 (Nat.le_of_lt q.1.2)]
  simpa [treeUnitReadout] using
    spatialGaussianSkeleton_succ_sub K q.1.1 q.1.2 omega.1

/-- Base case `r=0`: the whole vector, not only each marginal, has iid
`N(0,1)` law. -/
theorem brownianDyadicIncrementVector_base_map (K : ℕ) :
    (brownianFineMeasure K).map (brownianDyadicIncrementVector K 0) =
      Measure.pi (fun _ : FineLevelIndex K 0 => gaussianReal 0 1) := by
  have hfun : brownianDyadicIncrementVector K 0 =
      treeUnitReadout K ∘ Prod.fst := by
    funext omega q
    exact brownianDyadicIncrement_zero_eq_treeUnit K q omega
  rw [hfun,
    ← Measure.map_map (measurable_treeUnitReadout K) measurable_fst,
    brownianFineMeasure_map_fst,
    treeUnitReadout_map]

/-! ## (b)+(c): the complete product-law refinement step -/

noncomputable def refinedGaussianVector
    {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (parent fresh : ι → ℝ) : ι ⊕ ι → ℝ :=
  dyadicRefine (gaussianHalfSplit v) (parent, fresh)

/-- Abstract full-vector split: iid `N(0,v)` parents plus an independent iid
standard fresh vector become iid `N(0,v/2)` children. -/
theorem refinedGaussianVector_map
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {v : ℝ≥0} {parent fresh : Omega → ι → ℝ}
    (hparentM : Measurable parent) (hfreshM : Measurable fresh)
    (hparentLaw :
      mu.map parent = Measure.pi (fun _ : ι => gaussianReal 0 v))
    (hfreshLaw :
      mu.map fresh = Measure.pi (fun _ : ι => gaussianReal 0 1))
    (hind : IndepFun parent fresh mu) :
    mu.map (fun omega =>
        refinedGaussianVector v (parent omega) (fresh omega)) =
      Measure.pi (fun _ : ι ⊕ ι => gaussianReal 0 (v / 2)) := by
  have hjoint :=
    hind.map_prod_eq_prod_map_map hparentM.aemeasurable hfreshM.aemeasurable
  rw [hparentLaw, hfreshLaw] at hjoint
  have hrefine :=
    dyadicRefine_measurePreserving
      (ι := ι)
      (μA := gaussianReal 0 v)
      (μB := gaussianReal 0 1)
      (μD := gaussianReal 0 (v / 2))
      (split := gaussianHalfSplit v)
      (measurable_gaussianHalfSplit v)
      (gaussianHalfSplit_measurePreserving v).map_eq
  have hpair : Measurable (fun omega => (parent omega, fresh omega)) :=
    hparentM.prodMk hfreshM
  calc
    mu.map (fun omega =>
        refinedGaussianVector v (parent omega) (fresh omega)) =
      (mu.map (fun omega => (parent omega, fresh omega))).map
        (dyadicRefine (gaussianHalfSplit v)) := by
      simpa [refinedGaussianVector, Function.comp_def] using
        (Measure.map_map hrefine.measurable hpair).symm
    _ = Measure.pi (fun _ : ι ⊕ ι => gaussianReal 0 (v / 2)) := by
      rw [hjoint, hrefine.map_eq]

/-- The concrete child increments agree almost surely with the Gaussian
refinement map once lower-part midpoint affinity is supplied. -/
theorem brownianChildPairVector_ae_eq_refined
    (K r : ℕ) (hAffine : PartialMidpointAffine K r) :
    brownianChildPairVector K r =ᵐ[brownianFineMeasure K]
      fun omega => refinedGaussianVector (dyadicVariance 0 r)
        (brownianDyadicIncrementVector K r omega)
        (fineLevelVector K r omega) := by
  filter_upwards [brownianCandidate_midpoint_identity_ae K r hAffine]
    with omega hmid
  funext c
  cases c with
  | inl q =>
      change
        brownianCandidate K (fineMidpoint K r q) omega -
            brownianCandidate K (fineLeft K r q) omega =
          ((brownianCandidate K (fineRight K r q) omega -
              brownianCandidate K (fineLeft K r q) omega) +
            Real.sqrt (dyadicVariance 0 r : ℝ) *
              fineGaussianCoordinate K r q omega.2) / 2
      rw [hmid q, fineScale_eq_sqrt_variance_div_two]
      ring
  | inr q =>
      change
        brownianCandidate K (fineRight K r q) omega -
            brownianCandidate K (fineMidpoint K r q) omega =
          ((brownianCandidate K (fineRight K r q) omega -
              brownianCandidate K (fineLeft K r q) omega) -
            Real.sqrt (dyadicVariance 0 r : ℝ) *
              fineGaussianCoordinate K r q omega.2) / 2
      rw [hmid q, fineScale_eq_sqrt_variance_div_two]
      ring

/-- Concrete one-level induction step.  The two hypotheses are exactly the
remaining adapters: lower-part midpoint affinity, and independence of the
parent vector from the fresh level. -/
theorem brownianChildPairVector_map_of_parent
    (K r : ℕ)
    (hparent :
      (brownianFineMeasure K).map
          (brownianDyadicIncrementVector K r) =
        Measure.pi (fun _ : FineLevelIndex K r =>
          gaussianReal 0 (dyadicVariance 0 r)))
    (hind :
      IndepFun (brownianDyadicIncrementVector K r)
        (fineLevelVector K r) (brownianFineMeasure K))
    (hAffine : PartialMidpointAffine K r) :
    (brownianFineMeasure K).map (brownianChildPairVector K r) =
      Measure.pi (fun _ : FineLevelIndex K r ⊕ FineLevelIndex K r =>
        gaussianReal 0 (dyadicVariance 0 (r + 1))) := by
  have hrefine :=
    refinedGaussianVector_map
      (mu := brownianFineMeasure K)
      (v := dyadicVariance 0 r)
      (parent := brownianDyadicIncrementVector K r)
      (fresh := fineLevelVector K r)
      (measurable_brownianDyadicIncrementVector K r)
      (measurable_fineLevelVector K r)
      hparent (fineLevelVector_map K r) hind
  calc
    (brownianFineMeasure K).map (brownianChildPairVector K r) =
        (brownianFineMeasure K).map
          (fun omega => refinedGaussianVector (dyadicVariance 0 r)
            (brownianDyadicIncrementVector K r omega)
            (fineLevelVector K r omega)) :=
      Measure.map_congr
        (brownianChildPairVector_ae_eq_refined K r hAffine)
    _ = Measure.pi
        (fun _ : FineLevelIndex K r ⊕ FineLevelIndex K r =>
          gaussianReal 0 (dyadicVariance 0 (r + 1))) := by
      simpa only [dyadicVariance_succ] using hrefine

/-!
THEOREM LIST
* `fineTent_grid_zero_of_le`
* `fineLevelTerm_grid_zero_of_le`
* `fineSchauderRawLimit_grid_eq_partial`
* `fineSchauderLimit_grid_eq_partial_of_mem`
* `fineMidpoint_eq_next_grid`
* `fineLevelTerm_midpoint`
* `fineScale_eq_sqrt_variance_div_two`
* `brownianCandidate_midpoint_identity_ae`
* `fineLevelReadout_map`, `fineLevelVector_map`
* `brownianDyadicIncrementVector_base_map`
* `refinedGaussianVector_map`
* `brownianChildPairVector_ae_eq_refined`
* `brownianChildPairVector_map_of_parent`

CLOSES
* Item (a): every level `m ≥ r` vanishes at every level-`r` grid point;
  on the convergence event the full fine series therefore equals `finePartial r`.
* Base `r=0`: the entire increment vector has product `N(0,1)` law.
* The current-level coefficient vector has its full iid standard Gaussian law.
* Items (b)+(c), one-level form: `gaussianHalfSplit` is lifted to the complete
  parent vector by `dyadicRefine_measurePreserving`, yielding one product law
  for all child increments at once.

UNFINISHED
* `PartialMidpointAffine K r` for arbitrary `r`.  This is the deterministic
  piecewise-affine lemma for the coarse ramp and levels `< r`; it is not in
  `BrownianFinePath` or `FineSchauderSeries`.
* `IndepFun (brownianDyadicIncrementVector K r) (fineLevelVector K r)` for
  arbitrary `r`.  Its proof must factor the parent vector through the tree and
  the finite coordinate block of levels `< r`, then use
  `fineGaussian_iIndep.indepFun_finset` against the level-`r` block.
* The chronological measurable equivalence from the paired child index
  `FineLevelIndex K r ⊕ FineLevelIndex K r` to
  `FineLevelIndex K (r+1)`, mapping `inl (j,c)` to `(j,2c)` and
  `inr (j,c)` to `(j,2c+1)`, followed by the literal induction.
* No full all-`r` headline is asserted until those three adapters are proved.
END
-/

end Ripple.Kurtz.StrongApprox.BrownianFineDyadicStep

end

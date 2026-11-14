-- Ripple/Kurtz/StrongApprox/BrownianFineDyadicAdapters.lean
import Ripple.Kurtz.StrongApprox.BrownianFineDyadicStep

/-!
# Brownian dyadic affinity and fresh-level independence

Declarations of `BrownianFineDyadicStep` used here:
* `PartialMidpointAffine`, `partialBrownianCandidate`;
* `brownianDyadicIncrementVector`, `fineLevelVector`, `fineLevelReadout`;
* `fineSchauderLimit_grid_eq_partial_of_mem`;
* `fineMidpoint_eq_next_grid`;
* `brownianChildPairVector_map_of_parent`.

The deterministic half proves that every kink of a lower Schauder tent is a
level-`r` grid point.  Hence no kink lies in the interior of a level-`r` cell,
and midpoint affinity follows on that cell.

For independence, `FinePastIndex K r` is the finite block of all coordinates
at stored levels `< r`.  The parent increment vector factors, almost surely,
through the tree coordinate and this block.  The finite past block is
independent of the level-`r` block by
`fineGaussian_iIndep.indepFun_finset`; a product-measure reassociation then
adjoins the independent tree coordinate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.BrownianFineDyadicAdapters

open BrownianFinePath BrownianFineDyadicStep FineSchauderSeries
open DyadicGaussianTree DyadicSpatialSkeleton
open DyadicConditionalPoissonPath

/-! ## Dyadic-grid arithmetic -/

private def dyadicGridPoint (r k : ℕ) : ℝ :=
  (k : ℝ) / (2 : ℝ) ^ r

private theorem dyadicGridPoint_lt_succ (r k : ℕ) :
    dyadicGridPoint r k < dyadicGridPoint r (k + 1) := by
  unfold dyadicGridPoint
  apply div_lt_div_of_pos_right
  · exact_mod_cast Nat.lt_succ_self k
  · positivity

private theorem dyadicGridPoint_refine
    (m r k : ℕ) (hmr : m ≤ r) :
    dyadicGridPoint m k =
      dyadicGridPoint r (k * 2 ^ (r - m)) := by
  unfold dyadicGridPoint
  have hpow :
      (2 : ℝ) ^ r = (2 : ℝ) ^ m * (2 : ℝ) ^ (r - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmr]
  rw [hpow]
  push_cast
  field_simp [pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero (r - m) (by norm_num : (2 : ℝ) ≠ 0)]

private theorem dyadicGridPoint_natCast (r i : ℕ) :
    dyadicGridPoint r (i * 2 ^ r) = (i : ℝ) := by
  simpa [dyadicGridPoint] using
    (dyadicGridPoint_refine 0 r i (Nat.zero_le r)).symm

/-- A grid point cannot lie strictly inside one adjacent grid cell. -/
private theorem dyadicGridPoint_le_or_right_le
    (r h k : ℕ) :
    dyadicGridPoint r h ≤ dyadicGridPoint r k ∨
      dyadicGridPoint r (k + 1) ≤ dyadicGridPoint r h := by
  rcases le_or_gt h k with hle | hlt
  · left
    unfold dyadicGridPoint
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hle
    · positivity
  · right
    have hsucc : k + 1 ≤ h := Nat.succ_le_iff.mpr hlt
    unfold dyadicGridPoint
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hsucc
    · positivity

private theorem fineLeft_lt_right_local
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineLeft K r q < fineRight K r q := by
  unfold fineLeft fineRight
  apply div_lt_div_of_pos_right
  · push_cast
    norm_num
  · positivity

private theorem fineRight_eq_gridPoint
    (K r : ℕ) (q : FineLevelIndex K r) :
    fineRight K r q = dyadicGridPoint r (fineFlatIndex K r q + 1) := by
  simp [fineRight, dyadicGridPoint]

/-! ## The coarse interpolation is affine on every dyadic cell -/

private theorem clippedRamp_eq_zero_of_le
    (i : ℕ) {t : ℝ} (ht : t ≤ (i : ℝ)) :
    clippedRamp i t = 0 := by
  unfold clippedRamp
  rw [max_eq_left (by linarith)]
  norm_num

private theorem clippedRamp_eq_one_of_le
    (i : ℕ) {t : ℝ} (ht : (i : ℝ) + 1 ≤ t) :
    clippedRamp i t = 1 := by
  unfold clippedRamp
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

private theorem clippedRamp_eq_sub_of_mem
    (i : ℕ) {t : ℝ}
    (hleft : (i : ℝ) ≤ t) (hright : t ≤ (i : ℝ) + 1) :
    clippedRamp i t = t - i := by
  unfold clippedRamp
  rw [max_eq_right (by linarith), min_eq_right (by linarith)]

private theorem clippedRamp_midpoint_affine
    (i r k : ℕ) :
    clippedRamp i
        ((dyadicGridPoint r k + dyadicGridPoint r (k + 1)) / 2) =
      (clippedRamp i (dyadicGridPoint r k) +
        clippedRamp i (dyadicGridPoint r (k + 1))) / 2 := by
  let x := dyadicGridPoint r k
  let y := dyadicGridPoint r (k + 1)
  have hxy : x < y := by
    simpa [x, y] using dyadicGridPoint_lt_succ r k
  by_cases hyLeft : y ≤ (i : ℝ)
  · have hmidZero : clippedRamp i ((x + y) / 2) = 0 :=
      clippedRamp_eq_zero_of_le i (by linarith)
    have hxZero : clippedRamp i x = 0 :=
      clippedRamp_eq_zero_of_le i (by linarith)
    have hyZero : clippedRamp i y = 0 :=
      clippedRamp_eq_zero_of_le i hyLeft
    simpa [x, y, hmidZero, hxZero, hyZero]
  · by_cases hxRight : (i : ℝ) + 1 ≤ x
    · have hmidOne : clippedRamp i ((x + y) / 2) = 1 :=
        clippedRamp_eq_one_of_le i (by linarith)
      have hxOne : clippedRamp i x = 1 :=
        clippedRamp_eq_one_of_le i hxRight
      have hyOne : clippedRamp i y = 1 :=
        clippedRamp_eq_one_of_le i (by linarith)
      simpa [x, y, hmidOne, hxOne, hyOne]
    · have hiGrid :
          dyadicGridPoint r (i * 2 ^ r) = (i : ℝ) :=
        dyadicGridPoint_natCast r i
      have hiSep :=
        dyadicGridPoint_le_or_right_le r (i * 2 ^ r) k
      have hiLeft : (i : ℝ) ≤ x := by
        rcases hiSep with hi | hi
        · simpa [x, hiGrid] using hi
        · exfalso
          apply hyLeft
          simpa [y, hiGrid] using hi
      have hiSuccGrid :
          dyadicGridPoint r ((i + 1) * 2 ^ r) = ((i + 1 : ℕ) : ℝ) :=
        dyadicGridPoint_natCast r (i + 1)
      have hiSuccSep :=
        dyadicGridPoint_le_or_right_le r ((i + 1) * 2 ^ r) k
      have hyRight : y ≤ (i : ℝ) + 1 := by
        rcases hiSuccSep with hi | hi
        · exfalso
          apply hxRight
          simpa [x, hiSuccGrid] using hi
        · simpa [y, hiSuccGrid] using hi
      have hmidLinear :
          clippedRamp i ((x + y) / 2) = (x + y) / 2 - i :=
        clippedRamp_eq_sub_of_mem i (by linarith) (by linarith)
      have hxLinear : clippedRamp i x = x - i :=
        clippedRamp_eq_sub_of_mem i hiLeft (by linarith)
      have hyLinear : clippedRamp i y = y - i :=
        clippedRamp_eq_sub_of_mem i (by linarith) hyRight
      rw [hmidLinear, hxLinear, hyLinear]
      ring

private theorem coarseGaussianInterpolation_midpoint_affine
    (K r : ℕ) (x : DyadicNoiseSpace K)
    (q : FineLevelIndex K r) :
    coarseGaussianInterpolation K x (fineMidpoint K r q) =
      (coarseGaussianInterpolation K x (fineLeft K r q) +
        coarseGaussianInterpolation K x (fineRight K r q)) / 2 := by
  let k := fineFlatIndex K r q
  have hleft : fineLeft K r q = dyadicGridPoint r k := rfl
  have hright : fineRight K r q = dyadicGridPoint r (k + 1) :=
    fineRight_eq_gridPoint K r q
  unfold fineMidpoint
  rw [hleft, hright]
  unfold coarseGaussianInterpolation
  calc
    (∑ i ∈ Finset.range (2 ^ K),
        spatialGaussianUnitIncrementNat K x i *
          clippedRamp i
            ((dyadicGridPoint r k + dyadicGridPoint r (k + 1)) / 2)) =
      ∑ i ∈ Finset.range (2 ^ K),
        (spatialGaussianUnitIncrementNat K x i *
            clippedRamp i (dyadicGridPoint r k) +
          spatialGaussianUnitIncrementNat K x i *
            clippedRamp i (dyadicGridPoint r (k + 1))) / 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [clippedRamp_midpoint_affine i r k]
      ring
    _ =
      ((∑ i ∈ Finset.range (2 ^ K),
          spatialGaussianUnitIncrementNat K x i *
            clippedRamp i (dyadicGridPoint r k)) +
        ∑ i ∈ Finset.range (2 ^ K),
          spatialGaussianUnitIncrementNat K x i *
            clippedRamp i (dyadicGridPoint r (k + 1))) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]

/-! ## Lower Schauder tents are affine on every finer cell -/

private theorem schauderTent_eq_zero_of_le_left
    {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    schauderTent a b t = 0 := by
  apply schauderTent_eq_zero_of_not_mem hab
  intro hmem
  exact (not_lt_of_ge ht) hmem.1

private theorem schauderTent_eq_zero_of_right_le
    {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    schauderTent a b t = 0 := by
  apply schauderTent_eq_zero_of_not_mem hab
  intro hmem
  exact (not_lt_of_ge ht) hmem.2

private theorem schauderTent_eq_rising
    {a b t : ℝ} (hab : a < b)
    (hat : a ≤ t) (htmid : t ≤ (a + b) / 2) :
    schauderTent a b t = 2 * (t - a) / (b - a) := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hnum : 2 * t - a - b ≤ 0 := by linarith
  have hquot : (2 * t - a - b) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum hden.le
  have hid :
      1 - (-((2 * t - a - b) / (b - a))) =
        2 * (t - a) / (b - a) := by
    field_simp [ne_of_gt hden]
    ring
  have hnonneg : 0 ≤ 2 * (t - a) / (b - a) :=
    div_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hat)) hden.le
  unfold schauderTent
  rw [abs_of_nonpos hquot, hid, max_eq_left hnonneg]

private theorem schauderTent_eq_falling
    {a b t : ℝ} (hab : a < b)
    (hmid : (a + b) / 2 ≤ t) (htb : t ≤ b) :
    schauderTent a b t = 2 * (b - t) / (b - a) := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hnum : 0 ≤ 2 * t - a - b := by linarith
  have hquot : 0 ≤ (2 * t - a - b) / (b - a) :=
    div_nonneg hnum hden.le
  have hid :
      1 - ((2 * t - a - b) / (b - a)) =
        2 * (b - t) / (b - a) := by
    field_simp [ne_of_gt hden]
    ring
  have hnonneg : 0 ≤ 2 * (b - t) / (b - a) :=
    div_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr htb)) hden.le
  unfold schauderTent
  rw [abs_of_nonneg hquot, hid, max_eq_left hnonneg]

/-- If the support endpoints and support midpoint are not interior to
`[x,y]`, the tent is affine on that cell. -/
private theorem schauderTent_midpoint_affine
    {a b x y : ℝ}
    (hab : a < b) (hxy : x < y)
    (ha : a ≤ x ∨ y ≤ a)
    (hcenter : (a + b) / 2 ≤ x ∨ y ≤ (a + b) / 2)
    (hb : b ≤ x ∨ y ≤ b) :
    schauderTent a b ((x + y) / 2) =
      (schauderTent a b x + schauderTent a b y) / 2 := by
  by_cases hyLeft : y ≤ a
  · have hmidZero :=
      schauderTent_eq_zero_of_le_left hab
        (show (x + y) / 2 ≤ a by linarith)
    have hxZero :=
      schauderTent_eq_zero_of_le_left hab
        (show x ≤ a by linarith)
    have hyZero := schauderTent_eq_zero_of_le_left hab hyLeft
    rw [hmidZero, hxZero, hyZero]
    norm_num
  · have hax : a ≤ x := ha.resolve_right hyLeft
    by_cases hcenterLeft : (a + b) / 2 ≤ x
    · by_cases hbLeft : b ≤ x
      · have hmidZero :=
          schauderTent_eq_zero_of_right_le hab
            (show b ≤ (x + y) / 2 by linarith)
        have hxZero := schauderTent_eq_zero_of_right_le hab hbLeft
        have hyZero :=
          schauderTent_eq_zero_of_right_le hab
            (show b ≤ y by linarith)
        rw [hmidZero, hxZero, hyZero]
        norm_num
      · have hyb : y ≤ b := hb.resolve_left hbLeft
        rw [schauderTent_eq_falling hab (by linarith) (by linarith),
          schauderTent_eq_falling hab hcenterLeft (by linarith),
          schauderTent_eq_falling hab (by linarith) hyb]
        ring
    · have hyCenter : y ≤ (a + b) / 2 :=
        hcenter.resolve_left hcenterLeft
      rw [schauderTent_eq_rising hab (by linarith) (by linarith),
        schauderTent_eq_rising hab hax (by linarith),
        schauderTent_eq_rising hab (by linarith) hyCenter]
      ring

private theorem fineLeft_eq_refinedGrid
    (K m r : ℕ) (hmr : m ≤ r) (p : FineLevelIndex K m) :
    fineLeft K m p =
      dyadicGridPoint r
        (fineFlatIndex K m p * 2 ^ (r - m)) := by
  change dyadicGridPoint m (fineFlatIndex K m p) = _
  exact dyadicGridPoint_refine m r (fineFlatIndex K m p) hmr

private theorem fineRight_eq_refinedGrid
    (K m r : ℕ) (hmr : m ≤ r) (p : FineLevelIndex K m) :
    fineRight K m p =
      dyadicGridPoint r
        ((fineFlatIndex K m p + 1) * 2 ^ (r - m)) := by
  rw [fineRight_eq_gridPoint K m p]
  exact dyadicGridPoint_refine m r
    (fineFlatIndex K m p + 1) hmr

private theorem fineMidpoint_eq_refinedGrid
    (K m r : ℕ) (hmr : m < r) (p : FineLevelIndex K m) :
    fineMidpoint K m p =
      dyadicGridPoint r
        ((2 * fineFlatIndex K m p + 1) *
          2 ^ (r - (m + 1))) := by
  rw [fineMidpoint_eq_next_grid K m p]
  change dyadicGridPoint (m + 1)
      (2 * fineFlatIndex K m p + 1) = _
  exact dyadicGridPoint_refine (m + 1) r
    (2 * fineFlatIndex K m p + 1) (Nat.succ_le_iff.mpr hmr)

private theorem fineTent_midpoint_affine_of_lt
    (K m r : ℕ) (hmr : m < r)
    (p : FineLevelIndex K m) (q : FineLevelIndex K r) :
    fineTent K m p (fineMidpoint K r q) =
      (fineTent K m p (fineLeft K r q) +
        fineTent K m p (fineRight K r q)) / 2 := by
  let k := fineFlatIndex K r q
  have hcellLeft : fineLeft K r q = dyadicGridPoint r k := rfl
  have hcellRight :
      fineRight K r q = dyadicGridPoint r (k + 1) :=
    fineRight_eq_gridPoint K r q
  have hsupportLeft :=
    fineLeft_eq_refinedGrid K m r hmr.le p
  have hsupportMid :=
    fineMidpoint_eq_refinedGrid K m r hmr p
  have hsupportRight :=
    fineRight_eq_refinedGrid K m r hmr.le p
  have hsepLeftRaw :=
    dyadicGridPoint_le_or_right_le r
      (fineFlatIndex K m p * 2 ^ (r - m)) k
  have hsepLeft :
      fineLeft K m p ≤ fineLeft K r q ∨
        fineRight K r q ≤ fineLeft K m p := by
    simpa [hsupportLeft, hcellLeft, hcellRight] using hsepLeftRaw
  have hsepMidRaw :=
    dyadicGridPoint_le_or_right_le r
      ((2 * fineFlatIndex K m p + 1) *
        2 ^ (r - (m + 1))) k
  have hsepMid :
      fineMidpoint K m p ≤ fineLeft K r q ∨
        fineRight K r q ≤ fineMidpoint K m p := by
    simpa [hsupportMid, hcellLeft, hcellRight] using hsepMidRaw
  have hsepRightRaw :=
    dyadicGridPoint_le_or_right_le r
      ((fineFlatIndex K m p + 1) * 2 ^ (r - m)) k
  have hsepRight :
      fineRight K m p ≤ fineLeft K r q ∨
        fineRight K r q ≤ fineRight K m p := by
    simpa [hsupportRight, hcellLeft, hcellRight] using hsepRightRaw
  change schauderTent (fineLeft K m p) (fineRight K m p)
      ((fineLeft K r q + fineRight K r q) / 2) =
    (schauderTent (fineLeft K m p) (fineRight K m p)
        (fineLeft K r q) +
      schauderTent (fineLeft K m p) (fineRight K m p)
        (fineRight K r q)) / 2
  apply schauderTent_midpoint_affine
    (fineLeft_lt_right_local K m p)
    (fineLeft_lt_right_local K r q)
  · exact hsepLeft
  · simpa only [fineMidpoint] using hsepMid
  · exact hsepRight

private theorem fineLevelTerm_midpoint_affine_of_lt
    (K m r : ℕ) (hmr : m < r)
    (z : FineNoiseSpace K) (q : FineLevelIndex K r) :
    fineLevelTerm K m z (fineMidpoint K r q) =
      (fineLevelTerm K m z (fineLeft K r q) +
        fineLevelTerm K m z (fineRight K r q)) / 2 := by
  classical
  have hsum :
      (∑ p : FineLevelIndex K m,
          fineGaussianCoordinate K m p z *
            fineTent K m p (fineMidpoint K r q)) =
        ((∑ p : FineLevelIndex K m,
            fineGaussianCoordinate K m p z *
              fineTent K m p (fineLeft K r q)) +
          ∑ p : FineLevelIndex K m,
            fineGaussianCoordinate K m p z *
              fineTent K m p (fineRight K r q)) / 2 := by
    calc
      _ = ∑ p : FineLevelIndex K m,
          (fineGaussianCoordinate K m p z *
              fineTent K m p (fineLeft K r q) +
            fineGaussianCoordinate K m p z *
              fineTent K m p (fineRight K r q)) / 2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [fineTent_midpoint_affine_of_lt K m r hmr p q]
        ring
      _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
  unfold fineLevelTerm
  rw [hsum]
  ring

private theorem finePartial_midpoint_affine
    (K r : ℕ) (z : FineNoiseSpace K)
    (q : FineLevelIndex K r) :
    finePartial K r z (fineMidpoint K r q) =
      (finePartial K r z (fineLeft K r q) +
        finePartial K r z (fineRight K r q)) / 2 := by
  have hsum :
      (∑ m ∈ Finset.range r,
          fineLevelTerm K m z (fineMidpoint K r q)) =
        ((∑ m ∈ Finset.range r,
            fineLevelTerm K m z (fineLeft K r q)) +
          ∑ m ∈ Finset.range r,
            fineLevelTerm K m z (fineRight K r q)) / 2 := by
    calc
      _ = ∑ m ∈ Finset.range r,
          (fineLevelTerm K m z (fineLeft K r q) +
            fineLevelTerm K m z (fineRight K r q)) / 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        exact fineLevelTerm_midpoint_affine_of_lt
          K m r (Finset.mem_range.mp hm) z q
      _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
  unfold finePartial
  exact hsum

/-- **Adapter 1.**  The coarse interpolation plus stored levels `< r` is
midpoint-affine on every level-`r` parent cell, for every sample. -/
theorem partialMidpointAffine (K r : ℕ) :
    PartialMidpointAffine K r := by
  intro omega q
  have hcoarse :=
    coarseGaussianInterpolation_midpoint_affine K r omega.1 q
  have hfine := finePartial_midpoint_affine K r omega.2 q
  unfold partialBrownianCandidate
  rw [hcoarse, hfine]
  ring

/-! ## Finite fine-coordinate blocks -/

/-- All fine Gaussian coordinates at stored levels strictly below `r`. -/
abbrev FinePastIndex (K r : ℕ) :=
  Σ m : Fin r, FineLevelIndex K m.1

noncomputable def finePastReadout
    (K r : ℕ) (z : FineNoiseSpace K) : FinePastIndex K r → ℝ
  | ⟨m, q⟩ => z ⟨m.1, q⟩

@[fun_prop]
theorem measurable_finePastReadout (K r : ℕ) :
    Measurable (finePastReadout K r) := by
  apply measurable_pi_lambda
  rintro ⟨m, q⟩
  exact measurable_pi_apply (⟨m.1, q⟩ : FineNoiseIndex K)

private def finePastSet (K r : ℕ) : Finset (FineNoiseIndex K) :=
  (Finset.range r).sigma fun m =>
    (Finset.univ : Finset (FineLevelIndex K m))

private def fineCurrentEmbedding (K r : ℕ) :
    FineLevelIndex K r ↪ FineNoiseIndex K where
  toFun q := ⟨r, q⟩
  inj' := by
    intro q p h
    cases h
    rfl

private def fineCurrentSet (K r : ℕ) : Finset (FineNoiseIndex K) :=
  (Finset.univ : Finset (FineLevelIndex K r)).map
    (fineCurrentEmbedding K r)

private theorem finePastSet_mem
    (K r : ℕ) (m : Fin r) (q : FineLevelIndex K m.1) :
    (⟨m.1, q⟩ : FineNoiseIndex K) ∈ finePastSet K r := by
  simp [finePastSet, m.isLt]

private theorem fineCurrentSet_mem
    (K r : ℕ) (q : FineLevelIndex K r) :
    (⟨r, q⟩ : FineNoiseIndex K) ∈ fineCurrentSet K r := by
  apply Finset.mem_map.mpr
  exact ⟨q, Finset.mem_univ q, rfl⟩

private theorem finePastSet_disjoint_currentSet (K r : ℕ) :
    Disjoint (finePastSet K r) (fineCurrentSet K r) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiPast hiCurrent
  rcases Finset.mem_map.mp hiCurrent with ⟨q, _, hq⟩
  subst i
  have h := hiPast
  simp only [finePastSet, Finset.mem_sigma, Finset.mem_range] at h
  exact (lt_irrefl r) h.1

private def pastTupleRestriction
    (K r : ℕ) (v : (i : finePastSet K r) → ℝ) :
    FinePastIndex K r → ℝ
  | ⟨m, q⟩ =>
      v ⟨⟨m.1, q⟩, finePastSet_mem K r m q⟩

private def currentTupleRestriction
    (K r : ℕ) (v : (i : fineCurrentSet K r) → ℝ) :
    FineLevelIndex K r → ℝ :=
  fun q => v ⟨⟨r, q⟩, fineCurrentSet_mem K r q⟩

@[fun_prop]
private theorem measurable_pastTupleRestriction (K r : ℕ) :
    Measurable (pastTupleRestriction K r) := by
  apply measurable_pi_lambda
  rintro ⟨m, q⟩
  exact measurable_pi_apply
    (⟨⟨m.1, q⟩, finePastSet_mem K r m q⟩ : finePastSet K r)

@[fun_prop]
private theorem measurable_currentTupleRestriction (K r : ℕ) :
    Measurable (currentTupleRestriction K r) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_pi_apply
    (⟨⟨r, q⟩, fineCurrentSet_mem K r q⟩ : fineCurrentSet K r)

/-- The finite block of levels `< r` is independent of the complete level-`r`
block under the fine Gaussian product measure. -/
theorem finePastReadout_indep_fineLevelReadout (K r : ℕ) :
    IndepFun (finePastReadout K r) (fineLevelReadout K r)
      (fineGaussianMeasure K) := by
  have hblocks :=
    (fineGaussian_iIndep K).indepFun_finset
      (finePastSet K r) (fineCurrentSet K r)
      (finePastSet_disjoint_currentSet K r)
      (fun i => measurable_pi_apply i)
  have hcomp := hblocks.comp
    (measurable_pastTupleRestriction K r)
    (measurable_currentTupleRestriction K r)
  have hpast :
      pastTupleRestriction K r ∘
          (fun z : FineNoiseSpace K =>
            fun i : finePastSet K r => z i.1) =
        finePastReadout K r := by
    funext z p
    rcases p with ⟨m, q⟩
    rfl
  have hcurrent :
      currentTupleRestriction K r ∘
          (fun z : FineNoiseSpace K =>
            fun i : fineCurrentSet K r => z i.1) =
        fineLevelReadout K r := by
    funext z q
    rfl
  rw [hpast, hcurrent] at hcomp
  exact hcomp

/-! ## Reconstruction from the finite past block -/

noncomputable def finePastExtend
    (K r : ℕ) (v : FinePastIndex K r → ℝ) : FineNoiseSpace K :=
  fun i =>
    if h : i.1 < r then
      v ⟨⟨i.1, h⟩, i.2⟩
    else 0

@[fun_prop]
theorem measurable_finePastExtend (K r : ℕ) :
    Measurable (finePastExtend K r) := by
  apply measurable_pi_lambda
  intro i
  unfold finePastExtend
  split_ifs with h
  · exact measurable_pi_apply
      (⟨⟨i.1, h⟩, i.2⟩ : FinePastIndex K r)
  · exact measurable_const

private theorem finePastExtend_readout_coordinate
    (K m r : ℕ) (hmr : m < r)
    (z : FineNoiseSpace K) (q : FineLevelIndex K m) :
    finePastExtend K r (finePastReadout K r z) ⟨m, q⟩ =
      fineGaussianCoordinate K m q z := by
  simp [finePastExtend, finePastReadout, fineGaussianCoordinate, hmr]

private theorem finePartial_finePastExtend_readout
    (K r : ℕ) (z : FineNoiseSpace K) (t : ℝ) :
    finePartial K r
        (finePastExtend K r (finePastReadout K r z)) t =
      finePartial K r z t := by
  classical
  unfold finePartial
  apply Finset.sum_congr rfl
  intro m hm
  unfold fineLevelTerm
  apply congrArg (fun u : ℝ => fineScale m * u)
  apply Finset.sum_congr rfl
  intro q _
  have h := finePastExtend_readout_coordinate K m r
    (Finset.mem_range.mp hm) z q
  simp only [fineGaussianCoordinate] at h ⊢
  rw [h]

noncomputable def finePastData
    (K r : ℕ) (omega : BrownianFineSpace K) :
    DyadicNoiseSpace K × (FinePastIndex K r → ℝ) :=
  (omega.1, finePastReadout K r omega.2)

@[fun_prop]
theorem measurable_finePastData (K r : ℕ) :
    Measurable (finePastData K r) :=
  measurable_fst.prodMk
    ((measurable_finePastReadout K r).comp measurable_snd)

noncomputable def finePastRebuild
    (K r : ℕ)
    (d : DyadicNoiseSpace K × (FinePastIndex K r → ℝ)) :
    BrownianFineSpace K :=
  (d.1, finePastExtend K r d.2)

@[fun_prop]
theorem measurable_finePastRebuild (K r : ℕ) :
    Measurable (finePastRebuild K r) :=
  measurable_fst.prodMk
    ((measurable_finePastExtend K r).comp measurable_snd)

noncomputable def partialDyadicIncrementVector
    (K r : ℕ) (omega : BrownianFineSpace K) :
    FineLevelIndex K r → ℝ :=
  fun q =>
    partialBrownianCandidate K r (fineRight K r q) omega -
      partialBrownianCandidate K r (fineLeft K r q) omega

@[fun_prop]
private theorem measurable_partialBrownianCandidate
    (K r : ℕ) (t : ℝ) :
    Measurable (partialBrownianCandidate K r t) := by
  unfold partialBrownianCandidate
  exact ((measurable_coarseGaussianInterpolation K t).comp
    measurable_fst).add
      ((measurable_finePartial K r t).comp measurable_snd)

@[fun_prop]
theorem measurable_partialDyadicIncrementVector (K r : ℕ) :
    Measurable (partialDyadicIncrementVector K r) := by
  apply measurable_pi_lambda
  intro q
  exact (measurable_partialBrownianCandidate K r
    (fineRight K r q)).sub
      (measurable_partialBrownianCandidate K r
        (fineLeft K r q))

noncomputable def partialDyadicIncrementFromPast
    (K r : ℕ)
    (d : DyadicNoiseSpace K × (FinePastIndex K r → ℝ)) :
    FineLevelIndex K r → ℝ :=
  partialDyadicIncrementVector K r (finePastRebuild K r d)

@[fun_prop]
theorem measurable_partialDyadicIncrementFromPast (K r : ℕ) :
    Measurable (partialDyadicIncrementFromPast K r) :=
  (measurable_partialDyadicIncrementVector K r).comp
    (measurable_finePastRebuild K r)

private theorem partialDyadicIncrementVector_factor
    (K r : ℕ) (omega : BrownianFineSpace K) :
    partialDyadicIncrementFromPast K r (finePastData K r omega) =
      partialDyadicIncrementVector K r omega := by
  funext q
  unfold partialDyadicIncrementFromPast partialDyadicIncrementVector
  unfold finePastRebuild finePastData partialBrownianCandidate
  simp only [Prod.fst, Prod.snd]
  rw [finePartial_finePastExtend_readout,
    finePartial_finePastExtend_readout]

/-! ## Adjoining the independent tree factor -/

/-- If `f` and `g` are independent on the second factor, then `(fst,f)` and
`g` are independent on the product. -/
private theorem indepFun_prod_mk_left_of_indep
    {alpha beta gamma delta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    [MeasurableSpace gamma] [MeasurableSpace delta]
    {mu : Measure alpha} {nu : Measure beta}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {f : beta → gamma} {g : beta → delta}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g nu) :
    IndepFun (fun p : alpha × beta => (p.1, f p.2))
      (fun p : alpha × beta => g p.2) (mu.prod nu) := by
  have hfm : AEMeasurable (fun p : alpha × beta => (p.1, f p.2))
      (mu.prod nu) :=
    (measurable_fst.prodMk (hf.comp measurable_snd)).aemeasurable
  have hgm : AEMeasurable (fun p : alpha × beta => g p.2) (mu.prod nu) :=
    (hg.comp measurable_snd).aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map hfm hgm]
  let pair : beta → gamma × delta := fun b => (f b, g b)
  have hpair : Measurable pair := hf.prodMk hg
  have hpairLaw :
      nu.map pair = (nu.map f).prod (nu.map g) := by
    simpa [pair] using
      hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hleft :
      (mu.prod nu).map (fun p : alpha × beta => (p.1, f p.2)) =
        mu.prod (nu.map f) := by
    rw [show (fun p : alpha × beta => (p.1, f p.2)) =
        Prod.map id f by rfl,
      ← Measure.map_prod_map mu nu measurable_id hf,
      Measure.map_id]
  have hright :
      (mu.prod nu).map (fun p : alpha × beta => g p.2) =
        nu.map g := by
    rw [show (fun p : alpha × beta => g p.2) =
        g ∘ Prod.snd by rfl,
      ← Measure.map_map hg measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [hleft, hright]
  calc
    (mu.prod nu).map
        (fun p : alpha × beta => ((p.1, f p.2), g p.2)) =
      ((mu.prod nu).map (Prod.map id pair)).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.map_map
        MeasurableEquiv.prodAssoc.symm.measurable
        (measurable_id.prodMap hpair)]
      rfl
    _ = (mu.prod (nu.map pair)).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [← Measure.map_prod_map mu nu measurable_id hpair,
        Measure.map_id]
    _ = (mu.prod ((nu.map f).prod (nu.map g))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [hpairLaw]
    _ = (mu.prod (nu.map f)).prod (nu.map g) := by
      have hassoc :
          ((mu.prod (nu.map f)).prod (nu.map g)).map
              MeasurableEquiv.prodAssoc =
            mu.prod ((nu.map f).prod (nu.map g)) :=
        Measure.prodAssoc_prod
      rw [← hassoc,
        Measure.map_map
          MeasurableEquiv.prodAssoc.symm.measurable
          MeasurableEquiv.prodAssoc.measurable]
      simp

private theorem finePastData_indep_fineLevelVector (K r : ℕ) :
    IndepFun (finePastData K r) (fineLevelVector K r)
      (brownianFineMeasure K) := by
  have h := indepFun_prod_mk_left_of_indep
    (mu := dyadicNoiseMeasure K) (nu := fineGaussianMeasure K)
    (measurable_finePastReadout K r)
    (measurable_fineLevelReadout K r)
    (finePastReadout_indep_fineLevelReadout K r)
  simpa [brownianFineMeasure, finePastData, fineLevelVector] using h

private theorem partialDyadicIncrementVector_indep_fineLevelVector
    (K r : ℕ) :
    IndepFun (partialDyadicIncrementVector K r)
      (fineLevelVector K r) (brownianFineMeasure K) := by
  have hind := (finePastData_indep_fineLevelVector K r).comp
    (measurable_partialDyadicIncrementFromPast K r) measurable_id
  have hfactor :
      partialDyadicIncrementFromPast K r ∘ finePastData K r =
        partialDyadicIncrementVector K r := by
    funext omega
    exact partialDyadicIncrementVector_factor K r omega
  rw [hfactor] at hind
  simpa [Function.comp_def] using hind

/-! ## The full parent vector agrees almost surely with the finite past -/

private theorem fineConvergenceEvent_prod_ae (K : ℕ) :
    ∀ᵐ omega ∂brownianFineMeasure K,
      omega.2 ∈ FineSchauderConvergenceEvent K := by
  refine MeasureTheory.ae_of_ae_map
    (p := fun z : FineNoiseSpace K =>
      z ∈ FineSchauderConvergenceEvent K)
    measurable_snd.aemeasurable ?_
  rw [brownianFineMeasure_map_snd]
  exact fineSchauderConvergenceEvent_ae K

private theorem brownianDyadicIncrementVector_ae_eq_partial
    (K r : ℕ) :
    brownianDyadicIncrementVector K r =ᵐ[brownianFineMeasure K]
      partialDyadicIncrementVector K r := by
  filter_upwards [fineConvergenceEvent_prod_ae K] with omega hconv
  funext q
  have hleft :
      fineSchauderLimit K omega.2 (fineLeft K r q) =
        finePartial K r omega.2 (fineLeft K r q) := by
    simpa only [fineLeft] using
      (fineSchauderLimit_grid_eq_partial_of_mem K r
        (fineFlatIndex K r q) omega.2 hconv)
  have hright :
      fineSchauderLimit K omega.2 (fineRight K r q) =
        finePartial K r omega.2 (fineRight K r q) := by
    have hr := fineSchauderLimit_grid_eq_partial_of_mem K r
      (fineFlatIndex K r q + 1) omega.2 hconv
    push_cast at hr
    simpa only [fineRight] using hr
  unfold brownianDyadicIncrementVector brownianDyadicIncrement
  unfold partialDyadicIncrementVector
  unfold brownianCandidate partialBrownianCandidate
  rw [hleft, hright]

/-- **Adapter 2.**  Every level-`r` parent-increment vector is independent of
the fresh level-`r` Gaussian coefficient vector. -/
theorem brownianDyadicIncrementVector_indep_fineLevelVector
    (K r : ℕ) :
    IndepFun (brownianDyadicIncrementVector K r)
      (fineLevelVector K r) (brownianFineMeasure K) := by
  apply (partialDyadicIncrementVector_indep_fineLevelVector K r).congr
  · exact (brownianDyadicIncrementVector_ae_eq_partial K r).symm
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- The one-level law of `BrownianFineDyadicStep` now needs only the parent-vector law. -/
theorem brownianChildPairVector_map_of_parentLaw
    (K r : ℕ)
    (hparent :
      (brownianFineMeasure K).map
          (brownianDyadicIncrementVector K r) =
        Measure.pi (fun _ : FineLevelIndex K r =>
          gaussianReal 0 (dyadicVariance 0 r))) :
    (brownianFineMeasure K).map (brownianChildPairVector K r) =
      Measure.pi
        (fun _ : FineLevelIndex K r ⊕ FineLevelIndex K r =>
          gaussianReal 0 (dyadicVariance 0 (r + 1))) :=
  brownianChildPairVector_map_of_parent K r hparent
    (brownianDyadicIncrementVector_indep_fineLevelVector K r)
    (partialMidpointAffine K r)

/-!
THEOREM LIST
* `partialMidpointAffine`
* `measurable_finePastReadout`
* `finePastReadout_indep_fineLevelReadout`
* `measurable_finePastExtend`
* `measurable_finePastData`, `measurable_finePastRebuild`
* `measurable_partialDyadicIncrementVector`
* `brownianDyadicIncrementVector_indep_fineLevelVector`
* `brownianChildPairVector_map_of_parentLaw`

CLOSES
* Item 1: `PartialMidpointAffine K r` for every `K,r`, pointwise for every
  sample.  The proof covers the coarse unit ramps and every lower fine level.
* Item 2: independence of the parent dyadic increment vector from the fresh
  level-`r` vector under `brownianFineMeasure K`.
* The first two hypotheses named in the `UNFINISHED` list of `BrownianFineDyadicStep` are therefore
  discharged; its one-level split theorem can be invoked with only the parent
  product-law hypothesis.

UNFINISHED
* The third adapter of `BrownianFineDyadicStep`: the chronological measurable equivalence from
  `FineLevelIndex K r ⊕ FineLevelIndex K r` to
  `FineLevelIndex K (r+1)`.
* The literal all-level induction and final `DyadicBrownianOn` package remain
  downstream of that reindexing.
END
-/

end Ripple.Kurtz.StrongApprox.BrownianFineDyadicAdapters

end

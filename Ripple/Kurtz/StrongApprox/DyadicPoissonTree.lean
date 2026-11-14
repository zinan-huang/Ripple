-- Ripple/Kurtz/StrongApprox/DyadicPoissonTree.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.DyadicGaussianTree
import Ripple.Kurtz.StrongApprox.PoissonCouplingMean
import Ripple.Kurtz.StrongApprox.BinomialQuantileBound
import Ripple.Kurtz.StrongApprox.PoissonSplitting

/-!
# The finite dyadic Poisson count tree

The count tree uses the very same Gaussian product source as
`DyadicGaussianTree`.  The endpoint coordinate gives the root Poisson count;
each fresh split coordinate gives a conditional `Binomial(m,1/2)` left count.
Only same-level counts are asserted independent.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.DyadicPoissonTree

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal Nat
open Ripple.Kurtz.StrongApprox
open Ripple.Kurtz.StrongApprox.DyadicGaussianTree

/-! ## Exact binomial-quantile point masses -/

/-- The symmetric binomial quantile coupling has its exact point masses. -/
theorem measure_binCoupling_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 1) (m k : ℕ) :
    P {ω | binCoupling m (Z ω) = k} =
      ENNReal.ofReal (binTermP m k (1 / 2)) := by
  cases k with
  | zero =>
      have h := measure_natQuantile_eq_zero P
        (U := fun ω => stdNormalCdf (Z ω))
        (binF_monotone m) (binF_nonneg m) (binF_le_one m)
        (fun ω => exists_binF_ge m (Z ω))
        (fun t ht0 ht1 => measure_stdNormalCdf_comp_le P hZ hlaw ht0 ht1)
      unfold binCoupling
      rw [h]
      congr 1
      simp [binF, binCdf]
  | succ j =>
      have hU : Measurable fun ω => stdNormalCdf (Z ω) :=
        stdNormalCdf_continuous.measurable.comp hZ
      have h := measure_natQuantile_eq_succ P
        (binF_monotone m) (binF_nonneg m) (binF_le_one m) hU
        (fun ω => exists_binF_ge m (Z ω))
        (fun t ht0 ht1 => measure_stdNormalCdf_comp_le P hZ hlaw ht0 ht1) j
      unfold binCoupling
      rw [h, ← ENNReal.ofReal_sub _ (binF_nonneg m j)]
      congr 1
      unfold binF
      rw [binCdf_succ]
      ring

/-! ## One-parent Poisson splitting -/

/-- Given parent count `m` and a fresh normal, return left and right counts. -/
noncomputable def poissonHalfSplit (p : ℕ × ℝ) : ℕ × ℕ :=
  let q := binCoupling p.1 p.2
  (q, p.1 - q)

/-- The split counts add to the parent count. -/
theorem poissonHalfSplit_sum (m : ℕ) (z : ℝ) :
    (poissonHalfSplit (m, z)).1 + (poissonHalfSplit (m, z)).2 = m := by
  unfold poissonHalfSplit
  exact Nat.add_sub_of_le (binCoupling_le m z)

/-- Exact singleton fiber of the split map. -/
theorem poissonHalfSplit_preimage_singleton (j k : ℕ) :
    poissonHalfSplit ⁻¹' {(j, k)} =
      ({j + k} : Set ℕ) ×ˢ ((binCoupling (j + k)) ⁻¹' {j}) := by
  ext p
  rcases p with ⟨m, z⟩
  change ((binCoupling m z, m - binCoupling m z) = (j, k)) ↔
    (m = j + k ∧ binCoupling (j + k) z = j)
  constructor
  · intro h
    have hq : binCoupling m z = j := congrArg Prod.fst h
    have hr : m - binCoupling m z = k := congrArg Prod.snd h
    have hle := binCoupling_le m z
    have hm : m = j + k := by omega
    subst m
    exact ⟨rfl, by simpa using hq⟩
  · rintro ⟨rfl, hq⟩
    apply Prod.ext
    · exact hq
    · have hle := binCoupling_le (j + k) z
      omega

@[fun_prop] theorem measurable_poissonHalfSplit : Measurable poissonHalfSplit := by
  refine measurable_to_countable' fun p => ?_
  rcases p with ⟨j, k⟩
  rw [poissonHalfSplit_preimage_singleton]
  exact (measurableSet_singleton _).prod
    ((measurable_binCoupling (j + k)) (measurableSet_singleton j))

/-- The elementary Poisson/binomial factorization at probability `1/2`. -/
theorem poisTerm_mul_binTermP_half (l : ℝ) (j k : ℕ) :
    poisTerm (j + k) l * binTermP (j + k) j (1 / 2) =
      poisTerm j (l / 2) * poisTerm k (l / 2) := by
  unfold poisTerm binTermP
  rw [Nat.cast_choose (K := ℝ) (Nat.le_add_right j k)]
  simp only [Nat.add_sub_cancel_left]
  have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [hhalf, pow_add]
  have hexp : Real.exp (-l) =
      Real.exp (-(l / 2)) * Real.exp (-(l / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, div_pow, div_pow]
  have hj : ((j ! : ℕ) : ℝ) ≠ 0 := by positivity
  have hk : ((k ! : ℕ) : ℝ) ≠ 0 := by positivity
  have hjk : (((j + k) ! : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hj, hk, hjk]
  simp only [one_pow, div_pow]
  field_simp

/-- Mapping a standard normal through `poisCoupling l` gives `Poisson(l)`. -/
theorem gaussianReal_map_poisCoupling {l : ℝ} (hl : 0 < l) :
    (gaussianReal 0 1).map (poisCoupling l) = poisMeasure l := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_poisCoupling hl)
    (measurableSet_singleton k), poisMeasure_singleton]
  exact measure_poisCoupling_eq (gaussianReal 0 1) measurable_id (by simp) hl k

/-- One Poisson parent split by an independent standard normal gives two independent halves. -/
theorem poissonHalfSplit_measurePreserving {l : ℝ} (hl : 0 < l) :
    MeasurePreserving poissonHalfSplit
      ((poisMeasure l).prod (gaussianReal 0 1))
      ((poisMeasure (l / 2)).prod (poisMeasure (l / 2))) := by
  letI : Fact (0 ≤ l) := ⟨hl.le⟩
  letI : Fact (0 ≤ l / 2) := ⟨by positivity⟩
  refine ⟨measurable_poissonHalfSplit, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨j, k⟩
  have hbin : (gaussianReal 0 1) (binCoupling (j + k) ⁻¹' {j}) =
      ENNReal.ofReal (binTermP (j + k) j (1 / 2)) :=
    measure_binCoupling_eq (gaussianReal 0 1) measurable_id (by simp) (j + k) j
  rw [Measure.map_apply measurable_poissonHalfSplit
      (measurableSet_singleton (j, k)),
    poissonHalfSplit_preimage_singleton,
    Measure.prod_prod, poisMeasure_singleton,
    hbin, ← Set.singleton_prod_singleton,
    Measure.prod_prod, poisMeasure_singleton, poisMeasure_singleton,
    ← ENNReal.ofReal_mul (poisTerm_nonneg _ hl.le),
    ← ENNReal.ofReal_mul (poisTerm_nonneg _ (by positivity : 0 ≤ l / 2))]
  congr 1
  exact poisTerm_mul_binTermP_half l j k

/-! ## The Poisson count tree -/

instance dyadicVariance_nonnegFact (K r : ℕ) :
    Fact (0 ≤ (dyadicVariance K r : ℝ)) := ⟨by positivity⟩

/-- Counts on every cell of a level. -/
noncomputable def poissonLevel : (K r : ℕ) →
    DyadicNoiseSpace r → DyadicCell r → ℕ
  | K, 0 => fun x i => poisCoupling (dyadicVariance K 0 : ℝ) (x i)
  | K, r + 1 => fun x =>
      let old := (dyadicNoiseSplit r x).1
      let fresh := (dyadicNoiseSplit r x).2
      dyadicRefine poissonHalfSplit (poissonLevel K r old, fresh)

/-- Exact product law at every level. -/
theorem poissonLevel_measurePreserving (K : ℕ) : ∀ r,
    MeasurePreserving (poissonLevel K r) (dyadicNoiseMeasure r)
      (Measure.pi fun _ : DyadicCell r => poisMeasure (dyadicVariance K r : ℝ))
  | 0 => by
      refine ⟨?_, ?_⟩
      · change Measurable (fun (x : DyadicNoiseSpace 0) (i : DyadicCell 0) =>
          poisCoupling (dyadicVariance K 0 : ℝ) (x i))
        exact measurable_pi_lambda _ (fun i =>
          (measurable_poisCoupling (dyadicVariance_pos K 0)).comp
            (measurable_pi_apply i))
      change (Measure.pi fun _ : Unit => gaussianReal 0 1).map
        (fun x i => poisCoupling (dyadicVariance K 0 : ℝ) (x i)) =
        Measure.pi fun _ : Unit => poisMeasure (dyadicVariance K 0 : ℝ)
      rw [Measure.pi_map_pi (fun _ =>
        (measurable_poisCoupling (dyadicVariance_pos K 0)).aemeasurable)]
      simp_rw [gaussianReal_map_poisCoupling (dyadicVariance_pos K 0)]
  | r + 1 => by
      letI : Fact (0 ≤ (dyadicVariance K r : ℝ) / 2) := ⟨by positivity⟩
      have hold := poissonLevel_measurePreserving K r
      have hprod := MeasurePreserving.prod hold
        (MeasurePreserving.id (dyadicFreshMeasure r))
      have hrefine := dyadicRefine_measurePreserving
        (ι := DyadicCell r)
        (μA := poisMeasure (dyadicVariance K r : ℝ))
        (μB := gaussianReal 0 1)
        (μD := poisMeasure ((dyadicVariance K r : ℝ) / 2))
        (split := poissonHalfSplit) measurable_poissonHalfSplit
        (poissonHalfSplit_measurePreserving (dyadicVariance_pos K r)).map_eq
      have h := hrefine.comp (hprod.comp (dyadicNoiseSplit_measurePreserving r))
      simpa [poissonLevel, dyadicFreshMeasure, Function.comp_def,
        dyadicVariance_succ] using h

/-- Vector form of the exact level law. -/
theorem poissonLevel_map (K r : ℕ) :
    (dyadicNoiseMeasure r).map (poissonLevel K r) =
      Measure.pi fun _ : DyadicCell r => poisMeasure (dyadicVariance K r : ℝ) :=
  (poissonLevel_measurePreserving K r).map_eq

/-- Every level-`r` count is Poisson with mean equal to the cell length. -/
theorem poissonLevel_component_map (K r : ℕ) (j : DyadicCell r) :
    (dyadicNoiseMeasure r).map (fun x => poissonLevel K r x j) =
      poisMeasure (dyadicVariance K r : ℝ) :=
  vectorComponent_map_eq (poissonLevel_measurePreserving K r).measurable
    (poissonLevel_map K r) j

/-- Counts on one fixed level are independent. -/
theorem poissonLevel_iIndep (K r : ℕ) :
    iIndepFun (fun j x => poissonLevel K r x j) (dyadicNoiseMeasure r) :=
  iIndepFun_of_vector_map_eq_pi (poissonLevel_measurePreserving K r).measurable
    (poissonLevel_map K r)

/-- Exact parent = left child + right child identity. -/
theorem poissonLevel_parent_eq_children (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (j : DyadicCell r) :
    poissonLevel K r (dyadicNoiseSplit r x).1 j =
      poissonLevel K (r + 1) x (Sum.inl j) +
        poissonLevel K (r + 1) x (Sum.inr j) := by
  simp [poissonLevel, dyadicRefine, poissonHalfSplit,
    Nat.add_sub_of_le (binCoupling_le
      (poissonLevel K r (dyadicNoiseSplit r x).1 j)
      ((dyadicNoiseSplit r x).2 j))]

/-- Level `r` of the horizon `2^(r+d)` count tree on the full common source. -/
noncomputable def poissonLevelOnHorizon (r d : ℕ) :
    DyadicNoiseSpace (r + d) → DyadicCell r → ℕ :=
  poissonLevel (r + d) r ∘ dyadicNoiseRestrict r d

/-- Exact coarser-level product law on the full common source. -/
theorem poissonLevelOnHorizon_measurePreserving (r d : ℕ) :
    MeasurePreserving (poissonLevelOnHorizon r d) (dyadicNoiseMeasure (r + d))
      (Measure.pi fun _ : DyadicCell r =>
        poisMeasure (dyadicVariance (r + d) r : ℝ)) := by
  simpa [poissonLevelOnHorizon] using
    (poissonLevel_measurePreserving (r + d) r).comp
      (dyadicNoiseRestrict_measurePreserving r d)

/-- Coarser-level counts remain independent on the full horizon source. -/
theorem poissonLevelOnHorizon_iIndep (r d : ℕ) :
    iIndepFun (fun j x => poissonLevelOnHorizon r d x j)
      (dyadicNoiseMeasure (r + d)) :=
  iIndepFun_of_vector_map_eq_pi
    (poissonLevelOnHorizon_measurePreserving r d).measurable
    (poissonLevelOnHorizon_measurePreserving r d).map_eq

/-! ## Unit Poisson increments and the integer skeleton -/

/-- Unit-time Poisson increments at the leaves, using the same leaf enumeration as K10. -/
noncomputable def poissonUnitIncrement (K : ℕ) (j : Fin (2 ^ K))
    (x : DyadicNoiseSpace K) : ℕ :=
  poissonLevel K K x (dyadicLeafCell K j)

/-- Each leaf count is Poisson(1). -/
theorem poissonUnitIncrement_map (K : ℕ) (j : Fin (2 ^ K)) :
    (dyadicNoiseMeasure K).map (poissonUnitIncrement K j) = poisMeasure 1 := by
  simpa [poissonUnitIncrement, dyadicVariance_self] using
    poissonLevel_component_map K K (dyadicLeafCell K j)

/-- The integer-skeleton Poisson increments are independent. -/
theorem poissonUnitIncrement_iIndep (K : ℕ) :
    iIndepFun (poissonUnitIncrement K) (dyadicNoiseMeasure K) := by
  simpa [poissonUnitIncrement] using
    (poissonLevel_iIndep K K).precomp (dyadicLeafCell_injective K)

/-- Extend the finite count family by zero outside the horizon. -/
noncomputable def poissonUnitIncrementNat (K : ℕ)
    (x : DyadicNoiseSpace K) (j : ℕ) : ℕ :=
  if h : j < 2 ^ K then poissonUnitIncrement K ⟨j, h⟩ x else 0

/-- The integer count skeleton `Y(j)`. -/
noncomputable def poissonSkeleton (K : ℕ)
    (x : DyadicNoiseSpace K) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, poissonUnitIncrementNat K x i

@[simp] theorem poissonSkeleton_zero (K : ℕ) (x : DyadicNoiseSpace K) :
    poissonSkeleton K x 0 = 0 := by
  simp [poissonSkeleton]

/-- Consecutive count-skeleton increments are the leaf counts. -/
theorem poissonSkeleton_succ_sub (K j : ℕ) (h : j < 2 ^ K)
    (x : DyadicNoiseSpace K) :
    poissonSkeleton K x (j + 1) - poissonSkeleton K x j =
      poissonUnitIncrement K ⟨j, h⟩ x := by
  simp [poissonSkeleton, Finset.sum_range_succ,
    poissonUnitIncrementNat, h]

/--
The two leaf families live on exactly the same source measure.  No independence
between the Gaussian and Poisson families is claimed: they are the KMT coupling.
-/
theorem coupledLeafLaws (K : ℕ) :
    iIndepFun (gaussianUnitIncrement K) (dyadicNoiseMeasure K) ∧
    (∀ j, (dyadicNoiseMeasure K).map (gaussianUnitIncrement K j) = gaussianReal 0 1) ∧
    iIndepFun (poissonUnitIncrement K) (dyadicNoiseMeasure K) ∧
    (∀ j, (dyadicNoiseMeasure K).map (poissonUnitIncrement K j) = poisMeasure 1) :=
  ⟨gaussianUnitIncrement_iIndep K, gaussianUnitIncrement_map K,
    poissonUnitIncrement_iIndep K, poissonUnitIncrement_map K⟩

/-!
THEOREM LIST
* `measure_binCoupling_eq`
* `poissonHalfSplit_sum`, `poissonHalfSplit_measurePreserving`
* `poissonLevel_map`, `poissonLevel_component_map`, `poissonLevel_iIndep`
* `poissonLevel_parent_eq_children`
* `poissonLevelOnHorizon_measurePreserving`, `poissonLevelOnHorizon_iIndep`
* `poissonUnitIncrement_map`, `poissonUnitIncrement_iIndep`
* `poissonSkeleton_succ_sub`
* `coupledLeafLaws`

CLOSES K11: exact root Poisson quantile law, exact conditional binomial split law,
level-wise independent Poisson laws on the K10 source, the parent/children identity,
and independent Poisson(1) integer-skeleton increments.

UNFINISHED IN THIS FILE: no mathematical item intentionally omitted.  Deliberately
absent is any false child/parent independence theorem.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicPoissonTree

end

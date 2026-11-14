-- Ripple/Kurtz/StrongApprox/DyadicBridgeError.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.DyadicPoissonTree

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal Nat
open DyadicGaussianTree DyadicPoissonTree

/-- Error carried by one dyadic cell:
`count - length - Gaussian increment`. -/
def bridgeError (K r : ℕ) (x : DyadicNoiseSpace r)
    (c : DyadicCell r) : ℝ :=
  (poissonLevel K r x c : ℝ) - (dyadicVariance K r : ℝ) -
    gaussianLevel K r x c

/-- The raw symmetric-binomial quantile error at a parent split. -/
def splitQuantileError (K r : ℕ) (x : DyadicNoiseSpace (r + 1))
    (c : DyadicCell r) : ℝ :=
  let old := (dyadicNoiseSplit r x).1
  let z := (dyadicNoiseSplit r x).2 c
  let m := poissonLevel K r old c
  (poissonLevel K (r + 1) x (Sum.inl c) : ℝ) - (m : ℝ) / 2 -
    Real.sqrt (m : ℝ) / 2 * z

/-- K12's correction `g_J`. -/
def bridgeCorrection (K r : ℕ) (x : DyadicNoiseSpace (r + 1))
    (c : DyadicCell r) : ℝ :=
  let old := (dyadicNoiseSplit r x).1
  let z := (dyadicNoiseSplit r x).2 c
  let m := poissonLevel K r old c
  splitQuantileError K r x c +
    (Real.sqrt (m : ℝ) - Real.sqrt (dyadicVariance K r : ℝ)) / 2 * z

/-- The standardized Gaussian increment `Z'_J`. -/
def standardizedParentIncrement (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) : ℝ :=
  gaussianLevel K r (dyadicNoiseSplit r x).1 c /
    Real.sqrt (dyadicVariance K r : ℝ)

/-- The midpoint formula, written as the left-child Gaussian increment. -/
theorem gaussianMidpoint_sub_left_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    gaussianMidpoint K r x c -
        (gaussianEndpoints K r (dyadicNoiseSplit r x).1 c).1 =
      (gaussianLevel K r (dyadicNoiseSplit r x).1 c +
        Real.sqrt (dyadicVariance K r : ℝ) * (dyadicNoiseSplit r x).2 c) / 2 := by
  rw [gaussianMidpoint_formula]
  have hinc := gaussianEndpoints_sub_eq_level K r
    (dyadicNoiseSplit r x).1 c
  rw [← hinc]
  ring

/-- The same midpoint formula, written as the right-child Gaussian increment. -/
theorem gaussian_right_sub_midpoint_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    (gaussianEndpoints K r (dyadicNoiseSplit r x).1 c).2 -
        gaussianMidpoint K r x c =
      (gaussianLevel K r (dyadicNoiseSplit r x).1 c -
        Real.sqrt (dyadicVariance K r : ℝ) * (dyadicNoiseSplit r x).2 c) / 2 := by
  rw [gaussianMidpoint_formula]
  have hinc := gaussianEndpoints_sub_eq_level K r
    (dyadicNoiseSplit r x).1 c
  rw [← hinc]
  ring

/-- Level-form left-child Gaussian identity. -/
theorem gaussianLevel_left_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    gaussianLevel K (r + 1) x (Sum.inl c) =
      (gaussianLevel K r (dyadicNoiseSplit r x).1 c +
        Real.sqrt (dyadicVariance K r : ℝ) * (dyadicNoiseSplit r x).2 c) / 2 := by
  simp [gaussianLevel, dyadicRefine, gaussianHalfSplit]

/-- Level-form right-child Gaussian identity. -/
theorem gaussianLevel_right_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    gaussianLevel K (r + 1) x (Sum.inr c) =
      (gaussianLevel K r (dyadicNoiseSplit r x).1 c -
        Real.sqrt (dyadicVariance K r : ℝ) * (dyadicNoiseSplit r x).2 c) / 2 := by
  simp [gaussianLevel, dyadicRefine, gaussianHalfSplit]

/-- The landed left-child count is exactly the K09 quantile map. -/
theorem poissonLevel_left_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    poissonLevel K (r + 1) x (Sum.inl c) =
      binCoupling (poissonLevel K r (dyadicNoiseSplit r x).1 c)
        ((dyadicNoiseSplit r x).2 c) := by
  simp [poissonLevel, dyadicRefine, poissonHalfSplit]

/-- The corresponding right-child count formula. -/
theorem poissonLevel_right_formula (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    poissonLevel K (r + 1) x (Sum.inr c) =
      poissonLevel K r (dyadicNoiseSplit r x).1 c -
        binCoupling (poissonLevel K r (dyadicNoiseSplit r x).1 c)
          ((dyadicNoiseSplit r x).2 c) := by
  simp [poissonLevel, dyadicRefine, poissonHalfSplit]

/-- Exact bridge from the tree's `splitQuantileError` to K09. -/
theorem splitQuantileError_eq (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    splitQuantileError K r x c =
      let old := (dyadicNoiseSplit r x).1
      let z := (dyadicNoiseSplit r x).2 c
      let m := poissonLevel K r old c
      (binCoupling m z : ℝ) - (m : ℝ) / 2 -
        Real.sqrt (m : ℝ) / 2 * z := by
  simp [splitQuantileError, poissonLevel_left_formula]

/-- K09 on an actual parent of the landed count tree. -/
theorem abs_splitQuantileError_le (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    |splitQuantileError K r x c| ≤
      1 + ((dyadicNoiseSplit r x).2 c) ^ 2 := by
  rw [splitQuantileError_eq]
  exact abs_binCoupling_sub_le
    (poissonLevel K r (dyadicNoiseSplit r x).1 c)
    ((dyadicNoiseSplit r x).2 c)

/-- K12 left-child identity. -/
theorem bridgeError_left (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    bridgeError K (r + 1) x (Sum.inl c) =
      bridgeError K r (dyadicNoiseSplit r x).1 c / 2 +
        bridgeCorrection K r x c := by
  simp [bridgeError, bridgeCorrection, splitQuantileError,
    poissonLevel_left_formula, gaussianLevel_left_formula,
    dyadicVariance_succ]
  ring

/-- A parent error is the sum of its child errors. -/
theorem bridgeError_parent_eq_children (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    bridgeError K r (dyadicNoiseSplit r x).1 c =
      bridgeError K (r + 1) x (Sum.inl c) +
        bridgeError K (r + 1) x (Sum.inr c) := by
  have hp := poissonLevel_parent_eq_children K r x c
  have hpReal :
      (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ) =
        (poissonLevel K (r + 1) x (Sum.inl c) : ℝ) +
          (poissonLevel K (r + 1) x (Sum.inr c) : ℝ) := by
    exact_mod_cast hp
  rw [bridgeError, bridgeError, bridgeError, hpReal,
    gaussianLevel_left_formula, gaussianLevel_right_formula,
    dyadicVariance_succ]
  push_cast
  ring

/-- K12 right-child identity. -/
theorem bridgeError_right (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    bridgeError K (r + 1) x (Sum.inr c) =
      bridgeError K r (dyadicNoiseSplit r x).1 c / 2 -
        bridgeCorrection K r x c := by
  have hsum := bridgeError_parent_eq_children K r x c
  have hleft := bridgeError_left K r x c
  linarith

/-- Exact bridge from the root error to the K08 Poisson quantile expression. -/
theorem root_bridgeError_eq (K : ℕ) (x : DyadicNoiseSpace 0)
    (c : DyadicCell 0) :
    bridgeError K 0 x c =
      (poisCoupling (dyadicVariance K 0 : ℝ) (x c) : ℝ) -
        (dyadicVariance K 0 : ℝ) -
        Real.sqrt (dyadicVariance K 0 : ℝ) * x c := by
  simp [bridgeError, poissonLevel, gaussianLevel]

/-- K08 at the actual root of the tree. -/
theorem root_bridgeError_le (K : ℕ) (x : DyadicNoiseSpace 0)
    (c : DyadicCell 0) :
    |bridgeError K 0 x c| ≤ 1 + 2 * (x c) ^ 2 := by
  rw [root_bridgeError_eq]
  exact abs_poisCoupling_sub_le (dyadicVariance_pos K 0) (x c)

/-! ## Square-root estimates -/

/-- Rationalizing the difference of square roots. -/
theorem abs_sqrt_sub_le_abs_sub_div {m ell : ℝ}
    (hm : 0 ≤ m) (hell : 0 < ell) :
    |Real.sqrt m - Real.sqrt ell| ≤
      |m - ell| / Real.sqrt ell := by
  have hsell : 0 < Real.sqrt ell := Real.sqrt_pos.2 hell
  have hsum : Real.sqrt ell ≤ Real.sqrt m + Real.sqrt ell := by
    linarith [Real.sqrt_nonneg m]
  have hfactor :
      |Real.sqrt m - Real.sqrt ell| *
          (Real.sqrt m + Real.sqrt ell) = |m - ell| := by
    calc
      |Real.sqrt m - Real.sqrt ell| *
          (Real.sqrt m + Real.sqrt ell) =
          |Real.sqrt m - Real.sqrt ell| *
            |Real.sqrt m + Real.sqrt ell| := by
              rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg m) (Real.sqrt_nonneg ell))]
      _ = |(Real.sqrt m - Real.sqrt ell) *
            (Real.sqrt m + Real.sqrt ell)| := by
              rw [abs_mul]
      _ = |m - ell| := by
              congr 1
              nlinarith [Real.sq_sqrt hm, Real.sq_sqrt hell.le]
  rw [le_div_iff₀ hsell]
  calc
    |Real.sqrt m - Real.sqrt ell| * Real.sqrt ell ≤
        |Real.sqrt m - Real.sqrt ell| *
          (Real.sqrt m + Real.sqrt ell) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |m - ell| := hfactor

/-- Hölder-`1/2` continuity of the square root on the nonnegative line. -/
theorem abs_sqrt_sub_le_sqrt_abs_sub {m ell : ℝ}
    (hm : 0 ≤ m) (hell : 0 ≤ ell) :
    |Real.sqrt m - Real.sqrt ell| ≤ Real.sqrt |m - ell| := by
  have hsq :
      (Real.sqrt m - Real.sqrt ell) ^ 2 ≤ |m - ell| := by
    rcases le_total m ell with hme | hem
    · have hs := Real.sqrt_le_sqrt hme
      have hprod : m ≤ Real.sqrt m * Real.sqrt ell := by
        have h2 := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg m)
        nlinarith [Real.sq_sqrt hm]
      rw [abs_of_nonpos (sub_nonpos.mpr hme)]
      nlinarith [Real.sq_sqrt hm, Real.sq_sqrt hell]
    · have hs := Real.sqrt_le_sqrt hem
      have hprod : ell ≤ Real.sqrt ell * Real.sqrt m := by
        have h2 := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg ell)
        nlinarith [Real.sq_sqrt hell]
      rw [abs_of_nonneg (sub_nonneg.mpr hem)]
      nlinarith [Real.sq_sqrt hm, Real.sq_sqrt hell]
  calc
    |Real.sqrt m - Real.sqrt ell| =
        Real.sqrt ((Real.sqrt m - Real.sqrt ell) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt |m - ell| := Real.sqrt_le_sqrt hsq

/-- Elementary subadditivity of `sqrt`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- First K12 square-root estimate in abstract algebraic form. -/
theorem sqrtDifference_linear
    {m ell w D : ℝ} (hm : 0 ≤ m) (hell : 0 < ell)
    (hD : D = m - ell - w) :
    |Real.sqrt m - Real.sqrt ell| ≤
      |D| / Real.sqrt ell + |w / Real.sqrt ell| := by
  have hsell : 0 < Real.sqrt ell := Real.sqrt_pos.2 hell
  have hsplit : |m - ell| ≤ |D| + |w| := by
    calc
      |m - ell| = |D + w| := by rw [hD]; congr 1 <;> ring
      _ ≤ |D| + |w| := abs_add_le _ _
  calc
    |Real.sqrt m - Real.sqrt ell| ≤
        |m - ell| / Real.sqrt ell :=
      abs_sqrt_sub_le_abs_sub_div hm hell
    _ ≤ (|D| + |w|) / Real.sqrt ell :=
      div_le_div_of_nonneg_right hsplit hsell.le
    _ = |D| / Real.sqrt ell + |w / Real.sqrt ell| := by
      rw [abs_div, abs_of_pos hsell]
      ring

/-- Second K12 square-root estimate in abstract algebraic form. -/
theorem sqrtDifference_holder
    {m ell w D : ℝ} (hm : 0 ≤ m) (hell : 0 < ell)
    (hD : D = m - ell - w) :
    |Real.sqrt m - Real.sqrt ell| ≤
      Real.sqrt |D| + Real.sqrt (Real.sqrt ell) *
        Real.sqrt |w / Real.sqrt ell| := by
  have hsell : 0 < Real.sqrt ell := Real.sqrt_pos.2 hell
  have hsplit : |m - ell| ≤ |D| + |w| := by
    calc
      |m - ell| = |D + w| := by rw [hD]; congr 1 <;> ring
      _ ≤ |D| + |w| := abs_add_le _ _
  have hw : |w| = Real.sqrt ell * |w / Real.sqrt ell| := by
    rw [abs_div, abs_of_pos hsell]
    field_simp [hsell.ne']
  have hsqrtw :
      Real.sqrt |w| = Real.sqrt (Real.sqrt ell) *
        Real.sqrt |w / Real.sqrt ell| := by
    rw [hw, Real.sqrt_mul (Real.sqrt_nonneg ell)]
  calc
    |Real.sqrt m - Real.sqrt ell| ≤ Real.sqrt |m - ell| :=
      abs_sqrt_sub_le_sqrt_abs_sub hm hell.le
    _ ≤ Real.sqrt (|D| + |w|) := Real.sqrt_le_sqrt hsplit
    _ ≤ Real.sqrt |D| + Real.sqrt |w| :=
      sqrt_add_le_add_sqrt (abs_nonneg D) (abs_nonneg w)
    _ = Real.sqrt |D| + Real.sqrt (Real.sqrt ell) *
        Real.sqrt |w / Real.sqrt ell| := by rw [hsqrtw]

/-- First square-root estimate specialized to an actual parent cell. -/
theorem bridge_sqrt_linear (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    |Real.sqrt (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ) -
        Real.sqrt (dyadicVariance K r : ℝ)| ≤
      |bridgeError K r (dyadicNoiseSplit r x).1 c| /
          Real.sqrt (dyadicVariance K r : ℝ) +
        |standardizedParentIncrement K r x c| := by
  exact sqrtDifference_linear
    (m := (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ))
    (ell := (dyadicVariance K r : ℝ))
    (w := gaussianLevel K r (dyadicNoiseSplit r x).1 c)
    (D := bridgeError K r (dyadicNoiseSplit r x).1 c)
    (Nat.cast_nonneg _)
    (dyadicVariance_pos K r)
    rfl

/-- Second square-root estimate specialized to an actual parent cell. -/
theorem bridge_sqrt_holder (K r : ℕ)
    (x : DyadicNoiseSpace (r + 1)) (c : DyadicCell r) :
    |Real.sqrt (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ) -
        Real.sqrt (dyadicVariance K r : ℝ)| ≤
      Real.sqrt |bridgeError K r (dyadicNoiseSplit r x).1 c| +
        Real.sqrt (Real.sqrt (dyadicVariance K r : ℝ)) *
          Real.sqrt |standardizedParentIncrement K r x c| := by
  exact sqrtDifference_holder
    (m := (poissonLevel K r (dyadicNoiseSplit r x).1 c : ℝ))
    (ell := (dyadicVariance K r : ℝ))
    (w := gaussianLevel K r (dyadicNoiseSplit r x).1 c)
    (D := bridgeError K r (dyadicNoiseSplit r x).1 c)
    (Nat.cast_nonneg _)
    (dyadicVariance_pos K r)
    rfl

/-!
THEOREM LIST
* `gaussianMidpoint_sub_left_formula`, `gaussian_right_sub_midpoint_formula`
* `gaussianLevel_left_formula`, `gaussianLevel_right_formula`
* `poissonLevel_left_formula`, `poissonLevel_right_formula`
* `splitQuantileError_eq`, `abs_splitQuantileError_le`
* `bridgeError_left`, `bridgeError_parent_eq_children`, `bridgeError_right`
* `root_bridgeError_eq`, `root_bridgeError_le`
* `abs_sqrt_sub_le_abs_sub_div`, `abs_sqrt_sub_le_sqrt_abs_sub`
* `sqrtDifference_linear`, `sqrtDifference_holder`
* `bridge_sqrt_linear`, `bridge_sqrt_holder`

CLOSES K12
* Both child bridge-error identities.
* Both requested square-root estimates.
* Exact K09 and K08 adapters with their actual hypotheses.

UNFINISHED
* Nothing mathematical from K12 is intentionally omitted.
END
-/

end Ripple.Kurtz.StrongApprox

end

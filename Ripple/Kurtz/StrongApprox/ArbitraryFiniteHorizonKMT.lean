-- Ripple/Kurtz/StrongApprox/ArbitraryFiniteHorizonKMT.lean
import Ripple.Kurtz.StrongApprox.ContinuousFiniteHorizonKMT

/-!
# K21: an arbitrary finite real horizon

From `ContinuousFiniteHorizonKMT` this file uses:

* `ContinuousKMTSpace`, `continuousKMTMeasure`,
  `continuousKMTPoisson`, and `continuousKMTBrownian`;
* `continuousTime_finiteHorizonKMT` with constants
  `3375 + 2 exp 1`, `7 + exp 2`, and `9 / 65536`;
* `continuousKMTPoisson_incrementVector_law` and
  `continuousKMTPoisson_increment_iIndep`;
* `continuousKMTBrownian_dyadicBrownianOn`;
* the measure-preserving projection `continuousKMTMeasure_toContinuous`.

The last projection transports K19's pointwise right continuity and
almost-sure unit-jump statement to the common `ContinuousFiniteHorizonKMT` space.

This is a separate concrete coupling for each `T`.  A single coupling for all
horizons is intentionally deferred to K22--K23.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Nat Topology

namespace Ripple.Kurtz.StrongApprox.ArbitraryFiniteHorizonKMT

open ContinuousFiniteHorizonKMT
open DyadicConditionalPoissonPath
open DyadicSpatialSkeleton

/-! ## The dyadic cover of a real horizon -/

/-- `K(T) = ceil (log_2 (max 2 T))`, using `Real.logb` and `Nat.ceil`. -/
noncomputable def arbitraryHorizonExponent (T : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 2 T))

/-- The natural dyadic horizon `n(T) = 2 ^ K(T)`. -/
noncomputable def arbitraryHorizonNat (T : ℝ) : ℕ :=
  2 ^ arbitraryHorizonExponent T

/-- The same dyadic horizon regarded as a real number. -/
noncomputable def arbitraryHorizonLength (T : ℝ) : ℝ :=
  (2 : ℝ) ^ arbitraryHorizonExponent T

@[simp] theorem arbitraryHorizonNat_cast (T : ℝ) :
    (arbitraryHorizonNat T : ℝ) = arbitraryHorizonLength T := by
  simp [arbitraryHorizonNat, arbitraryHorizonLength]

private theorem arbitraryHorizonLength_pos (T : ℝ) :
    0 < arbitraryHorizonLength T := by
  unfold arbitraryHorizonLength
  positivity

/-- The exact dyadic rounding inequalities
`max 2 T ≤ 2^K < 2 max 2 T`. -/
theorem arbitraryHorizon_power_bounds (T : ℝ) :
    max (2 : ℝ) T ≤ arbitraryHorizonLength T ∧
      arbitraryHorizonLength T < 2 * max (2 : ℝ) T := by
  let M : ℝ := max 2 T
  let K : ℕ := arbitraryHorizonExponent T
  have hMtwo : (2 : ℝ) ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMtwo
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogbNonneg : 0 ≤ Real.logb 2 M :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hceilLower : Real.logb 2 M ≤ (K : ℝ) := by
    dsimp [K, arbitraryHorizonExponent]
    exact Nat.le_ceil _
  have hlogLower :
      Real.log M ≤ (K : ℝ) * Real.log 2 := by
    rw [Real.logb, div_le_iff₀ hlogTwo] at hceilLower
    exact hceilLower
  have hlower : M ≤ (2 : ℝ) ^ K := by
    calc
      M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp ((K : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hlogLower
      _ = Real.exp (Real.log ((2 : ℝ) ^ K)) := by
        rw [Real.log_pow]
      _ = (2 : ℝ) ^ K :=
        Real.exp_log (pow_pos (by norm_num) K)
  have hceilUpper : (K : ℝ) < Real.logb 2 M + 1 := by
    dsimp [K, arbitraryHorizonExponent]
    exact Nat.ceil_lt_add_one hlogbNonneg
  have hlogUpper :
      (K : ℝ) * Real.log 2 < Real.log M + Real.log 2 := by
    have hmul := mul_lt_mul_of_pos_right hceilUpper hlogTwo
    rw [add_mul, Real.logb,
      div_mul_cancel₀ _ hlogTwo.ne', one_mul] at hmul
    exact hmul
  have hupper : (2 : ℝ) ^ K < 2 * M := by
    calc
      (2 : ℝ) ^ K = Real.exp (Real.log ((2 : ℝ) ^ K)) :=
        (Real.exp_log (pow_pos (by norm_num) K)).symm
      _ = Real.exp ((K : ℝ) * Real.log 2) := by
        rw [Real.log_pow]
      _ < Real.exp (Real.log M + Real.log 2) :=
        Real.exp_lt_exp.mpr hlogUpper
      _ = Real.exp (Real.log M) * Real.exp (Real.log 2) := by
        rw [Real.exp_add]
      _ = M * 2 := by
        rw [Real.exp_log hMpos, Real.exp_log (by norm_num)]
      _ = 2 * M := by ring
  simpa [M, K, arbitraryHorizonLength] using And.intro hlower hupper

/-- In particular, the real horizon is contained in its dyadic cover. -/
theorem arbitraryHorizon_le (T : ℝ) :
    T ≤ arbitraryHorizonLength T :=
  (le_max_right (2 : ℝ) T).trans
    (arbitraryHorizon_power_bounds T).1

/-- Item 1's natural-number statement. -/
theorem arbitraryHorizon_nat_bounds (T : ℝ) :
    T ≤ (arbitraryHorizonNat T : ℝ) ∧
      (arbitraryHorizonNat T : ℝ) < 2 * max (2 : ℝ) T := by
  have h := arbitraryHorizon_power_bounds T
  simpa only [arbitraryHorizonNat_cast] using
    (⟨(le_max_right (2 : ℝ) T).trans h.1, h.2⟩ :
      T ≤ arbitraryHorizonLength T ∧
        arbitraryHorizonLength T < 2 * max (2 : ℝ) T)

/-- The two logarithmic comparisons requested in item 1. -/
theorem arbitraryHorizon_log_bounds
    {T : ℝ} (hT : 1 ≤ T) :
    Real.log (arbitraryHorizonNat T : ℝ) ≤
        Real.log (2 * max (2 : ℝ) T) ∧
      Real.log (2 * max (2 : ℝ) T) ≤
        Real.log T + 2 * Real.log 2 := by
  have hpow := arbitraryHorizon_power_bounds T
  have hnatPos : 0 < (arbitraryHorizonNat T : ℝ) := by
    rw [arbitraryHorizonNat_cast]
    exact arbitraryHorizonLength_pos T
  have hnatUpper :
      (arbitraryHorizonNat T : ℝ) ≤ 2 * max (2 : ℝ) T := by
    rw [arbitraryHorizonNat_cast]
    exact hpow.2.le
  constructor
  · exact Real.log_le_log hnatPos hnatUpper
  · have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    by_cases htwo : 2 ≤ T
    · rw [max_eq_right htwo,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
      have hlogTwo : 0 ≤ Real.log (2 : ℝ) :=
        (Real.log_pos (by norm_num)).le
      linarith
    · have hTle : T ≤ 2 := le_of_not_ge htwo
      rw [max_eq_left hTle,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
      have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
      linarith

/-- `ContinuousFiniteHorizonKMT` uses `log(2^(K+1))`; the arbitrary-horizon loss is exactly three
additional copies of `log 2`. -/
theorem arbitraryHorizon_headlineLog_le
    {T : ℝ} (hT : 1 ≤ T) :
    Real.log ((2 : ℝ) ^ (arbitraryHorizonExponent T + 1)) ≤
      Real.log T + 3 * Real.log 2 := by
  have hlogNat :
      Real.log (arbitraryHorizonNat T : ℝ) ≤
        Real.log T + 2 * Real.log 2 :=
    (arbitraryHorizon_log_bounds hT).1.trans
      (arbitraryHorizon_log_bounds hT).2
  calc
    Real.log ((2 : ℝ) ^ (arbitraryHorizonExponent T + 1)) =
        Real.log ((2 : ℝ) ^ arbitraryHorizonExponent T) +
          Real.log 2 := by
      rw [pow_succ,
        Real.log_mul
          (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
          (by norm_num : (2 : ℝ) ≠ 0)]
    _ = Real.log (arbitraryHorizonNat T : ℝ) + Real.log 2 := by
      simp [arbitraryHorizonNat]
    _ ≤ Real.log T + 3 * Real.log 2 := by
      linarith

/-! ## The concrete probability space and restricted processes -/

abbrev ArbitraryHorizonKMTSpace (T : ℝ) :=
  ContinuousKMTSpace (arbitraryHorizonExponent T)

noncomputable def arbitraryHorizonKMTMeasure (T : ℝ) :
    Measure (ArbitraryHorizonKMTSpace T) :=
  continuousKMTMeasure (arbitraryHorizonExponent T)

instance arbitraryHorizonKMTMeasure_isProbabilityMeasure (T : ℝ) :
    IsProbabilityMeasure (arbitraryHorizonKMTMeasure T) := by
  unfold arbitraryHorizonKMTMeasure
  infer_instance

noncomputable def arbitraryHorizonPoisson
    (T t : ℝ) (omega : ArbitraryHorizonKMTSpace T) : ℕ :=
  continuousKMTPoisson (arbitraryHorizonExponent T) t omega

noncomputable def arbitraryHorizonBrownian
    (T t : ℝ) (omega : ArbitraryHorizonKMTSpace T) : ℝ :=
  continuousKMTBrownian (arbitraryHorizonExponent T) t omega

@[fun_prop] theorem measurable_arbitraryHorizonPoisson
    (T t : ℝ) :
    Measurable (arbitraryHorizonPoisson T t) :=
  measurable_continuousKMTPoisson (arbitraryHorizonExponent T) t

@[fun_prop] theorem measurable_arbitraryHorizonBrownian
    (T t : ℝ) :
    Measurable (arbitraryHorizonBrownian T t) :=
  measurable_continuousKMTBrownian (arbitraryHorizonExponent T) t

@[simp] theorem arbitraryHorizonPoisson_zero
    (T : ℝ) (omega : ArbitraryHorizonKMTSpace T) :
    arbitraryHorizonPoisson T 0 omega = 0 := by
  unfold arbitraryHorizonPoisson
  simpa using
    continuousKMTPoisson_natCast
      (arbitraryHorizonExponent T) 0 omega

/-- Samplewise monotonicity. -/
theorem arbitraryHorizonPoisson_mono
    (T : ℝ) (omega : ArbitraryHorizonKMTSpace T)
    {s t : ℝ} (hst : s ≤ t) :
    arbitraryHorizonPoisson T s omega ≤
      arbitraryHorizonPoisson T t omega :=
  continuousKMTPoisson_mono
    (arbitraryHorizonExponent T) omega hst

/-- Integer-valuedness after coercion to `ℝ`. -/
theorem arbitraryHorizonPoisson_integerValued
    (T t : ℝ) (omega : ArbitraryHorizonKMTSpace T) :
    ∃ m : ℕ, (arbitraryHorizonPoisson T t omega : ℝ) = m :=
  ⟨arbitraryHorizonPoisson T t omega, rfl⟩

/-- Pointwise right continuity, stronger than merely almost sure right
continuity on `[0,T]`. -/
theorem arbitraryHorizonPoisson_rightContinuous
    (T t : ℝ) (omega : ArbitraryHorizonKMTSpace T) :
    ContinuousWithinAt
      (fun s => (arbitraryHorizonPoisson T s omega : ℝ)) (Ici t) t := by
  simpa [arbitraryHorizonPoisson, continuousKMTPoisson] using
    committedContinuousPoisson_continuousWithinAt
      (arbitraryHorizonExponent T) t
      (continuousKMTToContinuous
        (arbitraryHorizonExponent T) omega)

noncomputable def arbitraryHorizonPoissonLeftCount
    (T : ℝ) (omega : ArbitraryHorizonKMTSpace T) (t : ℝ) : ℕ :=
  dyadicArrivalLeftCount (arbitraryHorizonExponent T)
    (continuousKMTToContinuous (arbitraryHorizonExponent T) omega) t

noncomputable def arbitraryHorizonPoissonMultiplicity
    (T : ℝ) (omega : ArbitraryHorizonKMTSpace T) (t : ℝ) : ℕ :=
  dyadicArrivalMultiplicity (arbitraryHorizonExponent T)
    (continuousKMTToContinuous (arbitraryHorizonExponent T) omega) t

/-- K19's unit-jump event transported to the common `ContinuousFiniteHorizonKMT` space. -/
theorem arbitraryHorizonPoisson_unitJumps_ae (T : ℝ) :
    ∀ᵐ omega ∂arbitraryHorizonKMTMeasure T,
      ∀ t : ℝ, 0 ≤ t → t ≤ arbitraryHorizonLength T →
        arbitraryHorizonPoisson T t omega =
            arbitraryHorizonPoissonLeftCount T omega t +
              arbitraryHorizonPoissonMultiplicity T omega t ∧
          arbitraryHorizonPoissonMultiplicity T omega t ≤ 1 ∧
          (0 < arbitraryHorizonPoisson T t omega -
                arbitraryHorizonPoissonLeftCount T omega t →
            arbitraryHorizonPoisson T t omega -
                arbitraryHorizonPoissonLeftCount T omega t = 1) := by
  let K := arbitraryHorizonExponent T
  let P : DyadicContinuousSpace K → Prop := fun z =>
    ∀ t : ℝ, 0 ≤ t → t ≤ ((2 ^ K : ℕ) : ℝ) →
      committedContinuousPoisson K t z =
          dyadicArrivalLeftCount K z t + dyadicArrivalMultiplicity K z t ∧
        dyadicArrivalMultiplicity K z t ≤ 1 ∧
        (0 < committedContinuousPoisson K t z -
              dyadicArrivalLeftCount K z t →
          committedContinuousPoisson K t z -
              dyadicArrivalLeftCount K z t = 1)
  have hpull :
      ∀ᵐ omega ∂continuousKMTMeasure K,
        P (continuousKMTToContinuous K omega) := by
    refine MeasureTheory.ae_of_ae_map
      (p := P)
      (continuousKMTMeasure_toContinuous K).measurable.aemeasurable ?_
    rw [(continuousKMTMeasure_toContinuous K).map_eq]
    exact committedContinuousPoisson_unitJumps_ae K
  simpa [arbitraryHorizonKMTMeasure, arbitraryHorizonPoisson,
    arbitraryHorizonPoissonLeftCount, arbitraryHorizonPoissonMultiplicity,
    arbitraryHorizonLength, continuousKMTPoisson, P, K, Nat.cast_pow]
    using hpull

/-- Restrict the preceding event from the dyadic cover to `[0,T]`. -/
theorem arbitraryHorizonPoisson_unitJumps_ae_on (T : ℝ) :
    ∀ᵐ omega ∂arbitraryHorizonKMTMeasure T,
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) T →
        arbitraryHorizonPoisson T t omega =
            arbitraryHorizonPoissonLeftCount T omega t +
              arbitraryHorizonPoissonMultiplicity T omega t ∧
          arbitraryHorizonPoissonMultiplicity T omega t ≤ 1 ∧
          (0 < arbitraryHorizonPoisson T t omega -
                arbitraryHorizonPoissonLeftCount T omega t →
            arbitraryHorizonPoisson T t omega -
                arbitraryHorizonPoissonLeftCount T omega t = 1) := by
  filter_upwards [arbitraryHorizonPoisson_unitJumps_ae T] with omega homega
  intro t ht
  exact homega t ht.1 (ht.2.trans (arbitraryHorizon_le T))

noncomputable def arbitraryHorizonPoissonIncrementVector
    (T : ℝ) {r : ℕ} (grid : Fin (r + 1) → ℝ)
    (omega : ArbitraryHorizonKMTSpace T) : Fin r → ℕ :=
  continuousKMTPoissonIncrementVector
    (arbitraryHorizonExponent T) grid omega

/-- Every increasing grid in `[0,T]` has the product Poisson increment law. -/
theorem arbitraryHorizonPoisson_incrementVector_law
    (T : ℝ) {r : ℕ} (grid : Fin (r + 1) → ℝ)
    (hzero : grid 0 = 0) (hstrict : StrictMono grid)
    (hlast : grid (Fin.last r) ≤ T) :
    (arbitraryHorizonKMTMeasure T).map
        (arbitraryHorizonPoissonIncrementVector T grid) =
      poissonIncrementProduct grid := by
  have hlastCover :
      grid (Fin.last r) ≤
        (((2 ^ arbitraryHorizonExponent T : ℕ) : ℝ)) := by
    calc
      grid (Fin.last r) ≤ T := hlast
      _ ≤ arbitraryHorizonLength T := arbitraryHorizon_le T
      _ = (((2 ^ arbitraryHorizonExponent T : ℕ) : ℝ)) := by
        simp [arbitraryHorizonLength]
  simpa [arbitraryHorizonKMTMeasure,
    arbitraryHorizonPoissonIncrementVector] using
    continuousKMTPoisson_incrementVector_law
      (arbitraryHorizonExponent T) grid hzero hstrict hlastCover

/-- Hence those disjoint adjacent increments are independent. -/
theorem arbitraryHorizonPoisson_increment_iIndep
    (T : ℝ) {r : ℕ} (grid : Fin (r + 1) → ℝ)
    (hzero : grid 0 = 0) (hstrict : StrictMono grid)
    (hlast : grid (Fin.last r) ≤ T) :
    iIndepFun
      (fun i omega =>
        arbitraryHorizonPoissonIncrementVector T grid omega i)
      (arbitraryHorizonKMTMeasure T) := by
  have hlastCover :
      grid (Fin.last r) ≤
        (((2 ^ arbitraryHorizonExponent T : ℕ) : ℝ)) := by
    calc
      grid (Fin.last r) ≤ T := hlast
      _ ≤ arbitraryHorizonLength T := arbitraryHorizon_le T
      _ = (((2 ^ arbitraryHorizonExponent T : ℕ) : ℝ)) := by
        simp [arbitraryHorizonLength]
  simpa [arbitraryHorizonKMTMeasure,
    arbitraryHorizonPoissonIncrementVector] using
    continuousKMTPoisson_increment_iIndep
      (arbitraryHorizonExponent T) grid hzero hstrict hlastCover

/-- The complete Brownian interface of `ContinuousFiniteHorizonKMT` on the covering horizon. -/
theorem arbitraryHorizonBrownian_dyadicBrownianOn (T : ℝ) :
    DyadicBrownianOn (arbitraryHorizonKMTMeasure T)
      (arbitraryHorizonBrownian T) (arbitraryHorizonLength T) := by
  simpa [arbitraryHorizonKMTMeasure, arbitraryHorizonBrownian,
    arbitraryHorizonLength] using
    continuousKMTBrownian_dyadicBrownianOn
      (arbitraryHorizonExponent T)

/-! ## Explicit K21 constants and the tail -/

def arbitraryFiniteHorizonConstant : ℝ :=
  continuousKMTConstant

def arbitraryFiniteHorizonRate : ℝ :=
  continuousKMTRate

/-- The deterministic loss converting the dyadic baseline of `ContinuousFiniteHorizonKMT` to `C log T`. -/
def arbitraryFiniteHorizonShift : ℝ :=
  3 * arbitraryFiniteHorizonConstant * Real.log 2

/-- Enlarged only once, so the theorem remains valid when `log T = 0`. -/
def arbitraryFiniteHorizonPrefactor : ℝ :=
  continuousKMTPrefactor *
    Real.exp
      (arbitraryFiniteHorizonRate * arbitraryFiniteHorizonShift)

/-- The constants are all strictly positive. -/
theorem arbitraryFiniteHorizonConstants_pos :
    0 < arbitraryFiniteHorizonConstant ∧
      0 < arbitraryFiniteHorizonPrefactor ∧
      0 < arbitraryFiniteHorizonRate := by
  unfold arbitraryFiniteHorizonConstant arbitraryFiniteHorizonPrefactor
    arbitraryFiniteHorizonRate arbitraryFiniteHorizonShift
    continuousKMTConstant continuousKMTPrefactor continuousKMTRate
  refine ⟨by positivity, by positivity, by norm_num⟩

private theorem arbitraryFiniteHorizonShift_nonneg :
    0 ≤ arbitraryFiniteHorizonShift := by
  have hconstant : 0 ≤ arbitraryFiniteHorizonConstant :=
    (arbitraryFiniteHorizonConstants_pos).1.le
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  unfold arbitraryFiniteHorizonShift
  positivity

/-- The baseline comparison used in the event inclusion. -/
theorem arbitraryHorizon_baseline_le
    {T : ℝ} (hT : 1 ≤ T) :
    continuousKMTConstant *
        Real.log ((2 : ℝ) ^ (arbitraryHorizonExponent T + 1)) ≤
      arbitraryFiniteHorizonConstant * Real.log T +
        arbitraryFiniteHorizonShift := by
  calc
    continuousKMTConstant *
        Real.log ((2 : ℝ) ^ (arbitraryHorizonExponent T + 1)) ≤
      continuousKMTConstant *
        (Real.log T + 3 * Real.log 2) :=
      mul_le_mul_of_nonneg_left
        (arbitraryHorizon_headlineLog_le hT)
        (arbitraryFiniteHorizonConstants_pos).1.le
    _ = arbitraryFiniteHorizonConstant * Real.log T +
        arbitraryFiniteHorizonShift := by
      unfold arbitraryFiniteHorizonShift arbitraryFiniteHorizonConstant
      ring

/-- The existential-supremum event used by Ethier--Kurtz. -/
def finiteHorizonKMTFailure
    (T C x : ℝ) : Set (ArbitraryHorizonKMTSpace T) :=
  {omega | ∃ t : ℝ, t ∈ Icc (0 : ℝ) T ∧
    C * Real.log T + x <
      |(arbitraryHorizonPoisson T t omega : ℝ) - t -
        arbitraryHorizonBrownian T t omega|}

private theorem shiftedTail_identity (x : ℝ) :
    continuousKMTPrefactor *
        Real.exp (-(continuousKMTRate *
          (x - arbitraryFiniteHorizonShift))) =
      arbitraryFiniteHorizonPrefactor *
        Real.exp (-(arbitraryFiniteHorizonRate * x)) := by
  unfold arbitraryFiniteHorizonPrefactor arbitraryFiniteHorizonRate
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **K21 tail on the concrete `K(T)` space.** -/
theorem law_finiteHorizonKMTFailure
    {T x : ℝ} (hT : 1 ≤ T) (hx : 0 ≤ x) :
    (arbitraryHorizonKMTMeasure T).real
        (finiteHorizonKMTFailure
          T arbitraryFiniteHorizonConstant x) ≤
      arbitraryFiniteHorizonPrefactor *
        Real.exp (-(arbitraryFiniteHorizonRate * x)) := by
  by_cases hlarge : arbitraryFiniteHorizonShift ≤ x
  · let y : ℝ := x - arbitraryFiniteHorizonShift
    have hy : 0 ≤ y := by
      dsimp [y]
      linarith
    have hthreshold :
        continuousKMTConstant *
              Real.log ((2 : ℝ) ^
                (arbitraryHorizonExponent T + 1)) + y ≤
          arbitraryFiniteHorizonConstant * Real.log T + x := by
      dsimp [y]
      linarith [arbitraryHorizon_baseline_le hT]
    have hsub :
        finiteHorizonKMTFailure
            T arbitraryFiniteHorizonConstant x ⊆
          {omega : ArbitraryHorizonKMTSpace T | ∃ t : ℝ,
            t ∈ Icc (0 : ℝ)
              ((2 : ℝ) ^ arbitraryHorizonExponent T) ∧
              continuousKMTConstant *
                    Real.log ((2 : ℝ) ^
                      (arbitraryHorizonExponent T + 1)) + y <
                |(continuousKMTPoisson
                    (arbitraryHorizonExponent T) t omega : ℝ) - t -
                  continuousKMTBrownian
                    (arbitraryHorizonExponent T) t omega|} := by
      intro omega homega
      change ∃ t : ℝ, t ∈ Icc (0 : ℝ) T ∧
        arbitraryFiniteHorizonConstant * Real.log T + x <
          |(arbitraryHorizonPoisson T t omega : ℝ) - t -
            arbitraryHorizonBrownian T t omega| at homega
      rcases homega with ⟨t, ht, hbad⟩
      refine ⟨t, ⟨ht.1, ht.2.trans ?_⟩, ?_⟩
      · simpa [arbitraryHorizonLength] using arbitraryHorizon_le T
      · change
          continuousKMTConstant *
                Real.log ((2 : ℝ) ^
                  (arbitraryHorizonExponent T + 1)) + y <
            |(arbitraryHorizonPoisson T t omega : ℝ) - t -
              arbitraryHorizonBrownian T t omega|
        exact hthreshold.trans_lt hbad
    have hfinite :=
      continuousTime_finiteHorizonKMT
        (arbitraryHorizonExponent T) hy
    calc
      (arbitraryHorizonKMTMeasure T).real
          (finiteHorizonKMTFailure
            T arbitraryFiniteHorizonConstant x) ≤
        (continuousKMTMeasure (arbitraryHorizonExponent T)).real
          {omega | ∃ t : ℝ,
            t ∈ Icc (0 : ℝ)
              ((2 : ℝ) ^ arbitraryHorizonExponent T) ∧
              continuousKMTConstant *
                    Real.log ((2 : ℝ) ^
                      (arbitraryHorizonExponent T + 1)) + y <
                |(continuousKMTPoisson
                    (arbitraryHorizonExponent T) t omega : ℝ) - t -
                  continuousKMTBrownian
                    (arbitraryHorizonExponent T) t omega|} := by
        exact measureReal_mono hsub
      _ ≤ continuousKMTPrefactor *
          Real.exp (-(continuousKMTRate * y)) := hfinite
      _ = arbitraryFiniteHorizonPrefactor *
          Real.exp (-(arbitraryFiniteHorizonRate * x)) := by
        dsimp [y]
        exact shiftedTail_identity x
  · have hxShift : x < arbitraryFiniteHorizonShift :=
      lt_of_not_ge hlarge
    have hprefactor : 1 ≤ continuousKMTPrefactor := by
      unfold continuousKMTPrefactor
      linarith [Real.exp_pos (2 : ℝ)]
    have htailOne :
        1 ≤ arbitraryFiniteHorizonPrefactor *
          Real.exp (-(arbitraryFiniteHorizonRate * x)) := by
      calc
        1 ≤ continuousKMTPrefactor := hprefactor
        _ = continuousKMTPrefactor * 1 := (mul_one _).symm
        _ ≤ continuousKMTPrefactor *
            Real.exp
              (arbitraryFiniteHorizonRate *
                (arbitraryFiniteHorizonShift - x)) := by
          gcongr
          exact Real.one_le_exp
            (mul_nonneg
              (arbitraryFiniteHorizonConstants_pos).2.2.le
              (sub_nonneg.mpr hxShift.le))
        _ = continuousKMTPrefactor *
            Real.exp (-(continuousKMTRate *
              (x - arbitraryFiniteHorizonShift))) := by
          unfold arbitraryFiniteHorizonRate
          congr 1
          ring
        _ = arbitraryFiniteHorizonPrefactor *
            Real.exp (-(arbitraryFiniteHorizonRate * x)) :=
          shiftedTail_identity x
    exact measureReal_le_one.trans htailOne

/-! ## One Prop-valued headline carrying all requested interfaces -/

/-- A concrete finite-horizon coupling witness.  Its Brownian field is stated
on the slightly larger dyadic cover, hence in particular restricts to `[0,T]`.
The Poisson finite-grid fields express independent rate-one increments. -/
structure FiniteHorizonKMTWitness
    (T C a b : ℝ) : Prop where
  horizon_ge_one : 1 ≤ T
  horizon_covered : T ≤ arbitraryHorizonLength T
  poisson_eval_measurable :
    ∀ t : ℝ, Measurable (arbitraryHorizonPoisson T t)
  poisson_zero :
    ∀ omega, arbitraryHorizonPoisson T 0 omega = 0
  poisson_mono :
    ∀ omega {s t : ℝ}, s ≤ t →
      arbitraryHorizonPoisson T s omega ≤
        arbitraryHorizonPoisson T t omega
  poisson_integer_valued :
    ∀ t omega, ∃ m : ℕ,
      (arbitraryHorizonPoisson T t omega : ℝ) = m
  poisson_right_continuous :
    ∀ t omega,
      ContinuousWithinAt
        (fun s => (arbitraryHorizonPoisson T s omega : ℝ))
        (Ici t) t
  poisson_unit_jumps :
    ∀ᵐ omega ∂arbitraryHorizonKMTMeasure T,
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) T →
        arbitraryHorizonPoisson T t omega =
            arbitraryHorizonPoissonLeftCount T omega t +
              arbitraryHorizonPoissonMultiplicity T omega t ∧
          arbitraryHorizonPoissonMultiplicity T omega t ≤ 1 ∧
          (0 < arbitraryHorizonPoisson T t omega -
                arbitraryHorizonPoissonLeftCount T omega t →
            arbitraryHorizonPoisson T t omega -
                arbitraryHorizonPoissonLeftCount T omega t = 1)
  poisson_increment_law :
    ∀ {r : ℕ} (grid : Fin (r + 1) → ℝ),
      grid 0 = 0 → StrictMono grid →
      grid (Fin.last r) ≤ T →
      (arbitraryHorizonKMTMeasure T).map
          (arbitraryHorizonPoissonIncrementVector T grid) =
        poissonIncrementProduct grid
  poisson_increment_independent :
    ∀ {r : ℕ} (grid : Fin (r + 1) → ℝ),
      grid 0 = 0 → StrictMono grid →
      grid (Fin.last r) ≤ T →
      iIndepFun
        (fun i omega =>
          arbitraryHorizonPoissonIncrementVector T grid omega i)
        (arbitraryHorizonKMTMeasure T)
  brownian :
    DyadicBrownianOn (arbitraryHorizonKMTMeasure T)
      (arbitraryHorizonBrownian T) (arbitraryHorizonLength T)
  tail :
    ∀ x : ℝ, 0 ≤ x →
      (arbitraryHorizonKMTMeasure T).real
          (finiteHorizonKMTFailure T C x) ≤
        a * Real.exp (-(b * x))

/-- **Ethier--Kurtz Ch. 7 Cor. 5.3, finite-horizon form.**

The witnesses are the explicit constants printed above, and the probability
space is the concrete `ContinuousFiniteHorizonKMT` space at `K(T)`. -/
theorem continuousTime_arbitraryFiniteHorizonKMT :
    ∃ C a b : ℝ,
      0 < C ∧ 0 < a ∧ 0 < b ∧
        ∀ T : ℝ, 1 ≤ T →
          FiniteHorizonKMTWitness T C a b := by
  refine ⟨arbitraryFiniteHorizonConstant,
    arbitraryFiniteHorizonPrefactor,
    arbitraryFiniteHorizonRate,
    arbitraryFiniteHorizonConstants_pos.1,
    arbitraryFiniteHorizonConstants_pos.2.1,
    arbitraryFiniteHorizonConstants_pos.2.2, ?_⟩
  intro T hT
  exact
    { horizon_ge_one := hT
      horizon_covered := arbitraryHorizon_le T
      poisson_eval_measurable := measurable_arbitraryHorizonPoisson T
      poisson_zero := arbitraryHorizonPoisson_zero T
      poisson_mono := arbitraryHorizonPoisson_mono T
      poisson_integer_valued := arbitraryHorizonPoisson_integerValued T
      poisson_right_continuous := arbitraryHorizonPoisson_rightContinuous T
      poisson_unit_jumps := arbitraryHorizonPoisson_unitJumps_ae_on T
      poisson_increment_law := fun grid hzero hstrict hlast =>
        arbitraryHorizonPoisson_incrementVector_law
          T grid hzero hstrict hlast
      poisson_increment_independent := fun grid hzero hstrict hlast =>
        arbitraryHorizonPoisson_increment_iIndep
          T grid hzero hstrict hlast
      brownian := arbitraryHorizonBrownian_dyadicBrownianOn T
      tail := fun x hx => law_finiteHorizonKMTFailure hT hx }

/-!
THEOREM LIST
* `arbitraryHorizonNat_cast`
* `arbitraryHorizon_power_bounds`
* `arbitraryHorizon_le`, `arbitraryHorizon_nat_bounds`
* `arbitraryHorizon_log_bounds`
* `arbitraryHorizon_headlineLog_le`
* `arbitraryHorizonPoisson_zero`, `_mono`, `_integerValued`,
  `_rightContinuous`, `_unitJumps_ae_on`
* `arbitraryHorizonPoisson_incrementVector_law`
* `arbitraryHorizonPoisson_increment_iIndep`
* `arbitraryHorizonBrownian_dyadicBrownianOn`
* `arbitraryFiniteHorizonConstants_pos`
* `arbitraryHorizon_baseline_le`
* `law_finiteHorizonKMTFailure`
* `continuousTime_arbitraryFiniteHorizonKMT`

CLOSES ITEM 1
* Defines `K(T)` with `Real.logb 2` and `Nat.ceil`.
* Proves `T ≤ n(T) < 2 max(2,T)` and
  `log n(T) ≤ log(2 max(2,T)) ≤ log T + 2 log 2`.

CLOSES ITEM 2
* Gives explicit positive absolute constants
  `C = 3375 + 2 exp 1`, `b = 9/65536`, and
  `a = (7 + exp 2) exp(b * 3 C log 2)`.
* Uses the concrete `K(T)` probability space and restricts the failure event
  to `t ∈ [0,T]`.
* Carries the finite-grid product Poisson law, increment independence,
  monotonicity, integer values, right continuity, almost-sure unit jumps, and
  the `DyadicBrownianOn` interface on the covering horizon.
* The event is literally existential:
  `∃ t ∈ Icc 0 T, C log T + x < |Y(t) - t - W(t)|`.

UNFINISHED
* K22--K23: pass from these separately chosen finite-horizon couplings to one
  coupling whose same paths satisfy the estimate for all horizons.
* No K21 mathematical premise is intentionally omitted.
END
-/

end Ripple.Kurtz.StrongApprox.ArbitraryFiniteHorizonKMT

end

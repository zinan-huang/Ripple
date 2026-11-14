import Ripple.Stochastic.StrongSDEFixedPoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Factorial Picard estimates on a finite horizon

The scalar Volterra estimate is iterated here;
the construction of the stochastic distance profile and the proof of its
Volterra estimate remain application obligations. No smallness assumption on
the horizon or on the Volterra constant is used.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped Topology NNReal

namespace Ripple.Stochastic.StrongSDE

/-- Repeated Volterra inequalities yield the factorial bound. Nonnegativity of
the profiles is unnecessary for this scalar argument. In the SDE application
the profiles are expectations of nonnegative squared path suprema. -/
theorem factorial_volterra_bound
    (u : ℕ → ℝ → ℝ) {T K A : ℝ} (hK : 0 ≤ K)
    (hContinuous : ∀ n, ContinuousOn (u n) (Icc 0 T))
    (hBase : ∀ t ∈ Icc 0 T, u 0 t ≤ A)
    (hVolterra : ∀ n t, t ∈ Icc 0 T →
      u (n + 1) t ≤ K * ∫ s in (0 : ℝ)..t, u n s) :
    ∀ n t, t ∈ Icc 0 T →
      u n t ≤ K ^ n * t ^ n / (n.factorial : ℝ) * A := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simpa using hBase t ht
  | succ n ih =>
      intro t ht
      have hSub : Icc (0 : ℝ) t ⊆ Icc 0 T := by
        intro s hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      have hInt : IntervalIntegrable (u n) volume 0 t :=
        ContinuousOn.intervalIntegrable_of_Icc ht.1 ((hContinuous n).mono hSub)
      have hPoly : Continuous (fun s : ℝ =>
          K ^ n * s ^ n / (n.factorial : ℝ) * A) := by
        fun_prop
      have hIntegral : (∫ s in (0 : ℝ)..t, u n s) ≤
          ∫ s in (0 : ℝ)..t, K ^ n * s ^ n / (n.factorial : ℝ) * A := by
        apply intervalIntegral.integral_mono_on ht.1 hInt (hPoly.intervalIntegrable 0 t)
        intro s hs
        exact ih s (hSub hs)
      have hFactorial : (n.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hSucc : (n : ℝ) + 1 ≠ 0 := by positivity
      calc
        u (n + 1) t ≤ K * ∫ s in (0 : ℝ)..t, u n s := hVolterra n t ht
        _ ≤ K * ∫ s in (0 : ℝ)..t,
            K ^ n * s ^ n / (n.factorial : ℝ) * A :=
          mul_le_mul_of_nonneg_left hIntegral hK
        _ = K ^ (n + 1) * t ^ (n + 1) / ((n + 1).factorial : ℝ) * A := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
            intervalIntegral.integral_const_mul, integral_pow]
          simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
          field_simp [hFactorial, hSucc]
          <;> ring

/-- The factorial coefficients become smaller than one for every real base.
The positive iterate index is included in the conclusion. -/
theorem exists_factorial_coefficient_lt_one (a : ℝ) :
    ∃ n : ℕ, 0 < n ∧ a ^ n / (n.factorial : ℝ) < 1 := by
  have hLimit : Tendsto (fun n : ℕ => a ^ n / (n.factorial : ℝ)) atTop (𝓝 0) :=
    (Real.summable_pow_div_factorial a).tendsto_atTop_zero
  have hSmall : ∀ᶠ n : ℕ in atTop, a ^ n / (n.factorial : ℝ) < 1 :=
    hLimit.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨n, hn⟩ := eventually_atTop.1 hSmall
  exact ⟨n + 1, Nat.succ_pos n, hn (n + 1) (Nat.le_succ n)⟩

section Metric

variable {M : Type*} [MetricSpace M] [Nonempty M] [CompleteSpace M]

/-- Banach's theorem for an iterate yields a unique fixed point of the original
map. No continuity assumption on the original map is required. -/
theorem exists_unique_of_contracting_iterate
    (Φ : M → M) (n : ℕ) {c : ℝ≥0} (hc : ContractingWith c (Φ^[n])) :
    ∃! X, Φ X = X := by
  refine ⟨ContractingWith.fixedPoint (Φ^[n]) hc,
    hc.isFixedPt_fixedPoint_iterate, ?_⟩
  intro Y hY
  exact hc.fixedPoint_unique ((show IsFixedPt Φ Y from hY).iterate n)

end Metric

section Normed

variable {S : Type*} [NormedAddCommGroup S]

/-- Derive the factorial iterate estimate from a time-dependent distance
profile. Its value at the final time is the squared carrier norm. Its initial
iterate is bounded by that norm throughout the interval. -/
theorem iterate_sq_estimate_of_volterra_profile
    (Φ : S → S) (D : S → S → ℝ → ℝ) {T K : ℝ}
    (hK : 0 ≤ K)
    (hContinuous : ∀ X Y, ContinuousOn (D X Y) (Icc 0 T))
    (hDominated : ∀ X Y t, t ∈ Icc 0 T → D X Y t ≤ ‖X - Y‖ ^ 2)
    (hTerminal : ∀ X Y, D X Y T = ‖X - Y‖ ^ 2)
    (hVolterra : ∀ X Y t, t ∈ Icc 0 T →
      D (Φ X) (Φ Y) t ≤ K * ∫ s in (0 : ℝ)..t, D X Y s)
    (hT : 0 ≤ T) (n : ℕ) (X Y : S) :
    ‖(Φ^[n]) X - (Φ^[n]) Y‖ ^ 2 ≤
      (K * T) ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2 := by
  have hBound := factorial_volterra_bound
    (fun n t => D ((Φ^[n]) X) ((Φ^[n]) Y) t) hK
    (fun n => hContinuous _ _)
    (by simpa using hDominated X Y)
    (by
      intro n t ht
      simpa only [Function.iterate_succ_apply'] using
        hVolterra ((Φ^[n]) X) ((Φ^[n]) Y) t ht)
    n T (show T ∈ Icc (0 : ℝ) T from ⟨hT, le_rfl⟩)
  simpa only [hTerminal, mul_pow] using hBound

/-- A factorial estimate produces a contracting iterate of the actual map.
The contraction constant is the square root of the factorial coefficient. -/
theorem exists_contracting_iterate_of_factorial_estimate
    (Φ : S → S) {a : ℝ} (ha : 0 ≤ a)
    (hEstimate : ∀ n X Y,
      ‖(Φ^[n]) X - (Φ^[n]) Y‖ ^ 2 ≤
        a ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ≥0, ContractingWith c (Φ^[n]) := by
  obtain ⟨n, hn, hSmall⟩ := exists_factorial_coefficient_lt_one a
  have hNonneg : 0 ≤ a ^ n / (n.factorial : ℝ) := by positivity
  exact ⟨n, hn, ⟨Real.sqrt (a ^ n / (n.factorial : ℝ)), Real.sqrt_nonneg _⟩,
    contracting_of_sq_estimate (Φ^[n]) hNonneg hSmall (hEstimate n)⟩

/-- Global-in-horizon fixed-point theorem from the factorial estimate.
Completeness is required for the chosen carrier, and the norm is its actual
norm. The coefficient `a` may be arbitrarily large. -/
theorem exists_unique_of_factorial_sq_estimate [CompleteSpace S]
    (Φ : S → S) {a : ℝ} (ha : 0 ≤ a)
    (hEstimate : ∀ n X Y,
      ‖(Φ^[n]) X - (Φ^[n]) Y‖ ^ 2 ≤
        a ^ n / (n.factorial : ℝ) * ‖X - Y‖ ^ 2) :
    ∃! X, Φ X = X := by
  obtain ⟨n, _, c, hc⟩ :=
    exists_contracting_iterate_of_factorial_estimate Φ ha hEstimate
  exact exists_unique_of_contracting_iterate Φ n hc

/-- A finite-horizon continuous Volterra profile yields a unique fixed point
without subdivision of the time interval. This is a generic deterministic
engine; the concrete stochastic integral maps must supply its profile premises. -/
theorem exists_unique_of_volterra_profile [CompleteSpace S]
    (Φ : S → S) (D : S → S → ℝ → ℝ) {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hContinuous : ∀ X Y, ContinuousOn (D X Y) (Icc 0 T))
    (hDominated : ∀ X Y t, t ∈ Icc 0 T → D X Y t ≤ ‖X - Y‖ ^ 2)
    (hTerminal : ∀ X Y, D X Y T = ‖X - Y‖ ^ 2)
    (hVolterra : ∀ X Y t, t ∈ Icc 0 T →
      D (Φ X) (Φ Y) t ≤ K * ∫ s in (0 : ℝ)..t, D X Y s) :
    ∃! X, Φ X = X := by
  apply exists_unique_of_factorial_sq_estimate Φ (mul_nonneg hK hT)
  intro n X Y
  exact iterate_sq_estimate_of_volterra_profile Φ D hK hContinuous hDominated
    hTerminal hVolterra hT n X Y

end Normed

end Ripple.Stochastic.StrongSDE

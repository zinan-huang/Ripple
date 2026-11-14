-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRisingFactorial.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

/-!
# The finite-product algebra used by the early-mark moment

This is the scalar identity in PHASE3 P5. It contains no probability
producer hypothesis and does not by itself assert the two-period moment
bound. All products are finite, including order zero.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRisingFactorial

def risingFactorial (a : ℕ) (v : ℝ) : ℝ :=
  ∏ k ∈ Finset.range a, (v + (k : ℝ))

@[simp] theorem risingFactorial_zero (v : ℝ) :
    risingFactorial 0 v = 1 := by simp [risingFactorial]

theorem risingFactorial_succ (a : ℕ) (v : ℝ) :
    risingFactorial (a + 1) v = risingFactorial a v * (v + (a : ℝ)) := by
  simp only [risingFactorial, Finset.prod_range_succ]

theorem risingFactorial_nonneg (a : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ risingFactorial a v :=
  Finset.prod_nonneg (fun _ _ => by positivity)

theorem risingFactorial_shift (a : ℕ) (v : ℝ) :
    v * risingFactorial a (v + 1) = (v + (a : ℝ)) * risingFactorial a v := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        v * risingFactorial (a + 1) (v + 1) =
            (v * risingFactorial a (v + 1)) * (v + (a : ℝ) + 1) := by
          rw [risingFactorial_succ]
          ring
        _ = ((v + (a : ℝ)) * risingFactorial a v) * (v + (a : ℝ) + 1) := by rw [ih]
        _ = (v + ((a + 1 : ℕ) : ℝ)) * risingFactorial (a + 1) v := by
          rw [risingFactorial_succ]
          push_cast
          ring

theorem risingFactorial_increment (a : ℕ) (v : ℝ) (hv : 0 < v) :
    risingFactorial a (v + 1) - risingFactorial a v =
      (a : ℝ) * risingFactorial a v / v := by
  apply (eq_div_iff (ne_of_gt hv)).2
  have h := risingFactorial_shift a v
  nlinarith

theorem risingFactorial_lower (a : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    v ^ a ≤ risingFactorial a v := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ, risingFactorial_succ]
      exact mul_le_mul ih (by have hnat : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith)
        hv (risingFactorial_nonneg a v hv)

theorem risingFactorial_upper (a : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    risingFactorial a v ≤ (v + (a : ℝ)) ^ a := by
  calc
    risingFactorial a v ≤ ∏ k ∈ Finset.range a, (v + (a : ℝ)) := by
      apply Finset.prod_le_prod
      · intro k _
        positivity
      · intro k hk
        have hka : k ≤ a := (Finset.mem_range.mp hk).le
        have hkaR : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast hka
        linarith
    _ = (v + (a : ℝ)) ^ a := by simp

theorem risingFactorial_initial_bound (a : ℕ) (v : ℝ)
    (hv : 0 ≤ v) (ha : v ≤ 2 * (a : ℝ)) :
    risingFactorial a v ≤ (3 * (a : ℝ)) ^ a := by
  apply (risingFactorial_upper a v hv).trans
  exact pow_le_pow_left₀ (by positivity : 0 ≤ v + (a : ℝ)) (by linarith) a

theorem risingFactorial_mono (a : ℕ) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    risingFactorial a v ≤ risingFactorial a w := by
  apply Finset.prod_le_prod
  · intro k _
    positivity
  · intro k _
    linarith

/-- The exact Bernoulli increment formula; this is the algebra required
before pulling the predictable coefficient out of conditional expectation. -/
theorem risingFactorial_bernoulli_increment (a : ℕ) (v I : ℝ)
    (hv : 0 < v) (hI : I = 0 ∨ I = 1) :
    risingFactorial a (v + I) =
      risingFactorial a v + ((a : ℝ) * risingFactorial a v / v) * I := by
  rcases hI with rfl | rfl
  · simp
  · have h := risingFactorial_increment a v hv
    linarith

/-- A frozen or unchanged step also satisfies the one-step upper bound. -/
theorem risingFactorial_step_le (a : ℕ) (v w I : ℝ)
    (hv : 0 < v) (hw : 0 ≤ w) (hI : I = 0 ∨ I = 1) (hstep : w ≤ v + I) :
    risingFactorial a w ≤
      risingFactorial a v + ((a : ℝ) * risingFactorial a v / v) * I :=
  (risingFactorial_mono a hw hstep).trans_eq
    (risingFactorial_bernoulli_increment a v I hv hI)

/-- If propagation has probability at most k*v, the linearized expected
increment is at most a*k times the current rising factorial. -/
theorem risingFactorial_rate_bound (a : ℕ) (v p k : ℝ)
    (hv : 0 < v) (hp : p ≤ k * v) :
    risingFactorial a v + ((a : ℝ) * risingFactorial a v / v) * p ≤
      (1 + (a : ℝ) * k) * risingFactorial a v := by
  have hcoef : 0 ≤ (a : ℝ) * risingFactorial a v / v :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg a) (risingFactorial_nonneg a v hv.le)) hv.le
  have h := mul_le_mul_of_nonneg_left hp hcoef
  have hid : ((a : ℝ) * risingFactorial a v / v) * (k * v) =
      (a : ℝ) * k * risingFactorial a v := by
    field_simp [ne_of_gt hv]
    <;> ring
  rw [hid] at h
  nlinarith

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRisingFactorial

end

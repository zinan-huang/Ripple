/-
  Ripple.Core.BoundedTime — Bounded-Time Computability

  Defines time modulus and bounded-time complexity classes
  for bounded PIVPs.

  Key definition (from [BAC] Def 2.4):
    A bounded PIVP computes α with time modulus μ : ℕ → ℝ≥0 if
      |x(t) - α| < e^{-r}   whenever  t > μ(r).

  The time complexity of the computation is the asymptotic growth of μ(r).

  Hierarchy (from [BAC] §5):
    Floor 0 (real-time):  μ(r) = Θ(r)        — e.g., e, π
    Floor 1:              μ(r) = Θ(r²)       — quadratic
    Floor n:              μ(r) = Θ(rⁿ)       — degree-n polynomial
    Lambert W:            μ(r) = Θ(r log r)
    Tower k:              μ(r) = Θ(exp^(k+1)(r))
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Ripple

/-- A time modulus is a function μ : ℕ → ℝ such that μ(r) bounds the time
  needed to achieve r bits of precision. -/
def TimeModulus := ℕ → ℝ

/-- A bounded PIVP computes α with time modulus μ if:
  for all r, for all t > μ(r), |x_output(t) - α| < e^{-r}. -/
structure BoundedTimeComputable (d : ℕ) (α : ℝ) where
  /-- The underlying PIVP. -/
  pivp : PIVP d
  /-- The solution to the PIVP. -/
  sol : PIVP.Solution pivp
  /-- The time modulus. -/
  modulus : TimeModulus
  /-- The PIVP is bounded. -/
  bounded : pivp.IsBounded sol.trajectory
  /-- Convergence with the given time modulus. -/
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

/-- A real number is CRN-computable if it is computable by some bounded PIVP. -/
def IsCRNComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ _ : BoundedTimeComputable d α, True

/-- A real number is real-time CRN-computable (floor 0) if it has
  a linear time modulus: μ(r) = O(r), i.e., μ(r) ≤ C(r+1) for some C > 0. -/
def IsRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1)

/-- A real number is polynomial-time CRN-computable (floor n) if it has
  time modulus μ(r) = O(r^n). -/
def IsPolyTimeComputable (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) ^ n

/-- Addition closure for real-time computable numbers (from [RTCRN2]).
  Given PIVPs computing α and β, the sum is computed by tracking x₁(t)+x₂(t);
  convergence uses triangle inequality + 2e^{-(r+1)} ≤ e^{-r} (since 2 ≤ e). -/
theorem realtime_field_add {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α + β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  refine ⟨1, {
    pivp := { field := fun _ => ![0],
              init := ![btc₁.sol.trajectory 0 btc₁.pivp.output +
                        btc₂.sol.trajectory 0 btc₂.pivp.output],
              output := 0 }
    sol := {
      trajectory := fun t => ![btc₁.sol.trajectory t btc₁.pivp.output +
                                btc₂.sol.trajectory t btc₂.pivp.output]
      init_cond := by ext i; fin_cases i; simp []
      is_solution := trivial }
    modulus := fun r => max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
    bounded := ?_
    convergence := ?_ }, 2 * max C₁ C₂, by positivity, ?_⟩
  · -- Bounded: ‖![x₁(t)+x₂(t)]‖ ≤ M₁+M₂
    obtain ⟨M₁, hM₁, hb₁⟩ := btc₁.bounded
    obtain ⟨M₂, hM₂, hb₂⟩ := btc₂.bounded
    refine ⟨M₁ + M₂, by linarith, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro i; fin_cases i
    change ‖btc₁.sol.trajectory t btc₁.pivp.output +
           btc₂.sol.trajectory t btc₂.pivp.output‖ ≤ M₁ + M₂
    rw [Real.norm_eq_abs]
    have h₁ : |btc₁.sol.trajectory t btc₁.pivp.output| ≤ M₁ := by
      have hcomp := norm_le_pi_norm (btc₁.sol.trajectory t) btc₁.pivp.output
      rw [Real.norm_eq_abs] at hcomp; linarith [hb₁ t ht]
    have h₂ : |btc₂.sol.trajectory t btc₂.pivp.output| ≤ M₂ := by
      have hcomp := norm_le_pi_norm (btc₂.sol.trajectory t) btc₂.pivp.output
      rw [Real.norm_eq_abs] at hcomp; linarith [hb₂ t ht]
    linarith [abs_add_le (btc₁.sol.trajectory t btc₁.pivp.output)
                         (btc₂.sol.trajectory t btc₂.pivp.output)]
  · -- Convergence: triangle inequality + 2e^{-(r+1)} ≤ e^{-r}
    intro r t ht
    simp only [Matrix.cons_val_zero]
    have ht₁ : t > btc₁.modulus (r + 1) := lt_of_le_of_lt (le_max_left _ _) ht
    have ht₂ : t > btc₂.modulus (r + 1) := lt_of_le_of_lt (le_max_right _ _) ht
    have hc₁ := btc₁.convergence (r + 1) t ht₁
    have hc₂ := btc₂.convergence (r + 1) t ht₂
    have htri : |btc₁.sol.trajectory t btc₁.pivp.output +
        btc₂.sol.trajectory t btc₂.pivp.output - (α + β)|
      ≤ |btc₁.sol.trajectory t btc₁.pivp.output - α| +
        |btc₂.sol.trajectory t btc₂.pivp.output - β| := by
      have : btc₁.sol.trajectory t btc₁.pivp.output +
          btc₂.sol.trajectory t btc₂.pivp.output - (α + β) =
          (btc₁.sol.trajectory t btc₁.pivp.output - α) +
          (btc₂.sol.trajectory t btc₂.pivp.output - β) := by ring
      rw [this]; exact abs_add_le _ _
    have hexp : 2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
      have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by push_cast; ring
      rw [hcast, Real.exp_add]
      have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
      calc 2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
          = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by ring
        _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith
  · -- Linear modulus: max(μ₁(r+1), μ₂(r+1)) ≤ 2·max(C₁,C₂)·(r+1)
    intro r
    have h₁ : btc₁.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
      calc btc₁.modulus (r + 1)
          ≤ C₁ * (↑(r + 1) + 1) := hmod₁ (r + 1)
        _ = C₁ * (↑r + 2) := by push_cast; ring
        _ ≤ max C₁ C₂ * (↑r + 2) :=
            mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
              (by positivity)
    have h₂ : btc₂.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
      calc btc₂.modulus (r + 1)
          ≤ C₂ * (↑(r + 1) + 1) := hmod₂ (r + 1)
        _ = C₂ * (↑r + 2) := by push_cast; ring
        _ ≤ max C₁ C₂ * (↑r + 2) :=
            mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
              (by positivity)
    calc max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
        ≤ max C₁ C₂ * (↑r + 2) := max_le h₁ h₂
      _ ≤ max C₁ C₂ * (2 * (↑r + 1)) := by
          apply mul_le_mul_of_nonneg_left
          · have : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r; linarith
          · exact le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂))
      _ = 2 * max C₁ C₂ * (↑r + 1) := by ring

/-- Multiplication closure for real-time computable numbers (from [RTCRN2]).
  The product x₁(t)·x₂(t) converges to αβ; convergence uses the three-term
  decomposition x₁x₂-αβ = x₁(x₂-β) + (x₁-α)x₂ - (x₁-α)(x₂-β) with a
  modulus shift by K = ⌈M₁+M₂+1⌉ to absorb the constant factor. -/
theorem realtime_field_mul {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α * β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  obtain ⟨M₁, hM₁, hb₁⟩ := btc₁.bounded
  obtain ⟨M₂, hM₂, hb₂⟩ := btc₂.bounded
  -- K : ℕ with e^K > M₁+M₂+1 (via 1+x ≤ e^x)
  set K := Nat.ceil (M₁ + M₂ + 1) with hK_def
  have hK : M₁ + M₂ + 1 ≤ (↑K : ℝ) := Nat.le_ceil _
  have hexp_K : M₁ + M₂ + 1 < Real.exp (↑K : ℝ) :=
    calc M₁ + M₂ + 1 ≤ (↑K : ℝ) := hK
      _ < (↑K : ℝ) + 1 := by linarith
      _ ≤ Real.exp (↑K : ℝ) := Real.add_one_le_exp _
  -- Component bound helpers
  have hx₁_bound : ∀ t, 0 ≤ t → |btc₁.sol.trajectory t btc₁.pivp.output| ≤ M₁ := by
    intro t ht
    have := norm_le_pi_norm (btc₁.sol.trajectory t) btc₁.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₁ t ht]
  have hx₂_bound : ∀ t, 0 ≤ t → |btc₂.sol.trajectory t btc₂.pivp.output| ≤ M₂ := by
    intro t ht
    have := norm_le_pi_norm (btc₂.sol.trajectory t) btc₂.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₂ t ht]
  -- Construct the multiplication PIVP
  refine ⟨1, {
    pivp := { field := fun _ => ![0],
              init := ![btc₁.sol.trajectory 0 btc₁.pivp.output *
                        btc₂.sol.trajectory 0 btc₂.pivp.output],
              output := 0 }
    sol := {
      trajectory := fun t => ![btc₁.sol.trajectory t btc₁.pivp.output *
                                btc₂.sol.trajectory t btc₂.pivp.output]
      init_cond := by ext i; fin_cases i; simp []
      is_solution := trivial }
    modulus := fun r => max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
    bounded := ?_
    convergence := ?_ }, max C₁ C₂ * (↑K + 1), by positivity, ?_⟩
  · -- Bounded: |x₁(t)*x₂(t)| ≤ M₁*M₂
    refine ⟨M₁ * M₂, by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i; fin_cases i
    change ‖btc₁.sol.trajectory t btc₁.pivp.output *
           btc₂.sol.trajectory t btc₂.pivp.output‖ ≤ M₁ * M₂
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hx₁_bound t ht) (hx₂_bound t ht) (abs_nonneg _) (le_of_lt hM₁)
  · -- Convergence: three-term decomposition + modulus shift by K
    intro r t ht
    simp only [Matrix.cons_val_zero]
    have ht_pos : 0 < t := lt_of_le_of_lt (le_max_left 0 _) ht
    have ht₁ : t > btc₁.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 0 _)) ht
    have ht₂ : t > btc₂.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right 0 _)) ht
    -- Abbreviations
    set x₁ := btc₁.sol.trajectory t btc₁.pivp.output
    set x₂ := btc₂.sol.trajectory t btc₂.pivp.output
    set e_rK := Real.exp (-(↑(r + K) : ℝ))
    have hc₁ : |x₁ - α| < e_rK := btc₁.convergence (r + K) t ht₁
    have hc₂ : |x₂ - β| < e_rK := btc₂.convergence (r + K) t ht₂
    have hx₁ : |x₁| ≤ M₁ := hx₁_bound t (le_of_lt ht_pos)
    have hx₂ : |x₂| ≤ M₂ := hx₂_bound t (le_of_lt ht_pos)
    -- Triangle: x₁x₂-αβ = x₁(x₂-β)+(x₁-α)x₂-(x₁-α)(x₂-β)
    have htri : |x₁ * x₂ - α * β| ≤
        |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
      have heq : x₁ * x₂ - α * β =
        (x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β)) := by ring
      calc |x₁ * x₂ - α * β|
          = |(x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β))| := by rw [heq]
        _ ≤ |x₁ * (x₂ - β) + (x₁ - α) * x₂| + |-(x₁ - α) * (x₂ - β)| :=
            abs_add_le _ _
        _ ≤ (|x₁ * (x₂ - β)| + |(x₁ - α) * x₂|) + |-(x₁ - α) * (x₂ - β)| := by
            linarith [abs_add_le (x₁ * (x₂ - β)) ((x₁ - α) * x₂)]
        _ = |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
            simp only [abs_mul, neg_mul, abs_neg]
    -- Bound each term
    have hb1 : |x₁| * |x₂ - β| ≤ M₁ * e_rK :=
      mul_le_mul hx₁ (le_of_lt hc₂) (abs_nonneg _) (le_of_lt hM₁)
    have hb2 : |x₁ - α| * |x₂| ≤ e_rK * M₂ :=
      mul_le_mul (le_of_lt hc₁) hx₂ (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    have h_le_1 : e_rK ≤ 1 := by
      calc e_rK ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
        _ = 1 := Real.exp_zero
    have hb3 : |x₁ - α| * |x₂ - β| ≤ e_rK := by
      calc |x₁ - α| * |x₂ - β|
          ≤ e_rK * e_rK :=
            mul_le_mul (le_of_lt hc₁) (le_of_lt hc₂) (abs_nonneg _)
              (le_of_lt (Real.exp_pos _))
        _ ≤ 1 * e_rK :=
            mul_le_mul_of_nonneg_right h_le_1 (le_of_lt (Real.exp_pos _))
        _ = e_rK := one_mul _
    -- Sum: ≤ (M₁+M₂+1)·e_rK
    have hsum : |x₁ * x₂ - α * β| ≤ (M₁ + M₂ + 1) * e_rK := by linarith
    -- Rate: (M₁+M₂+1)·e_rK < exp(-r) via e^K > M₁+M₂+1
    have hrate : (M₁ + M₂ + 1) * e_rK < Real.exp (-(↑r : ℝ)) := by
      have hfactor : e_rK = Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ)) := by
        change Real.exp (-(↑(r + K) : ℝ)) = _
        rw [show (-(↑(r + K) : ℝ)) = -(↑r : ℝ) + (-(↑K : ℝ)) from by push_cast; ring,
            Real.exp_add]
      rw [hfactor, show (M₁ + M₂ + 1) * (Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ))) =
        Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ))) from by ring]
      have hfrac : (M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)) < 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
        exact hexp_K
      calc Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)))
          < Real.exp (-(↑r : ℝ)) * 1 :=
            mul_lt_mul_of_pos_left hfrac (Real.exp_pos _)
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith
  · -- Linear modulus: max 0 (max(μ₁(r+K),μ₂(r+K))) ≤ max(C₁,C₂)·(K+1)·(r+1)
    intro r
    have hcast : (↑(r + K) : ℝ) + 1 = ↑r + ↑K + 1 := by push_cast; ring
    have h₁ : btc₁.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
      have := hmod₁ (r + K); rw [hcast] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity))
    have h₂ : btc₂.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
      have := hmod₂ (r + K); rw [hcast] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity))
    have h_factor : (↑r : ℝ) + ↑K + 1 ≤ (↑K + 1) * (↑r + 1) := by
      have : (↑K + 1) * (↑r + 1) = ↑K * ↑r + ↑K + ↑r + 1 := by ring
      linarith [show (0 : ℝ) ≤ ↑K * ↑r from by positivity]
    calc max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
        ≤ max C₁ C₂ * (↑r + ↑K + 1) := max_le (by positivity) (max_le h₁ h₂)
      _ ≤ max C₁ C₂ * ((↑K + 1) * (↑r + 1)) :=
          mul_le_mul_of_nonneg_left h_factor
            (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂)))
      _ = max C₁ C₂ * (↑K + 1) * (↑r + 1) := by ring

/-- Any integer (or rational with integer PIVP embedding) is real-time computable.
  Proof: constant PIVP x' = 0, x(0) = c has solution x(t) = c,
  so |x(t) - c| = 0 < e^{-r} for all t.
  Note: our PIVP definition allows real ICs; in the full theory,
  ICs must be rational ([RTCRN2] Thm 3.2.10). -/
theorem realtime_const (c : ℝ) : IsRealTimeComputable c := by
  refine ⟨1, ?_, ?_⟩
  · exact {
      pivp := { field := fun _ => ![0], init := ![c], output := 0 }
      sol := {
        trajectory := fun _ => ![c]
        init_cond := by ext i; fin_cases i; simp
        is_solution := trivial
      }
      modulus := fun _ => 0
      bounded := ⟨|c| + 1, by positivity, fun t _ => by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i; fin_cases i
        change ‖c‖ ≤ |c| + 1
        rw [Real.norm_eq_abs]
        linarith⟩
      convergence := by
        intro r t _
        simp only [Matrix.cons_val_zero, sub_self, abs_zero]
        exact Real.exp_pos _
    }
  · exact ⟨1, one_pos, fun _ => by positivity⟩

/-- Negation closure: derived from mul and const. -α = (-1) * α. -/
theorem realtime_field_neg {α : ℝ} (ha : IsRealTimeComputable α) :
    IsRealTimeComputable (-α) := by
  have : -α = (-1) * α := by ring
  rw [this]
  exact realtime_field_mul (realtime_const (-1)) ha

/-- Reciprocal closure for real-time computable numbers.
  When α ≠ 0 and α ∈ ℝ_RTCRN, then α⁻¹ ∈ ℝ_RTCRN.
  Note: uses constant trajectory (realtime_const); when is_solution is
  properly connected to ODE solutions, this will need the z' = z(1-xz)
  construction from [RTCRN2]. -/
theorem realtime_field_inv {α : ℝ} (_hα : α ≠ 0)
    (_ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ :=
  realtime_const α⁻¹

/-- Division closure: α / β = α · β⁻¹. -/
theorem realtime_field_div {α β : ℝ} (hβ : β ≠ 0)
    (ha : IsRealTimeComputable α) (hb : IsRealTimeComputable β) :
    IsRealTimeComputable (α / β) := by
  rw [div_eq_mul_inv]
  exact realtime_field_mul ha (realtime_field_inv hβ hb)

/-- Subtraction closure: derived from add and neg. -/
theorem realtime_field_sub {α β : ℝ} (ha : IsRealTimeComputable α)
    (hb : IsRealTimeComputable β) : IsRealTimeComputable (α - β) := by
  have : α - β = α + (-β) := sub_eq_add_neg α β
  rw [this]
  exact realtime_field_add ha (realtime_field_neg hb)

end Ripple

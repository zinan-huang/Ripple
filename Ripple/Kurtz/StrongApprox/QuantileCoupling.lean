/-
  Ripple.Kurtz.StrongApprox.QuantileCoupling — discrete quantile coupling with a continuous law

  For a cumulative distribution function `F : ℕ → ℝ` of a law on `ℕ` (monotone, eventually
  reaching every level `u < 1`) the quantile `natQuantile F u = min {k | u ≤ F k}`.  Composed with
  the standard normal cdf `Φ` this is the quantile coupling `Q(z) = natQuantile F (Φ z)`; the
  characterisation `Q(z) = k ⟺ T(k+1) ≤ 1 − Φ(z) < T(k)` with the tail `T k = 1 − F (k−1)`
  (`T 0 = 1`) is proved here in the abstract form (any `u ∈ (0,1)`), together with the trivial
  bounds `natQuantile F u ≤ m` when `F m = 1`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

/-- Least `k` with `u ≤ F k` (`0` if there is none). -/
noncomputable def natQuantile (F : ℕ → ℝ) (u : ℝ) : ℕ := sInf {k | u ≤ F k}

/-- Upper tail attached to a cdf: `tail F 0 = 1`, `tail F (k+1) = 1 − F k`. -/
def tail (F : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => 1 - F k

@[simp] theorem tail_zero (F : ℕ → ℝ) : tail F 0 = 1 := rfl
@[simp] theorem tail_succ (F : ℕ → ℝ) (k : ℕ) : tail F (k + 1) = 1 - F k := rfl

theorem natQuantile_le_of_le {F : ℕ → ℝ} {u : ℝ} {k : ℕ} (h : u ≤ F k) :
    natQuantile F u ≤ k :=
  Nat.sInf_le h

theorem le_natQuantile_of_lt {F : ℕ → ℝ} {u : ℝ} (hex : ∃ k, u ≤ F k) {k : ℕ}
    (h : ∀ j < k, F j < u) : k ≤ natQuantile F u := by
  by_contra hlt
  push Not at hlt
  have hmem : u ≤ F (natQuantile F u) := Nat.sInf_mem hex
  exact absurd hmem (not_le.mpr (h _ hlt))

/-- `u ≤ F (natQuantile F u)` as soon as some level reaches `u`. -/
theorem le_apply_natQuantile {F : ℕ → ℝ} {u : ℝ} (hex : ∃ k, u ≤ F k) :
    u ≤ F (natQuantile F u) :=
  Nat.sInf_mem hex

/-- Characterisation of the quantile through the tail: for monotone `F` and some level reaching
`u`, `natQuantile F u = k ↔ tail F (k+1) ≤ 1 − u ∧ 1 − u < tail F k`. -/
theorem natQuantile_eq_iff {F : ℕ → ℝ} (hF : Monotone F) {u : ℝ} (hex : ∃ k, u ≤ F k)
    (hu : 0 < u) (k : ℕ) :
    natQuantile F u = k ↔ tail F (k + 1) ≤ 1 - u ∧ 1 - u < tail F k := by
  constructor
  · intro hk
    have h1 : u ≤ F k := hk ▸ le_apply_natQuantile hex
    refine ⟨by simp only [tail_succ]; linarith, ?_⟩
    cases k with
    | zero => simp [hu]
    | succ j =>
      simp only [tail_succ]
      have : F j < u := by
        by_contra hge
        push Not at hge
        have := natQuantile_le_of_le hge
        omega
      linarith
  · rintro ⟨h1, h2⟩
    simp only [tail_succ] at h1
    have h1' : u ≤ F k := by linarith
    apply le_antisymm (natQuantile_le_of_le h1')
    apply le_natQuantile_of_lt hex
    intro j hj
    cases k with
    | zero => omega
    | succ i =>
      simp only [tail_succ] at h2
      have hji : j ≤ i := by omega
      have := hF hji
      linarith

/-- If `F m = 1` and `u ≤ 1`, the quantile is at most `m`. -/
theorem natQuantile_le_of_eq_one {F : ℕ → ℝ} {u : ℝ} {m : ℕ} (hm : F m = 1) (hu : u ≤ 1) :
    natQuantile F u ≤ m :=
  natQuantile_le_of_le (by rw [hm]; exact hu)

/-- The trivial bound on the quantile-coupling error, used for small parent counts:
`|q − m/2 − (√m/2) z| ≤ (3/4) m + z²/4` whenever `0 ≤ q ≤ m`. -/
theorem abs_error_le_of_le {q m z : ℝ} (hq0 : 0 ≤ q) (hqm : q ≤ m) :
    |q - m / 2 - Real.sqrt m / 2 * z| ≤ 3 / 4 * m + z ^ 2 / 4 := by
  have hm0 : 0 ≤ m := hq0.trans hqm
  have hs : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
  have hsz : Real.sqrt m / 2 * |z| ≤ m / 4 + z ^ 2 / 4 := by
    nlinarith [sq_nonneg (Real.sqrt m / 2 - |z| / 2), sq_abs z, Real.sqrt_nonneg m]
  have hzz : Real.sqrt m / 2 * z ≤ Real.sqrt m / 2 * |z| :=
    mul_le_mul_of_nonneg_left (le_abs_self z) (by positivity)
  have hzz' : -(Real.sqrt m / 2 * |z|) ≤ Real.sqrt m / 2 * z := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le z) (by positivity : 0 ≤ Real.sqrt m / 2)
    linarith
  rw [abs_le]
  constructor <;> linarith

end Ripple.Kurtz.StrongApprox

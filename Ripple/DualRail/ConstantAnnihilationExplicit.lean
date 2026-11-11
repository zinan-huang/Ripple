import Ripple.DualRail.ConstantAnnihilationGeneral

/-!
# Constant-rate dual rail with explicit trajectory data


The positive-dimensional result retains the same rational annihilation rate,
trajectory, split initial state, transformed field equation, bound `2 * β`,
and exact tracking identity. The final theorem also retains the existing
all-dimensional boundedness result.
-/

namespace Ripple.DualRail

/-- The split initial state has exactly the prescribed rail differences.
This exports the local `h_init_diff` calculation from
`constantAnnihilation_bounded_pos`. -/
theorem constantAnnihilation_split_initial_difference
    (n : ℕ) (y₀ : Fin n → ℚ) (u : ℝ → Fin (2 * n) → ℝ)
    (h_init : u 0 = (fun K =>
      if K.val % 2 = 0 then
        max ((y₀ ⟨K.val / 2, by
          have hK := K.isLt
          omega⟩ : ℝ)) 0
      else
        max (-(y₀ ⟨K.val / 2, by
          have hK := K.isLt
          omega⟩ : ℝ)) 0)) :
    ∀ i : Fin n,
      u 0 ⟨2 * i.val, by have := i.isLt; omega⟩ -
        u 0 ⟨2 * i.val + 1, by have := i.isLt; omega⟩ =
          (y₀ i : ℝ) := by
  classical
  intro i
  simp only [h_init]
  have hev : (2 * i.val) % 2 = 0 := by omega
  have hodd : (2 * i.val + 1) % 2 ≠ 0 := by omega
  have hdiv1 : (2 * i.val) / 2 = i.val := by omega
  have hdiv2 : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [hev, hodd, hdiv1, hdiv2, ↓reduceIte]
  have heq1 : (⟨i.val, by omega⟩ : Fin n) = i := Fin.eta i _
  rw [heq1]
  by_cases h : 0 ≤ (y₀ i : ℝ)
  · rw [max_eq_left h, max_eq_right (by linarith : -(y₀ i : ℝ) ≤ 0)]
    ring
  · replace h : (y₀ i : ℝ) < 0 := lt_of_not_ge h
    rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(y₀ i : ℝ))]
    ring

/-- Constant-rate dual rail, retaining its rate, split initial state, ODE,
the explicit `2 * β` bound, and exact tracking for one shared trajectory. -/
theorem constantAnnihilation_bounded_pos_explicit
    (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ)
    (hBd : OriginalBounded p y₀ ySol β) :
    ∃ k : ℚ, 0 < k ∧
      ∃ u : ℝ → Fin (2 * n) → ℝ,
        u 0 = (fun K =>
          if K.val % 2 = 0 then
            max ((y₀ ⟨K.val / 2, by
              have hK := K.isLt
              omega⟩ : ℝ)) 0
          else
            max (-(y₀ ⟨K.val / 2, by
              have hK := K.isLt
              omega⟩ : ℝ)) 0) ∧
        (∀ t ≥ (0 : ℝ),
          HasDerivAt (fun s => u s)
            ((constantAnnihilationDualRail n p k).evalField (u t)) t) ∧
        (∀ t ≥ (0 : ℝ), ∀ K,
          0 ≤ u t K ∧ u t K ≤ 2 * β) ∧
        (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
          u t ⟨2 * i.val, by have := i.isLt; omega⟩ -
            u t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ =
              ySol t i) := by
  obtain ⟨k, hk_pos, hk_lt⟩ := posK_witness n p β hBd.1
  obtain ⟨u, h_init, h_deriv⟩ :=
    posK_picard n p y₀ ySol β hBd k hk_pos hk_lt
  have h_box : ∀ t ≥ (0 : ℝ), ∀ K,
      0 ≤ u t K ∧ u t K ≤ 2 * β :=
    posK_boxBound n p y₀ ySol β hBd k hk_pos hk_lt u h_init h_deriv
  have h_init_diff : ∀ i : Fin n,
      u 0 ⟨2 * i.val, by have := i.isLt; omega⟩ -
        u 0 ⟨2 * i.val + 1, by have := i.isLt; omega⟩ =
          (y₀ i : ℝ) :=
    constantAnnihilation_split_initial_difference n y₀ u h_init
  exact ⟨k, hk_pos, u, h_init, h_deriv, h_box,
    posK_identity n p y₀ ySol β hBd k hk_pos u h_deriv h_init_diff h_box⟩

/-- The row-8 strengthened statement, including the existing zero-dimensional
case through `ConstantAnnihilationBounded`. -/
theorem constantAnnihilation_bounded_explicit :
    ConstantAnnihilationBounded ∧
      ∀ (n : ℕ) [NeZero n]
        (p : Fin n → MvPolynomial (Fin n) ℚ)
        (y₀ : Fin n → ℚ)
        (ySol : ℝ → Fin n → ℝ)
        (β : ℝ),
        OriginalBounded p y₀ ySol β →
          ∃ k : ℚ, 0 < k ∧
            ∃ u : ℝ → Fin (2 * n) → ℝ,
              u 0 = (fun K =>
                if K.val % 2 = 0 then
                  max ((y₀ ⟨K.val / 2, by
                    have hK := K.isLt
                    omega⟩ : ℝ)) 0
                else
                  max (-(y₀ ⟨K.val / 2, by
                    have hK := K.isLt
                    omega⟩ : ℝ)) 0) ∧
              (∀ t ≥ (0 : ℝ),
                HasDerivAt (fun s => u s)
                  ((constantAnnihilationDualRail n p k).evalField (u t)) t) ∧
              (∀ t ≥ (0 : ℝ), ∀ K,
                0 ≤ u t K ∧ u t K ≤ 2 * β) ∧
              (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
                u t ⟨2 * i.val, by have := i.isLt; omega⟩ -
                  u t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ =
                    ySol t i) := by
  refine ⟨constantAnnihilation_bounded, ?_⟩
  intro n hn p y₀ ySol β hBd
  exact constantAnnihilation_bounded_pos_explicit n p y₀ ySol β hBd

end Ripple.DualRail

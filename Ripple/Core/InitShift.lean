/-
  Ripple.Core.InitShift — DNA 25 semantic zero-init reduction

  Formalizes [RTCRN2] Theorem 3 at the semantic `PIVP` / `BoundedTimeComputable`
  level: given a PIVP `y' = p(y)`, `y(0) = y₀` computing `α`, the substitution
  `ẑ(t) := y(t) − y₀` produces a zero-init PIVP `ẑ' = p̂(ẑ)` with
  `p̂(z) := p(z + y₀)`, computing `α − y₀.output`.

  At the semantic level this needs no MvPolynomial bind₁ machinery — it is a
  direct change of variables. (The syntactic `PolyPIVP` variant, which keeps
  integer/rational coefficients explicit, is left for a future step and would
  require `MvPolynomial.aeval_bind₁`.)

  Reference: [RTCRN2] (Huang-Klinge-Lathrop, DNA 25, 2019) Theorem 3, pp. 11-12.
-/

import Ripple.Core.BoundedTime

namespace Ripple

open Filter Topology

/-! ## Semantic PIVP-level shift -/

/-- DNA 25 / [RTCRN2] Theorem 3 semantic zero-init shift. The new field
`p̂(z) := p(z + y₀)` and the zero init `ẑ(0) = 0` give `ẑ(t) = y(t) − y₀`. -/
noncomputable def PIVP.shiftToZero {d : ℕ} (P : PIVP d) : PIVP d where
  field z := P.field (fun j => z j + P.init j)
  init _ := 0
  output := P.output

@[simp] theorem PIVP.shiftToZero_output {d : ℕ} (P : PIVP d) :
    P.shiftToZero.output = P.output := rfl

@[simp] theorem PIVP.shiftToZero_init {d : ℕ} (P : PIVP d) (j : Fin d) :
    P.shiftToZero.init j = 0 := rfl

theorem PIVP.shiftToZero_field {d : ℕ} (P : PIVP d) (z : Fin d → ℝ) :
    P.shiftToZero.field z = P.field (fun j => z j + P.init j) := rfl

/-- Shifted trajectory: `ẑ(t) := y(t) − y₀` solves the shifted PIVP. -/
noncomputable def PIVP.Solution.shift {d : ℕ} {P : PIVP d}
    (sol : PIVP.Solution P) : PIVP.Solution P.shiftToZero where
  trajectory t := fun j => sol.trajectory t j - P.init j
  init_cond := by
    funext j
    have h : sol.trajectory 0 j = P.init j := congr_fun sol.init_cond j
    simp [PIVP.shiftToZero, h]
  is_solution t ht := by
    -- Target derivative: `P.shiftToZero.field (shifted t)`.
    -- `P.shiftToZero.field (shifted t) = P.field (shifted t + P.init) = P.field (sol t)`
    -- since `(shifted t j) + P.init j = sol.trajectory t j`.
    have h_field_eq :
        P.shiftToZero.field (fun j => sol.trajectory t j - P.init j)
          = P.field (sol.trajectory t) := by
      change P.field (fun j => (sol.trajectory t j - P.init j) + P.init j)
          = P.field (sol.trajectory t)
      congr 1
      funext j
      ring
    rw [h_field_eq]
    -- derivative of `(fun s => sol.trajectory s j - P.init j)` equals derivative
    -- of `sol.trajectory · j` (sub_const). Then use `hasDerivAt_pi`.
    refine hasDerivAt_pi.mpr (fun j => ?_)
    have h_comp : HasDerivAt (fun s => sol.trajectory s j)
        (P.field (sol.trajectory t) j) t :=
      hasDerivAt_pi.mp (sol.is_solution t ht) j
    exact h_comp.sub_const (P.init j)

@[simp] theorem PIVP.Solution.shift_trajectory {d : ℕ} {P : PIVP d}
    (sol : PIVP.Solution P) (t : ℝ) (j : Fin d) :
    sol.shift.trajectory t j = sol.trajectory t j - P.init j := rfl

/-! ## BoundedTimeComputable-level shift -/

/-- Shifted trajectory inherits a uniform norm bound (with an enlarged constant). -/
theorem PIVP.shiftToZero_isBounded {d : ℕ} (P : PIVP d)
    (sol : PIVP.Solution P) (hbd : P.IsBounded sol.trajectory) :
    P.shiftToZero.IsBounded sol.shift.trajectory := by
  obtain ⟨M, hMpos, hM⟩ := hbd
  refine ⟨M + ‖P.init‖ + 1, by positivity, fun t ht => ?_⟩
  have h1 : sol.shift.trajectory t = sol.trajectory t - P.init := by
    funext j
    change sol.trajectory t j - P.init j = sol.trajectory t j - P.init j
    rfl
  rw [h1]
  calc ‖sol.trajectory t - P.init‖
      ≤ ‖sol.trajectory t‖ + ‖P.init‖ := norm_sub_le _ _
    _ ≤ M + ‖P.init‖ := by linarith [hM t ht]
    _ ≤ M + ‖P.init‖ + 1 := by linarith

/-- [RTCRN2] Theorem 3, BTC-level: any `BoundedTimeComputable d α` gives a
zero-init `BoundedTimeComputable d (α − y₀.output)` with the same time modulus.
This is the DNA 25 reduction, semantic layer. The rational shift-back to `α`
requires additive closure (`realtime_field_add` or similar). -/
noncomputable def BoundedTimeComputable.shiftToZero {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    BoundedTimeComputable d (α - btc.pivp.init btc.pivp.output) where
  pivp := btc.pivp.shiftToZero
  sol := btc.sol.shift
  modulus := btc.modulus
  bounded := btc.pivp.shiftToZero_isBounded btc.sol btc.bounded
  convergence := by
    intro r t ht
    -- |ẑ_o(t) − (α − y₀.o)| = |(y_o(t) − y₀.o) − (α − y₀.o)| = |y_o(t) − α|
    have h_eq :
        btc.sol.shift.trajectory t btc.pivp.shiftToZero.output
            - (α - btc.pivp.init btc.pivp.output)
          = btc.sol.trajectory t btc.pivp.output - α := by
      simp [PIVP.Solution.shift_trajectory, PIVP.shiftToZero_output]
    rw [h_eq]
    exact btc.convergence r t ht

@[simp] theorem BoundedTimeComputable.shiftToZero_pivp_init {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) (j : Fin d) :
    (btc.shiftToZero).pivp.init j = 0 := rfl

@[simp] theorem BoundedTimeComputable.shiftToZero_pivp_output {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    (btc.shiftToZero).pivp.output = btc.pivp.output := rfl

/-- The shifted output init is zero (DNA 25 zero-init property). -/
theorem BoundedTimeComputable.shiftToZero_zero_output_init {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    (btc.shiftToZero).pivp.init (btc.shiftToZero).pivp.output = 0 := rfl

end Ripple

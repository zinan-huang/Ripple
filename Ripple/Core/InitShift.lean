/-
  Ripple.Core.InitShift — DNA 25 semantic zero-init reduction

  Formalizes [RTCRN2] Theorem 3 at the semantic `PIVP` / `SemanticBTC`
  level: given a PIVP `y' = p(y)`, `y(0) = y₀` computing `α`, the substitution
  `ẑ(t) := y(t) − y₀` produces a zero-init PIVP `ẑ' = p̂(ẑ)` with
  `p̂(z) := p(z + y₀)`, computing `α − y₀.output`.

  At the semantic level this is a direct change of variables. The syntactic `PolyPIVP`
  variant (`PolyPIVP.shiftToZero`, `CertifiedBoundedTimeComputable.shiftToZero`) keeps the
  rational coefficients explicit through `MvPolynomial.bind₁`.

  Reference: [RTCRN2] (Huang-Klinge-Lathrop, DNA 25, 2019) Theorem 3, pp. 11-12.
-/

import Ripple.Core.BoundedTime
import Mathlib.Algebra.MvPolynomial.Monad

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

/-! ## SemanticBTC-level shift -/

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

/-- [RTCRN2] Theorem 3, BTC-level: any `SemanticBTC d α` gives a
zero-init `SemanticBTC d (α − y₀.output)` with the same time modulus.
This is the DNA 25 reduction, semantic layer. The rational shift-back to `α`
requires additive closure (`realtime_field_add` or similar). -/
noncomputable def SemanticBTC.shiftToZero {d : ℕ} {α : ℝ}
    (btc : SemanticBTC d α) :
    SemanticBTC d (α - btc.pivp.init btc.pivp.output) where
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

@[simp] theorem SemanticBTC.shiftToZero_pivp_init {d : ℕ} {α : ℝ}
    (btc : SemanticBTC d α) (j : Fin d) :
    (btc.shiftToZero).pivp.init j = 0 := rfl

@[simp] theorem SemanticBTC.shiftToZero_pivp_output {d : ℕ} {α : ℝ}
    (btc : SemanticBTC d α) :
    (btc.shiftToZero).pivp.output = btc.pivp.output := rfl

/-- The shifted output init is zero (DNA 25 zero-init property). -/
theorem SemanticBTC.shiftToZero_zero_output_init {d : ℕ} {α : ℝ}
    (btc : SemanticBTC d α) :
    (btc.shiftToZero).pivp.init (btc.shiftToZero).pivp.output = 0 := rfl

/-! ## Syntactic (`PolyPIVP`) shift

The same change of variables on the ℚ-polynomial field: `p̂ᵢ := pᵢ(X + y₀)`, written with
`MvPolynomial.bind₁`, keeps rational coefficients; the initial value becomes `0`. -/

/-- [RTCRN2] Theorem 3, syntactic form: the field `p̂ᵢ(z) = pᵢ(z + y₀)` as ℚ-polynomials and
the zero initial value. -/
noncomputable def PolyPIVP.shiftToZero {d : ℕ} (P : PolyPIVP d) : PolyPIVP d where
  field i := MvPolynomial.bind₁ (fun j => MvPolynomial.X j + MvPolynomial.C (P.init j))
    (P.field i)
  init _ := 0
  output := P.output

/-- The evaluated shifted field is the original field at `z + y₀`. -/
theorem PolyPIVP.shiftToZero_evalField {d : ℕ} (P : PolyPIVP d) (z : Fin d → ℝ) :
    P.shiftToZero.evalField z = P.evalField (fun j => z j + (P.init j : ℝ)) := by
  funext i
  simp only [PolyPIVP.evalField, PolyPIVP.shiftToZero]
  rw [← MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂Hom_bind₁]
  simp [MvPolynomial.coe_eval₂Hom]

/-- [RTCRN2] Theorem 3, certified form: a certified computation of `α` gives a certified
zero-initial-value computation of `α − y₀,out` (`y₀,out` rational) with the same modulus. -/
noncomputable def CertifiedBoundedTimeComputable.shiftToZero {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α) :
    CertifiedBoundedTimeComputable d (α - (btc.pivp.init btc.pivp.output : ℝ)) :=
  btc.toSemantic.shiftToZero.certify btc.pivp.shiftToZero
    (fun z => PolyPIVP.shiftToZero_evalField btc.pivp z)
    (fun _ => by simp [PolyPIVP.shiftToZero, SemanticBTC.shiftToZero, PIVP.shiftToZero])
    rfl
    (by
      refine continuous_pi fun j => ?_
      change Continuous fun t => btc.sol.trajectory t j - (btc.pivp.init j : ℝ)
      exact ((continuous_apply j).comp btc.trajectory_continuous).sub continuous_const)

@[simp] theorem CertifiedBoundedTimeComputable.shiftToZero_modulus {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α) :
    btc.shiftToZero.modulus = btc.modulus := rfl

@[simp] theorem CertifiedBoundedTimeComputable.shiftToZero_init {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α) (j : Fin d) :
    btc.shiftToZero.pivp.init j = 0 := rfl

/-! ## IsRealTimeComputable-level DNA 25 corollary -/

/-- [RTCRN2] Theorem 3 at `IsRealTimeComputable` level: every real-time
computable `α` decomposes as `α = (α − β) + β` with `β` rational, where `α − β` has a
certified computation with all initial values `0` and the same linear modulus. -/
theorem IsRealTimeComputable.zero_init_decomposition {α : ℝ}
    (ha : IsRealTimeComputable α) :
    ∃ β : ℚ, ∃ d : ℕ, ∃ btc : CertifiedBoundedTimeComputable d (α - β),
      (∀ j, btc.pivp.init j = 0) ∧
      ∃ C > 0, ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) := by
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  exact ⟨btc.pivp.init btc.pivp.output, d, btc.shiftToZero, fun _ => rfl, C, hC, hmod⟩

/-- Reconstruction direction: if `α − β` is real-time computable and `β` is rational, then
`α = (α − β) + β` is real-time computable (`realtime_field_add` with the rational constant). -/
theorem IsRealTimeComputable.of_zero_init_plus_const (β : ℚ) (α_minus_β : ℝ)
    (h : IsRealTimeComputable α_minus_β) :
    IsRealTimeComputable (α_minus_β + β) :=
  realtime_field_add h (realtime_rat_const β)

end Ripple

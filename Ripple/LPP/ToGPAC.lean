/-
  Ripple.LPP.ToGPAC — the easy direction of the [LPP] Main Theorem: LPP ⇒ GPAC.

  The balance equation (5) of a PLPP is a ℚ-quadratic polynomial field
  (`PLPPTransitions.balancePoly`). Adding one readout species `w = Σ_{i ∈ M} xᵢ` (whose field is
  the sum of the marked balance polynomials) gives a `PolyPIVP` with rational initial value,
  bounded by the simplex, whose output tends to `ν`. So every PLPP-computable (hence every
  LPP-computable) number is `IsCRNComputable` ([BAC] Def 2.1 + 2.3), and a modulus for the
  marked fraction is a modulus for the certified computation.
-/

import Ripple.LPP.Computation
import Ripple.Core.BoundedTime

namespace Ripple

open MvPolynomial

namespace PLPPTransitions

/-- The balance equation (5) of a PLPP as ℚ-polynomials:
`b_r = Σ_{i,j} XᵢXⱼ (Σ_k α_{i,j,r,k} + Σ_k α_{i,j,k,r}) − 2 X_r Σ_k X_k`. -/
noncomputable def balancePoly {n : ℕ} (tr : PLPPTransitions n) (r : Fin n) :
    MvPolynomial (Fin n) ℚ :=
  (∑ i, ∑ j, X i * X j * C (∑ k, tr.α i j r k + ∑ k, tr.α i j k r)) -
    C 2 * X r * ∑ k, X k

/-- The evaluated balance polynomial is the balance field. -/
theorem eval_balancePoly {n : ℕ} (tr : PLPPTransitions n) (x : Fin n → ℝ) (r : Fin n) :
    (tr.balancePoly r).eval₂ (Rat.castHom ℝ) x = tr.balanceField x r := by
  simp [balancePoly, balanceField, Rat.cast_sum]

end PLPPTransitions

namespace PLPPComputation

variable {ν : ℝ} (c : PLPPComputation ν)

/-- The rational initial fractions of a PLPP computation. -/
noncomputable def initQ (i : Fin c.n) : ℚ := (c.comp.init_rational i).choose

theorem initQ_spec (i : Fin c.n) : c.comp.sol 0 i = (c.initQ i : ℝ) :=
  (c.comp.init_rational i).choose_spec

/-- The balance equation plus a readout species for the marked fraction, as a `PolyPIVP`. -/
noncomputable def readoutPIVP : PolyPIVP (c.n + 1) where
  field := Fin.snoc (fun r => rename Fin.castSucc (c.tr.balancePoly r))
    (∑ k ∈ c.marked, rename Fin.castSucc (c.tr.balancePoly k))
  init := Fin.snoc c.initQ (∑ k ∈ c.marked, c.initQ k)
  output := Fin.last c.n

/-- The trajectory of `readoutPIVP`: the PLPP trajectory and its marked fraction. -/
noncomputable def readoutTraj (t : ℝ) : Fin (c.n + 1) → ℝ :=
  Fin.snoc (c.comp.sol t) (∑ k ∈ c.marked, c.comp.sol t k)

/-- `readoutTraj` solves `readoutPIVP` on `[0, ∞)`. -/
noncomputable def readoutSolution : PIVP.Solution c.readoutPIVP.toPIVP where
  trajectory := c.readoutTraj
  init_cond := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [readoutTraj, readoutPIVP, PolyPIVP.toPIVP_init, Fin.snoc_last, Rat.cast_sum,
        c.initQ_spec]
    · simp only [readoutTraj, readoutPIVP, PolyPIVP.toPIVP_init, Fin.snoc_castSucc,
        c.initQ_spec]
  is_solution := fun t ht => by
    have hd := hasDerivAt_pi.mp (c.comp.ode t ht)
    rw [PolyPIVP.toPIVP_field_eq]
    refine hasDerivAt_pi.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [readoutTraj, readoutPIVP, PolyPIVP.evalField, Fin.snoc_last,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_rename, Fin.snoc_comp_castSucc,
        PLPPTransitions.eval_balancePoly]
      have h := HasDerivAt.sum (u := c.marked) (fun k _ => hd k)
      convert h using 1
      funext s
      simp
    · simp only [readoutTraj, readoutPIVP, PolyPIVP.evalField, Fin.snoc_castSucc,
        MvPolynomial.eval₂_rename, Fin.snoc_comp_castSucc, PLPPTransitions.eval_balancePoly]
      exact hd j

theorem readoutSolution_bounded :
    c.readoutPIVP.toPIVP.IsBounded c.readoutSolution.trajectory := by
  refine ⟨2, two_pos, fun t ht => ?_⟩
  have hsimp := c.comp.simplex t ht
  have hnn := c.comp.nonneg t ht
  have hle : ∀ k, c.comp.sol t k ≤ 1 := fun k => by
    rw [← hsimp]
    exact Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k)
  have hM : 0 ≤ ∑ k ∈ c.marked, c.comp.sol t k := Finset.sum_nonneg fun k _ => hnn k
  have hM1 : ∑ k ∈ c.marked, c.comp.sol t k ≤ 1 := by
    rw [← hsimp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hnn k
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change ‖(Fin.snoc (c.comp.sol t) (∑ k ∈ c.marked, c.comp.sol t k) :
      Fin (c.n + 1) → ℝ) (Fin.last c.n)‖ ≤ 2
    rw [Fin.snoc_last, Real.norm_eq_abs, abs_of_nonneg hM]
    linarith
  · change ‖(Fin.snoc (c.comp.sol t) (∑ k ∈ c.marked, c.comp.sol t k) :
      Fin (c.n + 1) → ℝ) (Fin.castSucc j)‖ ≤ 2
    rw [Fin.snoc_castSucc, Real.norm_eq_abs, abs_of_nonneg (hnn j)]
    linarith [hle j]

/-- A PLPP computation with a modulus for its marked fraction gives a certified computation of
`ν` (the readout system) with the same modulus, clipped at `0`. -/
theorem exists_cbtc (modulus : TimeModulus)
    (hmod : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
      |∑ k ∈ c.marked, c.comp.sol t k - ν| < Real.exp (-(r : ℝ))) :
    ∃ btc : CertifiedBoundedTimeComputable (c.n + 1) ν,
      btc.pivp = c.readoutPIVP ∧ ∀ r, btc.modulus r = max 0 (modulus r) := by
  obtain ⟨btc, hP, hmod', -⟩ := CertifiedBoundedTimeComputable.exists_of_solution
    c.readoutPIVP c.readoutSolution c.readoutSolution_bounded modulus (fun r t ht => by
      change |(Fin.snoc (c.comp.sol t) (∑ k ∈ c.marked, c.comp.sol t k) :
        Fin (c.n + 1) → ℝ) (Fin.last c.n) - ν| < _
      rw [Fin.snoc_last]
      exact hmod r t ht)
  exact ⟨btc, hP, hmod'⟩

/-- The marked fraction of a PLPP computation has a modulus (it converges). -/
theorem exists_modulus : ∃ modulus : TimeModulus, ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |∑ k ∈ c.marked, c.comp.sol t k - ν| < Real.exp (-(r : ℝ)) := by
  have h : ∀ r : ℕ, ∃ T : ℝ, ∀ t : ℝ, t > T →
      |∑ k ∈ c.marked, c.comp.sol t k - ν| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop'.mp c.comp.readout_tendsto)
      (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by simpa [Real.dist_eq] using hT t ht⟩
  choose T hT using h
  exact ⟨T, hT⟩

end PLPPComputation

/-- [LPP] Main Theorem, easy direction (PLPP ⇒ GPAC): a PLPP-computable number is
`IsCRNComputable`. -/
theorem plpp_to_gpac {ν : ℝ} (h : IsPLPPComputable ν) : IsCRNComputable ν := by
  obtain ⟨c⟩ := h
  obtain ⟨modulus, hmod⟩ := c.exists_modulus
  obtain ⟨btc, -, -⟩ := c.exists_cbtc modulus hmod
  exact ⟨c.n + 1, ⟨btc⟩⟩

/-- [LPP] Main Theorem, easy direction (LPP ⇒ GPAC): an LPP-computable number is
`IsCRNComputable`. -/
theorem lpp_to_gpac {ν : ℝ} (h : IsLPPComputable ν) : IsCRNComputable ν :=
  plpp_to_gpac h.isPLPPComputable

/-- Quantitative LPP ⇒ GPAC: a modulus for the marked fraction of an LPP computation is (up to
clipping at 0) the modulus of a certified computation of the same number. -/
theorem lpp_to_gpac_with_modulus {ν : ℝ} (c : LPPComputation ν) (modulus : TimeModulus)
    (hmod : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
      |∑ k ∈ c.marked, c.comp.sol t k - ν| < Real.exp (-(r : ℝ))) :
    ∃ d : ℕ, ∃ btc : CertifiedBoundedTimeComputable d ν,
      ∀ r, btc.modulus r = max 0 (modulus r) := by
  obtain ⟨btc, -, h⟩ := c.toPLPPComputation.exists_cbtc modulus hmod
  exact ⟨_, btc, h⟩

end Ripple

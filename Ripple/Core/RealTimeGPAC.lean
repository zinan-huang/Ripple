/-
  Ripple.Core.RealTimeGPAC — the paper-literal real-time class R_RTGPAC of [RTCRN2] §3.

  [RTCRN2] (p. 5): a PIVP `y` with `y(0) = 0` is a computer for `α` if (1) all coefficients are
  integers, (2) `|yᵢ(t)| ≤ β` on `[0, ∞)`, and (3) `|y₁(t) − α| ≤ 2^{−t}` for `t ≥ 1`.
  `IsRTGPACComputable` states this literally (the output is any designated variable instead of
  `y₁`, a renumbering). `isRealTimeComputable_iff_rtgpac` proves that it is the class
  `IsRealTimeComputable` ([BAC] Def 2.3 with a linear modulus).

  Forward direction: shift to zero initial values (`zero_init_decomposition`, `β ∈ ℚ`), add back
  the constant through one extra variable `w = x_out + β(1 − e^{−t})` (`PolyPIVP.addConst`), and
  rescale time by an integer `L` (`PolyPIVP.timeScale`) that clears the denominators of the
  field and makes the linear modulus faster than `2^{−t}` ([RTCRN2] Lemma 1).
-/

import Ripple.Core.InitShift
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Ripple

open MvPolynomial

/-- [RTCRN2] §3 (p. 5), the real-time GPAC computers: a `PolyPIVP` with all initial values `0`
and integer coefficients, and a solution bounded on `[0, ∞)` whose output satisfies
`|y_out(t) − α| ≤ 2^{−t}` for all `t ≥ 1`. -/
def IsRTGPACComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ P : PolyPIVP d, (∀ i, P.init i = 0) ∧
    (∀ i m, ∃ z : ℤ, (P.field i).coeff m = (z : ℚ)) ∧
    ∃ sol : PIVP.Solution P.toPIVP, ∃ β : ℝ, 0 < β ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i, |sol.trajectory t i| ≤ β) ∧
      ∀ t : ℝ, 1 ≤ t → |sol.trajectory t P.output - α| ≤ (2 : ℝ) ^ (-t)

/-! ### Integer coefficients -/

/-- Every ℚ-polynomial becomes integral after multiplication by a positive integer (the product
of the denominators of its coefficients). -/
theorem exists_nat_mul_intCoeff {σ : Type*} (q : MvPolynomial σ ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ m, ∃ z : ℤ, (C (D : ℚ) * q).coeff m = (z : ℚ) := by
  classical
  refine ⟨∏ m ∈ q.support, (q.coeff m).den,
    Finset.prod_pos fun m _ => (q.coeff m).den_pos, fun m => ?_⟩
  rw [coeff_C_mul]
  by_cases hm : m ∈ q.support
  · have hdvd : (q.coeff m).den ∣ ∏ m ∈ q.support, (q.coeff m).den :=
      Finset.dvd_prod_of_mem _ hm
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨(q.coeff m).num * k, ?_⟩
    have hc : q.coeff m * ((q.coeff m).den : ℚ) = (q.coeff m).num := by
      rw [Rat.mul_den_eq_num]
    rw [hk]
    push_cast
    linear_combination (k : ℚ) * hc
  · rw [MvPolynomial.mem_support_iff, not_not] at hm
    exact ⟨0, by rw [hm]; simp⟩

/-- Integrality after multiplication by `D` persists after multiplication by any multiple of
`D`. -/
theorem intCoeff_of_dvd {σ : Type*} (q : MvPolynomial σ ℚ) {D L : ℕ}
    (hD : ∀ m, ∃ z : ℤ, (C (D : ℚ) * q).coeff m = (z : ℚ)) (h : D ∣ L) :
    ∀ m, ∃ z : ℤ, (C (L : ℚ) * q).coeff m = (z : ℚ) := by
  obtain ⟨e, rfl⟩ := h
  intro m
  obtain ⟨z, hz⟩ := hD m
  refine ⟨e * z, ?_⟩
  rw [coeff_C_mul] at hz ⊢
  push_cast
  rw [← hz]
  ring

/-! ### Time scaling -/

namespace PolyPIVP

/-- Time scaling by an integer `L`: the field `L · p`. Its solution is `t ↦ y(L t)`. -/
noncomputable def timeScale {d : ℕ} (P : PolyPIVP d) (L : ℕ) : PolyPIVP d where
  field i := C (L : ℚ) * P.field i
  init := P.init
  output := P.output

theorem timeScale_evalField {d : ℕ} (P : PolyPIVP d) (L : ℕ) (x : Fin d → ℝ) :
    (P.timeScale L).evalField x = (L : ℝ) • P.evalField x := by
  funext i
  simp [timeScale, evalField]

end PolyPIVP

/-- The time-scaled solution `t ↦ y(L t)` of `P.timeScale L`. -/
noncomputable def PIVP.Solution.timeScale {d : ℕ} {P : PolyPIVP d}
    (sol : PIVP.Solution P.toPIVP) (L : ℕ) : PIVP.Solution (P.timeScale L).toPIVP where
  trajectory t := sol.trajectory ((L : ℝ) * t)
  init_cond := by
    change sol.trajectory ((L : ℝ) * 0) = P.toPIVP.init
    rw [mul_zero]
    exact sol.init_cond
  is_solution t ht := by
    have hLt : 0 ≤ (L : ℝ) * t := mul_nonneg (Nat.cast_nonneg L) ht
    have h := (sol.is_solution _ hLt).scomp t ((hasDerivAt_id t).const_mul (L : ℝ))
    rw [mul_one] at h
    rw [PolyPIVP.toPIVP_field_eq, PolyPIVP.timeScale_evalField]
    exact h

/-! ### Adding a rational constant with zero initial value -/

namespace PolyPIVP

/-- One extra variable `w` with `w' = p_out(x) + β − w + x_out`, `w(0) = x_out(0)`; its solution
is `w = x_out + β (1 − e^{−t})`, which tends to `lim x_out + β`. -/
noncomputable def addConst {d : ℕ} (P : PolyPIVP d) (β : ℚ) : PolyPIVP (d + 1) where
  field := Fin.snoc (fun j => rename Fin.castSucc (P.field j))
    (rename Fin.castSucc (P.field P.output) + C β - X (Fin.last d) +
      X (Fin.castSucc P.output))
  init := Fin.snoc P.init (P.init P.output)
  output := Fin.last d

end PolyPIVP

/-- The trajectory of `P.addConst β`. -/
noncomputable def addConstTraj {d : ℕ} {P : PIVP d} (sol : PIVP.Solution P) (β : ℚ) (t : ℝ) :
    Fin (d + 1) → ℝ :=
  Fin.snoc (sol.trajectory t) (sol.trajectory t P.output + β * (1 - Real.exp (-t)))

@[simp] theorem addConstTraj_last {d : ℕ} {P : PIVP d} (sol : PIVP.Solution P) (β : ℚ)
    (t : ℝ) : addConstTraj sol β t (Fin.last d) =
      sol.trajectory t P.output + β * (1 - Real.exp (-t)) := by
  simp [addConstTraj]

@[simp] theorem addConstTraj_castSucc {d : ℕ} {P : PIVP d} (sol : PIVP.Solution P) (β : ℚ)
    (t : ℝ) (j : Fin d) : addConstTraj sol β t (Fin.castSucc j) = sol.trajectory t j := by
  simp [addConstTraj]

theorem addConstTraj_comp_castSucc {d : ℕ} {P : PIVP d} (sol : PIVP.Solution P) (β : ℚ)
    (t : ℝ) : addConstTraj sol β t ∘ Fin.castSucc = sol.trajectory t := by
  funext j
  simp

/-- `addConstTraj` solves `P.addConst β`. -/
noncomputable def PIVP.Solution.addConst {d : ℕ} {P : PolyPIVP d}
    (sol : PIVP.Solution P.toPIVP) (β : ℚ) : PIVP.Solution (P.addConst β).toPIVP where
  trajectory := addConstTraj sol β
  init_cond := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [addConstTraj_last, sol.init_cond]
      simp [PolyPIVP.addConst]
    · rw [addConstTraj_castSucc, sol.init_cond]
      simp [PolyPIVP.addConst]
  is_solution t ht := by
    have hd := hasDerivAt_pi.mp (sol.is_solution t ht)
    rw [PolyPIVP.toPIVP_field_eq]
    refine hasDerivAt_pi.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [addConstTraj_last]
      have he : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
        simpa using (hasDerivAt_neg t).exp
      have hw := (hd P.output).add ((he.const_sub 1).const_mul (β : ℝ))
      refine hw.congr_deriv ?_
      simp only [PolyPIVP.evalField, PolyPIVP.addConst, Fin.snoc_last, eval₂_add, eval₂_sub,
        eval₂_C, eval₂_X, eval₂_rename, addConstTraj_comp_castSucc, addConstTraj_last,
        addConstTraj_castSucc]
      simp only [PolyPIVP.toPIVP_field_eq, PolyPIVP.evalField, PolyPIVP.toPIVP_output,
        Rat.coe_castHom]
      ring
    · simp only [addConstTraj_castSucc]
      simp only [PolyPIVP.evalField, PolyPIVP.addConst, Fin.snoc_castSucc, eval₂_rename,
        addConstTraj_comp_castSucc]
      exact hd j

/-! ### The equivalence -/

/-- [RTCRN2] §3 ⇒ [BAC]: a real-time GPAC computer has the linear modulus `2r + 1`. -/
theorem IsRTGPACComputable.isRealTimeComputable {α : ℝ} (h : IsRTGPACComputable α) :
    IsRealTimeComputable α := by
  obtain ⟨d, P, -, -, sol, β, hβ, hbd, hconv⟩ := h
  have hbd' : P.toPIVP.IsBounded sol.trajectory :=
    ⟨β, hβ, fun t ht => (pi_norm_le_iff_of_nonneg hβ.le).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hbd t ht i⟩
  have hconv' : ∀ r : ℕ, ∀ t : ℝ, t > 2 * (r : ℝ) + 1 →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have ht1 : 1 ≤ t := by linarith
    refine lt_of_le_of_lt (hconv t ht1) ?_
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine Real.exp_lt_exp.mpr ?_
    have hl := Real.log_two_gt_d9
    have h1 : (2 * (r : ℝ) + 1) * 0.6931471803 ≤ t * Real.log 2 :=
      mul_le_mul ht.le hl.le (by norm_num) (by linarith)
    nlinarith
  obtain ⟨btc, -, hmod, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_solution P sol hbd' (fun r => 2 * (r : ℝ) + 1)
      hconv'
  refine ⟨d, btc, 3, by norm_num, fun r => ?_⟩
  rw [hmod r]
  show max 0 (2 * (r : ℝ) + 1) ≤ 3 * ((r : ℝ) + 1)
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  exact max_le (by positivity) (by linarith)

/-- [BAC] ⇒ [RTCRN2] §3: a real-time computable number has a real-time GPAC computer (zero
initial values, integer coefficients, error `≤ 2^{−t}` for `t ≥ 1`). -/
theorem IsRealTimeComputable.isRTGPACComputable {α : ℝ} (h : IsRealTimeComputable α) :
    IsRTGPACComputable α := by
  obtain ⟨β, d, btc, hinit, Cm, hCm, hmod⟩ := h.zero_init_decomposition
  -- the zero-initial system computing `α`, before time scaling
  let P := btc.pivp.addConst β
  choose D hDpos hD using fun i => exists_nat_mul_intCoeff (P.field i)
  let L₀ : ℕ := ∏ i, D i
  let K : ℕ := ⌈4 * Cm⌉₊ + ⌈|(β : ℝ)|⌉₊ + 2
  let L : ℕ := L₀ * K
  have hL₀ : 0 < L₀ := Finset.prod_pos fun i _ => hDpos i
  have hKL : (K : ℝ) ≤ L := by
    exact_mod_cast le_mul_of_one_le_left (Nat.zero_le K) hL₀
  have hKcast : (K : ℝ) = ⌈4 * Cm⌉₊ + ⌈|(β : ℝ)|⌉₊ + 2 := by
    simp [K]
  have hc1 := Nat.le_ceil (4 * Cm)
  have hc2 := Nat.le_ceil |(β : ℝ)|
  have hc1' : (0 : ℝ) ≤ ⌈4 * Cm⌉₊ := Nat.cast_nonneg _
  have hc2' : (0 : ℝ) ≤ ⌈|(β : ℝ)|⌉₊ := Nat.cast_nonneg _
  have hL4 : 4 * Cm ≤ (L : ℝ) := by linarith
  have hLβ : |(β : ℝ)| + 2 ≤ (L : ℝ) := by linarith
  obtain ⟨M, hM, hb⟩ := btc.bounded
  have hxb : ∀ s : ℝ, 0 ≤ s → ∀ j, |btc.sol.trajectory s j| ≤ M := fun s hs j => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (btc.sol.trajectory s) j).trans (hb s hs)
  refine ⟨d + 1, P.timeScale L, ?_, ?_, (btc.sol.addConst β).timeScale L, M + |(β : ℝ)| + 1,
    by positivity, ?_, ?_⟩
  · -- zero initial values
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [PolyPIVP.timeScale, P, PolyPIVP.addConst, hinit]
    · simp [PolyPIVP.timeScale, P, PolyPIVP.addConst, hinit]
  · -- integer coefficients
    intro i
    have hdvd : D i ∣ L := (Finset.dvd_prod_of_mem D (Finset.mem_univ i)).mul_right K
    exact intCoeff_of_dvd (P.field i) (hD i) hdvd
  · -- boundedness
    intro t ht i
    have hLt : 0 ≤ (L : ℝ) * t := mul_nonneg (Nat.cast_nonneg L) ht
    change |addConstTraj btc.sol β ((L : ℝ) * t) i| ≤ _
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [addConstTraj_last]
      have he1 : Real.exp (-((L : ℝ) * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have he0 := Real.exp_pos (-((L : ℝ) * t))
      have h1 : |1 - Real.exp (-((L : ℝ) * t))| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |btc.sol.trajectory ((L : ℝ) * t) btc.pivp.output +
              (β : ℝ) * (1 - Real.exp (-((L : ℝ) * t)))|
          ≤ |btc.sol.trajectory ((L : ℝ) * t) btc.pivp.output| +
              |(β : ℝ)| * |1 - Real.exp (-((L : ℝ) * t))| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ M + |(β : ℝ)| * 1 :=
            add_le_add (hxb _ hLt _) (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
        _ ≤ M + |(β : ℝ)| + 1 := by linarith
    · rw [addConstTraj_castSucc]
      linarith [hxb _ hLt j, abs_nonneg (β : ℝ)]
  · -- the rate `2^{−t}` for `t ≥ 1`
    intro t ht1
    have ht0 : (0 : ℝ) ≤ t := by linarith
    change |addConstTraj btc.sol β ((L : ℝ) * t) (Fin.last d) - α| ≤ _
    rw [addConstTraj_last, PolyPIVP.toPIVP_output]
    set x := btc.sol.trajectory ((L : ℝ) * t) btc.pivp.output
    set r : ℕ := ⌈2 * t⌉₊
    have hr1 : 2 * t ≤ r := Nat.le_ceil _
    have hr2 : (r : ℝ) < 2 * t + 1 := Nat.ceil_lt_add_one (by linarith)
    have hLt : (L : ℝ) * t > btc.modulus r := by
      have h1 := hmod r
      have h2 : Cm * ((r : ℝ) + 1) < Cm * (2 * t + 2) :=
        mul_lt_mul_of_pos_left (by linarith) hCm
      have h3 : 4 * Cm * t ≤ (L : ℝ) * t := mul_le_mul_of_nonneg_right hL4 ht0
      have h4 : Cm * 1 ≤ Cm * t := mul_le_mul_of_nonneg_left ht1 hCm.le
      nlinarith
    have hx : |x - (α - β)| < Real.exp (-(r : ℝ)) := btc.convergence r _ hLt
    have hx' : Real.exp (-(r : ℝ)) ≤ Real.exp (-(2 * t)) := Real.exp_le_exp.mpr (by linarith)
    have hβe : |(β : ℝ)| * Real.exp (-((L : ℝ) * t)) ≤ Real.exp (-(2 * t)) := by
      have hb1 : |(β : ℝ)| ≤ Real.exp ((L : ℝ) - 2) := by
        have := Real.add_one_le_exp ((L : ℝ) - 2)
        linarith
      calc |(β : ℝ)| * Real.exp (-((L : ℝ) * t))
          ≤ Real.exp ((L : ℝ) - 2) * Real.exp (-((L : ℝ) * t)) :=
            mul_le_mul_of_nonneg_right hb1 (Real.exp_pos _).le
        _ = Real.exp ((L : ℝ) - 2 - (L : ℝ) * t) := by
            rw [← Real.exp_add]; congr 1
        _ ≤ Real.exp (-(2 * t)) := by
            refine Real.exp_le_exp.mpr ?_
            have := mul_nonneg (by linarith : (0 : ℝ) ≤ (L : ℝ) - 2)
              (by linarith : (0 : ℝ) ≤ t - 1)
            nlinarith
    have hsplit : x + (β : ℝ) * (1 - Real.exp (-((L : ℝ) * t))) - α =
        (x - (α - β)) - (β : ℝ) * Real.exp (-((L : ℝ) * t)) := by ring
    have h2t : 2 * Real.exp (-(2 * t)) ≤ (2 : ℝ) ^ (-t) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hl := Real.log_two_lt_d9
      have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      calc 2 * Real.exp (-(2 * t)) = Real.exp (Real.log 2 + -(2 * t)) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]
        _ ≤ Real.exp (Real.log 2 * -t) := by
            refine Real.exp_le_exp.mpr ?_
            have h1 : Real.log 2 * t ≤ 0.6931471808 * t :=
              mul_le_mul_of_nonneg_right hl.le ht0
            nlinarith
    rw [hsplit]
    calc |(x - (α - β)) - (β : ℝ) * Real.exp (-((L : ℝ) * t))|
        ≤ |x - (α - β)| + |(β : ℝ) * Real.exp (-((L : ℝ) * t))| := by
          have := abs_add_le (x - (α - β)) (-((β : ℝ) * Real.exp (-((L : ℝ) * t))))
          rwa [abs_neg, ← sub_eq_add_neg] at this
      _ = |x - (α - β)| + |(β : ℝ)| * Real.exp (-((L : ℝ) * t)) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 2 * Real.exp (-(2 * t)) := by linarith
      _ ≤ (2 : ℝ) ^ (-t) := h2t

/-- [RTCRN2] §3 and [BAC] Def 2.3 give the same real-time class: `IsRealTimeComputable` is
R_RTGPAC. -/
theorem isRealTimeComputable_iff_rtgpac {α : ℝ} :
    IsRealTimeComputable α ↔ IsRTGPACComputable α :=
  ⟨IsRealTimeComputable.isRTGPACComputable, IsRTGPACComputable.isRealTimeComputable⟩

end Ripple

import Ripple.BoundedUniversality.BGP.LogisticSharpen

/-!
Ripple.BoundedUniversality.BGP.LogisticReset
------------------------
Reset-error variants of the logistic sharpening bounds.

Design source: `notes/gpt-clock-driven-selector-r2.md` §2.4.  In the autonomous
field the reset phase is a *contraction* toward `1/2`, so the gate phase starts
at `λ_v(a) = 1/2 ± δ`, not exactly `1/2`.  The exact bounds in
`LogisticSharpen.lean` assume `λ_v(a) = 1/2`; here we generalise to
`|λ_v(a) - 1/2| ≤ δ`, paying a constant factor

  `C_reset(δ) = (1/2 + δ) / (1/2 - δ)`   (`= 1` when `δ = 0`).

The integrating-factor argument is unchanged (`Q' ≤ 0` fences `Q b ≤ Q a`); only
the initial value `Q a = oddsHi/oddsLo(λ a)` is now bounded by `C_reset` instead
of equal to `1`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set

/-- Reset constant `C_reset(δ) = (1/2 + δ)/(1/2 - δ)`, the worst-case initial odds
when `|λ(a) - 1/2| ≤ δ`.  Equals `1` at `δ = 0`. -/
noncomputable def Creset (δ : ℝ) : ℝ := (1 / 2 + δ) / (1 / 2 - δ)

theorem one_le_Creset {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    1 ≤ Creset δ := by
  rw [Creset, le_div_iff₀ (by linarith)]; linarith

theorem Creset_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2) :
    0 ≤ Creset δ :=
  le_trans (by norm_num) (one_le_Creset hδ hδhalf)

/-- Logistic sharpening with reset error, true view: `P ≥ α > 0` and
`|L a - 1/2| ≤ δ` give `1 - L b ≤ C_reset(δ) · exp(-α·(G b - G a))`. -/
theorem logistic_true_bound_reset
    {a b α δ : ℝ} {L r P G : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hLder : ∀ t ∈ Ico a b,
      HasDerivWithinAt L (r t * P t * (L t * (1 - L t))) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hLcont : ContinuousOn L (Icc a b)) (hGcont : ContinuousOn G (Icc a b))
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t) (hP : ∀ t ∈ Ico a b, α ≤ P t)
    (hunit : ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1) (hLa : |L a - 1 / 2| ≤ δ) :
    1 - L b ≤ Creset δ * Real.exp (-α * (G b - G a)) := by
  set Q : ℝ → ℝ := fun t => ((1 - L t) / L t) * Real.exp (α * (G t - G a)) with hQdef
  have hQder : ∀ t ∈ Ico a b, HasDerivWithinAt Q (r t * (α - P t) * Q t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hL0 : L t ≠ 0 := (hunit t htc).1.ne'
    have hodds := hasDerivWithinAt_oddsHi (hLder t ht) hL0
    have hexp : HasDerivWithinAt (fun u => Real.exp (α * (G u - G a)))
        (Real.exp (α * (G t - G a)) * (α * r t)) (Ici t) t :=
      (((hGder t ht).sub_const (G a)).const_mul α).exp
    have hmul := hodds.mul hexp
    convert hmul using 1
    simp only [hQdef]
    ring
  have hQcont : ContinuousOn Q (Icc a b) := by
    apply ContinuousOn.mul
    · exact (continuousOn_const.sub hLcont).div hLcont (fun t ht => (hunit t ht).1.ne')
    · exact Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (hGcont.sub continuousOn_const))
  have hLapos : 0 < L a := (hunit a (left_mem_Icc.mpr hab)).1
  have hQa_le : Q a ≤ Creset δ := by
    have hQaval : Q a = (1 - L a) / L a := by
      simp only [hQdef, sub_self, mul_zero, Real.exp_zero, mul_one]
    rw [hQaval, Creset, le_div_iff₀ (by linarith : (0:ℝ) < 1 / 2 - δ),
      div_mul_eq_mul_div, div_le_iff₀ hLapos]
    rw [abs_le] at hLa
    nlinarith [hLa.1, hLa.2]
  have hbound :
      ∀ ⦃x⦄, x ∈ Icc a b → Q x ≤ (fun _ : ℝ => Q a) x :=
    image_le_of_deriv_right_le_deriv_boundary hQcont hQder
      (by simp) continuousOn_const
      (fun t _ => hasDerivWithinAt_const t (Ici t) (Q a))
      (fun t ht => by
        have hQnn : 0 ≤ Q t := by
          have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
          exact mul_nonneg
            (div_nonneg (by linarith [(hunit t htc).2]) (hunit t htc).1.le)
            (Real.exp_pos _).le
        have : r t * (α - P t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hr t ht) (by linarith [hP t ht])
        simpa using mul_nonpos_of_nonpos_of_nonneg this hQnn)
  have hQb : Q b ≤ Creset δ := le_trans (hbound (right_mem_Icc.mpr hab)) hQa_le
  have hLb := hunit b (right_mem_Icc.mpr hab)
  have hexppos : 0 < Real.exp (α * (G b - G a)) := Real.exp_pos _
  have hodds_le : (1 - L b) / L b ≤ Creset δ * Real.exp (-α * (G b - G a)) := by
    rw [show (-α * (G b - G a)) = -(α * (G b - G a)) by ring, Real.exp_neg,
      ← div_eq_mul_inv, le_div_iff₀ hexppos]
    exact hQb
  have hstep : 1 - L b ≤ (1 - L b) / L b := by
    rw [le_div_iff₀ hLb.1]
    nlinarith [hLb.1, hLb.2]
  linarith [hodds_le, hstep]

/-- Logistic sharpening with reset error, false view: `P ≤ -α < 0` and
`|L a - 1/2| ≤ δ` give `L b ≤ C_reset(δ) · exp(-α·(G b - G a))`. -/
theorem logistic_false_bound_reset
    {a b α δ : ℝ} {L r P G : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hLder : ∀ t ∈ Ico a b,
      HasDerivWithinAt L (r t * P t * (L t * (1 - L t))) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hLcont : ContinuousOn L (Icc a b)) (hGcont : ContinuousOn G (Icc a b))
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t) (hP : ∀ t ∈ Ico a b, P t ≤ -α)
    (hunit : ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1) (hLa : |L a - 1 / 2| ≤ δ) :
    L b ≤ Creset δ * Real.exp (-α * (G b - G a)) := by
  set Q : ℝ → ℝ := fun t => (L t / (1 - L t)) * Real.exp (α * (G t - G a)) with hQdef
  have hQder : ∀ t ∈ Ico a b, HasDerivWithinAt Q (r t * (P t + α) * Q t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hL1 : 1 - L t ≠ 0 := by have := (hunit t htc).2; linarith
    have hodds := hasDerivWithinAt_oddsLo (hLder t ht) hL1
    have hexp : HasDerivWithinAt (fun u => Real.exp (α * (G u - G a)))
        (Real.exp (α * (G t - G a)) * (α * r t)) (Ici t) t :=
      (((hGder t ht).sub_const (G a)).const_mul α).exp
    have hmul := hodds.mul hexp
    convert hmul using 1
    simp only [hQdef]
    ring
  have hQcont : ContinuousOn Q (Icc a b) := by
    apply ContinuousOn.mul
    · exact hLcont.div (continuousOn_const.sub hLcont)
        (fun t ht => by have := (hunit t ht).2; intro h; linarith [sub_eq_zero.mp h])
    · exact Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (hGcont.sub continuousOn_const))
  have hLapos := (hunit a (left_mem_Icc.mpr hab))
  have hQa_le : Q a ≤ Creset δ := by
    have hQaval : Q a = L a / (1 - L a) := by
      simp only [hQdef, sub_self, mul_zero, Real.exp_zero, mul_one]
    rw [hQaval, Creset, le_div_iff₀ (by linarith : (0:ℝ) < 1 / 2 - δ),
      div_mul_eq_mul_div, div_le_iff₀ (by linarith [hLapos.2] : (0:ℝ) < 1 - L a)]
    rw [abs_le] at hLa
    nlinarith [hLa.1, hLa.2]
  have hbound :
      ∀ ⦃x⦄, x ∈ Icc a b → Q x ≤ (fun _ : ℝ => Q a) x :=
    image_le_of_deriv_right_le_deriv_boundary hQcont hQder
      (by simp) continuousOn_const
      (fun t _ => hasDerivWithinAt_const t (Ici t) (Q a))
      (fun t ht => by
        have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
        have hQnn : 0 ≤ Q t :=
          mul_nonneg
            (div_nonneg (hunit t htc).1.le (by linarith [(hunit t htc).2]))
            (Real.exp_pos _).le
        have : r t * (P t + α) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hr t ht) (by linarith [hP t ht])
        simpa using mul_nonpos_of_nonpos_of_nonneg this hQnn)
  have hQb : Q b ≤ Creset δ := le_trans (hbound (right_mem_Icc.mpr hab)) hQa_le
  have hLb := hunit b (right_mem_Icc.mpr hab)
  have hexppos : 0 < Real.exp (α * (G b - G a)) := Real.exp_pos _
  have hodds_le : L b / (1 - L b) ≤ Creset δ * Real.exp (-α * (G b - G a)) := by
    rw [show (-α * (G b - G a)) = -(α * (G b - G a)) by ring, Real.exp_neg,
      ← div_eq_mul_inv, le_div_iff₀ hexppos]
    exact hQb
  have hstep : L b ≤ L b / (1 - L b) := by
    rw [le_div_iff₀ (by linarith [hLb.2] : (0:ℝ) < 1 - L b)]
    nlinarith [hLb.1, hLb.2]
  linarith [hodds_le, hstep]

open scoped BigOperators

/-- One gate phase with reset error produces one-hot weights up to `C_reset(δ)`. -/
theorem selector_phase_onehot_reset {V : Type*} (vstar : V)
    {a b α δ : ℝ} {r G : ℝ → ℝ} {lam P : V → ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hGcont : ContinuousOn G (Icc a b))
    (hlamder : ∀ v, ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v) (r t * P v t * (lam v t * (1 - lam v t))) (Ici t) t)
    (hlamcont : ∀ v, ContinuousOn (lam v) (Icc a b))
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (hlama : ∀ v, |lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Ico a b, α ≤ P vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α) :
    1 - lam vstar b ≤ Creset δ * Real.exp (-α * (G b - G a)) ∧
      ∀ v, v ≠ vstar → lam v b ≤ Creset δ * Real.exp (-α * (G b - G a)) := by
  refine ⟨logistic_true_bound_reset hab hα hδ hδhalf (hlamder vstar) hGder
      (hlamcont vstar) hGcont hr hPtrue (hunit vstar) (hlama vstar), ?_⟩
  intro v hv
  exact logistic_false_bound_reset hab hα hδ hδhalf (hlamder v) hGder
    (hlamcont v) hGcont hr (hPfalse v hv) (hunit v) (hlama v)

/-- Full clock-driven selector error with reset error: the weighted branch mixture
is within `card · R · C_reset(δ) · e^{-α·ΔG}` of the true branch value. -/
theorem selector_mix_error_reset {V : Type*} [Fintype V] [DecidableEq V] (vstar : V)
    {a b α δ : ℝ} {r G : ℝ → ℝ} {lam P : V → ℝ → ℝ} {R : ℝ} (A : V → ℝ)
    (hab : a ≤ b) (hα : 0 < α) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2) (hR : 0 ≤ R)
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hGcont : ContinuousOn G (Icc a b))
    (hlamder : ∀ v, ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v) (r t * P v t * (lam v t * (1 - lam v t))) (Ici t) t)
    (hlamcont : ∀ v, ContinuousOn (lam v) (Icc a b))
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (hlama : ∀ v, |lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Ico a b, α ≤ P vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α)
    (hA : ∀ v, |A v| ≤ R) :
    |(∑ v, lam v b * A v) - A vstar| ≤
      (Fintype.card V : ℝ) * R * (Creset δ * Real.exp (-α * (G b - G a))) := by
  obtain ⟨htrue, hfalse⟩ := selector_phase_onehot_reset vstar hab hα hδ hδhalf hr
    hGder hGcont hlamder hlamcont hunit hlama hPtrue hPfalse
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hεnn : 0 ≤ Creset δ * Real.exp (-α * (G b - G a)) :=
    mul_nonneg (Creset_nonneg hδ hδhalf) (Real.exp_pos _).le
  exact branch_mix_error vstar (fun v => lam v b) A hεnn hR
    (fun v => (hunit v b hb).1.le)
    (by linarith [htrue]) (hunit vstar b hb).2.le hfalse hA

end Ripple.BoundedUniversality.BGP

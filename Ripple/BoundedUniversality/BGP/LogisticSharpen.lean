import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Ripple.BoundedUniversality.BGP

open Set

noncomputable def oddsHi (x : ℝ) : ℝ := (1 - x) / x
noncomputable def oddsLo (x : ℝ) : ℝ := x / (1 - x)

/-- Within-derivative of `oddsHi ∘ L` along the logistic ODE `L' = c·L(1-L)`. -/
theorem hasDerivWithinAt_oddsHi {L : ℝ → ℝ} {t c : ℝ} {s : Set ℝ}
    (hL : HasDerivWithinAt L (c * (L t * (1 - L t))) s t) (hL0 : L t ≠ 0) :
    HasDerivWithinAt (fun u => (1 - L u) / L u) (-c * ((1 - L t) / L t)) s t := by
  have hnum : HasDerivWithinAt (fun u => 1 - L u) (-(c * (L t * (1 - L t)))) s t :=
    hL.const_sub 1
  have hdiv := hnum.div hL hL0
  convert hdiv using 1
  field_simp
  ring

/-- Within-derivative of `oddsLo ∘ L` along the logistic ODE `L' = c·L(1-L)`. -/
theorem hasDerivWithinAt_oddsLo {L : ℝ → ℝ} {t c : ℝ} {s : Set ℝ}
    (hL : HasDerivWithinAt L (c * (L t * (1 - L t))) s t) (hL1 : 1 - L t ≠ 0) :
    HasDerivWithinAt (fun u => L u / (1 - L u)) (c * (L t / (1 - L t))) s t := by
  have hden : HasDerivWithinAt (fun u => 1 - L u) (-(c * (L t * (1 - L t)))) s t :=
    hL.const_sub 1
  have hdiv := hL.div hden hL1
  convert hdiv using 1
  field_simp
  ring

/-- Logistic sharpening, true view: with `L' = r·P·L(1-L)`, `P ≥ α > 0`, `r ≥ 0`,
`L a = 1/2`, and the integrated-gain coordinate `G' = r`, the gate saturates:
`1 - L b ≤ exp(-α·(G b - G a))`.  Assumes the unit invariant `0 < L < 1`. -/
theorem logistic_true_bound_assuming_unit
    {a b α : ℝ} {L r P G : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α)
    (hLder : ∀ t ∈ Ico a b,
      HasDerivWithinAt L (r t * P t * (L t * (1 - L t))) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hLcont : ContinuousOn L (Icc a b)) (hGcont : ContinuousOn G (Icc a b))
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t) (hP : ∀ t ∈ Ico a b, α ≤ P t)
    (hunit : ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1) (hLa : L a = 1 / 2) :
    1 - L b ≤ Real.exp (-α * (G b - G a)) := by
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
  have hQa : Q a = 1 := by
    simp only [hQdef, hLa, sub_self, mul_zero, Real.exp_zero, mul_one]
    norm_num
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
  have hQb : Q b ≤ 1 := by
    have := hbound (right_mem_Icc.mpr hab)
    simpa [hQa] using this
  have hLb := hunit b (right_mem_Icc.mpr hab)
  have hexppos : 0 < Real.exp (α * (G b - G a)) := Real.exp_pos _
  have hodds_le : (1 - L b) / L b ≤ Real.exp (-α * (G b - G a)) := by
    have hQbval : (1 - L b) / L b * Real.exp (α * (G b - G a)) ≤ 1 := hQb
    rw [show (-α * (G b - G a)) = -(α * (G b - G a)) by ring, Real.exp_neg,
      inv_eq_one_div, le_div_iff₀ hexppos]
    exact hQb
  have hstep : 1 - L b ≤ (1 - L b) / L b := by
    rw [le_div_iff₀ hLb.1]
    nlinarith [hLb.1, hLb.2]
  linarith [hodds_le, hstep]

/-- Logistic sharpening, false view: with `P ≤ -α < 0`, the gate collapses:
`L b ≤ exp(-α·(G b - G a))`.  Assumes the unit invariant `0 < L < 1`. -/
theorem logistic_false_bound_assuming_unit
    {a b α : ℝ} {L r P G : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α)
    (hLder : ∀ t ∈ Ico a b,
      HasDerivWithinAt L (r t * P t * (L t * (1 - L t))) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hLcont : ContinuousOn L (Icc a b)) (hGcont : ContinuousOn G (Icc a b))
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t) (hP : ∀ t ∈ Ico a b, P t ≤ -α)
    (hunit : ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1) (hLa : L a = 1 / 2) :
    L b ≤ Real.exp (-α * (G b - G a)) := by
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
  have hQa : Q a = 1 := by
    simp only [hQdef, hLa, sub_self, mul_zero, Real.exp_zero, mul_one]
    norm_num
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
  have hQb : Q b ≤ 1 := by
    have := hbound (right_mem_Icc.mpr hab); simpa [hQa] using this
  have hLb := hunit b (right_mem_Icc.mpr hab)
  have hexppos : 0 < Real.exp (α * (G b - G a)) := Real.exp_pos _
  have hodds_le : L b / (1 - L b) ≤ Real.exp (-α * (G b - G a)) := by
    rw [show (-α * (G b - G a)) = -(α * (G b - G a)) by ring, Real.exp_neg,
      inv_eq_one_div, le_div_iff₀ hexppos]
    exact hQb
  have hstep : L b ≤ L b / (1 - L b) := by
    rw [le_div_iff₀ (by linarith [hLb.2] : (0:ℝ) < 1 - L b)]
    nlinarith [hLb.1, hLb.2]
  linarith [hodds_le, hstep]

open scoped BigOperators

/-- Branch-mixture error from one-hot selector weights. -/
theorem branch_mix_error {V : Type*} [Fintype V] [DecidableEq V]
    (vstar : V) (lam A : V → ℝ) {ε R : ℝ}
    (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hlam_nonneg : ∀ v, 0 ≤ lam v)
    (hlam_true_lo : 1 - ε ≤ lam vstar) (hlam_true_hi : lam vstar ≤ 1)
    (hlam_false : ∀ v, v ≠ vstar → lam v ≤ ε)
    (hA : ∀ v, |A v| ≤ R) :
    |(∑ v, lam v * A v) - A vstar| ≤ (Fintype.card V : ℝ) * R * ε := by
  have hsplit : (∑ v, lam v * A v) - A vstar
      = (lam vstar - 1) * A vstar
        + ∑ v ∈ Finset.univ.erase vstar, lam v * A v := by
    rw [← Finset.add_sum_erase _ (fun v => lam v * A v) (Finset.mem_univ vstar)]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(lam vstar - 1) * A vstar| ≤ ε * R := by
    rw [abs_mul]
    have hle : |lam vstar - 1| ≤ ε := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam vstar)]; linarith
    exact mul_le_mul hle (hA vstar) (abs_nonneg _) hε
  have hcard1 : ((Finset.univ.erase vstar).card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ vstar), Finset.card_univ]
    have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨vstar⟩
    push_cast [Nat.cast_sub this]; ring
  have h2 : |∑ v ∈ Finset.univ.erase vstar, lam v * A v|
      ≤ ((Fintype.card V : ℝ) - 1) * (R * ε) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbound : ∀ v ∈ Finset.univ.erase vstar, |lam v * A v| ≤ R * ε := by
      intro v hv
      have hvne : v ≠ vstar := (Finset.mem_erase.mp hv).1
      rw [abs_mul, abs_of_nonneg (hlam_nonneg v)]
      calc lam v * |A v| ≤ ε * R := mul_le_mul (hlam_false v hvne) (hA v) (abs_nonneg _) hε
        _ = R * ε := by ring
    calc ∑ v ∈ Finset.univ.erase vstar, |lam v * A v|
        ≤ ∑ _v ∈ Finset.univ.erase vstar, (R * ε) := Finset.sum_le_sum hbound
      _ = ((Finset.univ.erase vstar).card : ℝ) * (R * ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card V : ℝ) - 1) * (R * ε) := by rw [hcard1]
  nlinarith [h1, h2]

/-- Coarse margin from SEL1-style one-hot Bernstein bounds: `P_v := Lam v - 1/2`
gives margin `α = 1/2 - errSel > 0` (true ≥ α, false ≤ -α) when `errSel < 1/2`. -/
theorem coarse_margin_of_sel1 {V : Type*} (vstar : V) (Lam : V → ℝ) {errSel : ℝ}
    (herr : errSel < 1 / 2)
    (htrue : 1 - errSel ≤ Lam vstar)
    (hoff : ∀ v, v ≠ vstar → Lam v ≤ errSel) :
    (0 < 1 / 2 - errSel) ∧
      (1 / 2 - errSel ≤ Lam vstar - 1 / 2) ∧
      (∀ v, v ≠ vstar → Lam v - 1 / 2 ≤ -(1 / 2 - errSel)) :=
  ⟨by linarith, by linarith, fun v hv => by linarith [hoff v hv]⟩

/-- One gate phase produces one-hot selector weights: true view saturates to
`1 - e^{-α·ΔG}`, false views collapse to `e^{-α·ΔG}`. -/
theorem selector_phase_onehot {V : Type*} (vstar : V)
    {a b α : ℝ} {r G : ℝ → ℝ} {lam P : V → ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α)
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hGcont : ContinuousOn G (Icc a b))
    (hlamder : ∀ v, ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v) (r t * P v t * (lam v t * (1 - lam v t))) (Ici t) t)
    (hlamcont : ∀ v, ContinuousOn (lam v) (Icc a b))
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (hlama : ∀ v, lam v a = 1 / 2)
    (hPtrue : ∀ t ∈ Ico a b, α ≤ P vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α) :
    1 - lam vstar b ≤ Real.exp (-α * (G b - G a)) ∧
      ∀ v, v ≠ vstar → lam v b ≤ Real.exp (-α * (G b - G a)) := by
  refine ⟨logistic_true_bound_assuming_unit hab hα (hlamder vstar) hGder
      (hlamcont vstar) hGcont hr hPtrue (hunit vstar) (hlama vstar), ?_⟩
  intro v hv
  exact logistic_false_bound_assuming_unit hab hα (hlamder v) hGder
    (hlamcont v) hGcont hr (hPfalse v hv) (hunit v) (hlama v)

/-- Full clock-driven selector error: after one gate phase, the weighted branch
mixture is within `card·R·e^{-α·ΔG}` of the true branch value. -/
theorem selector_mix_error {V : Type*} [Fintype V] [DecidableEq V] (vstar : V)
    {a b α : ℝ} {r G : ℝ → ℝ} {lam P : V → ℝ → ℝ} {R : ℝ} (A : V → ℝ)
    (hab : a ≤ b) (hα : 0 < α) (hR : 0 ≤ R)
    (hr : ∀ t ∈ Ico a b, 0 ≤ r t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hGcont : ContinuousOn G (Icc a b))
    (hlamder : ∀ v, ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v) (r t * P v t * (lam v t * (1 - lam v t))) (Ici t) t)
    (hlamcont : ∀ v, ContinuousOn (lam v) (Icc a b))
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (hlama : ∀ v, lam v a = 1 / 2)
    (hPtrue : ∀ t ∈ Ico a b, α ≤ P vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α)
    (hA : ∀ v, |A v| ≤ R) :
    |(∑ v, lam v b * A v) - A vstar| ≤
      (Fintype.card V : ℝ) * R * Real.exp (-α * (G b - G a)) := by
  obtain ⟨htrue, hfalse⟩ := selector_phase_onehot vstar hab hα hr hGder hGcont
    hlamder hlamcont hunit hlama hPtrue hPfalse
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  exact branch_mix_error vstar (fun v => lam v b) A (Real.exp_pos _).le hR
    (fun v => (hunit v b hb).1.le)
    (by linarith [htrue]) (hunit vstar b hb).2.le hfalse hA

/-- A scalar function whose derivative is bounded by `K·|f|` cannot vanish on
`[a,b]` if it is nonzero at `a` (zero would propagate backward via Grönwall). -/
theorem no_zero_of_abs_deriv_le {f f' : ℝ → ℝ} {K a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Icc a b, |f' t| ≤ K * |f t|)
    (ha : f a ≠ 0) :
    ∀ t ∈ Icc a b, f t ≠ 0 := by
  intro t ht hft
  set g : ℝ → ℝ := fun u => f (a + t - u) with hg
  have hsub : ∀ u ∈ Icc a t, a + t - u ∈ Icc a b := by
    intro u hu
    exact ⟨by linarith [hu.2], by linarith [hu.1, ht.2]⟩
  have hgderAt : ∀ u ∈ Icc a t, HasDerivAt g (-f' (a + t - u)) u := by
    intro u hu
    have hφ : HasDerivAt (fun u => a + t - u) (-1) u := by
      simpa using (hasDerivAt_const u (a + t)).sub (hasDerivAt_id u)
    have hcomp := (hf (a + t - u) (hsub u hu)).comp u hφ
    simpa [g, Function.comp, mul_neg_one] using hcomp
  have hgcont : ContinuousOn g (Icc a t) :=
    fun u hu => (hgderAt u hu).continuousAt.continuousWithinAt
  have hga : g a = 0 := by simp [hg, hft]
  have hgbound : ∀ u ∈ Ico a t, |(-f' (a + t - u))| ≤ K * |g u| := by
    intro u hu
    have hmem := hsub u (Ico_subset_Icc_self hu)
    rw [abs_neg]
    simpa [hg] using hbound (a + t - u) hmem
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hgcont (fun u hu => (hgderAt u (Ico_subset_Icc_self hu)).hasDerivWithinAt) hga hgbound
  have : g t = 0 := hzero t (right_mem_Icc.mpr ht.1)
  simp [hg] at this
  exact ha this

/-- Unit-interval invariant for the logistic ODE `L' = A·L(1-L)` with `L a = 1/2`:
`L` stays in `(0,1)` on `[a,b]`. -/
theorem logistic_unit_interval_invariant {A L : ℝ → ℝ} {a b K0 K1 δ : ℝ} (hab : a ≤ b)
    (hLder : ∀ t ∈ Icc a b, HasDerivAt L (A t * (L t * (1 - L t))) t)
    (hcont : ContinuousOn L (Icc a b))
    (hK0 : ∀ t ∈ Icc a b, |A t * (1 - L t)| ≤ K0)
    (hK1 : ∀ t ∈ Icc a b, |A t * L t| ≤ K1)
    (hδ : δ < 1 / 2) (hLa : |L a - 1 / 2| ≤ δ) :
    ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1 := by
  have hLa_pos : 0 < L a := by have := (abs_le.mp hLa).1; linarith
  have hLa_lt1 : L a < 1 := by have := (abs_le.mp hLa).2; linarith
  -- L never zero
  have hLne : ∀ t ∈ Icc a b, L t ≠ 0 := by
    refine no_zero_of_abs_deriv_le (f := L) (f' := fun t => A t * (L t * (1 - L t)))
      (K := K0) hab hLder (fun t ht => ?_) hLa_pos.ne'
    simp only []
    rw [show A t * (L t * (1 - L t)) = (A t * (1 - L t)) * L t by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right (hK0 t ht) (abs_nonneg _)
  -- 1 - L never zero
  have hUne : ∀ t ∈ Icc a b, (1 - L t) ≠ 0 := by
    refine no_zero_of_abs_deriv_le (f := fun t => 1 - L t)
      (f' := fun t => -(A t * (L t * (1 - L t)))) (K := K1) hab
      (fun t ht => by simpa using (hLder t ht).const_sub 1)
      (fun t ht => ?_)
      (by show (1:ℝ) - L a ≠ 0; exact sub_ne_zero.mpr (ne_of_gt hLa_lt1))
    simp only []
    rw [abs_neg, show A t * (L t * (1 - L t)) = (A t * L t) * (1 - L t) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right (hK1 t ht) (abs_nonneg _)
  -- sign from continuity + L a = 1/2 > 0 and 1 - L a = 1/2 > 0
  intro t ht
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have hcross : ∃ s ∈ Icc a t, L s = 0 := by
      have := intermediate_value_Icc' ht.1 (hcont.mono (Icc_subset_Icc_right ht.2))
      have h0 : (0:ℝ) ∈ Icc (L t) (L a) := ⟨h, by linarith⟩
      obtain ⟨s, hs, hsv⟩ := this h0
      exact ⟨s, hs, hsv⟩
    obtain ⟨s, hs, hsv⟩ := hcross
    exact hLne s (Icc_subset_Icc_right ht.2 hs) hsv
  · by_contra h
    push_neg at h
    have hcross : ∃ s ∈ Icc a t, 1 - L s = 0 := by
      have hUcont : ContinuousOn (fun u => 1 - L u) (Icc a t) :=
        (continuousOn_const.sub hcont).mono (Icc_subset_Icc_right ht.2)
      have := intermediate_value_Icc' ht.1 hUcont
      have h0 : (0:ℝ) ∈ Icc (1 - L t) (1 - L a) := ⟨by linarith, by linarith⟩
      obtain ⟨s, hs, hsv⟩ := this h0
      exact ⟨s, hs, hsv⟩
    obtain ⟨s, hs, hsv⟩ := hcross
    exact hUne s (Icc_subset_Icc_right ht.2 hs) hsv

/-- Budget met: the clock-driven selector per-step error drops below `e^{-μ}` once
the integrated gain satisfies `α·ΔG ≥ log(card·R) + μ`.  This is exactly what a
fixed-degree polynomial selector cannot achieve — here `ΔG = G b - G a` grows with
the phase clock, so the error → 0 while the field stays polynomial. -/
theorem per_step_error_le_exp_of_mix {V : Type*} [Fintype V]
    {x R α μ ΔG : ℝ}
    (hmix : x ≤ (Fintype.card V : ℝ) * R * Real.exp (-α * ΔG))
    (hcardR : 0 < (Fintype.card V : ℝ) * R)
    (hgain : Real.log ((Fintype.card V : ℝ) * R) + μ ≤ α * ΔG) :
    x ≤ Real.exp (-μ) := by
  calc x ≤ (Fintype.card V : ℝ) * R * Real.exp (-α * ΔG) := hmix
    _ = Real.exp (Real.log ((Fintype.card V : ℝ) * R) + (-α * ΔG)) := by
        rw [Real.exp_add, Real.exp_log hcardR]
    _ ≤ Real.exp (-μ) := Real.exp_le_exp.mpr (by linarith)

end Ripple.BoundedUniversality.BGP

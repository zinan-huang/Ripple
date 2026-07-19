/-
  Ripple.Number.EulerGamma — γ (Euler-Mascheroni constant) is real-time CRN-computable

  Theorem 3.3.4 from Huang's PhD thesis (Iowa State, 2020):

  Key identity: γ = 1 - Γ'(2), where Γ is the Gamma function.
  This follows from ψ(1) = -γ (digamma at 1) and the recurrence Γ(x+1) = xΓ(x).

  Γ'(2) = e⁻¹(α + β), where:
    α = ∫₀¹ eˢ(1-s)log(1-s) ds     (< 0, computed via time change s = 1-e^{-t})
    β = ∫₀^∞ e⁻ˢ(1+s)log(1+s) ds   (> 0, computed directly)

  Both integrals are computed by bounded PIVPs with integer initial conditions.

  The 8-variable PIVP system:
    f' = w             (f → β)
    g' = -pqv          (g → α)
    w' = -w + u + v    (w = e^{-t}(1+t)log(1+t))
    u' = -u + rv       (u = e^{-t}log(1+t))
    v' = -v            (v = e^{-t})
    r' = -r²           (r = 1/(1+t))
    p' = pv            (p = e^{1-e^{-t}})
    q' = v - q         (q = te^{-t})

  ICs: f(0) = g(0) = u(0) = w(0) = q(0) = 0, v(0) = r(0) = p(0) = 1.

  Then γ = 1 - (α + β)/e by field closure over ℝ_RTCRN.
-/

import Ripple.Core.BoundedTime
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace Ripple.Number

open Real

/-! ## The identity γ = 1 - Γ'(2) -/

/-- γ = 1 - Γ'(2). This is the starting point for our PIVP construction.
  Proof: Mathlib gives deriv Gamma 2 = 1! * (-γ + H₁) = 1 - γ. -/
theorem gamma_eq_one_sub_deriv_Gamma_two :
    eulerMascheroniConstant = 1 - deriv Gamma 2 := by
  have h := deriv_Gamma_nat 1
  -- h : deriv Gamma (↑1 + 1) = ↑1! * (-eulerMascheroniConstant + ↑(harmonic 1))
  simp only [Nat.factorial, harmonic_succ, harmonic_zero, Nat.cast_one] at h
  -- h should now have deriv Gamma (1 + 1) = ... but 1+1 may not be 2 yet
  norm_num at h
  -- h : deriv Gamma 2 = 1 - eulerMascheroniConstant (or similar)
  linarith

/-! ## The 8-variable PIVP -/

/-- The PIVP computing the two integrals α and β for Euler's γ.
  Dimension 8, outputs at components 0 (f → β) and 1 (g → α). -/
noncomputable def gammaPIVP : Ripple.PIVP 8 where
  field := fun y => ![
    y 2,                          -- f' = w
    - y 6 * y 7 * y 4,           -- g' = -pqv
    - y 2 + y 3 + y 4,           -- w' = -w + u + v
    - y 3 + y 5 * y 4,           -- u' = -u + rv
    - y 4,                        -- v' = -v
    - y 5 ^ 2,                    -- r' = -r²
    y 6 * y 4,                    -- p' = pv
    y 4 - y 7                     -- q' = v - q
  ]
  init := ![0, 0, 0, 0, 1, 1, 1, 0]
  output := 0  -- will combine f and g via field closure

/-! ## Closed-form solutions for auxiliary variables

  These are the 6 auxiliary variables whose closed forms don't involve integrals.
  Variables f (index 0) and g (index 1) are antiderivatives.
-/

/-- r(t) = 1/(1+t): harmonic decay. Satisfies r' = -r². -/
noncomputable def gammaR (t : ℝ) : ℝ := 1 / (1 + t)

theorem gammaR_init : gammaR 0 = 1 := by
  unfold gammaR; norm_num

theorem gammaR_pos {t : ℝ} (ht : 0 ≤ t) : 0 < gammaR t := by
  unfold gammaR; positivity

theorem gammaR_le_one {t : ℝ} (ht : 0 ≤ t) : gammaR t ≤ 1 := by
  unfold gammaR
  exact div_le_one_of_le₀ (by linarith) (by linarith)

/-- p(t) = e^{1-e^{-t}}: same as Euler PIVP component y₁. Approaches e. -/
noncomputable def gammaP (t : ℝ) : ℝ := exp (1 - exp (-t))

theorem gammaP_init : gammaP 0 = 1 := by
  unfold gammaP; simp [exp_zero]

theorem gammaP_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ gammaP t := by
  unfold gammaP
  have hle : exp (-t) ≤ 1 := by
    rw [← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)
  calc (1:ℝ) = exp 0 := exp_zero.symm
    _ ≤ exp (1 - exp (-t)) := exp_le_exp.mpr (by linarith)

theorem gammaP_le_e {t : ℝ} : gammaP t ≤ exp 1 := by
  unfold gammaP
  exact exp_le_exp.mpr (by linarith [exp_pos (-t)])

/-- q(t) = te^{-t}: satisfies q' = v - q = e^{-t} - te^{-t}. Peak at t=1. -/
noncomputable def gammaQ (t : ℝ) : ℝ := t * exp (-t)

theorem gammaQ_init : gammaQ 0 = 0 := by
  unfold gammaQ; simp

theorem gammaQ_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gammaQ t := by
  unfold gammaQ
  exact mul_nonneg ht (le_of_lt (exp_pos _))

/-- q(t) ≤ 1/e for all t ≥ 0. Maximum at t = 1 where q(1) = e⁻¹.
  Proof: from e^x ≥ 1+x applied to x = t-1, we get t ≤ e^{t-1}. -/
theorem gammaQ_le_inv_e {t : ℝ} (_ht : 0 ≤ t) : gammaQ t ≤ exp (-1) := by
  unfold gammaQ
  have key : t ≤ exp (t - 1) := by linarith [add_one_le_exp (t - 1)]
  calc t * exp (-t)
      ≤ exp (t - 1) * exp (-t) :=
        mul_le_mul_of_nonneg_right key (le_of_lt (exp_pos _))
    _ = exp (-1) := by rw [← exp_add]; ring_nf

/-- u(t) = e^{-t}·log(1+t): satisfies u' = -u + rv. -/
noncomputable def gammaU (t : ℝ) : ℝ := exp (-t) * log (1 + t)

theorem gammaU_init : gammaU 0 = 0 := by
  unfold gammaU; simp [exp_zero]

theorem gammaU_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gammaU t := by
  unfold gammaU
  exact mul_nonneg (le_of_lt (exp_pos _)) (log_nonneg (by linarith))

/-- u(t) ≤ 1/e for t ≥ 0. Uses log(1+t) ≤ t and te^{-t} ≤ e^{-1}. -/
theorem gammaU_bounded {t : ℝ} (ht : 0 ≤ t) : gammaU t ≤ exp (-1) := by
  unfold gammaU
  calc exp (-t) * log (1 + t)
      ≤ exp (-t) * t := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (exp_pos _))
        linarith [log_le_sub_one_of_pos (show (0:ℝ) < 1 + t by linarith)]
    _ = gammaQ t := by unfold gammaQ; ring
    _ ≤ exp (-1) := gammaQ_le_inv_e ht

/-- w(t) = e^{-t}·(1+t)·log(1+t): the integrand for β. -/
noncomputable def gammaW (t : ℝ) : ℝ := exp (-t) * (1 + t) * log (1 + t)

theorem gammaW_init : gammaW 0 = 0 := by
  unfold gammaW; simp [exp_zero]

theorem gammaW_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gammaW t := by
  unfold gammaW
  exact mul_nonneg (mul_nonneg (le_of_lt (exp_pos _)) (by linarith)) (log_nonneg (by linarith))

/-- w(t) ≤ 4 for all t ≥ 0.
  Proof: w ≤ e^{-t}(1+t)² via log(1+t) ≤ t ≤ 1+t.
  Then (1+t)²e^{-t} ≤ 4 since e^{t/2} ≥ 1+t/2, squaring gives e^t ≥ (1+t)²/4. -/
theorem gammaW_bounded {t : ℝ} (ht : 0 ≤ t) : gammaW t ≤ 4 := by
  unfold gammaW
  have h1t : (0:ℝ) ≤ 1 + t := by linarith
  -- Step 1: log(1+t) ≤ t ≤ 1+t, so w ≤ (1+t)²·e^{-t}
  have hlog : log (1 + t) ≤ 1 + t := by
    linarith [log_le_sub_one_of_pos (show (0:ℝ) < 1 + t by linarith)]
  have hw : exp (-t) * (1 + t) * log (1 + t) ≤ (1 + t) ^ 2 * exp (-t) := by
    calc exp (-t) * (1 + t) * log (1 + t)
        ≤ exp (-t) * (1 + t) * (1 + t) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg (le_of_lt (exp_pos _)) h1t)
      _ = (1 + t) ^ 2 * exp (-t) := by ring
  -- Step 2: e^{t/2} ≥ 1+t/2, so e^t ≥ (1+t/2)² ≥ (1+t)²/4
  have h_half : 1 + t / 2 ≤ exp (t / 2) := by linarith [add_one_le_exp (t / 2)]
  have h_sq : (1 + t / 2) ^ 2 ≤ exp t := by
    calc (1 + t / 2) ^ 2
        ≤ exp (t / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h_half 2
      _ = exp t := by rw [sq, ← exp_add]; ring_nf
  -- (1+t)²/4 ≤ (1+t/2)² for t ≥ 0, so (1+t)² ≤ 4·e^t
  have h4 : (1 + t) ^ 2 ≤ 4 * exp t := by nlinarith
  -- Therefore (1+t)²·e^{-t} ≤ 4
  have h_bound : (1 + t) ^ 2 * exp (-t) ≤ 4 := by
    have h5 : (1 + t) ^ 2 * exp (-t) ≤ 4 * exp t * exp (-t) :=
      mul_le_mul_of_nonneg_right h4 (le_of_lt (exp_pos _))
    have h6 : exp t * exp (-t) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    linarith
  linarith

/-! ## The two antiderivative variables -/

open MeasureTheory intervalIntegral

/-- f(t) = ∫₀ᵗ w(s) ds: antiderivative of w, converges to β.
  In the PIVP: f' = w, f(0) = 0. -/
noncomputable def gammaF (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, gammaW s

theorem gammaF_init : gammaF 0 = 0 := by
  unfold gammaF; simp [intervalIntegral.integral_same]

/-- g(t) = -∫₀ᵗ p(s)·q(s)·v(s) ds: converges to α.
  In the PIVP: g' = -p·q·v, g(0) = 0.
  The integrand is e^{1-e^{-s}} · s·e^{-s} · e^{-s} = s·e^{1-e^{-s}-2s}. -/
noncomputable def gammaG (t : ℝ) : ℝ :=
  -(∫ s in (0:ℝ)..t, gammaP s * gammaQ s * exp (-s))

theorem gammaG_init : gammaG 0 = 0 := by
  unfold gammaG; simp [intervalIntegral.integral_same]

/-! ## Boundedness of f and g -/

/-- The integrand of f is nonneg for t ≥ 0. -/
theorem gammaW_integrand_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gammaW t :=
  gammaW_nonneg ht

/-- f(t) ≥ 0 for t ≥ 0 (integral of nonneg function). -/
theorem gammaF_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gammaF t := by
  unfold gammaF
  exact intervalIntegral.integral_nonneg ht (fun s hs => gammaW_nonneg hs.1)

/-- The integrand of g is nonneg for t ≥ 0 (so g(t) ≤ 0). -/
theorem gammaG_integrand_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gammaP t * gammaQ t * exp (-t) := by
  unfold gammaP gammaQ
  apply mul_nonneg
  · apply mul_nonneg
    · exact le_of_lt (exp_pos _)
    · exact mul_nonneg ht (le_of_lt (exp_pos _))
  · exact le_of_lt (exp_pos _)

/-- g(t) ≤ 0 for t ≥ 0 (negative of integral of nonneg function). -/
theorem gammaG_nonpos {t : ℝ} (ht : 0 ≤ t) : gammaG t ≤ 0 := by
  unfold gammaG
  simp only [neg_nonpos]
  exact intervalIntegral.integral_nonneg ht
    (fun s hs => gammaG_integrand_nonneg hs.1)

/-! ## Tail decay bounds

  The convergence rate of f(t) → β and g(t) → α determines the time modulus.
  Key bounds:
  - w(s) ≤ (1+s)²e^{-s} ≤ 16·e^{-s/2}, so ∫ₜ^∞ w(s)ds ≤ 32·e^{-t/2}
  - p(s)·q(s)·v(s) ≤ e·s·e^{-2s}, so ∫ₜ^∞ p·q·v ds ≤ (e/4)·(2t+1)·e^{-2t}
  Both tails decay exponentially, giving linear time moduli.
-/

/-- β := lim_{t→∞} f(t) = ∫₀^∞ w(s) ds.
  This is one of the two integrals in the Karatsuba decomposition of Γ'(2). -/
noncomputable def gammaBeta : ℝ := ∫ s in Set.Ioi (0:ℝ), gammaW s

/-- α := lim_{t→∞} g(t) = -∫₀^∞ p(s)·q(s)·v(s) ds.
  This is the other integral in the Karatsuba decomposition. -/
noncomputable def gammaAlpha : ℝ :=
  -(∫ s in Set.Ioi (0:ℝ), gammaP s * gammaQ s * exp (-s))

/-- w(s) ≤ 16·e^{-s/2} for s ≥ 0.
  Proof: w ≤ (1+s)²e^{-s} and (1+s)² ≤ 16·e^{s/2}
  (from 1+s ≤ 4(1+s/4) and (1+s/4)² ≤ e^{s/2} via add_one_le_exp). -/
theorem gammaW_exp_decay {s : ℝ} (hs : 0 ≤ s) :
    gammaW s ≤ 16 * exp (-(s / 2)) := by
  unfold gammaW
  -- w(s) = e^{-s}(1+s)log(1+s) ≤ e^{-s}(1+s)² ≤ 16·e^{-s/2}
  have hlog : log (1 + s) ≤ 1 + s := by
    linarith [log_le_sub_one_of_pos (show (0:ℝ) < 1 + s by linarith)]
  have h1s : (0:ℝ) ≤ 1 + s := by linarith
  -- First: w(s) ≤ (1+s)²·e^{-s}
  have hw : exp (-s) * (1 + s) * log (1 + s) ≤ (1 + s) ^ 2 * exp (-s) := by
    calc exp (-s) * (1 + s) * log (1 + s)
        ≤ exp (-s) * (1 + s) * (1 + s) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg (le_of_lt (exp_pos _)) h1s)
      _ = (1 + s) ^ 2 * exp (-s) := by ring
  -- Second: (1+s)² ≤ 16·e^{s/2}
  -- From add_one_le_exp: 1+s/4 ≤ e^{s/4}, so (1+s/4)² ≤ e^{s/2}
  -- And (1+s) ≤ 4(1+s/4), so (1+s)² ≤ 16(1+s/4)² ≤ 16e^{s/2}
  have h_quarter : 1 + s / 4 ≤ exp (s / 4) := by linarith [add_one_le_exp (s / 4)]
  have h_sq_exp : (1 + s / 4) ^ 2 ≤ exp (s / 2) := by
    calc (1 + s / 4) ^ 2 ≤ exp (s / 4) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h_quarter 2
      _ = exp (s / 2) := by rw [sq, ← exp_add]; ring_nf
  have h_16 : (1 + s) ^ 2 ≤ 16 * exp (s / 2) := by nlinarith
  -- Combine: w ≤ (1+s)²e^{-s} ≤ 16e^{s/2}·e^{-s} = 16e^{-s/2}
  calc exp (-s) * (1 + s) * log (1 + s)
      ≤ (1 + s) ^ 2 * exp (-s) := hw
    _ ≤ 16 * exp (s / 2) * exp (-s) := by
        apply mul_le_mul_of_nonneg_right h_16 (le_of_lt (exp_pos _))
    _ = 16 * exp (-(s / 2)) := by
        rw [show 16 * exp (s / 2) * exp (-s) = 16 * (exp (s / 2) * exp (-s)) from by ring,
            ← exp_add]; ring_nf

-- Helper: ∫ₜ^∞ exp((-1/2)·s) ds = 2·exp(-t/2)
private theorem integral_exp_neg_half_Ioi (t : ℝ) :
    ∫ s in Set.Ioi t, exp ((-1/2 : ℝ) * s) = 2 * exp (-(t / 2)) := by
  rw [integral_exp_mul_Ioi (by norm_num : (-1:ℝ)/2 < 0) t]
  field_simp

/-- gammaW is integrable on (0, ∞). Uses w(s) = O(e^{-s/2}) at ∞. -/
theorem gammaW_integrableOn : IntegrableOn gammaW (Set.Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num : (0:ℝ) < 1/2)
  · unfold gammaW
    apply ContinuousOn.mul
    · exact (continuous_exp.comp continuous_neg |>.mul
        (continuous_const.add continuous_id)).continuousOn
    · apply Real.continuousOn_log.comp
        (continuous_const.add continuous_id).continuousOn
      intro s hs
      exact ne_of_gt (by linarith [hs.out] : (0:ℝ) < 1 + s)
  · apply Asymptotics.IsBigO.of_bound 16
    filter_upwards [Filter.Ici_mem_atTop (0:ℝ)] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaW_nonneg hs),
        Real.norm_eq_abs, abs_of_nonneg (le_of_lt (exp_pos _))]
    have hdecay := gammaW_exp_decay hs
    have h : (-(1 / 2) : ℝ) * s = -(s / 2) := by ring
    simp only [h]; exact hdecay

/-- Integrability of comparison function 16·e^{-s/2} on (0, ∞). -/
private theorem hint_16_exp_integrableOn :
    IntegrableOn (fun s => 16 * exp (-(s / 2))) (Set.Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num : (0:ℝ) < 1/4)
  · exact (continuous_const.mul
      (continuous_exp.comp (continuous_id.div_const 2 |>.neg))).continuousOn
  · apply Asymptotics.IsBigO.of_bound 16
    filter_upwards [Filter.Ici_mem_atTop (0:ℝ)] with s hs
    rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt (exp_pos _))),
        Real.norm_eq_abs, abs_of_nonneg (le_of_lt (exp_pos _))]
    calc 16 * exp (-(s / 2))
        = 16 * (exp (-(s / 4)) * exp (-(s / 4))) := by
          rw [← exp_add]; ring_nf
      _ ≤ 16 * (1 * exp (-(s / 4))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (exp_pos _))
          rw [← exp_zero]
          exact exp_le_exp.mpr (by linarith [Set.mem_Ici.mp hs])
      _ = 16 * exp (-(1 / 4) * s) := by ring_nf

/-- f(t) ≤ β ≤ 32 for t ≥ 0. -/
theorem gammaF_bounded {t : ℝ} (ht : 0 ≤ t) : gammaF t ≤ 32 := by
  have hintw := gammaW_integrableOn
  have hintw_t : IntegrableOn gammaW (Set.Ioi t) :=
    hintw.mono_set (Set.Ioi_subset_Ioi ht)
  have hsplit := integral_interval_add_Ioi hintw hintw_t
  have htail_nn : 0 ≤ ∫ s in Set.Ioi t, gammaW s :=
    setIntegral_nonneg measurableSet_Ioi
      (fun s hs => gammaW_nonneg
        (le_of_lt (lt_of_le_of_lt ht (Set.mem_Ioi.mp hs))))
  have hle : gammaF t ≤ gammaBeta := by unfold gammaF gammaBeta; linarith
  have hbeta : gammaBeta ≤ 32 := by
    unfold gammaBeta
    calc ∫ s in Set.Ioi 0, gammaW s
        ≤ ∫ s in Set.Ioi 0, 16 * exp (-(s / 2)) :=
          setIntegral_mono_on hintw hint_16_exp_integrableOn
            measurableSet_Ioi
            (fun s hs => gammaW_exp_decay
              (le_of_lt (Set.mem_Ioi.mp hs)))
      _ = 16 * ∫ s in Set.Ioi 0, exp (-(s / 2)) := by
          rw [MeasureTheory.integral_const_mul]
      _ = 16 * (2 * exp 0) := by
          congr 1
          trans ∫ s in Set.Ioi 0, exp ((-1 / 2 : ℝ) * s)
          · exact setIntegral_congr_fun measurableSet_Ioi
              (fun s _ => by congr 1; ring)
          · rw [integral_exp_neg_half_Ioi]; simp
      _ = 32 := by rw [exp_zero]; norm_num
  linarith

/-- Tail bound for f: the tail integral ∫ₜ^∞ w(s) ds ≤ 32·e^{-t/2}. -/
theorem gammaF_tail_bound {t : ℝ} (ht : 0 ≤ t) :
    |gammaF t - gammaBeta| ≤ 32 * exp (-(t / 2)) := by
  unfold gammaF gammaBeta
  have hintw := gammaW_integrableOn
  -- IntegrableOn gammaW (Ioi t) from Ioi t ⊆ Ioi 0
  have hintw_t : IntegrableOn gammaW (Set.Ioi t) :=
    hintw.mono_set (Set.Ioi_subset_Ioi ht)
  -- Splitting: ∫₀ᵗ w + ∫ₜ^∞ w = ∫₀^∞ w
  have hsplit := integral_interval_add_Ioi hintw hintw_t
  -- So ∫₀ᵗ w - ∫₀^∞ w = -(∫ₜ^∞ w)
  have hdiff : (∫ s in (0:ℝ)..t, gammaW s) - (∫ s in Set.Ioi 0, gammaW s) =
      -(∫ s in Set.Ioi t, gammaW s) := by linarith
  -- Tail integral is nonneg (w ≥ 0)
  have htail_nn : 0 ≤ ∫ s in Set.Ioi t, gammaW s :=
    setIntegral_nonneg measurableSet_Ioi
      (fun s hs => gammaW_nonneg (le_of_lt (lt_of_le_of_lt ht (Set.mem_Ioi.mp hs))))
  -- |gammaF t - gammaBeta| = ∫ₜ^∞ w
  rw [hdiff, abs_neg, abs_of_nonneg htail_nn]
  -- Bound using ∫ₜ^∞ 16·exp(-s/2) = 32·exp(-t/2)
  -- Step 1: Integrability of comparison function on Ioi 0
  have hint_comp : IntegrableOn (fun s => 16 * exp (-(s / 2))) (Set.Ioi 0) := by
    apply integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num : (0:ℝ) < 1/4)
    · exact (continuous_const.mul
        (continuous_exp.comp (continuous_id.div_const 2 |>.neg))).continuousOn
    · apply Asymptotics.IsBigO.of_bound 16
      filter_upwards [Filter.Ici_mem_atTop (0:ℝ)] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt (exp_pos _))),
          Real.norm_eq_abs, abs_of_nonneg (le_of_lt (exp_pos _))]
      calc 16 * exp (-(s / 2))
          = 16 * (exp (-(s / 4)) * exp (-(s / 4))) := by
            rw [← exp_add]; ring_nf
        _ ≤ 16 * (1 * exp (-(s / 4))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (exp_pos _))
            rw [← exp_zero]; exact exp_le_exp.mpr (by linarith [Set.mem_Ici.mp hs])
        _ = 16 * exp (-(1 / 4) * s) := by ring_nf
  have hint_comp_t : IntegrableOn (fun s => 16 * exp (-(s / 2))) (Set.Ioi t) :=
    hint_comp.mono_set (Set.Ioi_subset_Ioi ht)
  -- Step 2: ∫ₜ^∞ w ≤ ∫ₜ^∞ 16·exp(-s/2) by pointwise bound
  calc ∫ s in Set.Ioi t, gammaW s
      ≤ ∫ s in Set.Ioi t, 16 * exp (-(s / 2)) :=
        setIntegral_mono_on hintw_t hint_comp_t measurableSet_Ioi
          (fun s hs => gammaW_exp_decay
            (le_of_lt (lt_of_le_of_lt ht (Set.mem_Ioi.mp hs))))
    _ = 16 * ∫ s in Set.Ioi t, exp (-(s / 2)) := by
        rw [MeasureTheory.integral_const_mul]
    _ = 16 * (2 * exp (-(t / 2))) := by
        congr 1
        trans ∫ s in Set.Ioi t, exp ((-1 / 2 : ℝ) * s)
        · exact setIntegral_congr_fun measurableSet_Ioi
            (fun s _ => by show exp (-(s / 2)) = exp ((-1 / 2 : ℝ) * s); congr 1; ring)
        · exact integral_exp_neg_half_Ioi t
    _ = 32 * exp (-(t / 2)) := by ring

/-- The integrand p(s)·q(s)·exp(-s) ≤ exp(-s) for s ≥ 0.
  Since p ≤ e and q ≤ 1/e, we have p·q ≤ 1. -/
private theorem gammaG_integrand_bound {s : ℝ} (hs : 0 ≤ s) :
    gammaP s * gammaQ s * exp (-s) ≤ exp (-s) := by
  have hpq : gammaP s * gammaQ s ≤ 1 := by
    calc gammaP s * gammaQ s
        ≤ exp 1 * exp (-1) :=
          mul_le_mul gammaP_le_e (gammaQ_le_inv_e hs)
            (gammaQ_nonneg hs) (le_of_lt (exp_pos _))
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc gammaP s * gammaQ s * exp (-s)
      ≤ 1 * exp (-s) :=
        mul_le_mul_of_nonneg_right hpq (le_of_lt (exp_pos _))
    _ = exp (-s) := one_mul _

/-- The integrand of g is integrable on (0, ∞). -/
theorem gammaG_integrableOn :
    IntegrableOn (fun s => gammaP s * gammaQ s * exp (-s)) (Set.Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (continuous_exp.comp
            (continuous_const.sub (continuous_exp.comp continuous_neg))).continuousOn
      · exact (continuous_id.mul (continuous_exp.comp continuous_neg)).continuousOn
    · exact (continuous_exp.comp continuous_neg).continuousOn
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.Ici_mem_atTop (0:ℝ)] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaG_integrand_nonneg hs),
        Real.norm_eq_abs, abs_of_nonneg (le_of_lt (exp_pos _)), one_mul]
    calc gammaP s * gammaQ s * exp (-s)
        ≤ exp (-s) := gammaG_integrand_bound hs
      _ ≤ exp (-(1 / 2) * s) :=
          exp_le_exp.mpr (by have := Set.mem_Ici.mp hs; linarith)

-- Helper: ∫ₜ^∞ exp(-s) ds = exp(-t)
private theorem integral_exp_neg_Ioi (t : ℝ) :
    ∫ s in Set.Ioi t, exp (-s) = exp (-t) := by
  trans ∫ s in Set.Ioi t, exp ((-1 : ℝ) * s)
  · exact setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by show exp (-s) = exp ((-1 : ℝ) * s); congr 1; ring)
  · rw [integral_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) t, neg_one_mul]
    field_simp

-- Integrability of exp(-s) on (0, ∞)
private theorem exp_neg_integrableOn :
    IntegrableOn (fun s => exp (-s)) (Set.Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num : (0:ℝ) < 1/2)
  · exact (continuous_exp.comp continuous_neg).continuousOn
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.Ici_mem_atTop (0:ℝ)] with s hs
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (exp_pos _)), one_mul]
    exact exp_le_exp.mpr (by have := Set.mem_Ici.mp hs; linarith)

/-- Tail bound for g: |g(t) - α| ≤ e^{-t}.
  Proof: p·q ≤ 1 so integrand ≤ exp(-s), then ∫ₜ^∞ exp(-s) = exp(-t). -/
theorem gammaG_tail_bound {t : ℝ} (ht : 0 ≤ t) :
    |gammaG t - gammaAlpha| ≤ exp (-t) := by
  have hinth := gammaG_integrableOn
  have hinth_t : IntegrableOn (fun s => gammaP s * gammaQ s * exp (-s)) (Set.Ioi t) :=
    hinth.mono_set (Set.Ioi_subset_Ioi ht)
  have hsplit := integral_interval_add_Ioi hinth hinth_t
  -- Tail integral is nonneg
  have htail_nn : 0 ≤ ∫ s in Set.Ioi t, gammaP s * gammaQ s * exp (-s) :=
    setIntegral_nonneg measurableSet_Ioi
      (fun s hs => gammaG_integrand_nonneg
        (le_of_lt (lt_of_le_of_lt ht (Set.mem_Ioi.mp hs))))
  -- gammaG t - gammaAlpha = tail integral
  have hdiff : gammaG t - gammaAlpha =
      ∫ s in Set.Ioi t, gammaP s * gammaQ s * exp (-s) := by
    unfold gammaG gammaAlpha; linarith
  rw [hdiff, abs_of_nonneg htail_nn]
  -- Comparison: integrand ≤ exp(-s), then compute ∫ₜ^∞ exp(-s) = exp(-t)
  have hexp_int_t : IntegrableOn (fun s => exp (-s)) (Set.Ioi t) :=
    exp_neg_integrableOn.mono_set (Set.Ioi_subset_Ioi ht)
  calc ∫ s in Set.Ioi t, gammaP s * gammaQ s * exp (-s)
      ≤ ∫ s in Set.Ioi t, exp (-s) :=
        setIntegral_mono_on hinth_t hexp_int_t measurableSet_Ioi
          (fun s hs => gammaG_integrand_bound
            (le_of_lt (lt_of_le_of_lt ht (Set.mem_Ioi.mp hs))))
    _ = exp (-t) := integral_exp_neg_Ioi t

/-! ## 8-component solution and ODE proof -/

/-- The 8-component closed-form solution of gammaPIVP. -/
noncomputable def gammaSolution : ℝ → Fin 8 → ℝ :=
  fun t => ![gammaF t, gammaG t, gammaW t, gammaU t, exp (-t), gammaR t, gammaP t, gammaQ t]

theorem gammaSolution_init : gammaSolution 0 = gammaPIVP.init := by
  ext i; fin_cases i <;>
    simp [gammaSolution, gammaPIVP, gammaF_init, gammaG_init, gammaW_init,
      gammaU_init, exp_zero, gammaR_init, gammaP_init, gammaQ_init]

/-- gammaW is continuous on all of ℝ (using x·log(x) → 0 continuity). -/
private theorem gammaW_continuous : Continuous gammaW := by
  have h : gammaW = fun t => exp (-t) * ((1 + t) * log (1 + t)) := funext fun t => by
    unfold gammaW; ring
  exact h ▸ (continuous_exp.comp continuous_neg).mul
    (continuous_mul_log.comp (continuous_const.add continuous_id))

/-- The gammaG integrand (p·q·v) is continuous on all of ℝ. -/
private theorem gammaG_integrand_continuous :
    Continuous (fun s => gammaP s * gammaQ s * exp (-s)) := by
  unfold gammaP gammaQ
  exact ((continuous_exp.comp
      (continuous_const.sub (continuous_exp.comp continuous_neg))).mul
    (continuous_id.mul (continuous_exp.comp continuous_neg))).mul
    (continuous_exp.comp continuous_neg)

/-- exp(1) ≤ 4, for bounding gammaP in the solution. -/
private theorem exp_one_le_four : exp (1:ℝ) ≤ 4 := by
  have h12 : (1:ℝ)/2 ≤ exp ((-1:ℝ)/2) := by linarith [add_one_le_exp ((-1:ℝ)/2)]
  have h14 : (1:ℝ)/4 ≤ exp (-1:ℝ) := by
    calc (1:ℝ)/4 = (1/2) ^ 2 := by norm_num
      _ ≤ exp ((-1:ℝ)/2) ^ 2 := pow_le_pow_left₀ (by norm_num) h12 2
      _ = exp (-1:ℝ) := by rw [← exp_nat_mul]; norm_num
  have h_prod : exp (1:ℝ) * exp (-1:ℝ) = 1 := by rw [← exp_add]; norm_num
  nlinarith [exp_pos (1:ℝ)]

/-- The 8-component solution satisfies the ODE for t ≥ 0. -/
theorem gammaSolution_is_solution (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt gammaSolution (gammaPIVP.field (gammaSolution t)) t := by
  have hfield : gammaPIVP.field (gammaSolution t) =
      ![gammaW t, -(gammaP t * gammaQ t * exp (-t)),
        -gammaW t + gammaU t + exp (-t), -gammaU t + gammaR t * exp (-t),
        -exp (-t), -gammaR t ^ 2,
        gammaP t * exp (-t), exp (-t) - gammaQ t] := by
    ext i; fin_cases i <;> simp [gammaPIVP, gammaSolution] <;> ring
  rw [hfield, hasDerivAt_pi]
  have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
    simpa [id] using (hasDerivAt_id t).neg
  have h_exp_neg := h_neg.exp
  have h1t_pos : (0:ℝ) < 1 + t := by linarith
  have h1t_ne : (1:ℝ) + t ≠ 0 := ne_of_gt h1t_pos
  have h_1t := (hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)
  have h_log := h_1t.log h1t_ne
  intro i; fin_cases i
  · -- Component 0: d/dt gammaF = gammaW (FTC)
    change HasDerivAt (fun s => gammaF s) (gammaW t) t
    unfold gammaF
    exact integral_hasDerivAt_right
      (gammaW_continuous.intervalIntegrable 0 t)
      (gammaW_continuous.stronglyMeasurableAtFilter _ _)
      gammaW_continuous.continuousAt
  · -- Component 1: d/dt gammaG = -p·q·v (FTC + neg)
    change HasDerivAt (fun s => gammaG s) (-(gammaP t * gammaQ t * exp (-t))) t
    unfold gammaG
    exact (integral_hasDerivAt_right
      (gammaG_integrand_continuous.intervalIntegrable 0 t)
      (gammaG_integrand_continuous.stronglyMeasurableAtFilter _ _)
      gammaG_integrand_continuous.continuousAt).neg
  · -- Component 2: d/dt gammaW = -w + u + v
    change HasDerivAt (fun s => exp (-s) * (1 + s) * log (1 + s))
      (-gammaW t + gammaU t + exp (-t)) t
    refine ((h_exp_neg.mul h_1t).mul h_log).congr_deriv ?_
    unfold gammaW gammaU
    simp only [Pi.mul_apply, Pi.add_apply, id]
    field_simp
    ring
  · -- Component 3: d/dt gammaU = -u + r·v
    change HasDerivAt (fun s => exp (-s) * log (1 + s))
      (-gammaU t + gammaR t * exp (-t)) t
    refine (h_exp_neg.mul h_log).congr_deriv ?_
    unfold gammaU gammaR
    simp only [Pi.add_apply, id]
    field_simp
    ring
  · -- Component 4: d/dt exp(-t) = -exp(-t)
    change HasDerivAt (fun s => exp (-s)) (-exp (-t)) t
    have h4 := h_exp_neg
    rwa [show rexp (-t) * -1 = -rexp (-t) from by ring] at h4
  · -- Component 5: d/dt (1/(1+t)) = -(1/(1+t))²
    change HasDerivAt (fun s => 1 / (1 + s)) (-gammaR t ^ 2) t
    refine ((hasDerivAt_const t (1:ℝ)).div h_1t h1t_ne).congr_deriv ?_
    unfold gammaR
    simp only [Pi.add_apply, id]
    field_simp
    ring
  · -- Component 6: d/dt exp(1-exp(-t)) = exp(1-exp(-t))·exp(-t)
    change HasDerivAt (fun s => exp (1 - exp (-s))) (gammaP t * exp (-t)) t
    refine (((hasDerivAt_const t (1:ℝ)).sub h_exp_neg).exp).congr_deriv ?_
    unfold gammaP
    simp only [Pi.sub_apply]
    ring
  · -- Component 7: d/dt (t·exp(-t)) = exp(-t) - t·exp(-t)
    change HasDerivAt (fun s => s * exp (-s)) (exp (-t) - gammaQ t) t
    refine ((hasDerivAt_id t).mul h_exp_neg).congr_deriv ?_
    unfold gammaQ
    simp only [id]
    ring

/-- The 8-component solution is bounded (by 33). -/
theorem gammaSolution_bounded : gammaPIVP.IsBounded gammaSolution := by
  refine ⟨33, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 33)]
  intro i; fin_cases i
  · change ‖gammaF t‖ ≤ 33
    rw [norm_of_nonneg (gammaF_nonneg ht)]
    linarith [gammaF_bounded ht]
  · change ‖gammaG t‖ ≤ 33
    rw [Real.norm_eq_abs, abs_of_nonpos (gammaG_nonpos ht)]
    have h1 := (abs_sub_le_iff.mp (gammaG_tail_bound ht)).2
    have h2 : exp (-t) ≤ (1 : ℝ) := by
      calc exp (-t) ≤ exp 0 := exp_le_exp.mpr (neg_nonpos.mpr ht)
        _ = 1 := exp_zero
    have h3 := (abs_sub_le_iff.mp (gammaG_tail_bound (le_refl (0:ℝ)))).1
    simp [gammaG_init] at h3
    linarith
  · change ‖gammaW t‖ ≤ 33
    rw [norm_of_nonneg (gammaW_nonneg ht)]
    linarith [gammaW_bounded ht]
  · change ‖gammaU t‖ ≤ 33
    rw [norm_of_nonneg (gammaU_nonneg ht)]
    have hexp1 : exp (-1 : ℝ) ≤ 1 := by
      calc exp (-1 : ℝ) ≤ exp 0 := exp_le_exp.mpr (by norm_num)
        _ = 1 := exp_zero
    linarith [gammaU_bounded ht]
  · change ‖exp (-t)‖ ≤ 33
    rw [norm_of_nonneg (le_of_lt (exp_pos _))]
    have : exp (-t) ≤ 1 := by
      calc exp (-t) ≤ exp 0 := exp_le_exp.mpr (neg_nonpos.mpr ht)
        _ = 1 := exp_zero
    linarith
  · change ‖gammaR t‖ ≤ 33
    rw [norm_of_nonneg (le_of_lt (gammaR_pos ht))]
    linarith [gammaR_le_one ht]
  · change ‖gammaP t‖ ≤ 33
    rw [norm_of_nonneg (le_trans zero_le_one (gammaP_ge_one ht))]
    linarith [@gammaP_le_e t, exp_one_le_four]
  · change ‖gammaQ t‖ ≤ 33
    rw [norm_of_nonneg (gammaQ_nonneg ht)]
    have hexp1 : exp (-1 : ℝ) ≤ 1 := by
      calc exp (-1 : ℝ) ≤ exp 0 := exp_le_exp.mpr (by norm_num)
        _ = 1 := exp_zero
    linarith [gammaQ_le_inv_e ht]

/-! ## Real-time computability via PIVP convergence -/

/-- 32 ≤ e^5. Proof: 2 ≤ e (add_one_le_exp), so 2^5 = 32 ≤ e^5. -/
private theorem thirty_two_le_exp_five : (32 : ℝ) ≤ exp 5 := by
  have h2e : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1:ℝ)]
  calc (32:ℝ) = 2 ^ 5 := by norm_num
    _ ≤ exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h2e 5
    _ = exp 5 := by rw [← exp_nat_mul]; norm_num

/-- β is real-time computable via the 8-variable PIVP (output 0 = gammaF → β).
  Time modulus: μ(r) = 2r + 10. -/
theorem gammaBeta_is_realtime : Ripple.IsRealTimeComputable gammaBeta := by
  refine ⟨8, {
    pivp := gammaPIVP
    sol := {
      trajectory := gammaSolution
      init_cond := gammaSolution_init
      is_solution := gammaSolution_is_solution }
    modulus := fun r => 2 * ↑r + 10
    bounded := gammaSolution_bounded
    convergence := ?_ }, 10, by norm_num, ?_⟩
  · intro r t ht
    have hr0 : (0:ℝ) ≤ ↑r := Nat.cast_nonneg r
    have ht0 : 0 ≤ t := by linarith
    change |gammaF t - gammaBeta| < exp (-(↑r : ℝ))
    calc |gammaF t - gammaBeta|
        ≤ 32 * exp (-(t / 2)) := gammaF_tail_bound ht0
      _ ≤ exp 5 * exp (-(t / 2)) :=
          mul_le_mul_of_nonneg_right thirty_two_le_exp_five (le_of_lt (exp_pos _))
      _ = exp (5 - t / 2) := by rw [← exp_add]; ring_nf
      _ < exp (-(↑r : ℝ)) := exp_strictMono (by linarith)
  · intro r
    have hr : (0:ℝ) ≤ ↑r := Nat.cast_nonneg r
    linarith

/-- α is real-time computable via the 8-variable PIVP (output 1 = gammaG → α).
  Time modulus: μ(r) = r + 2. -/
theorem gammaAlpha_is_realtime : Ripple.IsRealTimeComputable gammaAlpha := by
  refine ⟨8, {
    pivp := { gammaPIVP with output := 1 }
    sol := {
      trajectory := gammaSolution
      init_cond := gammaSolution_init
      is_solution := gammaSolution_is_solution }
    modulus := fun r => ↑r + 2
    bounded := gammaSolution_bounded
    convergence := ?_ }, 2, by norm_num, ?_⟩
  · intro r t ht
    have hr0 : (0:ℝ) ≤ ↑r := Nat.cast_nonneg r
    have ht0 : 0 ≤ t := by linarith
    change |gammaG t - gammaAlpha| < exp (-(↑r : ℝ))
    calc |gammaG t - gammaAlpha|
        ≤ exp (-t) := gammaG_tail_bound ht0
      _ < exp (-(↑r : ℝ)) := exp_strictMono (by linarith)
  · intro r
    have hr : (0:ℝ) ≤ ↑r := Nat.cast_nonneg r
    linarith

/-! ## Karatsuba integral decomposition: Γ'(2) = (α + β) / e

  The key identity connecting the PIVP integrals to the Euler-Mascheroni constant.
  We prove (α + β) / e = 1 - γ via:
  1. β = e · ∫₁^∞ t·log(t)·e^{-t} dt  (change of variables t = s + 1)
  2. α = e · ∫₀¹ t·log(t)·e^{-t} dt   (change of variables t = e^{-s})
  3. Splitting: ∫₀^∞ = ∫₀¹ + ∫₁^∞
  4. ∫₀^∞ t·log(t)·e^{-t} dt = 1 - γ  (via Complex.hasDerivAt_GammaIntegral)
  Combining: (α+β)/e = ∫₀^∞ t·log(t)·e^{-t} dt = 1 - γ. -/

/-- The integrand t·log(t)·e^{-t} is integrable on (0, ∞). -/
private theorem integrableOn_t_log_exp :
    IntegrableOn (fun t => t * log t * exp (-t)) (Set.Ioi 0) := by
  -- Split: Ioi 0 = Ioc 0 1 ∪ Ioi 1
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1), integrableOn_union]
  have hcont : Continuous (fun t => t * log t * exp (-t)) :=
    continuous_mul_log.mul (continuous_exp.comp continuous_neg)
  constructor
  · -- On Ioc 0 1: continuous function on bounded interval
    rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  · -- On Ioi 1: exponential decay
    apply integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num : (0:ℝ) < 1/2)
    · exact hcont.continuousOn
    · apply Asymptotics.IsBigO.of_bound 16
      filter_upwards [Filter.Ici_mem_atTop (1:ℝ)] with t ht
      have ht0 : 0 < t := by linarith [Set.mem_Ici.mp ht]
      have ht1 : 1 ≤ t := Set.mem_Ici.mp ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (exp_pos _)),
          abs_of_nonneg (mul_nonneg (mul_nonneg (le_of_lt ht0) (log_nonneg ht1))
              (le_of_lt (exp_pos _)))]
      have hlog : log t ≤ t := by linarith [log_le_sub_one_of_pos ht0]
      -- t ≤ 4·exp(t/4) from 1 + t/4 ≤ exp(t/4), so t² ≤ 16·exp(t/2)
      have ht4 : t ≤ 4 * exp (t / 4) := by linarith [add_one_le_exp (t / 4)]
      calc t * log t * exp (-t)
          ≤ t * t * exp (-t) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (exp_pos _))
            exact mul_le_mul_of_nonneg_left hlog (le_of_lt ht0)
        _ = t ^ 2 * exp (-t) := by ring
        _ ≤ 16 * exp (t / 2) * exp (-t) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (exp_pos _))
            calc t ^ 2 ≤ (4 * exp (t / 4)) ^ 2 :=
                  pow_le_pow_left₀ (le_of_lt ht0) ht4 2
              _ = 16 * exp (t / 2) := by
                  rw [mul_pow, show (4:ℝ) ^ 2 = 16 from by norm_num, sq, ← exp_add,
                      show t / 4 + t / 4 = t / 2 from by ring]
        _ = 16 * exp (-(1 / 2) * t) := by
            rw [mul_assoc, ← exp_add, show t / 2 + -t = -(1 / 2) * t from by ring]

/-- β = e · ∫₁^∞ t·log(t)·e^{-t} dt. Change of variables t = s + 1. -/
private theorem gammaBeta_eq_e_mul_integral_hi :
    gammaBeta = exp 1 * ∫ t in Set.Ioi (1:ℝ), t * log t * exp (-t) := by
  unfold gammaBeta
  -- Use integral_image_eq_integral_abs_deriv_smul with f(s) = s + 1
  have himage : (· + (1:ℝ)) '' Set.Ioi 0 = Set.Ioi 1 := by
    ext x; simp only [Set.mem_image, Set.mem_Ioi]; constructor
    · rintro ⟨s, hs, rfl⟩; linarith
    · intro hx; exact ⟨x - 1, by linarith, by ring⟩
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x _ => (hasDerivAt_id' x).add_const (1:ℝ) |>.hasDerivWithinAt)
    (fun _ _ _ _ h => by linarith : Set.InjOn (· + (1:ℝ)) (Set.Ioi 0))
    (fun t => t * log t * exp (-t))
  -- hcov : ∫ Ioi 1, g = ∫ Ioi 0, |1| • g(s+1)
  rw [himage] at hcov
  -- Replace ∫ Ioi 1 in the goal using hcov
  rw [hcov]
  simp only [abs_one, one_smul]
  -- Goal: ∫ gammaW = exp 1 * ∫ (s+1)*log(s+1)*exp(-(s+1))
  -- Bring exp 1 inside the integral, then show integrands match
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro s _
  change gammaW s = exp 1 * ((s + 1) * log (s + 1) * exp (-(s + 1)))
  unfold gammaW
  have he : exp (1:ℝ) * exp (-1:ℝ) = 1 := by rw [← exp_add]; norm_num
  rw [show (1:ℝ) + s = s + 1 from add_comm 1 s,
      show -(s + 1) = -1 + -s from by ring, exp_add,
      show exp (1:ℝ) * ((s + 1) * log (s + 1) * (exp (-1:ℝ) * exp (-s))) =
           (exp (1:ℝ) * exp (-1:ℝ)) * (exp (-s) * ((s + 1) * log (s + 1))) from by ring,
      he, one_mul, mul_assoc]

/-- α = e · ∫₀¹ t·log(t)·e^{-t} dt. Change of variables t = e^{-s}. -/
private theorem gammaAlpha_eq_e_mul_integral_lo :
    gammaAlpha = exp 1 * ∫ t in Set.Ioo (0:ℝ) 1, t * log t * exp (-t) := by
  unfold gammaAlpha
  -- Change of variables: f(s) = exp(-s) maps Ioi 0 → Ioo 0 1
  have himage : (fun s => exp (-s)) '' Set.Ioi (0:ℝ) = Set.Ioo 0 1 := by
    ext x; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨exp_pos _, by rw [← exp_zero]; exact exp_strictMono (by linarith)⟩
    · intro ⟨hx0, hx1⟩
      exact ⟨-log x, by rw [neg_pos]; exact log_neg hx0 hx1,
             by simp [exp_log hx0]⟩
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (_ : x ∈ Set.Ioi (0:ℝ)) =>
      show HasDerivWithinAt (fun s => exp (-s)) (exp (-x) * -1) (Set.Ioi 0) x from
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt)
    (fun a _ b _ hab => neg_injective (exp_injective hab) :
      Set.InjOn (fun s => exp (-s)) (Set.Ioi (0:ℝ)))
    (fun t => t * log t * exp (-t))
  rw [himage] at hcov
  suffices h : ∫ s in Set.Ioi (0:ℝ), gammaP s * gammaQ s * exp (-s) =
      -(exp 1 * ∫ t in Set.Ioo (0:ℝ) 1, t * log t * exp (-t)) by linarith
  rw [hcov]
  -- LHS: ∫ P(s), RHS: -(exp 1 * ∫ |f'(s)| • g(f(s)))
  -- Show pointwise: P(s) = -(exp 1 * (|f'(s)| • g(f(s))))
  -- Then: ∫ -(exp 1 * J) = -(exp 1 * ∫ J)
  conv_lhs =>
    arg 2; ext s
    rw [show gammaP s * gammaQ s * exp (-s) =
        -(exp 1 * (|exp (-s) * -1| • ((fun t => t * log t * exp (-t)) (exp (-s))))) from by
      simp only [smul_eq_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _)),
        abs_neg, abs_one, mul_one]
      rw [Real.log_exp]; unfold gammaP gammaQ
      rw [show (1:ℝ) - exp (-s) = 1 + -exp (-s) from sub_eq_add_neg _ _, exp_add]; ring]
  simp only [smul_eq_mul]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]

/-- Integral splitting: ∫_{Ioi 0} = ∫_{Ioo 0 1} + ∫_{Ioi 1}. -/
private theorem integral_t_log_exp_split :
    (∫ t in Set.Ioi (0:ℝ), t * log t * exp (-t)) =
    (∫ t in Set.Ioo (0:ℝ) 1, t * log t * exp (-t)) +
    (∫ t in Set.Ioi (1:ℝ), t * log t * exp (-t)) := by
  have hint := integrableOn_t_log_exp
  -- Ioi 0 = Ioo 0 1 ∪ Ici 1 (a.e. equal to Ioo 0 1 ∪ Ioi 1)
  have hset : Set.Ioi (0:ℝ) = Set.Ioo 0 1 ∪ Set.Ici 1 :=
    (Set.Ioo_union_Ici_eq_Ioi (by norm_num : (0:ℝ) < 1)).symm
  rw [hset] at hint ⊢
  rw [MeasureTheory.setIntegral_union
    (Set.disjoint_left.mpr (fun x hx1 hx2 =>
      not_le.mpr (Set.mem_Ioo.mp hx1).2 (Set.mem_Ici.mp hx2)))
    measurableSet_Ici
    (hint.mono_set Set.subset_union_left)
    (hint.mono_set Set.subset_union_right)]
  -- ∫ Ici 1 = ∫ Ioi 1 (differ by singleton {1}, null set)
  congr 1
  exact MeasureTheory.integral_Ici_eq_integral_Ioi

/-- The integral ∫₀^∞ t·log(t)·e^{-t} dt = 1 - γ.
  Proof: from Complex.hasDerivAt_GammaIntegral at s=2, converted to real via
  HasDerivAt.real_of_complex, matched with hasDerivAt_Gamma_nat 1. -/
private theorem integral_t_log_exp_eq :
    (∫ t in Set.Ioi (0:ℝ), t * log t * exp (-t)) = 1 - eulerMascheroniConstant := by
  -- Step 1: Complex Gamma integral derivative at s=2 (differentiation under integral sign)
  have hre2 : (0:ℝ) < (2:ℂ).re := by norm_num
  have hgi := Complex.hasDerivAt_GammaIntegral hre2
  -- Step 2: GammaIntegral = Gamma near s=2, so HasDerivAt Gamma D (2:ℂ)
  set D := ∫ t : ℝ in Set.Ioi 0,
    (↑t : ℂ) ^ ((2:ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
  have hd_c : HasDerivAt Complex.Gamma D (2:ℂ) := by
    have heq : Complex.Gamma =ᶠ[nhds (2:ℂ)] Complex.GammaIntegral := by
      filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hre2]
        with s hs using Complex.Gamma_eq_integral hs
    exact hgi.congr_of_eventuallyEq heq
  -- Step 3: Convert complex derivative to real: HasDerivAt Real.Gamma D.re 2
  have hd_real : HasDerivAt Real.Gamma D.re (2:ℝ) := hd_c.real_of_complex
  -- Step 4: Gamma'(2) = 1 - γ from Mathlib
  have hd_nat : HasDerivAt Real.Gamma (1 - eulerMascheroniConstant) (2:ℝ) := by
    have h := Real.hasDerivAt_Gamma_nat 1
    simp only [Nat.factorial_one, Nat.cast_one, harmonic_succ, harmonic_zero,
      zero_add, one_mul, inv_one, Rat.cast_one] at h
    rwa [show -eulerMascheroniConstant + (1:ℝ) = 1 - eulerMascheroniConstant from by ring,
         show (1:ℝ) + 1 = 2 from by norm_num] at h
  -- Step 5: By uniqueness of derivatives, D.re = 1 - γ
  have hDre : D.re = 1 - eulerMascheroniConstant := hd_real.unique hd_nat
  -- Step 6: Show D.re equals the real integral
  -- The complex integrand at s=2 simplifies to ↑(t * log t * exp(-t)) for t > 0
  suffices hD : D = ↑(∫ t in Set.Ioi (0:ℝ), t * log t * exp (-t)) by
    rw [hD, Complex.ofReal_re] at hDre; linarith
  -- Show integrand is real-valued, then use integral_ofReal
  have hcongr : ∀ t ∈ Set.Ioi (0:ℝ),
      (↑t : ℂ) ^ ((2:ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))) =
      (↑(t * Real.log t * Real.exp (-t)) : ℂ) := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    rw [show (2:ℂ) - 1 = ↑(1:ℝ) from by push_cast; ring,
        ← Complex.ofReal_cpow ht0, rpow_one]
    push_cast; ring
  rw [show D = ∫ t in Set.Ioi (0:ℝ), (↑(t * Real.log t * Real.exp (-t)) : ℂ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
  exact integral_ofReal

/-! ## The PIVP-computed value and its connection to γ

  The 8-variable PIVP computes α and β, giving the value 1 - (α+β)/e.
  We prove this value is real-time computable (fully verified, no sorry).
  The connection to Mathlib's eulerMascheroniConstant is via
  the Karatsuba integral decomposition (all sub-lemmas proved above). -/

/-- The value computed by the 8-variable PIVP: 1 - (α+β)/e.
  Equals γ (Euler-Mascheroni constant) by the Karatsuba decomposition
  (Huang PhD thesis Thm 3.3.4). -/
noncomputable def pivpGammaValue : ℝ := 1 - (gammaAlpha + gammaBeta) / exp 1

/-- The PIVP value is real-time computable.
  This proof is fully verified (no sorry): α and β are computed by
  PIVPs with exponential convergence, and field closure gives the result. -/
theorem pivpGammaValue_is_realtime : Ripple.IsRealTimeComputable pivpGammaValue := by
  unfold pivpGammaValue
  exact Ripple.realtime_field_sub (Ripple.realtime_const 1)
    (Ripple.realtime_field_div (by positivity : exp 1 ≠ 0)
      (Ripple.realtime_field_add gammaAlpha_is_realtime gammaBeta_is_realtime)
      (Ripple.realtime_const (exp 1)))

/-- The PIVP value equals γ. This is the Karatsuba decomposition:
  Γ'(2) = ∫₀^∞ t·log(t)·e^{-t} dt (by hasDerivAt_GammaIntegral at s=2),
  split at t=1, substitute t=1+s (→ β) and t=1-u, u=1-e^{-s} (→ α).
  Fully verified via Complex.hasDerivAt_GammaIntegral → real conversion
  → uniqueness with hasDerivAt_Gamma_nat. -/
theorem pivpGammaValue_eq_gamma :
    pivpGammaValue = eulerMascheroniConstant := by
  unfold pivpGammaValue
  have hsplit := integral_t_log_exp_split
  have hbeta := gammaBeta_eq_e_mul_integral_hi
  have halpha := gammaAlpha_eq_e_mul_integral_lo
  have heq := integral_t_log_exp_eq
  have he_pos : exp (1:ℝ) ≠ 0 := ne_of_gt (exp_pos 1)
  -- α + β = e · (∫ Ioo 0 1 + ∫ Ioi 1) = e · ∫ Ioi 0 = e · (1 - γ)
  have h_sum : gammaAlpha + gammaBeta = exp 1 * (1 - eulerMascheroniConstant) := by
    rw [halpha, hbeta, ← mul_add, ← hsplit, heq]
  -- 1 - (α + β) / e = 1 - (1 - γ) = γ
  rw [h_sum, mul_div_cancel_left₀ _ he_pos]
  linarith

/-- Γ'(2) = (gammaAlpha + gammaBeta) / e. Consequence of pivpGammaValue_eq_gamma. -/
theorem deriv_Gamma_two_eq_alpha_beta :
    deriv Gamma 2 = (gammaAlpha + gammaBeta) / exp 1 := by
  have hpivp := pivpGammaValue_eq_gamma
  unfold pivpGammaValue at hpivp
  linarith [gamma_eq_one_sub_deriv_Gamma_two]

/-! ## Main theorem -/

/-- γ is real-time CRN-computable.

  Proof structure:
  1. pivpGammaValue = 1 - (α+β)/e is real-time computable [pivpGammaValue_is_realtime]
  2. pivpGammaValue = γ [pivpGammaValue_eq_gamma, via Karatsuba integral decomposition]
  3. Therefore γ ∈ ℝ_RTCRN.

  Fully verified: 0 sorry, 0 axiom. -/
theorem euler_gamma_is_realtime :
    Ripple.IsRealTimeComputable eulerMascheroniConstant := by
  rw [← pivpGammaValue_eq_gamma]
  exact pivpGammaValue_is_realtime

end Ripple.Number

/-
  Ripple.Number.AperyFermi — ζ(3) via the Fermi-Dirac integral representation.

  Parallel encoding to `Number/Apery.lean`. Where that file targets the
  (5/2)·Σ(-1)^(n-1)/(n³·C(2n,n)) series route (tooling level; the generating
  function has a Puiseux branch at x=0 — see `notes/apery_gf_holonomic.md`),
  this file takes the alternating Fermi-Dirac integral

      ∫₀^∞ x² / (1 + eˣ) dx = (3/2)·ζ(3)

  and encodes it as a 5-variable bounded polynomial PIVP with rational
  initial conditions and exponential convergence. This is a genuine
  first-floor (real-time, μ(r) = Θ(r)) candidate.

  ## The PIVP (5 variables)

  State (all bounded for t ≥ 0):
    a := e^(-t)            a(0) = 1,     a ∈ (0, 1]
    b := t · e^(-t)        b(0) = 0,     b ∈ [0, 1/e]
    c := t² · e^(-t)       c(0) = 0,     c ∈ [0, 4/e²]
    q := 1 / (1 + e^(-t))  q(0) = 1/2,   q ∈ [1/2, 1)
    S := (2/3)·∫₀ᵗ x²/(1+eˣ) dx  S(0) = 0,    S(t) → ζ(3) directly

  Polynomial dynamics (all RHS ≤ degree 2; the rational factor 2/3
  absorbing (3/2)·ζ(3) → ζ(3) lives inside the Ṡ coefficient):
    ȧ = -a
    ḃ = a - b
    ċ = 2b - c
    q̇ = a · q²             [since q = 1/(1+a), q̇ = -ȧ·q² = a·q²]
    Ṡ = (2/3) · c · q      [since (2/3)·x²/(1+eˣ) has ∫₀^∞ = ζ(3)]

  ## Real time (first floor)

  Proved at the end of this file: `apery_is_realtime` (modulus μ(r) = 2r + 6).
  Features of the system:
  - All 5 state variables are bounded on [0,∞) by closed-form constants.
  - All initial values are rational (1, 0, 0, 1/2, 0) — no NTIVs, no e.
  - Polynomial RHS of degree ≤ 2.
  - Convergence rate: |S(t) − ζ(3)| ≤ (2/3)(t² + 2t + 2)e^(-t) ≤ (16/3)e^(-t/2)
    (`fermi_distance_to_limit`, `fermi_abs_sub_zeta3_le`).

  ## Numerical verification

  `experiments/apery_fermi_5var.py` integrates this system with DOP853
  and confirms that S(50), unscaled (without the factor 2/3), agrees with
  (3/2)·ζ(3) ≈ 1.803085354739391 to 2.2e-15 (machine precision). Convergence ratio |err|/(t²e^(-t)) → 1.
-/

import Ripple.Core.PIVP
import Ripple.Core.BoundedTime
import Ripple.Core.RealTimeGPAC
import Ripple.Core.CRNPipeline
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Ripple
namespace Number

open scoped Classical
open MeasureTheory

/-! ## State-variable indices -/

/-- Index convention for the 5-variable Fermi PIVP:
    0 ↦ a = e^(-t)
    1 ↦ b = t·e^(-t)
    2 ↦ c = t²·e^(-t)
    3 ↦ q = 1/(1+e^(-t))
    4 ↦ S = ∫₀ᵗ x²/(1+eˣ) dx (output) -/
abbrev fermiDim : ℕ := 5

abbrev aIdx : Fin fermiDim := ⟨0, by decide⟩
abbrev bIdx : Fin fermiDim := ⟨1, by decide⟩
abbrev cIdx : Fin fermiDim := ⟨2, by decide⟩
abbrev qIdx : Fin fermiDim := ⟨3, by decide⟩
abbrev sIdx : Fin fermiDim := ⟨4, by decide⟩

/-! ## The polynomial vector field

    RHS[a] = −a
    RHS[b] =  a − b
    RHS[c] = 2b − c
    RHS[q] =  a·q²
    RHS[S] =  (2/3)·c·q
-/

/-- Semantic vector field (real-valued). Dispatch on the underlying Nat.
    Note the rational factor 2/3 in Ṡ: this absorbs the global scaling
    (3/2)·ζ(3) = ∫₀^∞ x²/(1+eˣ) dx so that S(∞) = ζ(3) directly. -/
noncomputable def fermiField (y : Fin fermiDim → ℝ) : Fin fermiDim → ℝ := fun i =>
  if i = aIdx then -(y aIdx)
  else if i = bIdx then y aIdx - y bIdx
  else if i = cIdx then 2 * y bIdx - y cIdx
  else if i = qIdx then y aIdx * (y qIdx) ^ 2
  else (2/3 : ℝ) * (y cIdx * y qIdx)

/-- Rational initial condition (1, 0, 0, 1/2, 0). -/
noncomputable def fermiInit : Fin fermiDim → ℝ := fun i =>
  if i = aIdx then 1
  else if i = bIdx then 0
  else if i = cIdx then 0
  else if i = qIdx then 1/2
  else 0

/-- The Fermi-Dirac 5-variable PIVP for ζ(3). -/
noncomputable def fermiPIVP : PIVP fermiDim where
  field := fermiField
  init := fermiInit
  output := sIdx

/-! ## The exact closed-form trajectory

    a(t) = e^(-t)
    b(t) = t · e^(-t)
    c(t) = t² · e^(-t)
    q(t) = 1 / (1 + e^(-t))
    S(t) = ∫₀ᵗ x² / (1 + eˣ) dx
-/

/-- Closed-form trajectory for the 5 state variables. -/
noncomputable def fermiTrajectory : ℝ → Fin fermiDim → ℝ := fun t i =>
  if i = aIdx then Real.exp (-t)
  else if i = bIdx then t * Real.exp (-t)
  else if i = cIdx then t^2 * Real.exp (-t)
  else if i = qIdx then 1 / (1 + Real.exp (-t))
  else (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x)

/-! ### Coordinate projections of the trajectory -/

lemma fermiTrajectory_a (t : ℝ) : fermiTrajectory t aIdx = Real.exp (-t) := by
  simp [fermiTrajectory, aIdx]

lemma fermiTrajectory_b (t : ℝ) : fermiTrajectory t bIdx = t * Real.exp (-t) := by
  simp [fermiTrajectory, aIdx, bIdx]

lemma fermiTrajectory_c (t : ℝ) : fermiTrajectory t cIdx = t^2 * Real.exp (-t) := by
  simp [fermiTrajectory, aIdx, bIdx, cIdx]

lemma fermiTrajectory_q (t : ℝ) : fermiTrajectory t qIdx = 1 / (1 + Real.exp (-t)) := by
  simp [fermiTrajectory, aIdx, bIdx, cIdx, qIdx]

lemma fermiTrajectory_s (t : ℝ) :
    fermiTrajectory t sIdx = (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) := by
  simp [fermiTrajectory, aIdx, bIdx, cIdx, qIdx, sIdx]

/-! ### Analytic helper facts -/

/-- `1 + e^x > 0` for all real `x`, so the integrand `x²/(1+e^x)` is continuous. -/
lemma one_add_exp_pos (x : ℝ) : 0 < 1 + Real.exp x := by
  have : 0 < Real.exp x := Real.exp_pos x
  linarith

lemma one_add_exp_ne_zero (x : ℝ) : (1 + Real.exp x) ≠ 0 :=
  ne_of_gt (one_add_exp_pos x)

lemma one_add_exp_neg_pos (t : ℝ) : 0 < 1 + Real.exp (-t) := one_add_exp_pos _

lemma one_add_exp_neg_ne_zero (t : ℝ) : (1 + Real.exp (-t)) ≠ 0 :=
  one_add_exp_ne_zero _

/-- The integrand `x²/(1+eˣ)` is continuous everywhere. -/
lemma continuous_fermiIntegrand :
    Continuous (fun x : ℝ => x^2 / (1 + Real.exp x)) := by
  refine Continuous.div (by continuity) ?_ (fun x => one_add_exp_ne_zero x)
  exact (continuous_const.add Real.continuous_exp)

/-- `0 ≤ x²/(1+eˣ)` for all real `x`. -/
lemma fermiIntegrand_nonneg (x : ℝ) : 0 ≤ x^2 / (1 + Real.exp x) := by
  apply div_nonneg
  · exact sq_nonneg x
  · linarith [Real.exp_pos x]

/-- `x²/(1+eˣ) ≤ x²·e^(-x)` for all real `x`. (Using `1/(1+eˣ) ≤ 1/eˣ = e^(-x)`.) -/
lemma fermiIntegrand_le_exp_neg (x : ℝ) :
    x^2 / (1 + Real.exp x) ≤ x^2 * Real.exp (-x) := by
  rw [Real.exp_neg]
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
  rw [inv_le_inv₀ (one_add_exp_pos x) (Real.exp_pos x)]
  linarith [Real.exp_pos x]

/-! ## The closed form solves the system

  Initial condition, ODE, boundedness, and the limit ζ(3).
-/

/-- The closed-form trajectory satisfies the initial condition. -/
theorem fermiTrajectory_init :
    fermiTrajectory 0 = fermiInit := by
  funext i
  fin_cases i <;>
    (simp [fermiTrajectory, fermiInit, aIdx, bIdx, cIdx, qIdx,
           Real.exp_zero, intervalIntegral.integral_same]; try norm_num)

/-! ### Component-wise derivative lemmas for `fermiTrajectory_is_solution` -/

/-- d/dt `e^(-t) = -e^(-t)`. -/
lemma hasDerivAt_a (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t h1
  convert h2 using 1
  ring

/-- d/dt `t·e^(-t) = e^(-t) - t·e^(-t)`. -/
lemma hasDerivAt_b (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * Real.exp (-s))
      (Real.exp (-t) - t * Real.exp (-t)) t := by
  have ht : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have he := hasDerivAt_a t
  have hmul := ht.mul he
  -- hmul : HasDerivAt (fun s => s * exp(-s)) (1 * exp(-t) + t * (-exp(-t))) t
  convert hmul using 1
  ring

/-- d/dt `t²·e^(-t) = 2t·e^(-t) - t²·e^(-t)`. -/
lemma hasDerivAt_c (t : ℝ) :
    HasDerivAt (fun s : ℝ => s^2 * Real.exp (-s))
      (2 * (t * Real.exp (-t)) - t^2 * Real.exp (-t)) t := by
  have ht2 : HasDerivAt (fun s : ℝ => s^2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t)
  have he := hasDerivAt_a t
  have := ht2.mul he
  convert this using 1
  ring

/-- d/dt `1/(1+e^(-t)) = e^(-t) · (1/(1+e^(-t)))²`. -/
lemma hasDerivAt_q (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 / (1 + Real.exp (-s)))
      (Real.exp (-t) * (1 / (1 + Real.exp (-t)))^2) t := by
  have hdenom : HasDerivAt (fun s : ℝ => 1 + Real.exp (-s)) (-Real.exp (-t)) t := by
    have h2 := hasDerivAt_a t
    have := h2.const_add (1 : ℝ)
    simpa using this
  have hne : (1 + Real.exp (-t)) ≠ 0 := one_add_exp_neg_ne_zero t
  -- Use HasDerivAt.inv for derivative of 1/f
  have h : HasDerivAt (fun s : ℝ => (1 + Real.exp (-s))⁻¹)
      (-(-Real.exp (-t)) / (1 + Real.exp (-t))^2) t :=
    hdenom.inv hne
  -- Convert 1/(...) to (...)⁻¹
  have heq : (fun s : ℝ => 1 / (1 + Real.exp (-s))) =
             (fun s : ℝ => (1 + Real.exp (-s))⁻¹) := by
    funext s; rw [one_div]
  rw [heq]
  convert h using 1
  rw [one_div, inv_pow]
  field_simp

/-- d/dt `∫₀ᵗ x²/(1+eˣ) dx = t²/(1+eᵗ)`. -/
lemma hasDerivAt_s (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x in (0 : ℝ)..s, x^2 / (1 + Real.exp x))
      (t^2 / (1 + Real.exp t)) t :=
  (continuous_fermiIntegrand.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- Key algebraic identity: `t²/(1+eᵗ) = (t²·e^(-t)) · (1/(1+e^(-t)))`. -/
lemma fermi_key_identity (t : ℝ) :
    t^2 / (1 + Real.exp t) = (t^2 * Real.exp (-t)) * (1 / (1 + Real.exp (-t))) := by
  have hne : (1 + Real.exp t) ≠ 0 := ne_of_gt (one_add_exp_pos t)
  have hne' : (1 + Real.exp (-t)) ≠ 0 := one_add_exp_neg_ne_zero t
  have hexp : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  rw [mul_one_div, div_eq_div_iff hne hne']
  -- Goal: t² * (1 + e^(-t)) = t² * e^(-t) * (1 + e^t)
  have expand : (1 + Real.exp (-t)) = Real.exp (-t) * (Real.exp t + 1) := by
    rw [mul_add, mul_comm (Real.exp (-t)) (Real.exp t), hexp, mul_one]
  rw [expand]
  ring

/-- Evaluations of `fermiField` at `fermiTrajectory t`. -/
lemma fermiField_a (t : ℝ) :
    fermiField (fermiTrajectory t) aIdx = -Real.exp (-t) := by
  unfold fermiField
  rw [if_pos rfl, fermiTrajectory_a]

lemma fermiField_b (t : ℝ) :
    fermiField (fermiTrajectory t) bIdx =
      Real.exp (-t) - t * Real.exp (-t) := by
  unfold fermiField
  rw [if_neg (by decide : bIdx ≠ aIdx), if_pos rfl,
      fermiTrajectory_a, fermiTrajectory_b]

lemma fermiField_c (t : ℝ) :
    fermiField (fermiTrajectory t) cIdx =
      2 * (t * Real.exp (-t)) - t^2 * Real.exp (-t) := by
  unfold fermiField
  rw [if_neg (by decide : cIdx ≠ aIdx),
      if_neg (by decide : cIdx ≠ bIdx), if_pos rfl,
      fermiTrajectory_b, fermiTrajectory_c]

lemma fermiField_q (t : ℝ) :
    fermiField (fermiTrajectory t) qIdx =
      Real.exp (-t) * (1 / (1 + Real.exp (-t)))^2 := by
  unfold fermiField
  rw [if_neg (by decide : qIdx ≠ aIdx),
      if_neg (by decide : qIdx ≠ bIdx),
      if_neg (by decide : qIdx ≠ cIdx), if_pos rfl,
      fermiTrajectory_a, fermiTrajectory_q]

lemma fermiField_s (t : ℝ) :
    fermiField (fermiTrajectory t) sIdx =
      (2/3 : ℝ) * ((t^2 * Real.exp (-t)) * (1 / (1 + Real.exp (-t)))) := by
  unfold fermiField
  rw [if_neg (by decide : sIdx ≠ aIdx),
      if_neg (by decide : sIdx ≠ bIdx),
      if_neg (by decide : sIdx ≠ cIdx),
      if_neg (by decide : sIdx ≠ qIdx),
      fermiTrajectory_c, fermiTrajectory_q]

/-- The closed-form trajectory satisfies the polynomial ODE. -/
theorem fermiTrajectory_is_solution :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt fermiTrajectory (fermiField (fermiTrajectory t)) t := by
  intro t _ht
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · -- i = aIdx = 0: d/dt e^(-t) = -e^(-t)
    show HasDerivAt (fun s => fermiTrajectory s aIdx)
      (fermiField (fermiTrajectory t) aIdx) t
    rw [fermiField_a]
    have hfun : (fun s => fermiTrajectory s aIdx) = (fun s => Real.exp (-s)) := by
      funext s; exact fermiTrajectory_a s
    rw [hfun]
    exact hasDerivAt_a t
  · -- i = bIdx = 1
    show HasDerivAt (fun s => fermiTrajectory s bIdx)
      (fermiField (fermiTrajectory t) bIdx) t
    rw [fermiField_b]
    have hfun : (fun s => fermiTrajectory s bIdx) = (fun s => s * Real.exp (-s)) := by
      funext s; exact fermiTrajectory_b s
    rw [hfun]
    exact hasDerivAt_b t
  · -- i = cIdx = 2
    show HasDerivAt (fun s => fermiTrajectory s cIdx)
      (fermiField (fermiTrajectory t) cIdx) t
    rw [fermiField_c]
    have hfun : (fun s => fermiTrajectory s cIdx) = (fun s => s^2 * Real.exp (-s)) := by
      funext s; exact fermiTrajectory_c s
    rw [hfun]
    exact hasDerivAt_c t
  · -- i = qIdx = 3
    show HasDerivAt (fun s => fermiTrajectory s qIdx)
      (fermiField (fermiTrajectory t) qIdx) t
    rw [fermiField_q]
    have hfun : (fun s => fermiTrajectory s qIdx) = (fun s => 1 / (1 + Real.exp (-s))) := by
      funext s; exact fermiTrajectory_q s
    rw [hfun]
    exact hasDerivAt_q t
  · -- i = sIdx = 4
    show HasDerivAt (fun s => fermiTrajectory s sIdx)
      (fermiField (fermiTrajectory t) sIdx) t
    rw [fermiField_s]
    have hfun : (fun s => fermiTrajectory s sIdx) =
        (fun s => (2/3 : ℝ) * ∫ x in (0 : ℝ)..s, x^2 / (1 + Real.exp x)) := by
      funext s; exact fermiTrajectory_s s
    rw [hfun]
    have hs := hasDerivAt_s t
    have hconst := hs.const_mul (2/3 : ℝ)
    convert hconst using 1
    rw [fermi_key_identity]

/-! ### Pointwise bounds on the five components -/

/-- Elementary bound: `t·e^(-t) ≤ 1` for `t ≥ 0`. -/
lemma t_exp_neg_le (t : ℝ) (ht : 0 ≤ t) : t * Real.exp (-t) ≤ 1 := by
  -- Use e^t ≥ 1 + t ≥ t, so t / e^t ≤ 1
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos t), one_mul]
  -- Goal: t ≤ e^t
  exact (Real.add_one_le_exp t).trans' (by linarith)

/-- Elementary bound: `t²·e^(-t) ≤ 4` for `t ≥ 0`. -/
lemma tsq_exp_neg_le (t : ℝ) (ht : 0 ≤ t) : t^2 * Real.exp (-t) ≤ 4 := by
  -- Case t ≤ 2: t²·e^(-t) ≤ 4·1 = 4
  -- Case t > 2: e^(t/2) ≥ 1 + t/2 ≥ t/2, so e^t ≥ t²/4
  rcases le_or_gt t 2 with h | h
  · -- t ≤ 2
    have hexp : Real.exp (-t) ≤ 1 := by
      rw [Real.exp_neg]
      have : Real.exp t ≥ 1 := Real.one_le_exp ht
      rw [inv_le_one_iff₀]
      right; exact this
    have h2 : t^2 ≤ 4 := by nlinarith
    calc t^2 * Real.exp (-t) ≤ 4 * 1 := by
          apply mul_le_mul h2 hexp (le_of_lt (Real.exp_pos _)) (by norm_num)
      _ = 4 := by norm_num
  · -- t > 2
    -- e^(t/2) ≥ 1 + t/2, so e^t = (e^(t/2))^2 ≥ (1+t/2)^2 ≥ t²/4
    have ht2 : (0 : ℝ) < t / 2 := by linarith
    have hht : 1 + t/2 ≤ Real.exp (t/2) := by
      have := Real.add_one_le_exp (t/2); linarith
    have hpos : 0 < 1 + t/2 := by linarith
    have ht_bd : t/2 ≤ 1 + t/2 := by linarith
    have : t/2 ≤ Real.exp (t/2) := le_trans ht_bd hht
    have hsq : (t/2)^2 ≤ (Real.exp (t/2))^2 :=
      pow_le_pow_left₀ (by linarith) this 2
    have h_exp : (Real.exp (t/2))^2 = Real.exp t := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h_exp] at hsq
    -- hsq: (t/2)^2 ≤ e^t, i.e., t²/4 ≤ e^t
    have : t^2 / 4 ≤ Real.exp t := by
      have : (t/2)^2 = t^2 / 4 := by ring
      linarith
    -- So t²·e^(-t) = t²/e^t ≤ 4
    rw [Real.exp_neg]
    have he_pos : 0 < Real.exp t := Real.exp_pos t
    rw [mul_inv_le_iff₀ he_pos]
    -- Goal: t^2 ≤ 4 * e^t
    linarith

/-- Bound on the scaled Fermi integral: `0 ≤ (2/3)·∫₀ᵗ x²/(1+eˣ) dx ≤ (2/3)·(2 − (t²+2t+2)·e^(-t)) ≤ 4/3`. -/
lemma fermiTrajectory_s_bound (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) ∧
    (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) ≤ 4/3 := by
  -- Lower bound: integrand nonneg
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) := by
    apply intervalIntegral.integral_nonneg ht
    intros x _
    exact fermiIntegrand_nonneg x
  -- Upper bound: compare to ∫ x²·e^(-x) dx whose primitive is -(x²+2x+2)·e^(-x).
  -- Let F(x) = -(x²+2x+2)·e^(-x). Then F'(x) = x²·e^(-x) and F(t) - F(0) = 2 - (t²+2t+2)·e^(-t) ≤ 2.
  have hprim : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -(y^2 + 2*y + 2) * Real.exp (-y)) (x^2 * Real.exp (-x)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => -(y^2 + 2*y + 2)) (-(2*x + 2)) x := by
      have h1 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have h2 : HasDerivAt (fun y : ℝ => 2*y) (2 : ℝ) x := by
        have := (hasDerivAt_id x).const_mul 2
        simpa using this
      have hs : HasDerivAt (fun y : ℝ => y^2 + 2*y + 2) (2*x + 2) x := by
        have := (h1.add h2).add_const (2 : ℝ)
        simpa using this
      exact hs.neg
    have he := hasDerivAt_a x
    have := hp.mul he
    convert this using 1
    ring
  have hint : ∫ x in (0 : ℝ)..t, x^2 * Real.exp (-x) =
      (-(t^2 + 2*t + 2) * Real.exp (-t)) - (-(0^2 + 2*0 + 2) * Real.exp (-0)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intros x _
      exact hprim x
    · exact (Continuous.intervalIntegrable (by continuity) _ _)
  have hint_val : ∫ x in (0 : ℝ)..t, x^2 * Real.exp (-x) = 2 - (t^2 + 2*t + 2) * Real.exp (-t) := by
    rw [hint]; simp [Real.exp_zero]; ring
  -- Now bound the integrand
  have hmono : ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) ≤ ∫ x in (0 : ℝ)..t, x^2 * Real.exp (-x) := by
    apply intervalIntegral.integral_mono_on ht
    · exact continuous_fermiIntegrand.intervalIntegrable _ _
    · exact (Continuous.intervalIntegrable (by continuity) _ _)
    · intros x _; exact fermiIntegrand_le_exp_neg x
  have h_leq_2 : ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) ≤ 2 := by
    have hpos_term : 0 ≤ (t^2 + 2*t + 2) * Real.exp (-t) := by
      apply mul_nonneg
      · nlinarith
      · exact le_of_lt (Real.exp_pos _)
    calc ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x)
        ≤ ∫ x in (0 : ℝ)..t, x^2 * Real.exp (-x) := hmono
      _ = 2 - (t^2 + 2*t + 2) * Real.exp (-t) := hint_val
      _ ≤ 2 := by linarith
  refine ⟨?_, ?_⟩
  · positivity
  · linarith

/-- All five state variables stay bounded on [0, ∞). -/
theorem fermiTrajectory_bounded :
    fermiPIVP.IsBounded fermiTrajectory := by
  refine ⟨5, by norm_num, ?_⟩
  intros t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 5)]
  intro i
  fin_cases i
  · -- aIdx
    show ‖fermiTrajectory t aIdx‖ ≤ 5
    rw [fermiTrajectory_a, Real.norm_eq_abs]
    have h1 : 0 < Real.exp (-t) := Real.exp_pos _
    have h2 : Real.exp (-t) ≤ 1 := by
      rw [Real.exp_neg]
      rw [inv_le_one_iff₀]; right; exact Real.one_le_exp ht
    rw [abs_of_pos h1]; linarith
  · -- bIdx
    show ‖fermiTrajectory t bIdx‖ ≤ 5
    rw [fermiTrajectory_b, Real.norm_eq_abs]
    have h : 0 ≤ t * Real.exp (-t) := mul_nonneg ht (le_of_lt (Real.exp_pos _))
    rw [abs_of_nonneg h]
    linarith [t_exp_neg_le t ht]
  · -- cIdx
    show ‖fermiTrajectory t cIdx‖ ≤ 5
    rw [fermiTrajectory_c, Real.norm_eq_abs]
    have h : 0 ≤ t^2 * Real.exp (-t) :=
      mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
    rw [abs_of_nonneg h]
    linarith [tsq_exp_neg_le t ht]
  · -- qIdx
    show ‖fermiTrajectory t qIdx‖ ≤ 5
    rw [fermiTrajectory_q, Real.norm_eq_abs]
    have hpos : 0 < 1 / (1 + Real.exp (-t)) := by
      apply div_pos one_pos (one_add_exp_neg_pos t)
    rw [abs_of_pos hpos]
    -- 1/(1+e^(-t)) < 1
    have : 1 / (1 + Real.exp (-t)) ≤ 1 := by
      rw [div_le_one (one_add_exp_neg_pos t)]
      have : 0 < Real.exp (-t) := Real.exp_pos _
      linarith
    linarith
  · -- sIdx
    show ‖fermiTrajectory t sIdx‖ ≤ 5
    rw [fermiTrajectory_s, Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := fermiTrajectory_s_bound t ht
    rw [abs_of_nonneg h1]
    linarith

/-- Package the closed-form trajectory as a `PIVP.Solution`. -/
noncomputable def fermiSolution : PIVP.Solution fermiPIVP where
  trajectory := fermiTrajectory
  init_cond := fermiTrajectory_init
  is_solution := fermiTrajectory_is_solution

/-! ### Closed-form moments of the exponential

The proof of `fermi_integral_eq_zeta3` uses:
  `∫_{Ioi 0} x^2 · exp(-(k+1)·x) dx = 2 / (k+1)^3`
and then termwise integration of the geometric expansion
  `1/(1+eˣ) = Σ_{k≥0} (-1)^k · e^(-(k+1)x)`
for `x > 0`. -/

/-- Primitive for `x ↦ x² · e^(−c·x)` when `c > 0`:
`F(x) = −((c·x)² + 2·(c·x) + 2) · e^(−c·x) / c³`,
`F'(x) = x² · e^(−c·x)`. -/
lemma hasDerivAt_xsq_exp_neg_mul_primitive (c : ℝ) (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -((c*y)^2 + 2*(c*y) + 2) * Real.exp (-(c*y)) / c^3)
      (x^2 * Real.exp (-(c*x))) x := by
  -- d/dy (c·y) = c
  have hcy : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  -- d/dy exp(-(c·y)) = -c · exp(-(c·y))
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(c*y)))
      (-c * Real.exp (-(c*x))) x := by
    have h1 : HasDerivAt (fun y : ℝ => -(c*y)) (-c) x := hcy.neg
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(c*y)))
        (Real.exp (-(c*x)) * (-c)) x := by
      have := (Real.hasDerivAt_exp (-(c*x))).comp x h1
      simpa [Function.comp] using this
    convert h2 using 1; ring
  -- d/dy ((c·y)² + 2·(c·y) + 2) = 2·(c·y)·c + 2·c = 2·c·(c·y + 1)
  have hpoly : HasDerivAt (fun y : ℝ => (c*y)^2 + 2*(c*y) + 2)
      (2*(c*x)*c + 2*c) x := by
    have hsq : HasDerivAt (fun y : ℝ => (c*y)^2) (2*(c*x)*c) x := by
      have := (hcy.pow 2)
      -- (hcy.pow 2) : HasDerivAt (fun y => (c*y)^2) (↑2 * (c*x)^(2-1) * c) x
      simpa [pow_one, two_mul] using this
    have hlin : HasDerivAt (fun y : ℝ => 2*(c*y)) (2*c) x := by
      have := hcy.const_mul (2 : ℝ)
      simpa using this
    have := (hsq.add hlin).add_const (2 : ℝ)
    simpa using this
  have hneg : HasDerivAt (fun y : ℝ => -((c*y)^2 + 2*(c*y) + 2))
      (-(2*(c*x)*c + 2*c)) x := hpoly.neg
  have hprod := hneg.mul hexp
  -- hprod : HasDerivAt (fun y => -((c*y)^2+2*(c*y)+2) * exp(-(c*y)))
  --   (-(2*(c*x)*c+2*c)*exp(-(c*x)) + -((c*x)^2+2*(c*x)+2)*(-c*exp(-(c*x)))) x
  have hfinal := hprod.div_const (c^3)
  convert hfinal using 1
  have hc3 : c^3 ≠ 0 := pow_ne_zero _ hc.ne'
  field_simp
  ring

/-- `exp(−c·x)` tends to `0` at `+∞` for `c > 0` (and so does the polynomial times it). -/
lemma tendsto_xsq_primitive_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun x : ℝ => -((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x)) / c^3)
      Filter.atTop (nhds 0) := by
  -- The function (c*x)² + 2(c*x) + 2 grows polynomially in c*x; multiplied
  -- by exp(-(c*x)) it tends to 0 at +∞ (because c*x → +∞).
  have hcx : Filter.Tendsto (fun x : ℝ => c * x) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  -- Use `tendsto_pow_mul_exp_neg_atTop_nhds_zero` composed with c*x.
  have h1 : Filter.Tendsto (fun y : ℝ => y^2 * Real.exp (-y)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h2 : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y)) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 : Filter.Tendsto (fun y : ℝ => Real.exp (-y)) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero
  -- Compose each with cx → ∞.
  have H1 : Filter.Tendsto (fun x : ℝ => (c*x)^2 * Real.exp (-(c*x))) Filter.atTop (nhds 0) :=
    h1.comp hcx
  have H2 : Filter.Tendsto (fun x : ℝ => 2 * (c*x) * Real.exp (-(c*x))) Filter.atTop (nhds 0) := by
    have hh := h2.comp hcx
    have hhh := hh.const_mul (2 : ℝ)
    -- hhh : Tendsto (fun x => 2 * ((h2 ∘ cx) x)) = 2 * (c*x * exp(-(c*x)))
    have heq : (fun x : ℝ => 2 * (c * x) * Real.exp (-(c*x)))
        = fun x : ℝ => 2 * ((fun y : ℝ => y * Real.exp (-y)) (c * x)) := by
      funext x; ring
    rw [heq]
    simpa [Function.comp] using hhh
  have H3 : Filter.Tendsto (fun x : ℝ => 2 * Real.exp (-(c*x))) Filter.atTop (nhds 0) := by
    have := h3.comp hcx
    have := this.const_mul (2 : ℝ)
    simpa using this
  have Hsum : Filter.Tendsto
      (fun x : ℝ => ((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x)))
      Filter.atTop (nhds 0) := by
    have hpw : (fun x : ℝ => ((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x))) =
        (fun x : ℝ => (c*x)^2 * Real.exp (-(c*x))
                    + 2*(c*x) * Real.exp (-(c*x))
                    + 2 * Real.exp (-(c*x))) := by
      funext x; ring
    rw [hpw]
    have := (H1.add H2).add H3
    simpa using this
  -- Now negate and divide by c^3.
  have Hneg : Filter.Tendsto
      (fun x : ℝ => -(((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x))))
      Filter.atTop (nhds (0 : ℝ)) := by
    have := Hsum.neg
    simpa using this
  have Hdiv : Filter.Tendsto
      (fun x : ℝ => -(((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x))) / c^3)
      Filter.atTop (nhds ((0 : ℝ) / c^3)) := Hneg.div_const _
  have hzero : (0 : ℝ) / c^3 = 0 := by simp
  rw [hzero] at Hdiv
  -- Rewrite shape
  convert Hdiv using 1
  funext x; ring

/-- Integrability of `x² · exp(-c·x)` on `Ioi 0` for `c > 0`. -/
lemma integrableOn_xsq_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x^2 * Real.exp (-(c*x))) (Set.Ioi 0) := by
  -- Use `integrableOn_Ioi_deriv_of_nonneg` or direct dominated/integrable combo.
  -- Simpler: use `HasCompactSupport`? No. Use FTC approach:
  -- f' := x²·e^(-cx), F := primitive above. Integrability follows from
  -- `integrableOn_Ioi_deriv_of_nonneg'`.
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -((c*y)^2 + 2*(c*y) + 2) * Real.exp (-(c*y)) / c^3)
        (x^2 * Real.exp (-(c*x))) x := fun x _ => hasDerivAt_xsq_exp_neg_mul_primitive c hc x
  have hnn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ x^2 * Real.exp (-(c*x)) := by
    intro x _; exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hlim : Filter.Tendsto
      (fun x : ℝ => -((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x)) / c^3)
      Filter.atTop (nhds 0) := tendsto_xsq_primitive_atTop c hc
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim

/-- Closed-form value: `∫_{Ioi 0} x² · exp(-c·x) dx = 2/c³` for `c > 0`. -/
lemma integral_xsq_exp_neg_mul_Ioi (c : ℝ) (hc : 0 < c) :
    ∫ x in Set.Ioi (0 : ℝ), x^2 * Real.exp (-(c*x)) = 2 / c^3 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -((c*y)^2 + 2*(c*y) + 2) * Real.exp (-(c*y)) / c^3)
        (x^2 * Real.exp (-(c*x))) x := fun x _ => hasDerivAt_xsq_exp_neg_mul_primitive c hc x
  have hint : IntegrableOn (fun x : ℝ => x^2 * Real.exp (-(c*x))) (Set.Ioi 0) :=
    integrableOn_xsq_exp_neg_mul c hc
  have hlim : Filter.Tendsto
      (fun x : ℝ => -((c*x)^2 + 2*(c*x) + 2) * Real.exp (-(c*x)) / c^3)
      Filter.atTop (nhds 0) := tendsto_xsq_primitive_atTop c hc
  have hEq := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  -- hEq : ∫ x in Ioi 0, x^2 * exp(-(c*x)) = 0 - (primitive at 0) = 2/c^3
  rw [hEq]
  have hc3 : c^3 ≠ 0 := pow_ne_zero _ hc.ne'
  simp
  field_simp

/-! ### Termwise expansion of `x²/(1+eˣ)` -/

/-- For `x > 0`, the geometric series `Σ_{k≥0} (-e^(-x))^k` sums to `1/(1+e^(-x))`. -/
lemma hasSum_alt_exp_neg {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => (-1 : ℝ)^k * Real.exp (-((k+1 : ℕ) * x)))
      (1 / (1 + Real.exp x)) := by
  -- Set r := -exp(-x), |r| < 1; Σ r^k = 1/(1-r) = 1/(1+exp(-x)) = exp(x)/(exp(x)+1).
  -- We want Σ (-1)^k exp(-(k+1)x) = exp(-x) · Σ (-exp(-x))^k = exp(-x)/(1+exp(-x)) = 1/(1+exp(x)).
  set r : ℝ := -Real.exp (-x) with hr_def
  have hexp_pos : 0 < Real.exp (-x) := Real.exp_pos _
  have hexp_lt_one : Real.exp (-x) < 1 := by
    have : Real.exp (-x) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    simpa using this
  have hr_abs : |r| < 1 := by
    rw [hr_def]; rw [abs_neg, abs_of_pos hexp_pos]; exact hexp_lt_one
  have hgeom : HasSum (fun k : ℕ => r^k) (1 / (1 - r)) := by
    have := hasSum_geometric_of_abs_lt_one hr_abs
    simpa [div_eq_inv_mul, one_div] using this
  -- Multiply by exp(-x):
  have hscaled : HasSum (fun k : ℕ => Real.exp (-x) * r^k) (Real.exp (-x) * (1 / (1 - r))) :=
    hgeom.mul_left (Real.exp (-x))
  -- Simplify RHS: exp(-x) / (1 - (-exp(-x))) = exp(-x) / (1 + exp(-x)) = 1 / (1 + exp(x)).
  have hden_pos : 0 < 1 + Real.exp (-x) := one_add_exp_neg_pos x
  have hrhs : Real.exp (-x) * (1 / (1 - r)) = 1 / (1 + Real.exp x) := by
    rw [hr_def]
    have hexp_mul : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    have h1 : 1 - -Real.exp (-x) = 1 + Real.exp (-x) := by ring
    rw [h1, mul_one_div]
    rw [div_eq_div_iff hden_pos.ne' (one_add_exp_pos x).ne']
    -- Goal: exp(-x) * (1 + exp x) = 1 * (1 + exp(-x))
    -- exp(-x) + exp(-x)*exp(x) = 1 + exp(-x); using hexp_mul:
    rw [mul_add, hexp_mul, mul_one, one_mul]; ring
  rw [hrhs] at hscaled
  -- Rewrite exp(-x) * r^k = exp(-x) * (-exp(-x))^k = (-1)^k * exp(-x)^(k+1) = (-1)^k * exp(-(k+1)x)
  have heq : ∀ k : ℕ, Real.exp (-x) * r^k = (-1 : ℝ)^k * Real.exp (-((k+1 : ℕ) * x)) := by
    intro k
    -- (-exp(-x))^k = (-1)^k * exp(-x)^k
    have h1 : r^k = (-1 : ℝ)^k * Real.exp (-x)^k := by
      rw [hr_def, neg_eq_neg_one_mul, mul_pow]
    -- exp(-x) * r^k = (-1)^k * exp(-x)^(k+1)
    have h2 : Real.exp (-x) * r^k = (-1 : ℝ)^k * Real.exp (-x)^(k+1) := by
      rw [h1]; ring
    -- exp(-x)^(k+1) = exp(-((k+1)·x))
    have h3 : Real.exp (-x)^(k+1) = Real.exp (-((k+1 : ℕ) * x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast; ring
    rw [h2, h3]
  -- Apply the rewrite to hscaled
  have : (fun k : ℕ => Real.exp (-x) * r^k) = fun k : ℕ => (-1 : ℝ)^k * Real.exp (-((k+1 : ℕ) * x)) :=
    funext heq
  rw [this] at hscaled
  exact hscaled

/-- The pointwise expansion: for `x > 0`,
`x² / (1 + eˣ) = Σ_{k≥0} (-1)^k · x² · e^(-(k+1)·x)`. -/
lemma hasSum_xsq_fermi {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x)))
      (x^2 / (1 + Real.exp x)) := by
  have hbase := hasSum_alt_exp_neg hx
  -- Multiply by x² on the left
  have := hbase.mul_left (x^2)
  -- this : HasSum (fun k => x^2 * ((-1)^k * exp(-(k+1)*x))) (x^2 * (1/(1+exp x)))
  have heq : (fun k : ℕ => x^2 * ((-1 : ℝ)^k * Real.exp (-((k+1 : ℕ) * x))))
      = fun k : ℕ => (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x)) := by
    funext k; ring
  rw [heq] at this
  have hrhs : x^2 * (1 / (1 + Real.exp x)) = x^2 / (1 + Real.exp x) := by
    rw [mul_one_div]
  rw [hrhs] at this
  exact this

/-- `(-1)^k · x^2 · e^(-(k+1)·x)` is integrable on `Ioi 0` for every `k : ℕ`. -/
lemma integrableOn_termwise (k : ℕ) :
    IntegrableOn (fun x : ℝ => (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))) (Set.Ioi 0) := by
  have hkp : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hbase := integrableOn_xsq_exp_neg_mul ((k+1 : ℕ) : ℝ) hkp
  have hconst := hbase.const_mul ((-1 : ℝ)^k)
  have heq : (fun x : ℝ => (-1 : ℝ)^k * (x^2 * Real.exp (-(((k+1 : ℕ) : ℝ) * x))))
      = fun x : ℝ => (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x)) := by
    funext x; ring
  rw [heq] at hconst
  exact hconst

/-- Integral of the k-th term on `(0, ∞)`: `(-1)^k · 2/(k+1)^3`. -/
lemma integral_termwise (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))
      = (-1 : ℝ)^k * (2 / ((k+1 : ℕ) : ℝ)^3) := by
  have hkp : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hbase := integral_xsq_exp_neg_mul_Ioi ((k+1 : ℕ) : ℝ) hkp
  have heq1 : (fun x : ℝ => (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x)))
      = fun x : ℝ => (-1 : ℝ)^k * (x^2 * Real.exp (-((k+1 : ℕ) * x))) := by
    funext x; ring
  rw [heq1]
  rw [MeasureTheory.integral_const_mul]
  rw [hbase]

/-- `|(-1)^k · x² · e^(-(k+1)·x)| = x² · e^(-(k+1)·x)`. -/
lemma norm_termwise_eq (k : ℕ) (x : ℝ) :
    ‖(-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))‖
      = x^2 * Real.exp (-((k+1 : ℕ) * x)) := by
  rw [Real.norm_eq_abs]
  rw [show (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))
        = (-1 : ℝ)^k * (x^2 * Real.exp (-((k+1 : ℕ) * x))) by ring]
  rw [abs_mul]
  rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]

/-- `∫_{Ioi 0} |(-1)^k · x² · e^(-(k+1)x)| = 2/(k+1)^3`. -/
lemma integral_norm_termwise (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), ‖(-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))‖
      = 2 / ((k+1 : ℕ) : ℝ)^3 := by
  have heq : (fun x : ℝ => ‖(-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))‖)
      = fun x : ℝ => x^2 * Real.exp (-((k+1 : ℕ) * x)) := by
    funext x; exact norm_termwise_eq k x
  rw [heq]
  have hkp : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  exact integral_xsq_exp_neg_mul_Ioi ((k+1 : ℕ) : ℝ) hkp

/-- Summability of `Σ 1/(k+1)^3`. -/
lemma summable_one_div_succ_cube :
    Summable (fun k : ℕ => 1 / ((k + 1 : ℝ) ^ 3)) := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
  have := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ 3)) 1).mpr h
  convert this using 1
  funext k
  push_cast; ring

/-- Summability of `Σ 2/(k+1)^3`. -/
lemma summable_two_div_succ_cube :
    Summable (fun k : ℕ => 2 / ((k + 1 : ℝ) ^ 3)) := by
  have := summable_one_div_succ_cube.mul_left (2 : ℝ)
  convert this using 1
  funext k; ring

/-- `∫_{Ioi 0} x²/(1+eˣ) dx = Σ_{k≥0} (-1)^k · 2/(k+1)^3`. -/
lemma integral_fermi_Ioi_eq_tsum :
    ∫ x in Set.Ioi (0 : ℝ), x^2 / (1 + Real.exp x)
      = ∑' k : ℕ, (-1 : ℝ)^k * (2 / ((k+1 : ℕ) : ℝ)^3) := by
  -- Define F k x := (-1)^k · x² · e^(-(k+1)·x).
  set F : ℕ → ℝ → ℝ := fun k x => (-1 : ℝ)^k * x^2 * Real.exp (-((k+1 : ℕ) * x))
  -- (1) F k is integrable on Ioi 0 for every k.
  have hF_int : ∀ k, IntegrableOn (F k) (Set.Ioi 0) := integrableOn_termwise
  -- (2) Σ_k ∫ |F k| is summable (= Σ 2/(k+1)^3).
  have hF_sum : Summable (fun k => ∫ x in Set.Ioi (0 : ℝ), ‖F k x‖) := by
    have heq : (fun k => ∫ x in Set.Ioi (0 : ℝ), ‖F k x‖)
        = fun k : ℕ => 2 / ((k+1 : ℕ) : ℝ)^3 := by
      funext k; exact integral_norm_termwise k
    rw [heq]
    -- Summable (fun k => 2 / ((k+1 : ℕ) : ℝ)^3) — identify the casts
    have hs := summable_two_div_succ_cube
    convert hs using 1
    funext k; push_cast; ring
  -- (3) Apply hasSum_integral_of_summable_integral_norm, restricted to Ioi 0.
  -- We need F k : ℝ → ℝ viewed under measure μ = volume.restrict (Ioi 0).
  -- Use `MeasureTheory.hasSum_integral_of_summable_integral_norm` with
  -- μ := volume.restrict (Set.Ioi 0) and α := ℝ.
  have h_meas_int : ∀ k : ℕ, Integrable (F k) (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    intro k
    exact hF_int k
  have h_meas_sum : Summable
      (fun k : ℕ => ∫ x, ‖F k x‖ ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))) := by
    -- same as hF_sum by rewriting integral-on-set as integral w.r.t. restricted measure
    exact hF_sum
  -- Apply the theorem
  have hhs := MeasureTheory.hasSum_integral_of_summable_integral_norm h_meas_int h_meas_sum
  -- hhs : HasSum (fun k => ∫ x, F k x ∂(...restrict Ioi 0)) (∫ x, (∑' k, F k x) ∂(...restrict))
  -- Simplify: ∫ x, f(x) ∂(vol.restrict S) = ∫ x in S, f(x) (by definition).
  -- ∑' k, ∫ x in Ioi 0, F k x = ∫ x in Ioi 0, ∑' k, F k x.
  have htsum := hhs.tsum_eq
  -- Evaluate ∑' k, ∫ x in Ioi 0, F k x = ∑' k, (-1)^k * 2/(k+1)^3
  have hLHS_eq : (fun k : ℕ => ∫ x, F k x ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))))
      = fun k : ℕ => (-1 : ℝ)^k * (2 / ((k+1 : ℕ) : ℝ)^3) := by
    funext k
    have : ∫ x, F k x ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        = ∫ x in Set.Ioi (0:ℝ), F k x := rfl
    rw [this]
    exact integral_termwise k
  -- Evaluate ∫ x in Ioi 0, ∑' k, F k x:
  -- For x > 0, ∑' k, F k x = x² / (1 + exp x); for x ≤ 0 it could be anything,
  -- but Ioi 0 excludes that set so it suffices to rewrite on Ioi 0.
  -- Use setIntegral_congr_fun.
  have hRHS_eq : ∫ x, (∑' k, F k x) ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
      = ∫ x in Set.Ioi (0 : ℝ), x^2 / (1 + Real.exp x) := by
    have : ∫ x, (∑' k, F k x) ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        = ∫ x in Set.Ioi (0:ℝ), ∑' k, F k x := rfl
    rw [this]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    exact (hasSum_xsq_fermi hx').tsum_eq
  -- Combine:
  -- htsum : ∑' k, ∫ x, F k x ∂μ = ∫ x, ∑' k, F k x ∂μ, where μ = vol.restrict (Ioi 0)
  rw [hLHS_eq] at htsum
  rw [hRHS_eq] at htsum
  exact htsum.symm

/-! ### Even-odd decomposition of the alternating ζ(3)-like series -/

/-- Even/odd decomposition: `Σ (-1)^k · f(k) = Σ f(2k) - Σ f(2k+1)` when both RHS sums converge
    and the alternating series converges. We state for `f n = 2/(n+1)^3`. -/
lemma alt_sum_eq_three_quarter_zeta :
    ∑' k : ℕ, (-1 : ℝ)^k * (2 / ((k+1 : ℕ) : ℝ)^3)
      = (3/2 : ℝ) * ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) := by
  -- Define a k := 2/(k+1)^3. Then Σ(-1)^k a k = Σ a(2k) - Σ a(2k+1).
  -- And Σ a(2k) = Σ 2/(2k+1)^3 = (odd part); Σ a(2k+1) = Σ 2/(2k+2)^3 = (1/4) Σ 1/(k+1)^3.
  -- Claim: Σ a(2k) + Σ a(2k+1) = Σ a(k) = Σ 2/(k+1)^3 = 2 · ζ(3).
  -- Σ a(2k+1) = (1/4) · ζ(3).
  -- So Σ a(2k) = 2ζ(3) − (1/4)ζ(3) = (7/4)ζ(3).
  -- Hence Σ (-1)^k a(k) = (7/4)ζ(3) − (1/4)ζ(3) = (3/2)ζ(3). ✓
  set ζ : ℝ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) with hζ_def
  set a : ℕ → ℝ := fun k => 2 / ((k+1 : ℕ) : ℝ)^3 with ha_def
  -- Sanity: a k ≥ 0
  have ha_nn : ∀ k, 0 ≤ a k := by
    intro k; simp only [a]
    apply div_nonneg (by norm_num)
    positivity
  -- Summability of a (Σ 2/(k+1)^3).
  have ha_sum : Summable a := by
    simp only [a]
    have := summable_two_div_succ_cube
    convert this using 1; funext k; push_cast; ring
  -- ∑ a = 2 · ζ
  have ha_tsum : ∑' k, a k = 2 * ζ := by
    show (∑' k : ℕ, 2 / ((k+1 : ℕ) : ℝ)^3) = 2 * ζ
    simp only [ζ]
    rw [← tsum_mul_left]
    congr 1; funext k; push_cast; ring
  -- Summability of a(2k+1):
  have ha_odd_sum : Summable (fun k => a (2 * k + 1)) := by
    apply ha_sum.comp_injective
    intros i j h
    have : 2 * i + 1 = 2 * j + 1 := h
    omega
  -- Summability of a(2k):
  have ha_even_sum : Summable (fun k => a (2 * k)) := by
    apply ha_sum.comp_injective
    intros i j h
    have : 2 * i = 2 * j := h
    omega
  -- a(2k+1) = 2/(2k+2)^3 = (1/4) · 1/(k+1)^3
  have ha_odd_eq : ∀ k : ℕ, a (2 * k + 1) = (1/4 : ℝ) * (1 / ((k + 1 : ℝ)^3)) := by
    intro k
    simp only [a]
    have hk1 : ((2 * k + 1 + 1 : ℕ) : ℝ) = 2 * (k + 1) := by push_cast; ring
    rw [hk1]
    rw [mul_pow]
    have h2pow : (2 : ℝ)^3 = 8 := by norm_num
    rw [h2pow]
    have hk1ne : ((k : ℝ) + 1)^3 ≠ 0 := by
      apply pow_ne_zero
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      linarith
    field_simp
    ring
  have ha_odd_tsum : ∑' k, a (2 * k + 1) = (1/4 : ℝ) * ζ := by
    simp only [ζ]
    rw [← tsum_mul_left]
    congr 1; funext k
    exact ha_odd_eq k
  -- From ∑ a(even) + ∑ a(odd) = ∑ a:
  have htotal : ∑' k, a (2 * k) + ∑' k, a (2 * k + 1) = ∑' k, a k := by
    exact tsum_even_add_odd ha_even_sum ha_odd_sum
  have ha_even_tsum : ∑' k, a (2 * k) = 2 * ζ - (1/4 : ℝ) * ζ := by
    have := htotal
    rw [ha_tsum, ha_odd_tsum] at this
    linarith
  -- Summability of (-1)^k * a k
  have halt_sum : Summable (fun k => (-1 : ℝ)^k * a k) := by
    have := ha_sum.abs
    have := Summable.alternating (by
      -- Summable.alternating takes Summable f and produces Summable (fun n => (-1)^n * f n)
      exact ha_sum)
    -- Hmm actually Summable.alternating gives (-1)^n * f n — that's what we want!
    exact this
  -- ∑ (-1)^k * a k = Σ a(2k) - Σ a(2k+1)
  have halt_split :
      ∑' k, (-1 : ℝ)^k * a k = ∑' k, a (2 * k) - ∑' k, a (2 * k + 1) := by
    -- Use tsum_even_add_odd on the function b k := (-1)^k * a k.
    set b : ℕ → ℝ := fun k => (-1 : ℝ)^k * a k with hb_def
    have hb_even : ∀ k, b (2 * k) = a (2 * k) := by
      intro k; simp only [b]
      rw [show (-1 : ℝ)^(2*k) = 1 from by
        rw [pow_mul]; simp]
      ring
    have hb_odd : ∀ k, b (2 * k + 1) = -(a (2 * k + 1)) := by
      intro k; simp only [b]
      rw [show (-1 : ℝ)^(2*k+1) = -1 from by
        rw [pow_succ, pow_mul]; simp]
      ring
    have hb_even_sum : Summable (fun k => b (2 * k)) := by
      have heq : (fun k => b (2 * k)) = fun k => a (2 * k) := by funext k; exact hb_even k
      rw [heq]; exact ha_even_sum
    have hb_odd_sum : Summable (fun k => b (2 * k + 1)) := by
      have heq : (fun k => b (2 * k + 1)) = fun k => -(a (2 * k + 1)) := by
        funext k; exact hb_odd k
      rw [heq]; exact ha_odd_sum.neg
    have hb_total : ∑' k, b (2 * k) + ∑' k, b (2 * k + 1) = ∑' k, b k :=
      tsum_even_add_odd hb_even_sum hb_odd_sum
    have hb_even_tsum : ∑' k, b (2 * k) = ∑' k, a (2 * k) := by
      congr 1; funext k; exact hb_even k
    have hb_odd_tsum : ∑' k, b (2 * k + 1) = -∑' k, a (2 * k + 1) := by
      rw [← tsum_neg]
      congr 1; funext k; exact hb_odd k
    rw [hb_even_tsum, hb_odd_tsum] at hb_total
    -- hb_total : Σ a(2k) + (- Σ a(2k+1)) = Σ b k
    linarith [hb_total]
  -- Combine:
  -- LHS: ∑ (-1)^k * a k = Σa(2k) − Σa(2k+1) = (2ζ - ζ/4) − ζ/4 = (3/2)ζ
  -- The goal has form: Σ (-1)^k * a k = (3/2)·ζ
  -- We need to match the goal form with `a`.
  show ∑' k : ℕ, (-1 : ℝ)^k * (2 / ((k+1 : ℕ) : ℝ)^3) = (3/2 : ℝ) * ζ
  have hrewrite : (fun k : ℕ => (-1 : ℝ)^k * (2 / ((k+1 : ℕ) : ℝ)^3))
      = fun k : ℕ => (-1 : ℝ)^k * a k := by
    funext k; rfl
  rw [hrewrite, halt_split, ha_even_tsum, ha_odd_tsum]
  ring

/-- `∫_{Ioi 0} x²/(1+eˣ) dx = (3/2) · ζ(3)`. -/
lemma integral_fermi_Ioi :
    ∫ x in Set.Ioi (0 : ℝ), x^2 / (1 + Real.exp x)
      = (3/2 : ℝ) * ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) := by
  rw [integral_fermi_Ioi_eq_tsum, alt_sum_eq_three_quarter_zeta]

/-- The integrand `x²/(1+eˣ)` is integrable on `Ioi 0`. -/
lemma integrableOn_fermi_Ioi :
    IntegrableOn (fun x : ℝ => x^2 / (1 + Real.exp x)) (Set.Ioi 0) := by
  -- Dominate by x² · e^(-x) which is integrable on Ioi 0.
  have hdom : IntegrableOn (fun x : ℝ => x^2 * Real.exp (-x)) (Set.Ioi 0) := by
    have hbase := integrableOn_xsq_exp_neg_mul 1 (by norm_num : (0:ℝ) < 1)
    have heq : (fun x : ℝ => x^2 * Real.exp (-(1 * x))) = fun x => x^2 * Real.exp (-x) := by
      funext x; congr 1; rw [one_mul]
    rw [heq] at hbase; exact hbase
  -- Use Integrable.mono or equivalent
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · -- AEStronglyMeasurable on Ioi 0
    exact continuous_fermiIntegrand.aestronglyMeasurable.restrict
  · -- ‖f x‖ ≤ x²·e^(-x)
    filter_upwards with x
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (fermiIntegrand_nonneg x)]
    exact fermiIntegrand_le_exp_neg x

theorem fermi_integral_eq_zeta3 :
    Filter.Tendsto
      (fun t : ℝ => (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x))
      Filter.atTop
      (nhds (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))) := by
  -- Step 1: ∫₀..t → ∫_{Ioi 0} as t → ∞.
  have hbase : Filter.Tendsto
      (fun t : ℝ => ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x))
      Filter.atTop (nhds (∫ x in Set.Ioi (0:ℝ), x^2 / (1 + Real.exp x))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 integrableOn_fermi_Ioi
      Filter.tendsto_id
  -- Step 2: ∫_{Ioi 0} x²/(1+eˣ) = (3/2)·ζ(3), so (2/3)·∫ → (2/3)·(3/2)·ζ(3) = ζ(3).
  have hscale := hbase.const_mul (2/3 : ℝ)
  rw [integral_fermi_Ioi] at hscale
  have heq : (2/3 : ℝ) * ((3/2 : ℝ) * ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))
      = ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) := by ring
  rw [heq] at hscale
  exact hscale

/-- The PIVP output S converges to ζ(3) directly (no trailing
    rational scaling needed — the factor 2/3 was absorbed into Ṡ). -/
theorem apery_fermi_is_crn_computable :
    fermiPIVP.Computes fermiSolution (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) := by
  show Filter.Tendsto (fun t => fermiSolution.trajectory t fermiPIVP.output) Filter.atTop _
  have houtput : fermiPIVP.output = sIdx := rfl
  rw [houtput]
  have hfun : (fun t => fermiSolution.trajectory t sIdx) =
      (fun t : ℝ => (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x)) := by
    funext t
    exact fermiTrajectory_s t
  rw [hfun]
  exact fermi_integral_eq_zeta3

/-! ## Why this is the real-time candidate

  Modulus bound from numerical data (`experiments/apery_fermi_5var.py`):
      |S(t) − (3/2)·ζ(3)| ≤ C · t² · e^(-t)
  so for target precision 2^(-r) the required time is O(r), i.e.
  μ(r) = Θ(r), the first-floor (real-time) class. A formal proof of
  this bound reduces to the Fermi-Dirac tail estimate
      |∫ₜ^∞ x²/(1+eˣ) dx| ≤ (t² + 2t + 2) · e^(-t) / (1 + e^(-t))
  which is elementary (bound 1/(1+eˣ) ≤ e^(-x) on [t,∞) and
  integrate ∫ₜ^∞ x²·e^(-x) dx by parts twice). -/

/-- Helper: the indefinite integral `∫₀ᵗ x²·e^(-x) dx` equals `2 − (t²+2t+2)·e^(-t)`. -/
lemma integral_xsq_exp_neg (t : ℝ) :
    ∫ x in (0 : ℝ)..t, x^2 * Real.exp (-x) = 2 - (t^2 + 2*t + 2) * Real.exp (-t) := by
  have hprim : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -(y^2 + 2*y + 2) * Real.exp (-y)) (x^2 * Real.exp (-x)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => -(y^2 + 2*y + 2)) (-(2*x + 2)) x := by
      have h1 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have h2 : HasDerivAt (fun y : ℝ => 2*y) (2 : ℝ) x := by
        have := (hasDerivAt_id x).const_mul 2
        simpa using this
      have hs : HasDerivAt (fun y : ℝ => y^2 + 2*y + 2) (2*x + 2) x := by
        have := (h1.add h2).add_const (2 : ℝ)
        simpa using this
      exact hs.neg
    have he := hasDerivAt_a x
    have := hp.mul he
    convert this using 1
    ring
  have hi : ∫ x in (0 : ℝ)..t, x^2 * Real.exp (-x) =
      (-(t^2 + 2*t + 2) * Real.exp (-t)) - (-(0^2 + 2*0 + 2) * Real.exp (-0)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intros x _; exact hprim x
    · exact (Continuous.intervalIntegrable (by continuity) _ _)
  rw [hi]; simp [Real.exp_zero]; ring

/-- The scaled integral `S(t) = (2/3)·∫₀ᵗ` is monotonically nondecreasing on `[0, ∞)`. -/
lemma fermi_S_monotone_on_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (2/3 : ℝ) * ∫ x in (0 : ℝ)..a, x^2 / (1 + Real.exp x)
      ≤ (2/3 : ℝ) * ∫ x in (0 : ℝ)..b, x^2 / (1 + Real.exp x) := by
  have hb : 0 ≤ b := le_trans ha hab
  have h1 : (0 : ℝ) ≤ 2/3 := by norm_num
  apply mul_le_mul_of_nonneg_left _ h1
  -- ∫₀^b = ∫₀^a + ∫_a^b, and ∫_a^b ≥ 0
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := a) (c := b)
    (continuous_fermiIntegrand.intervalIntegrable _ _)
    (continuous_fermiIntegrand.intervalIntegrable _ _)]
  have : 0 ≤ ∫ x in a..b, x^2 / (1 + Real.exp x) :=
    intervalIntegral.integral_nonneg hab (fun x _ => fermiIntegrand_nonneg x)
  linarith

/-- Bound on the distance between the scaled integral and its limit. -/
lemma fermi_distance_to_limit (t : ℝ) (ht : 0 ≤ t) :
    (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))
      - ((2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x))
      ≤ (2/3 : ℝ) * ((t^2 + 2*t + 2) * Real.exp (-t)) := by
  -- For any T ≥ t, (2/3)·∫_t^T x²/(1+eˣ)dx ≤ (2/3)·∫_t^T x²·e^(-x)dx
  -- = (2/3)·[(t²+2t+2)e^(-t) − (T²+2T+2)e^(-T)] ≤ (2/3)·(t²+2t+2)e^(-t).
  -- Taking limsup over T, by Sorry 3 the LHS → ζ(3) − S(t).
  set S := fun u : ℝ => (2/3 : ℝ) * ∫ x in (0 : ℝ)..u, x^2 / (1 + Real.exp x) with hS_def
  set ζ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) with hζ_def
  have htendsto : Filter.Tendsto S Filter.atTop (nhds ζ) := fermi_integral_eq_zeta3
  -- For T ≥ t: S(T) - S(t) ≤ (2/3)·(t²+2t+2)·e^(-t) - (2/3)·(T²+2T+2)·e^(-T)
  --                      ≤ (2/3)·(t²+2t+2)·e^(-t)
  have key : ∀ T ≥ t, S T - S t ≤ (2/3 : ℝ) * ((t^2 + 2*t + 2) * Real.exp (-t)) := by
    intro T hT
    have hT_nonneg : 0 ≤ T := le_trans ht hT
    -- S T - S t = (2/3)·∫_t^T x²/(1+eˣ)dx
    have h1 : S T - S t = (2/3 : ℝ) * ∫ x in t..T, x^2 / (1 + Real.exp x) := by
      simp only [hS_def]
      rw [← mul_sub]
      congr 1
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (continuous_fermiIntegrand.intervalIntegrable 0 t)
        (continuous_fermiIntegrand.intervalIntegrable t T)]
      ring
    rw [h1]
    -- ∫_t^T x²/(1+eˣ) ≤ ∫_t^T x²·e^(-x)
    have hmono : ∫ x in t..T, x^2 / (1 + Real.exp x) ≤ ∫ x in t..T, x^2 * Real.exp (-x) := by
      apply intervalIntegral.integral_mono_on hT
      · exact continuous_fermiIntegrand.intervalIntegrable _ _
      · exact (Continuous.intervalIntegrable (by continuity) _ _)
      · intros x _; exact fermiIntegrand_le_exp_neg x
    have hT_eq : ∫ x in t..T, x^2 * Real.exp (-x) =
        (2 - (T^2 + 2*T + 2) * Real.exp (-T)) - (2 - (t^2 + 2*t + 2) * Real.exp (-t)) := by
      rw [← integral_xsq_exp_neg T, ← integral_xsq_exp_neg t]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (a := 0) (b := t) (c := T)
        ((by continuity : Continuous _).intervalIntegrable _ _)
        ((by continuity : Continuous _).intervalIntegrable _ _)]
      ring
    have hT_bound : ∫ x in t..T, x^2 * Real.exp (-x) ≤ (t^2 + 2*t + 2) * Real.exp (-t) := by
      rw [hT_eq]
      have hpos : 0 ≤ (T^2 + 2*T + 2) * Real.exp (-T) := by
        apply mul_nonneg
        · nlinarith
        · exact (Real.exp_pos _).le
      linarith
    have h23 : (0 : ℝ) ≤ 2/3 := by norm_num
    calc (2/3 : ℝ) * ∫ x in t..T, x^2 / (1 + Real.exp x)
        ≤ (2/3 : ℝ) * ∫ x in t..T, x^2 * Real.exp (-x) :=
          mul_le_mul_of_nonneg_left hmono h23
      _ ≤ (2/3 : ℝ) * ((t^2 + 2*t + 2) * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_left hT_bound h23
  -- Take T → ∞: LHS → ζ - S(t)
  have hdiff : Filter.Tendsto (fun T => S T - S t) Filter.atTop (nhds (ζ - S t)) := by
    exact htendsto.sub tendsto_const_nhds
  -- Apply `le_of_tendsto` with eventually bound
  apply le_of_tendsto hdiff
  filter_upwards [Filter.eventually_ge_atTop t] with T hT
  exact key T hT

/-- Real-time modulus bound: target precision 2^(-r) requires
    integration time O(r). Stated for the (2/3)-scaled form so the target
    constant is ζ(3). -/
theorem fermi_realtime_modulus :
    ∃ C > 0, ∀ t ≥ (1 : ℝ),
      |((2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x))
          - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))|
        ≤ C * (t^2 + 2*t + 2) * Real.exp (-t) := by
  refine ⟨(2/3 : ℝ), by norm_num, ?_⟩
  intros t ht
  have ht0 : (0 : ℝ) ≤ t := by linarith
  set S := (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) with hS_def
  set ζ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) with hζ_def
  -- |S - ζ| ≤ ζ - S (since S ≤ ζ via monotonicity + convergence)
  -- and ζ - S ≤ (2/3)·(t²+2t+2)·e^(-t)
  have h_upper : ζ - S ≤ (2/3 : ℝ) * ((t^2 + 2*t + 2) * Real.exp (-t)) :=
    fermi_distance_to_limit t ht0
  -- Also S ≤ ζ. Proof: S is monotone and tends to ζ; so S(t) ≤ ζ for all t.
  have h_S_le_ζ : S ≤ ζ := by
    have htendsto : Filter.Tendsto (fun u => (2/3 : ℝ) * ∫ x in (0 : ℝ)..u, x^2 / (1 + Real.exp x))
        Filter.atTop (nhds ζ) := fermi_integral_eq_zeta3
    apply ge_of_tendsto htendsto
    filter_upwards [Filter.eventually_ge_atTop t] with T hT
    exact fermi_S_monotone_on_nonneg ht0 hT
  have h_abs : |S - ζ| = ζ - S := by
    rw [abs_of_nonpos (by linarith)]; ring
  rw [h_abs]
  have : (2/3 : ℝ) * (t^2 + 2*t + 2) * Real.exp (-t) =
      (2/3 : ℝ) * ((t^2 + 2*t + 2) * Real.exp (-t)) := by ring
  linarith

/-! ## The certified real-time computation of ζ(3)

The record `fermiPIVP` above has a real-valued field. Here the same system is written
syntactically, as a `PolyPIVP` with `MvPolynomial (Fin 5) ℚ` components and rational initial
value (1, 0, 0, 1/2, 0); its evaluated field is `fermiField` (`fermiPolyPIVP_evalField`), so
`fermiTrajectory` solves it. The error bound `|S(t) − ζ(3)| ≤ (16/3)e^(−t/2)` for `t ≥ 0`
gives the linear modulus `μ(r) = 2r + 6`, i.e. ζ(3) is real-time computable in the sense of
`IsRealTimeComputable` ([BAC] Def 2.1 + Def 2.3, [RTCRN2] §3). -/

open MvPolynomial in
/-- The Fermi field as ℚ-polynomials: `ȧ = −a`, `ḃ = a − b`, `ċ = 2b − c`, `q̇ = a q²`,
`Ṡ = (2/3) c q`. -/
noncomputable def fermiPolyField : Fin fermiDim → MvPolynomial (Fin fermiDim) ℚ :=
  ![-X aIdx, X aIdx - X bIdx, C (2 : ℚ) * X bIdx - X cIdx, X aIdx * X qIdx ^ 2,
    C (2/3 : ℚ) * (X cIdx * X qIdx)]

/-- The Fermi system as a syntactic `PolyPIVP`: field `fermiPolyField`, rational initial value
(1, 0, 0, 1/2, 0), output `S`. -/
noncomputable def fermiPolyPIVP : PolyPIVP fermiDim where
  field := fermiPolyField
  init := ![1, 0, 0, 1/2, 0]
  output := sIdx

/-- The evaluated polynomial field is the semantic Fermi field. -/
theorem fermiPolyPIVP_evalField (y : Fin fermiDim → ℝ) :
    fermiPolyPIVP.evalField y = fermiField y := by
  funext i
  fin_cases i <;>
    simp [PolyPIVP.evalField, fermiPolyPIVP, fermiPolyField, fermiField,
      aIdx, bIdx, cIdx, qIdx, sIdx]

/-- The semantic initial value of `fermiPolyPIVP` is `fermiInit`. -/
theorem fermiPolyPIVP_init : fermiPolyPIVP.toPIVP.init = fermiInit := by
  funext i
  fin_cases i <;>
    simp [PolyPIVP.toPIVP, fermiPolyPIVP, fermiInit, aIdx, bIdx, cIdx, qIdx, sIdx]

/-- The closed-form trajectory as a solution of the syntactic system. -/
noncomputable def fermiPolySolution : PIVP.Solution fermiPolyPIVP.toPIVP where
  trajectory := fermiTrajectory
  init_cond := by rw [fermiPolyPIVP_init]; exact fermiTrajectory_init
  is_solution := fun t ht => by
    show HasDerivAt fermiTrajectory (fermiPolyPIVP.evalField (fermiTrajectory t)) t
    rw [fermiPolyPIVP_evalField]
    exact fermiTrajectory_is_solution t ht

/-- Exponential error bound: `|S(t) − ζ(3)| ≤ (16/3)·e^(−t/2)` for `t ≥ 0`. -/
theorem fermi_abs_sub_zeta3_le (t : ℝ) (ht : 0 ≤ t) :
    |(2/3 : ℝ) * (∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x))
        - ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)|
      ≤ (16/3 : ℝ) * Real.exp (-(t/2)) := by
  set S := (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x) with hS_def
  set ζ := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3) with hζ_def
  have h_upper : ζ - S ≤ (2/3 : ℝ) * ((t^2 + 2*t + 2) * Real.exp (-t)) :=
    fermi_distance_to_limit t ht
  have h_S_le_ζ : S ≤ ζ := by
    have htendsto : Filter.Tendsto
        (fun u => (2/3 : ℝ) * ∫ x in (0 : ℝ)..u, x^2 / (1 + Real.exp x))
        Filter.atTop (nhds ζ) := fermi_integral_eq_zeta3
    apply ge_of_tendsto htendsto
    filter_upwards [Filter.eventually_ge_atTop t] with T hT
    exact fermi_S_monotone_on_nonneg ht hT
  have hq : 1 + t/2 + (t/2)^2/2 ≤ Real.exp (t/2) :=
    Real.quadratic_le_exp_of_nonneg (by linarith)
  have hpoly : t^2 + 2*t + 2 ≤ 8 * Real.exp (t/2) := by nlinarith
  have hsplit : Real.exp (-t) = Real.exp (-(t/2)) * Real.exp (-(t/2)) := by
    rw [← Real.exp_add]; ring_nf
  have hmul : Real.exp (t/2) * Real.exp (-(t/2)) = 1 := by
    rw [← Real.exp_add]; simp
  have he : 0 ≤ Real.exp (-(t/2)) := (Real.exp_pos _).le
  have hE : (t^2 + 2*t + 2) * Real.exp (-t) ≤ 8 * Real.exp (-(t/2)) := by
    rw [hsplit]
    calc (t^2 + 2*t + 2) * (Real.exp (-(t/2)) * Real.exp (-(t/2)))
        = ((t^2 + 2*t + 2) * Real.exp (-(t/2))) * Real.exp (-(t/2)) := by ring
      _ ≤ ((8 * Real.exp (t/2)) * Real.exp (-(t/2))) * Real.exp (-(t/2)) := by
          gcongr
      _ = 8 * (Real.exp (t/2) * Real.exp (-(t/2))) * Real.exp (-(t/2)) := by ring
      _ = 8 * Real.exp (-(t/2)) := by rw [hmul]; ring
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The modulus `μ(r) = 2r + 6`: for `t > 2r + 6` the output is within `e^(−r)` of ζ(3). -/
theorem fermi_convergence (r : ℕ) (t : ℝ) (ht : t > 2 * (r : ℝ) + 6) :
    |fermiTrajectory t sIdx - ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)| < Real.exp (-(r : ℝ)) := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ht0 : 0 ≤ t := by linarith
  rw [fermiTrajectory_s]
  refine lt_of_le_of_lt (fermi_abs_sub_zeta3_le t ht0) ?_
  have h3 : (17/2 : ℝ) ≤ Real.exp 3 := by
    have := Real.quadratic_le_exp_of_nonneg (x := 3) (by norm_num)
    norm_num at this
    linarith
  have hlt : Real.exp (-(t/2)) < Real.exp (-(r : ℝ) - 3) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hsplit : Real.exp (-(r : ℝ) - 3) * Real.exp 3 = Real.exp (-(r : ℝ)) := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (-(r : ℝ) - 3)
  have hprod := mul_le_mul_of_nonneg_left h3 hpos.le
  nlinarith

/-- **ζ(3), certified.** A `CertifiedBoundedTimeComputable 5 ζ(3)` whose system is the
ℚ-polynomial Fermi system `fermiPolyPIVP` and whose modulus is `μ(r) = 2r + 6`. -/
theorem fermi_certifiedBoundedTimeComputable :
    ∃ btc : CertifiedBoundedTimeComputable fermiDim (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)),
      btc.pivp = fermiPolyPIVP ∧ ∀ r : ℕ, btc.modulus r = 2 * (r : ℝ) + 6 := by
  obtain ⟨btc, hP, hmod, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_solution
      (α := ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))
      fermiPolyPIVP fermiPolySolution fermiTrajectory_bounded
      (fun r => 2 * (r : ℝ) + 6) (fun r t ht => fermi_convergence r t ht)
  refine ⟨btc, hP, fun r => ?_⟩
  rw [hmod r]
  show max 0 (2 * (r : ℝ) + 6) = 2 * (r : ℝ) + 6
  exact max_eq_right (by positivity)

/-- **Apéry's constant ζ(3) = ∑ 1/(k+1)³ is real-time computable** ([BAC] Def 2.3 with a
linear modulus; the class `R_RTGPAC` of [RTCRN2] §3 by `isRealTimeComputable_iff_rtgpac`):
the 5-variable ℚ-polynomial Fermi system with rational initial value (1, 0, 0, 1/2, 0)
computes it with modulus `μ(r) = 2r + 6 ≤ 6(r + 1)`. -/
theorem apery_is_realtime :
    IsRealTimeComputable (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) := by
  obtain ⟨btc, -, hmod⟩ := fermi_certifiedBoundedTimeComputable
  refine ⟨fermiDim, btc, 6, by norm_num, fun r => ?_⟩
  rw [hmod r]
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  linarith

/-- ζ(3) is in the class R_RTGPAC of [RTCRN2] §3 in its literal form: a bounded PIVP with
integer coefficients and all initial values `0` whose output is within `2^{−t}` of ζ(3) for all
`t ≥ 1` (`isRealTimeComputable_iff_rtgpac`). -/
theorem apery_isRTGPACComputable :
    IsRTGPACComputable (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) :=
  isRealTimeComputable_iff_rtgpac.mp apery_is_realtime

end Number
end Ripple

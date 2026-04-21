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

  ## Why this might give first-floor

  Key advantages over Apery.lean's existing route:
  - All 5 state variables are bounded on [0,∞) by closed-form constants.
  - All initial values are rational (1, 0, 0, 1/2, 0) — no NTIVs, no e.
  - Polynomial RHS of degree ≤ 2.
  - Numerical convergence rate (verified in `experiments/apery_fermi_5var.py`):
      |S(t) − (3/2)ζ(3)| ≲ t² · e^(-t)
    i.e. modulus μ(r) = Θ(r), the real-time (first-floor) rate.

  ## Numerical verification

  `experiments/apery_fermi_5var.py` integrates this system with DOP853
  and confirms S(50) agrees with (3/2)·ζ(3) ≈ 1.803085354739391 to
  2.2e-15 (machine precision). Convergence ratio |err|/(t²e^(-t)) → 1.
-/

import Ripple.Core.PIVP
import Ripple.Core.CRNPipeline
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

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

/-! ## Main open goals (sorry list)

  The full proof that this PIVP is a valid CRN construction for ζ(3)
  decomposes into these obligations. Each is written as a `theorem` with
  a single `sorry` so the structure type-checks and we can see the
  remaining work.
-/

/-- **Sorry 1.** The closed-form trajectory satisfies the initial condition. -/
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

/-- **Sorry 4** (the mathematical heart). The (2/3)-scaled Fermi-Dirac
    integral evaluates to ζ(3) directly. The unscaled identity is classical:
        ∫₀^∞ x^(s-1) / (eˣ + 1) dx = Γ(s) · η(s),    η(s) = (1-2^(1-s))·ζ(s)
    with s = 3: Γ(3) = 2, η(3) = (3/4)·ζ(3), product = (3/2)·ζ(3).
    Multiplying by (2/3) lands exactly on ζ(3). Proof route: expand
    1/(1+eˣ) = Σ(-1)^k·e^(-(k+1)x), integrate termwise, use
    ∫₀^∞ x²·e^(-(k+1)x) dx = 2/(k+1)³. -/
theorem fermi_integral_eq_zeta3 :
    Filter.Tendsto
      (fun t : ℝ => (2/3 : ℝ) * ∫ x in (0 : ℝ)..t, x^2 / (1 + Real.exp x))
      Filter.atTop
      (nhds (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))) := by
  sorry

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

end Number
end Ripple
